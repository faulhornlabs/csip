{-# language ViewPatterns, BlockArguments #-}

import Circom
import MAlonzo.Code.CircomA
import Unsafe.Coerce

------------------------------------- Agda <-> Haskell conversion functions

showVar n = "v" ++ show n

trLin :: Lin -> Linear
trLin Z = MkLinear 0 []
trLin (LCons f n (trLin -> MkLinear c xs))
  | n == 0    = MkLinear (c + mkF f) xs
  | otherwise = MkLinear c ((mkF f, showVar n): xs)

getVal :: forall a. VVec -> [a]
getVal VNil = []
getVal (VCons f vs) = unsafeCoerce f: getVal vs

mkVec :: forall a. [a] -> VVec
mkVec [] = VNil
mkVec (f: fs) = VCons (unsafeCoerce f) (mkVec fs)

list :: forall a. List -> [a]
list Nil = []
list (Cons a as) = unsafeCoerce a: list as

getP (I p) = p
getP (O p) = p

mkP n p = [showVar n | p]

trCon :: Constr -> Constraint Lin
trCon (CstrEq  a b)   = CEq  (unsafeCoerce a) (unsafeCoerce b)
trCon (CstrMul a b c) = CMul (unsafeCoerce a) (unsafeCoerce b) (unsafeCoerce c)

showPublic True = "P"
showPublic False = "S"

instance Show Sig where
  show (I b) = "I" ++ showPublic b
  show (O b) = "O" ++ showPublic b

---------------------------------------------------------

runTest :: Circ -> [F] -> IO ()
runTest circ i = do
  putStrLn "---------------------------- publish"
  putStrLn $ "signature: " <> show s
  publishCircom cname tt
  putStrLn "---------------------------- make witness"
  print i
  putStrLn "  ==>"
  print witness
  putStrLn $ "output: " <> show [f | (O True, f) <- zip s witness]
  putStrLn "---------------------------- make proof"
  out <- runCircom cname inp
  putStrLn "---------------------------- check proof"
  b <- verifyCircom cname out
  print b
 where
  test = runFun circ
  ss = sig test
  s = list @Sig ss
  ct = extractIO test
  ect = evalC (liS ss) ct
  witness = map mkF $ getVal @Integer $ evalV ss ect $ mkVec $ map fromIntegral i

  tt = MkCircom
         { signals     = map showVar $ take (length s) [1..]
         , output      = concat $ zipWith mkP [1..] $ map getP s
         , constraints = map (fmap trLin . trCon) $ list @Constr $ circuit 1 test
         }

  cname = "test"
  inp = MkCircomInput $ zip (map showVar [1..]) witness

--------------------------------------------------------- tests

isZero =
  MkCirc Felt (Wrap (TBits 1)) \i ->
  MLet L Felt i \i -> Mlu i \i' ->
  MunsafeLet (mlconst 1 `div` i') \inv -> Mlu inv \inv' -> 
  MunsafeLet (mlconst 1 `sub` (i' `mul` inv')) \o ->
  MMulEq i inv (Mconst 1 `Msub` o) $
  MMulEq i o (Mconst 0) $
  MunsafeWrap o
 where
  mlconst i = Mbuiltin (Bconst i)
  div = f Bdiv
  sub = f Bsub
  mul = f Bmul
  f b x y = App Felt (App (Arr Felt Felt) (Mbuiltin b) x) y

test0 = runTest testCirc [[2, 1, 3]]
test1 = runTest (MkCirc Felt Felt (\_ -> Mconst 3)) [[5]]
test2 = runTest (MkCirc (Tup Felt Felt) (Tup Felt Felt) (\p -> MkTup (Snd Felt p) (Fst Felt p))) [[3,4]]
test3 = runTest isZero [[0], [3]]

main = test0
