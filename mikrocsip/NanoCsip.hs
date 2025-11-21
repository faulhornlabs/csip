{-# language ViewPatterns, PatternSynonyms, LambdaCase, MultilineStrings #-}

import Data.Char
import Data.List

-------------------------

pattern Print :: (Read a, Show a) => a -> String
pattern Print a <- (reads -> [(a, "")])
  where Print a =  show a

-------------------------

type Name     = String
type Bound    = Bool
type NeedsRet = Bool

isCon :: Name -> Bool
isCon (c: _) = isUpper c || isDigit c

data EnvItem
  = EDec                --  \x -> 
  | EVal Bound    Val   --  True: \x ->    False: x =
  | ETm  NeedsRet Tm    --  True: x =>     False: x ==>
  deriving Show

type Env = [(Name, EnvItem)]

data LetKind = LDef | LRule NeedsRet        --   = | =>, ==>
  deriving Show

data Tm
  = Var Name
  | App Tm Tm
  | Lam Name Tm
  | Let LetKind Name Tm Tm
  deriving Show

data Val
  = VVar Name
  | Val :$ Val
  | Closure Env Name Tm    -- \x -> e
  | NameClosure Env Name   -- x => e
  deriving Show

pattern VRet x = VVar "Ret" :$ x
pattern VNat i = VVar (Print (i :: Int))

getApps ((getApps -> (a, bs)) :$ b) = (a, b: bs)
getApps a = (a, [])

pattern Apps a bs <- (getApps -> (a, bs))
  where Apps a bs =  foldr (flip ($$)) a bs

-------------------------

eval :: Env -> Tm -> Val
eval g = \case
  Lam x a              -> Closure g x a
  App a b              -> eval g a $$ eval g b
  Let LDef       x a b -> eval ((x, EVal False (eval g a)): g) b
  Let (LRule nr) x a b -> eval ((x, ETm  nr a):             g) b
  Var x -> case lookup x g of
    Just (EVal _ a)    -> a
    Just ETm{}         -> simplify (NameClosure g x)
    _                  -> VVar x

($$) :: Val -> Val -> Val
b $$ a = simplify (b :$ a)

simplify = \case
  Closure d x t :$ a -> eval ((x, EVal True a): d) t
  VVar "Mul" :$ VNat a :$ VNat b -> VNat (a * b)
  VVar "Add" :$ VNat a :$ VNat b -> VNat (a + b)
  VVar "Sub" :$ VNat a :$ VNat b -> VNat (a - b)
  Apps (VVar x) as :$ (VVar "Match" :$ VVar x' :$ ok :$ fail)
    | x' == x -> Apps ok as
    | isCon x -> fail $$ VVar "_"
  Apps (NameClosure d x) as
    | Just (ETm nr a) <- lookup x d
    , a' <- eval d a
    , Just r <- needsRet nr $ Apps a' as
    -> r
  a -> a
 where
  needsRet :: Bool -> Val -> Maybe Val
  needsRet False v = Just v
  needsRet True (VRet v) = Just v
{-
  needsRet True (Closure g x a)
    | Just r <- needsRet True (eval ((x, EDec): g) a)
    , t <- quote g r
    = Just (Closure g x t)
-}
  needsRet _ _ = Nothing

conv :: Int -> Val -> Val -> Bool
conv i a@Closure{} b | x <- VVar ("q" <> show i) = conv (i+1) (a $$ x) (b $$ x)
conv i a b@Closure{} | x <- VVar ("q" <> show i) = conv (i+1) (a $$ x) (b $$ x)
conv _ (VVar x) (VVar y) | x == y = True
conv i (a :$ b) (a' :$ b') = conv i a a' && conv i b b'
conv i (NameClosure g x) (NameClosure g' x') | x == x' = convEnv i (bEnv g) (bEnv g')
 where
  bEnv g = [a | (_, EVal True a) <- reverse g]

  convEnv _ [] [] = True
  convEnv i (a: g) (a': g') = conv i a a' && convEnv i g g'
  convEnv _ _ _ = False
conv _ _ _ = False

quote :: Env -> Val -> Tm
quote g = \case
  VVar x -> Var x
  a :$ b -> App (quote g a) (quote g b)
  Closure d x t -> Lam x $ quote ((x, EDec): g) $ eval d t
  NameClosure d x -> quoteEnv g d $ Var x
 where
  -- TODO: use Env argument
  quoteEnv :: Env -> Env -> Tm -> Tm
  quoteEnv g [] a = a
  quoteEnv g ((x, EVal _ a): d) b = quoteEnv g d (Let LDef x (quote g a) b)
  quoteEnv g ((x, ETm nr a): d) b = quoteEnv g d (Let (LRule nr) x a b)


-------------------------------------- tests

a === b = conv 0 (eval [] $ parse a) (eval [] $ parse b)
a =/= b = not (a === b)

tests =
  [     "fact => x. x (Match 0 (Ret 1) (_. Ret (Mul x (fact (Sub x 1))))); fact 4"
    === "24"

  , """
      even => x. x (Match S (n. Ret (odd  n)) (_.Ret True));
      odd  => x. x (Match S (n. Ret (even n)) (_.Ret False));
      odd (S (S (S Z)))
    """
    === "True"

  , """
      add = x.(
        f => y. y (Match S (n. Ret (S (f n))) (_. Ret x));
        f
      );
      add (S (S Z)) (S (S Z))
    """
    === "S (S (S (S Z)))"

  , """
      natElim  =>  natElim1;
      natElim1 ==> z s n. n (Match Z (Ret z) (_. natElim2 z s n));
      natElim2 ==> z s n. n (Match S (a. Ret (s a (natElim z s a))) Fail);
      natElim  = natElim;
      add      = a b. natElim b (_. S) a;
      mul      = a b. natElim Z (_. add b) a;
      three    = S (S (S Z));
      mul three three
    """
    === "S (S (S (S (S (S (S (S (S Z))))))))"

-- conversion checking tests

  ,     "fact => x. x (Match 0 (Ret 1) (_. Ret (Mul x (fact (Sub x 1))))); fact"
    === "fact => x. x (Match 0 (Ret 1) (_. Ret (Mul x (fact (Sub x 1))))); f = 3; g = fact; g"

  ,     "add = x.(f => y. y. y (Match S (n. Ret (S (f n))) (_. Ret x)); f); add (S (S Z))"
    === "add = x.(f => y. y. y (Match S (n. Ret (S (f n))) (_. Ret x)); z = 3; g = f; g); add (S (S Z))"

  ,     "add = x.(f => y. y. y (Match S (n. Ret (S (f n))) (_. Ret x)); f); add (S (S Z))"
    =/= "add = x.(f => y. y. y (Match S (n. Ret (S (f n))) (_. Ret x)); f); add (S Z)"

  ,     "id1 => x. Ret x; y. id1 y"
    === "id2 => x. Ret x; id2"

  ,     "id1 => x. Ret x; f = id1; y. f y"
    === "id2 => x. Ret x; id2"

  ,     "id1 => x. Ret x; id1"
    === "x. x"

  ,     "id1 ==> x. x; id1"
    === "x. x"

  ,     "id1 => x. Ret x; f = id1; f"
    === "id2 => x. Ret x; g = id2; g"

  ,     "id1 => x. x (Match True (Ret True) (_. Ret False)); id1"
    =/= "id2 => x. x (Match True (Ret True) (_. Ret False)); id2"

  ,     "id1 => x. x (Match True (Ret True) (_. Ret False)); id1"
    =/= "x. x"

  ,     "f => Ret 1; f"
    === "1"
  ]

quoteTest = quote [("x", ETm True (Var "1"))] (eval [] $ parse "x => 1; T2 x x")


------------------------- parsing

isAlphaNumeric c = isAlphaNum c || c == '_' || c == '\'' || c == '#'
isGraphic c = c `elem` "*+-^=@%$&~.!?:<>/\\|"

tokenize = filter (not . all isSpace) . groupBy g where
  g a b = isAlphaNumeric a && isAlphaNumeric b
       || isGraphic a      && isGraphic b

parse :: String -> Tm
parse = h0 end . tokenize   where

  end a [] = a
  end _ ts = error $ "end of file expected instead of\n" <> unwords ts

  expect t r (t': ts) | t' == t = r ts
  expect t _ ts = error $ "expected " <> show t <> " at\n" <> unwords ts

  h9 r _ ("(": ts) = h0 (\b -> expect ")" $ r b) ts
  h9 r _ (t: ts) | all isAlphaNumeric t = r (Var t) ts
  h9 _ z ts = z ts

  h8 r = h9 (h8' r) (\ss -> error $ "unknown token at\n" <> unwords ss)
  h8' r a ts = h9 (\b -> h8' r (App a b)) (r a) ts

  hn os g r = g (hn' r) where
    hn' r a (n: ts) | Just f <- lookup n os = hn os g (\b -> r (f a b)) ts
    hn' r a        ts  = r a ts

  h0 = hn [(";", def)]
     $ hn [("=", Equal "="), ("=>", Equal "=>"), ("==>", Equal "==>")]
     $ hn [(".", lam)] h8

  lam (App as a) b = lam as $ lam a b
  lam (Var a) b = Lam a b

  def (Equal "="   (Var x) a) b = Let LDef          x a b
  def (Equal "=>"  (Var x) a) b = Let (LRule True)  x a b
  def (Equal "==>" (Var x) a) b = Let (LRule False) x a b

pattern Equal  s a b = Var s `App` a `App` b
