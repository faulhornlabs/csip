
{-# LINE 1 "src/C4_Desug.hs" #-}
module C4_Desug
  () where

import B_Base
import C1_Name
import C2_NameLiterals
import C3_Parse


--------------- unop and op ---------------

topOp = \case
  Empty -> T4 Nil Empty Nil Empty
  Node2 l a r     -> T4 (a :.      Nil) l       Nil  r
  Node3 l a m b r -> T4 (a :. b :. Nil) l (m :. Nil) r

unop :: NameSeq Layout -> Mem (ExpTree' Layout)
unop Empty = pure N22
unop (topOp -> T4 os l ts r) = do
  ur  <- unop r
  ul  <- unop l
  uts <- mapM unop ts
  t   <- tokensToName os
  pure $ case T2 (leftPrec t == leftPrec precALPHA) (rightPrec t == rightPrec precALPHA) of
    T2 True  True  -> ul .@ apps t uts
    T2 True  False -> ul .@ (Apps t uts :@ ur)
    T2 False True  -> Apps t (ul :. uts)
    T2 False False -> Apps t (ul :. uts) :@ ur
 where
  N22 .@ y = y
  x     .@ y = x :@ y

  -- TODO: implement inverse of this in op
  apps N23 ((RVar t :@ N22 :@ N22) :. Nil) | isInfix t = RVar t
  apps t fs = Apps t fs

op :: ExpTree' Layout -> NameSeq Layout
op = removeSuperfluousParens . opt  where

  opt = \case
    N22 -> Empty
    Apps (tokens -> os) args -> alter mempty (enrich os) (map opt args)

  alter acc         Nil       Nil   =        parens acc
  alter acc         Nil   (a:. as)  = alter (parens acc <> a) Nil as
  alter acc (N24:. os) (a:. as)  = alter (       acc <> a) os as
  alter acc (N24:. os)     Nil   = alter         acc       os Nil
  alter acc (o :.     os)      as   = alter (acc <> singOpSeq o) os as

  enrich :: List (Name a) -> List (Name a)
  enrich Nil = (impossible "src/C4_Desug.hs" 51)
  enrich (o:. os) = g True o os where

    g p o os
      = condCons (p && leftPrec o /= leftPrec precALPHA) N24
        (o:. f (rightPrec o /= rightPrec precALPHA) os)

    f p Nil = condCons p N24 Nil
    f p (o:. os) = g p o os

  parens a@(Node2 Empty _ Empty) = a
  parens a = N25 <> a <> N26

  removeSuperfluousParens :: NameSeq Layout -> NameSeq Layout
  removeSuperfluousParens = flr Nothing Nothing  where

    flr x y = \case
      Empty -> Empty
      Node2 a (singOpSeq -> v) b
        -> flr x (Just v) a <> v <> flr (Just v) y b
      Node3 a@Empty N25 b N26 Empty | p a b -> flr x y b
      Node3 a       N25 b N26 Empty | noLeft b, p a b -> flr x y $ a <> b
      Node3 a       N25 b N26 Empty -> flr x y $ a <> N12 <> b <> N13
      Node3 a (singOpSeq -> v) b (singOpSeq -> w) c
        -> flr x (Just v) a <> v <> flr (Just v) (Just w) b <> w <> flr (Just w) y c
     where
      p a b = a > b && maybe True (< a) x && maybe True (< b) x && maybe True (b >) y

      noLeft = \case
        Empty -> True
        Node2 Empty _ _ -> True
        Node3 Empty _ _ _ _ -> True
        _ -> False

instance Parse (ExpTree' Layout) where  parse = parse >=> runMem . unop
instance Print (ExpTree' Layout) where  print = print . op


--------------- patch and unpatch ---------------

joinName t (RVar a) (RVar b) = RVar $ joinName_ t a b
joinName _ _ _ = (impossible "src/C4_Desug.hs" 92)

patch :: ExpTree' Layout -> ExpTree' PatchedOp
patch = \case
  a :@ b -> patch a .@ patch b
  RVar n -> RVar $ coerce n
 where
  a@N27      .@ (b@N28 :@ x :@ y) = joinName N29 a b :@ x :@ y
  a@N23      .@ (b@N28 :@ x :@ y) = joinName N30 a b :@ x :@ y
  N23        .@ a     = a
  N31 :@ a     .@ _     = a
  N21 :@ N22 .@ a     = a
  N21 :@ a     .@ N22 = a
  a             .@ b     = a :@ b

-- TODO: move to separate phase?
defEnd :: ExpTree' PatchedOp -> ExpTree' PatchedOp
defEnd = f where
  f = \case
    e@(Saturated (Apps l _)) | l == N28 || l == N32 || l == N33 || l == N34 || l == N35 || l == N36
      -> N21 :@ g e :@ N20
    t@N21 :@ a :@ b -> t :@ g a :@ f b
    a :@ b -> f a :@ f b
    t -> t

  g = \case
    l@N32 :@ (u@N28 :@ a :@ b) :@ c -> l :@ (u :@ f a :@ f b) :@ f c   -- hack
    a :@ b -> f a :@ f b
    t -> t

instance Parse (ExpTree' PatchedOp) where  parse = (defEnd . patch <$>) . parse
instance Print (ExpTree' PatchedOp) where  print = print . (coerce :: ExpTree' PatchedOp -> ExpTree' Layout)


--------------- desugar and sugar ---------------

getBind = \case
  n@N30 -> Just n
  n@N29 -> Just n
  _ -> Nothing

pattern Bind a b c <- (getBind -> Just a) :@ b :@ c

isBind Bind{} = True
isBind _ = False

getArr = \case
  n@N37 -> Just n
  n@N38    -> Just n
  _ -> Nothing

pattern Arr a b c <- (getArr -> Just a) :@ b :@ c


desugar :: ExpTree' PatchedOp -> Mem (ExpTree' Desug)
desugar e = pure $ coerce $ etr3 $ etr2 $ etr e where

  etr :: ExpTree' PatchedOp -> ExpTree' PatchedOp
  etr = \case
    l :@ (w :@ RApp n m :@ a) :@ b | l == N37 || l == N38, w == N30 || w == N29
      -> etr $ l :@ (w :@ n :@ a) :@ (l :@ (w :@ m :@ a) :@ b)
    l :@ (w@N27 :@ RApp n m) :@ b | l == N37 || l == N38
      -> etr $ l :@ (w :@ n) :@ (l :@ (w :@ m) :@ b)
    l :@ RApp a b :@ e | l == N37 || l == N38 && isBind b
      -> etr $ l :@ a :@ (l :@ b :@ e)
    a :@ b -> etr a :@ etr b
    l -> l

  etr2 :: ExpTree' PatchedOp -> ExpTree' PatchedOp
  etr2 = \case
    l :@ (w@N27 :@ a) :@ b | l == N37 || l == N38 -> l :@ (joinName N29 w N28 :@ etr2 a :@ N39) :@ etr2 b
    l@N37     :@ a  :@ b | not (isBind a) -> l :@ (N30 :@ etr2 a :@ N39) :@ etr2 b
    l@N38        :@ a  :@ b | not (isBind a) -> l :@ (N30 :@ N39 :@ etr2 a) :@ etr2 b
    z :@ n@RVar{} :@ b | z == N33 || z == N32 -> z :@ (N28 :@ etr2 n :@ N39) :@ etr2 b
    N21 :@ (l@N28 :@ n :@ t) :@ (w@N21 :@ (z :@ n' :@ b) :@ m) | z == N33 || z == N32, n == n'
      -> etr2 $ w :@ (z :@ (l :@ n' :@ t) :@ b) :@ m
    w@N21 :@ (N32 :@ n :@ b) :@ m | notVar n -> w :@ (N40 :@ etr2 n :@ etr2 b) :@ etr2 m
    a :@ b -> etr2 a :@ etr2 b
    l -> l

  etr3 :: ExpTree' PatchedOp -> ExpTree' PatchedOp
  etr3 = \case
    N21 :@ (N41 :@ a :@ b) :@ c -> N42 :@ etr3 b :@ (N37 :@ (N30 :@ etr3 a :@ N39) :@ etr3 c)
    N21       :@ b :@ c | isExp b -> N42 :@ etr3 b :@ (N37 :@ (N30 :@ N39   :@ N39) :@ etr3 c)
    a :@ b  -> etr3 a :@ etr3 b
    l -> l

  -- TODO: remove?
  notVar = \case RVar{} -> False; N28 :@ _ :@ _ -> False; _ -> True

  -- TODO: remove
  isExp = \case
    N33   :@ _ :@ _ -> False
    N32    :@ _ :@ _ -> False
    N28    :@ _ :@ _ -> False
    N36 :@ _ :@ _ -> False
    N35    :@ _ :@ _ -> False
    N34 :@ _ -> False
    N40 :@ _ :@ _ -> False
    _ -> True

sugar :: ExpTree' Desug -> ExpTree' PatchedOp
sugar = coerce . sug . sug0  where

  sug0 :: ExpTree' Desug -> ExpTree' Desug
  sug0 = \case
    l@N37 :@ (N30 :@ a :@ N39) :@ b -> l :@ sug0 a :@ sug0 b
    l@N38    :@ (N30 :@ N39 :@ a) :@ b -> l :@ sug0 a :@ sug0 b
    l :@ (N28 :@ n :@ N39) :@ b | l == N33 || l == N32 -> l :@ sug0 n :@ sug0 b
    a :@ b -> sug0 a :@ sug0 b
    a -> a

  sug :: ExpTree' Desug -> ExpTree' Desug
  sug = \case
    Arr l n b -> arrow l (sug n) (sug b)
    a :@ b -> sug a :@ sug b
    a -> a

  arrow :: ExpTree' Desug -> ExpTree' Desug -> ExpTree' Desug -> ExpTree' Desug
  arrow arr n (Arr arr' m e) | arr == arr', Just nm <- n +@ m = arr :@ nm :@ e  where

    a +@ RApp b c | arr == N37, Just ab <- a +@ b = Just $ ab :@ c
    Bind pl n t +@ Bind pl' m t' | pl == pl', t == t' = Just $ pl :@ (n ++@ m) :@ t
    a +@ b | arr == N37 || isBind a && isBind b = Just $ a :@ b
    _ +@ _ = Nothing

    n ++@ (a :@ b) = (n ++@ a) :@ b
    n ++@ m = n :@ m
  arrow arr n e = arr :@ n :@ e

instance Parse (ExpTree' Desug) where  parse = parse >=> runMem . desugar
instance Print (ExpTree' Desug) where  print = print . sugar


--------------- import module ---------------

importModule :: String -> ExpTree' Desug -> IO (ExpTree' Desug)
importModule n s = case n of
  "Builtins" -> runMem (addrToCharArray "\ndata builtin Type : Type where\n\n-- (~>) is constructor application\nconstructor builtin Ap : (a ~> b) -> a -> b\n\n\ndata builtin Bool : Type where\n  builtin True  : Bool\n  builtin False : Bool\n\nconstructor builtin Word : Type\n\nconstructor builtin DecWord    : Word -> Word\nconstructor builtin AddWord    : Word -> Word -> Word\nconstructor builtin MulWord    : Word -> Word -> Word\nconstructor builtin ModWord    : Word -> Word -> Word\nconstructor builtin DivWord    : Word -> Word -> Word\nconstructor builtin EqWord     : Word -> Word -> Bool\n\ndata WSucView : Type where\n  builtin WSucOk    : Word -> WSucView\n  builtin WSucFail  : WSucView\n\nbuiltin SuccView : Word -> WSucView\nSuccView 0 = WSucFail\nSuccView n = WSucOk (DecWord n)\n\nconstructor builtin WSuc : Word -> Word\n\n-- pattern WSuc n <- (SuccView --> WSucOk n)\n-- WSuc = \\n -> AddWord 1 n\n\n\nconstructor builtin String : Type\n\nconstructor builtin AppendStr : String -> String -> String\nconstructor builtin EqStr     : String -> String -> Bool\nconstructor builtin TakeStr   : Word -> String -> String\nconstructor builtin DropStr   : Word -> String -> String\n\ndata ConsViewData : Type where\n  builtin ConsOk    : String -> String -> ConsViewData\n  builtin ConsFail  : ConsViewData\n\nbuiltin ConsView : String -> ConsViewData\nConsView \"\" = ConsFail\nConsView n = ConsOk (TakeStr 1 n) (DropStr 1 n)\n\nconstructor builtin ConsStr : String -> String -> String\n-- pattern ConsStr a b <- (ConsView --> ConsOk a b)\n\n\ndata builtin Nat : Type where\n  Zero : Nat\n  Suc  : Nat -> Nat\n\nbuiltin wordToNat : Word -> Nat\nwordToNat 0 = Zero\nwordToNat (WSuc i) = Suc (wordToNat i)\n\n\n-- Object code\nconstructor builtin Ty : Type\nconstructor builtin Code : Ty -> Type\n\nconstructor builtin Arr : Ty -> Ty -> Ty\nconstructor builtin Lam : {a b : Ty} -> (a -> b) -> Arr a b\nconstructor builtin App : Arr a b -> a -> b\nconstructor builtin Let : {a b : Ty} -> a -> (a -> b) -> b\nconstructor builtin TopLet : {a b : Ty} -> a -> a -> b -> b\n\nconstructor builtin Prod : Ty -> Ty -> Ty\nconstructor builtin Pair : {a b : Ty} -> a -> b -> Prod a b\nconstructor builtin Fst : Prod a b -> a\nconstructor builtin Snd : Prod a b -> b\n\ndata builtin OBool : Ty where\n  builtin OTrue  : OBool\n  builtin OFalse : OBool\n\ndata builtin OString : Ty where\n  builtin MkOString : String -> OString\n\nconstructor builtin OEqStr : OString -> OString -> OBool\n\ndata builtin OWord : Ty where\n  builtin MkOWord : Word -> OWord\n\nconstructor builtin OEqWord : OWord -> OWord -> OBool\n\n\n-- Type classes\n\nbuiltin lookupDict : (a : Type) -> a\n\ndata builtin SuperClassList : (a : Type) -> Type where\n  builtin SuperClassNil  : (a : Type) -> SuperClassList a\n  builtin SuperClassCons : (a : Type) -> (b : Type) -> (a -> b) -> SuperClassList a -> SuperClassList a\n\nbuiltin superClasses : (a : Type) -> SuperClassList a"#) >>= mkFileString' "Builtins" <&> f
  "Prelude"  -> runMem (addrToCharArray "\nimport Builtins\n\n\nappendStr = AppendStr\n\nclass Eq (a : Type) where\n  (==) : a -> a -> Bool\n\ninstance Eq Word where\n  a == b = EqWord a b\n\ninstance Eq String where\n  a == b = EqStr a b\n\n\nclass Num (a : Type) where\n  (+)     : a -> a -> a\n  (*)     : a -> a -> a\n  fromWord : Word -> a\n\ninstance Num Word where\n  a + b = AddWord a b\n  a * b = MulWord a b\n  fromWord n = n\n\neven : Word -> Bool\n  = \\n -> ModWord n 2 == 0\nodd  : Word -> Bool\n  = \\n -> ModWord n 2 == 1\n\ndiv = DivWord\n\n\nthe : (a : Type) -> a -> a\n  = \\_ x -> x\n\n\ndata Unit : Type where\n  TT : Unit\n\ndata Tuple2 : Type -> Type -> Type where\n  T2 : a -> b -> Tuple2 a b\n\nfirst : (a -> b) -> Tuple2 a c -> Tuple2 b c\nfirst f (T2 x y) = T2 (f x) y\n\nsecond : (a -> b) -> Tuple2 c a -> Tuple2 c b\nsecond f (T2 x y) = T2 x (f y)\n\n\ndata Tuple3 : Type -> Type -> Type -> Type where\n  T3 : a -> b -> c -> Tuple3 a b c\n\ndata Maybe : Type ~> Type where\n  Nothing : Maybe a\n  Just    : a -> Maybe a\n\ndata List : Type ~> Type where\n  Nil    : List a\n  Cons  : a -> List a -> List a"# ) >>= mkFileString' "Prelude"  <&> f
  n -> fail $ "Can't find " <> print n
 where
  f :: ExpTree' Desug -> ExpTree' Desug
  f = \case
    N21 :@ a :@ b -> N21 :@ a :@ f b
    N20 -> s
    x -> error $ "include: " <> print x

preprocess :: ExpTree' Desug -> IO (ExpTree' Import)
preprocess = f  where
  f = \case
    N21 :@ (N34 :@ RVar m) :@ e -> runMem (print m) >>= \m -> importModule m e >>= f
    RVar n -> pure $ RVar $ coerce n
    a :@ b -> (:@) <$> f a <*> f b


instance Parse (ExpTree' Import) where  parse = parse >=> preprocess
instance Print (ExpTree' Import) where  print = print . (coerce :: ExpTree' Import -> ExpTree' Desug)
