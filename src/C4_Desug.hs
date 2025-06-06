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
unop Empty = pure "__"B
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
  "__"B .@ y = y
  x     .@ y = x :@ y

  -- TODO: implement inverse of this in op
  apps "( )"B ((RVar t :@ "__"B :@ "__"B) :. Nil) | isInfix t = RVar t
  apps t fs = Apps t fs

op :: ExpTree' Layout -> NameSeq Layout
op = removeSuperfluousParens . opt  where

  opt = \case
    "__"B -> Empty
    Apps (tokens -> os) args -> alter mempty (enrich os) (map opt args)

  alter acc         Nil       Nil   =        parens acc
  alter acc         Nil   (a:. as)  = alter (parens acc <> a) Nil as
  alter acc ("___"B:. os) (a:. as)  = alter (       acc <> a) os as
  alter acc ("___"B:. os)     Nil   = alter         acc       os Nil
  alter acc (o :.     os)      as   = alter (acc <> singOpSeq o) os as

  enrich :: List (Name a) -> List (Name a)
  enrich Nil = $impossible
  enrich (o:. os) = g True o os where

    g p o os
      = condCons (p && leftPrec o /= leftPrec precALPHA) "___"B
        (o:. f (rightPrec o /= rightPrec precALPHA) os)

    f p Nil = condCons p "___"B Nil
    f p (o:. os) = g p o os

  parens a@(Node2 Empty _ Empty) = a
  parens a = "<!"B <> a <> "!>"B

  removeSuperfluousParens :: NameSeq Layout -> NameSeq Layout
  removeSuperfluousParens = flr Nothing Nothing  where

    flr x y = \case
      Empty -> Empty
      Node2 a (singOpSeq -> v) b
        -> flr x (Just v) a <> v <> flr (Just v) y b
      Node3 a@Empty "<!"B b "!>"B Empty | p a b -> flr x y b
      Node3 a       "<!"B b "!>"B Empty | noLeft b, p a b -> flr x y $ a <> b
      Node3 a       "<!"B b "!>"B Empty -> flr x y $ a <> "("B <> b <> ")"B
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
joinName _ _ _ = $impossible

patch :: ExpTree' Layout -> ExpTree' PatchedOp
patch = \case
  a :@ b -> patch a .@ patch b
  RVar n -> RVar $ coerce n
 where
  a@"{ }"B      .@ (b@":"B :@ x :@ y) = joinName "{ : }"B a b :@ x :@ y
  a@"( )"B      .@ (b@":"B :@ x :@ y) = joinName "( : )"B a b :@ x :@ y
  "( )"B        .@ a     = a
  "#"B :@ a     .@ _     = a
  ";"B :@ "__"B .@ a     = a
  ";"B :@ a     .@ "__"B = a
  a             .@ b     = a :@ b

-- TODO: move to separate phase?
defEnd :: ExpTree' PatchedOp -> ExpTree' PatchedOp
defEnd = f where
  f = \case
    e@(Saturated (Apps l _)) | l == ":"B || l == "="B || l == ":="B || l == "import"B || l == "whereBegin whereEnd"B || l == "--->"B
      -> ";"B :@ g e :@ "ModuleEnd"B
    t@";"B :@ a :@ b -> t :@ g a :@ f b
    a :@ b -> f a :@ f b
    t -> t

  g = \case
    l@"="B :@ (u@":"B :@ a :@ b) :@ c -> l :@ (u :@ f a :@ f b) :@ f c   -- hack
    a :@ b -> f a :@ f b
    t -> t

instance Parse (ExpTree' PatchedOp) where  parse = (defEnd . patch <$>) . parse
instance Print (ExpTree' PatchedOp) where  print = print . (coerce :: ExpTree' PatchedOp -> ExpTree' Layout)


--------------- desugar and sugar ---------------

getBind = \case
  n@"( : )"B -> Just n
  n@"{ : }"B -> Just n
  _ -> Nothing

pattern Bind a b c <- (getBind -> Just a) :@ b :@ c

isBind Bind{} = True
isBind _ = False

getArr = \case
  n@"\\ ->"B -> Just n
  n@"->"B    -> Just n
  _ -> Nothing

pattern Arr a b c <- (getArr -> Just a) :@ b :@ c


desugar :: ExpTree' PatchedOp -> Mem (ExpTree' Desug)
desugar e = pure $ coerce $ etr3 $ etr2 $ etr e where

  etr :: ExpTree' PatchedOp -> ExpTree' PatchedOp
  etr = \case
    l :@ (w :@ RApp n m :@ a) :@ b | l == "\\ ->"B || l == "->"B, w == "( : )"B || w == "{ : }"B
      -> etr $ l :@ (w :@ n :@ a) :@ (l :@ (w :@ m :@ a) :@ b)
    l :@ (w@"{ }"B :@ RApp n m) :@ b | l == "\\ ->"B || l == "->"B
      -> etr $ l :@ (w :@ n) :@ (l :@ (w :@ m) :@ b)
    l :@ RApp a b :@ e | l == "\\ ->"B || l == "->"B && isBind b
      -> etr $ l :@ a :@ (l :@ b :@ e)
    a :@ b -> etr a :@ etr b
    l -> l

  etr2 :: ExpTree' PatchedOp -> ExpTree' PatchedOp
  etr2 = \case
    l :@ (w@"{ }"B :@ a) :@ b | l == "\\ ->"B || l == "->"B -> l :@ (joinName "{ : }"B w ":"B :@ etr2 a :@ "_"B) :@ etr2 b
    l@"\\ ->"B     :@ a  :@ b | not (isBind a) -> l :@ ("( : )"B :@ etr2 a :@ "_"B) :@ etr2 b
    l@"->"B        :@ a  :@ b | not (isBind a) -> l :@ ("( : )"B :@ "_"B :@ etr2 a) :@ etr2 b
    z :@ n@RVar{} :@ b | z == ":="B || z == "="B -> z :@ (":"B :@ etr2 n :@ "_"B) :@ etr2 b
    ";"B :@ (l@":"B :@ n :@ t) :@ (w@";"B :@ (z :@ n' :@ b) :@ m) | z == ":="B || z == "="B, n == n'
      -> etr2 $ w :@ (z :@ (l :@ n' :@ t) :@ b) :@ m
    w@";"B :@ ("="B :@ n :@ b) :@ m | notVar n -> w :@ ("==>"B :@ etr2 n :@ etr2 b) :@ etr2 m
    a :@ b -> etr2 a :@ etr2 b
    l -> l

  etr3 :: ExpTree' PatchedOp -> ExpTree' PatchedOp
  etr3 = \case
    ";"B :@ ("<-"B :@ a :@ b) :@ c -> ">>="B :@ etr3 b :@ ("\\ ->"B :@ ("( : )"B :@ etr3 a :@ "_"B) :@ etr3 c)
    ";"B       :@ b :@ c | isExp b -> ">>="B :@ etr3 b :@ ("\\ ->"B :@ ("( : )"B :@ "_"B   :@ "_"B) :@ etr3 c)
    a :@ b  -> etr3 a :@ etr3 b
    l -> l

  -- TODO: remove?
  notVar = \case RVar{} -> False; ":"B :@ _ :@ _ -> False; _ -> True

  -- TODO: remove
  isExp = \case
    ":="B   :@ _ :@ _ -> False
    "="B    :@ _ :@ _ -> False
    ":"B    :@ _ :@ _ -> False
    "--->"B :@ _ :@ _ -> False
    "whereBegin whereEnd"B    :@ _ :@ _ -> False
    "import"B :@ _ -> False
    "==>"B :@ _ :@ _ -> False
    _ -> True

sugar :: ExpTree' Desug -> ExpTree' PatchedOp
sugar = coerce . sug . sug0  where

  sug0 :: ExpTree' Desug -> ExpTree' Desug
  sug0 = \case
    l@"\\ ->"B :@ ("( : )"B :@ a :@ "_"B) :@ b -> l :@ sug0 a :@ sug0 b
    l@"->"B    :@ ("( : )"B :@ "_"B :@ a) :@ b -> l :@ sug0 a :@ sug0 b
    l :@ (":"B :@ n :@ "_"B) :@ b | l == ":="B || l == "="B -> l :@ sug0 n :@ sug0 b
    a :@ b -> sug0 a :@ sug0 b
    a -> a

  sug :: ExpTree' Desug -> ExpTree' Desug
  sug = \case
    Arr l n b -> arrow l (sug n) (sug b)
    a :@ b -> sug a :@ sug b
    a -> a

  arrow :: ExpTree' Desug -> ExpTree' Desug -> ExpTree' Desug -> ExpTree' Desug
  arrow arr n (Arr arr' m e) | arr == arr', Just nm <- n +@ m = arr :@ nm :@ e  where

    a +@ RApp b c | arr == "\\ ->"B, Just ab <- a +@ b = Just $ ab :@ c
    Bind pl n t +@ Bind pl' m t' | pl == pl', t == t' = Just $ pl :@ (n ++@ m) :@ t
    a +@ b | arr == "\\ ->"B || isBind a && isBind b = Just $ a :@ b
    _ +@ _ = Nothing

    n ++@ (a :@ b) = (n ++@ a) :@ b
    n ++@ m = n :@ m
  arrow arr n e = arr :@ n :@ e

instance Parse (ExpTree' Desug) where  parse = parse >=> runMem . desugar
instance Print (ExpTree' Desug) where  print = print . sugar


--------------- import module ---------------

importModule :: String -> ExpTree' Desug -> IO (ExpTree' Desug)
importModule n s = case n of
  "Builtins" -> runMem (addrToCharArray $builtinsModule) >>= mkFileString' "Builtins" <&> f
  "Prelude"  -> runMem (addrToCharArray $preludeModule ) >>= mkFileString' "Prelude"  <&> f
  n -> fail $ "Can't find " <> print n
 where
  f :: ExpTree' Desug -> ExpTree' Desug
  f = \case
    ";"B :@ a :@ b -> ";"B :@ a :@ f b
    "ModuleEnd"B -> s
    x -> error $ "include: " <> print x

preprocess :: ExpTree' Desug -> IO (ExpTree' Import)
preprocess = f  where
  f = \case
    ";"B :@ ("import"B :@ RVar m) :@ e -> runMem (print m) >>= \m -> importModule m e >>= f
    RVar n -> pure $ RVar $ coerce n
    a :@ b -> (:@) <$> f a <*> f b


instance Parse (ExpTree' Import) where  parse = parse >=> preprocess
instance Print (ExpTree' Import) where  print = print . (coerce :: ExpTree' Import -> ExpTree' Desug)
