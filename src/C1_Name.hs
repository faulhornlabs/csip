module C1_Name
  ( Arity, HasArity, arity
  , precALPHA, isInfix
  , Phase (..), Name (RNat, RString), newName, fromStr, showName, showName', setNameName, rename, mapName
  , tokens, tokensToName, joinName_, selName_
  , NameStr, SName, HasName (name), nameStr, nameOf, isScoped
  , IsName, fromName, eqName
  , mainReset
  , newId
  ) where

import B_Base


------------------------------------------------------

type Arity = Word

class HasArity a where
  arity :: a -> Arity

instance HasArity (List Precedences) where

  arity Nil = $impossible
  arity (o :. Nil) | isInfix o = 1
  arity (o :. os) = g 1 True o os where

    condCons True i = 1 + i
    condCons _    i = i

    g acc p o os
      = f (condCons (p && leftPrec o /= leftPrec precALPHA) acc)
          (rightPrec o /= rightPrec precALPHA) os

    f acc p Nil = condCons p acc
    f acc p (o:. os) = g acc p o os


------------------------------------------------------

$specialPrecedences

defaultPrecedences (ConsChar c _) | isGraphic c = precGRAPHIC
defaultPrecedences _ = precALPHA

isInfix :: HasPrecedences a => a -> Bool
isInfix (precedences -> p) = precMINPREC `less` p && p `less` precMAXPREC  where

  MkPrecedences a b `less` MkPrecedences c d = a < c && b < d

instance HasPrecedences (List Precedences) where

  precedences Nil = $impossible
  precedences (t :. ts) = f (leftPrec t) (rightPrec t) ts where
    f l r Nil = MkPrecedences l r
    f l _ (t :. ts) = f l (rightPrec t) ts


-----------------------------------------------

splitNameString :: String -> List String
splitNameString s@(ConsChar c _) | c == ' ' || c == '"' = s :. Nil
splitNameString s = words s  where

  words (spanStr (/= ' ') -> T2 as bs) = as :. case bs of
    ConsChar ' ' bs -> words bs
    _ -> Nil


----------------------------------

data NameInfo = MkTI Word{-id-} Word{-old id, used by Name-} Precedences Arity (List NameInfo)

instance HasId          NameInfo where getId       (MkTI i _ _ _ _) = i
instance HasPrecedences NameInfo where precedences (MkTI _ _ p _ _) = p
instance HasArity       NameInfo where arity       (MkTI _ _ _ a _) = a

----------------------------------

data Phase
  = Spaced | Stringed | Uncomment | Uncomments | Unspaced | Layout | PatchedOp | Desug | Import | Scope

data Name (a :: Phase) = MkName NameInfo String

type NameStr = Name Import
type SName   = Name Scope

class HasName a where name :: a -> SName

showName (MkName _ s) = s

showName' n@(MkName (MkTI i oi _ _ _) s)
  | isScoped n = s <> "_" <> showWord i <> "_" <> showWord oi
  | True = showName n

setNameName s (MkName ti _) = MkName ti s

instance HasId          (Name a) where getId (MkName h _) = getId h
instance Ord            (Name a) where compare = compare `on` getId
instance HasPrecedences (Name a) where precedences (MkName i _) = precedences i
instance HasArity       (Name t) where arity (MkName a _) = arity a
instance Print          (Name a) where print = pure . showName


tokens :: Name a -> List (Name a)
tokens t@(MkName (MkTI _ _ _ _ tis) s) = case tis of
  Nil -> t :. Nil
  _ -> zipWith MkName tis $ splitNameString s

------------------------

{-# noinline mainReset #-}
mainReset :: Reset
mainReset = topMem (newRef (pure T0))

{-# noinline idRef #-}
idRef :: Ref Word
idRef = topRef mainReset 0

newId :: Mem Word
newId = stateRef idRef \i -> T2 (i+1) i

------------------------

insertSM' :: String -> String -> Precedences -> StringMap NameInfo -> Mem NameInfo
insertSM' msg s c m = do
  b <- newId
  tis <- case splitNameString s of
    _ :. Nil -> pure Nil
    ss -> mapM getTI ss
  let as = case tis of
        Nil -> c :. Nil
        _   -> map precedences tis
  let info = MkTI b b (precedences as) (arity as) tis
  traceShow "token" $ pure $ msg <> ": " {- <> s -} <> " " <> showWord (getId info)
  insertSM s info m
  pure info
 where
  getTI s = lookupSM s m <&> \case
    Just ti -> ti
    _ -> $impossible

{-# noinline tokenMap #-}
tokenMap :: StringMap NameInfo
tokenMap = topStringMap mainReset \m -> do
  forM_ $precTable \(T2 a b) -> add m a b
  forM_ $stringliterals \s -> add m s (defaultPrecedences s)
 where
  add m s p = lookupSM s m >>= \case
    Just{} -> fail $ "impossible at tokenMap: " -- <> pure (showchars s)
    _      -> insertSM' "B" s p m

  consTable s l r t = T2 s (MkPrecedences l r) :. t
  emptyTable = Nil

newName :: String -> Mem (Name a)
newName cs = do
  ti <- lookupSM cs tokenMap >>= \case
    Just i -> pure i
    Nothing -> insertSM' "C" cs (defaultPrecedences cs) tokenMap
  pure $ MkName ti cs

fromStr :: Addr# -> Name a
fromStr s = topMem (newString s >>= newName)

--------------------------------------------


nameOf :: NameStr -> Mem SName
nameOf (MkName (MkTI _ oi b ar ts) s) = do
  i <- newId
  pure $ MkName (MkTI i oi b ar ts) s

isScoped :: Name a{-TODO?-} -> Bool
isScoped (MkName (MkTI i oi _ _ _) _) = i /= oi

nameStr :: SName -> NameStr
nameStr (MkName (MkTI _ i b ar ts) s) = MkName (MkTI i i b ar ts) s

rename :: NameStr -> SName -> SName
rename (MkName (MkTI _ i b ar ts) s) n = MkName (MkTI (getId n) i b ar ts) s

--------------------------------------------

mapName :: (String -> String) -> Name a -> Mem (Name b)
mapName f = newName . f . showName

showNames Nil = ""
showNames (t :. Nil) = showName t
showNames (t :. ts) = showName t <> " " <> showNames ts

tokensToName :: List (Name a) -> Mem (Name a)
tokensToName (t :. Nil) = pure t
tokensToName ts = newName (showNames ts)

joinName_ t@(tokens -> cs) (tokens -> as) (tokens -> bs) = setNameName (showNames $ f cs as bs) t
 where
  f (x :. xs) (y :. ys) bs | y == x = y :. f xs ys bs
  f _         as        bs = bs <> as

selName_ t@(tokens -> xs) (tokens -> ys) = setNameName (showNames $ f xs ys) t where
  f (x :. xs) (y :. ys) | y == x = y :. f xs ys
  f xs        (_ :. ys) = f xs ys
  f Nil       Nil       = Nil
  f _ _ = $impossible

-------------------

getWord s@(ConsChar c _) | isDigit c = Just $ lazy case readWord s of
  Just w -> w
  _ -> $impossible
getWord _ = Nothing

pattern RNat :: Lazy Word -> Name a
pattern RNat n <- MkName _ (getWord -> Just n)

getString (ConsChar '"' s) = Just $ lazy case s of
  SnocChar s '"' -> s
  _ -> $impossible
getString _ = Nothing

pattern RString :: Lazy String -> Name a
pattern RString n <- MkName _ (getString -> Just n)

---------------------------

class IsName t where
  fromName :: Name a -> t
  eqName   :: Name a -> t -> Bool

instance IsName (Name a) where
  fromName a = coerce a
  eqName a b = getId a == getId b
