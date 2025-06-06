
{-# LINE 1 "src/C1_Name.hs" #-}
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

  arity Nil = (impossible "src/C1_Name.hs" 24)
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

precMAXPREC = MkPrecedences 63 63
precMINPREC = MkPrecedences 38 38
precALPHA = MkPrecedences 68 69
precGRAPHIC = MkPrecedences 59 60
{-# LINE 41 "src/C1_Name.hs" #-}


defaultPrecedences (ConsChar c _) | isGraphic c = precGRAPHIC
defaultPrecedences _ = precALPHA

isInfix :: HasPrecedences a => a -> Bool
isInfix (precedences -> p) = precMINPREC `less` p && p `less` precMAXPREC  where

  MkPrecedences a b `less` MkPrecedences c d = a < c && b < d

instance HasPrecedences (List Precedences) where

  precedences Nil = (impossible "src/C1_Name.hs" 53)
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
    _ -> (impossible "src/C1_Name.hs" 141)

{-# noinline tokenMap #-}
tokenMap :: StringMap NameInfo
tokenMap = topStringMap mainReset \m -> do
  forM_ (consTable "\t" 14 12 $ consTable "\n" 4 3 $ consTable "\r" 12 13 $ consTable " " 11 10 $ consTable "!>" 15 69 $ consTable "\"" 2 1 $ consTable "#" 25 24 $ consTable "###" 68 69 $ consTable "&&" 44 43 $ consTable "(" 68 15 $ consTable ")" 15 69 $ consTable "*" 55 56 $ consTable "**" 34 33 $ consTable "+" 53 54 $ consTable "," 27 26 $ consTable "-" 53 54 $ consTable "--" 6 5 $ consTable "--->" 34 33 $ consTable "-->" 34 33 $ consTable "->" 34 33 $ consTable "-}" 7 8 $ consTable "." 61 62 $ consTable "/" 55 56 $ consTable "/=" 45 46 $ consTable ":" 34 33 $ consTable ":->" 34 33 $ consTable "::" 50 49 $ consTable ":=" 29 28 $ consTable ";" 23 22 $ consTable "<" 45 46 $ consTable "<!" 68 15 $ consTable "<$>" 47 48 $ consTable "<&>" 39 40 $ consTable "<*>" 47 48 $ consTable "<-" 36 35 $ consTable "<=" 45 46 $ consTable "<>" 52 51 $ consTable "=" 29 28 $ consTable "==" 45 46 $ consTable "==>" 34 33 $ consTable "=>" 34 33 $ consTable ">" 45 46 $ consTable ">=" 45 46 $ consTable ">>" 39 40 $ consTable ">>=" 39 40 $ consTable "@" 64 65 $ consTable "SEMI" 14 13 $ consTable "[" 68 15 $ consTable "\\" 68 34 $ consTable "]" 15 69 $ consTable "^" 58 57 $ consTable "case" 68 21 $ consTable "class" 68 20 $ consTable "constructor" 68 67 $ consTable "data" 68 20 $ consTable "do" 14 13 $ consTable "else" 16 37 $ consTable "if" 68 16 $ consTable "import" 68 67 $ consTable "in" 16 32 $ consTable "instance" 68 20 $ consTable "let" 68 16 $ consTable "of" 14 13 $ consTable "ofBeg" 21 69 $ consTable "ofBegin" 66 19 $ consTable "ofEnd" 19 69 $ consTable "then" 18 17 $ consTable "where" 14 13 $ consTable "whereBeg" 20 69 $ consTable "whereBegin" 66 19 $ consTable "whereEnd" 19 69 $ consTable "{" 68 15 $ consTable "{-" 9 7 $ consTable "|" 31 30 $ consTable "|->" 34 33 $ consTable "||" 42 41 $ consTable "}" 15 69 $ consTable "~>" 34 33 $ emptyTable) \(T2 a b) -> add m a b
  forM_ ("ModuleEnd" :. "__" :. "( )" :. "___" :. "{ }" :. "{ : }" :. "( : )" :. "whereBegin whereEnd" :. "\\ ->" :. "_" :. "Rule" :. "[ ]" :. "class whereBeg" :. "instance whereBeg" :. "data whereBeg" :. "ofBegin ofEnd" :. "case ofBeg" :. "builtin" :. "caseFun" :. "App" :. "Pi" :. "HPi" :. "CPi" :. "IPi" :. "IGNORE" :. "()" :. "( , )" :. "[]" :. "newline" :. "begin" :. "end" :. "quote" :. "Var" :. "= ;" :. "n" :. "v" :. "c" :. "Sup" :. "Con" :. "Meta" :. "PrimOp" :. "Fun" :. "TGen" :. "i" :. "s" :. "a" :. "l" :. "m" :. "lookupDict" :. "Fail" :. "superClasses" :. "SuccView" :. "ConsView" :. "wordToNat" :. "matchRet" :. "TRet" :. "AppendStr" :. "EqStr" :. "TakeStr" :. "DropStr" :. "DecWord" :. "AddWord" :. "MulWord" :. "DivWord" :. "ModWord" :. "EqWord" :. "True" :. "False" :. "X" :. "TMatch" :. "Lam" :. "Let" :. "Erased" :. "View" :. "Guard" :. "Dot" :. "fail" :. "Match" :. "d" :. "WSuc" :. "WSucOk" :. "ConsStr" :. "ConsOk" :. "MkOString" :. "OEqStr" :. "OTrue" :. "MkOWord" :. "OEqWord" :. "SuperClassCons" :. "SuperClassNil" :. "p" :. "Arr" :. "Code" :. "Ty" :. "Type" :. "String" :. "OString" :. "Word" :. "Nat" :. "OWord" :. "z" :. "Ap" :. "e" :. "h" :. "TopLet" :. "Bool" :. "t" :. "PCode" :. "Computation" :. "PLet" :. "PLam" :. "PApp" :. "Prod" :. "Pair" :. "Fst" :. "Snd" :. "noreturn" :. Nil) \s -> add m s (defaultPrecedences s)
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
  f _ _ = (impossible "src/C1_Name.hs" 205)

-------------------

getWord s@(ConsChar c _) | isDigit c = Just $ lazy case readWord s of
  Just w -> w
  _ -> (impossible "src/C1_Name.hs" 211)
getWord _ = Nothing

pattern RNat :: Lazy Word -> Name a
pattern RNat n <- MkName _ (getWord -> Just n)

getString (ConsChar '"' s) = Just $ lazy case s of
  SnocChar s '"' -> s
  _ -> (impossible "src/C1_Name.hs" 219)
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
