module M3_Parse
  ( Phase (..)
  , ISource, Token, OpSeq

  , Arity
  , Name, nameOf
  , NameStr, nameStr, nameId
  , mkName, mkName', mapName, rename, isConName, isVarName
  , showMixfix, showName
  , mkIntToken

  , ExpTree_
    ( Apps, RVar, (:@), Lam, RLam, RHLam, RPi, RHPi, RCPi, RIPi, RLet, ROLet, RLetTy, RConstructor, RBuiltin
    , Hole, RRule, RDot, RApp, RHApp, RView, REmbed, RGuard
    , RClass, RInstance, RData, RNat, RString, REnd, RAnn)
  , PPrint (pprint)
  , showM
  , zVar
  , coerceExpTree

  , Mixfix, addPrefix, addSuffix, isGraphicMixfix
  , OpSeq', ExpTree', Raw_, Scoped_
  ) where

-- TODO: remove
import Unsafe.Coerce (unsafeCoerce)

--import B_Prelude (getDataFileName, readFile)
import M1_Base
import M2_OpSeq


type Arity = Int
class HasArity a where arity :: a -> Arity



------------------------------------------------------
--------------- precedence calculation ---------------
------------------------------------------------------


precedenceTableString :: String
precedenceTableString = topM do
  f <- getDataFileName "precedences"
  readFile f


{-# noinline precedenceTable #-}
precedenceTable :: StringMap (Precedence, Precedence)
precedenceTable = topStringMap \m -> forM_ precedenceTable_ $ add m
 where
  add m (s, (l, r)) = lookupSM s m >>= \case
    Nothing -> insertSM s (f l 0, f r 0) m
    Just (l', r') -> insertSM s (f l l', f r r') m
  f Nil x = x
  f (p:. _) _ = p

{-# noinline lookupPrec #-}
lookupPrec :: String -> Maybe (Precedence, Precedence)
lookupPrec s = topM $ lookupSM s precedenceTable

precedenceTable_ :: List (String, (List Precedence, List Precedence))
precedenceTable_ = mkTable (lines precedenceTableString)
 where
  mkTable
    = concat
    . numberWith ff 1
    . reverse
    . map (mconcat . map g . words)

  g ('_':. s) = \p -> [(h s, ([p], Nil))]
  g s | last s == '_' = \p -> [(h (init s), (Nil, [p]))]
  g _ = impossible

  h "SEMI"    = "\v"
  h "END"     = "\r"
  h "BEGIN"   = "\t"
  h "NEWLINE" = "\n"
  h "SPACE"   = " "
  h s         = s

  ff n f = f n

strPrecedence :: String -> (Precedence, Precedence)
strPrecedence cs
  | Just p <- lookupPrec cs = p
strPrecedence (c:. _)
  | isAlphaNum c || c == '\"'  = fromJust $ lookupPrec "ALPHA"
  | isGraphic  c  = fromJust $ lookupPrec "GRAPHIC"
strPrecedence s@(_ :. _)
  = error $ "unknown first char in " <> stringToSource s
strPrecedence _ = impossible

topPrec = fromJust $ lookupPrec "ALPHA"
maxPrec = fromJust $ lookupPrec "MAXPREC"
minPrec = fromJust $ lookupPrec "MINPREC"

isInfix :: Token a -> Bool
isInfix (precedence -> p) = minPrec `less` p && p `less` maxPrec
 where
  (a, b) `less` (c, d) = a < c && b < d

isAtom :: Token a -> Bool
isAtom t = precedence t == topPrec || isInfix t

operator [_] = True
operator a = a `elem`
  [ ["if", "then", "else"]
  , ["(", ")"]
  , ["{", "}"]
  , ["[", "]"]
  , ["let", "in"]
  , ["class",    "whereBegin", "whereEnd"]
  , ["instance", "whereBegin", "whereEnd"]
  , ["data",     "whereBegin", "whereEnd"]
  ]


---------------------------------------------------
--------------- unindent and indent ---------------
---------------------------------------------------


newtype ISource = MkISource {unISource :: Source}
--  deriving Show

instance IsString ISource where
  fromString' = MkISource . fromString'

instance Parse ISource where
  parse = parse >=> pure . unindent

instance Print ISource where
  print = pure . indent >=> print

unindent :: Source -> ISource
unindent s = MkISource $ dropNl $ h "\n" 0 $ s <> "\n"
 where
  dropNl (Cons' '\n' s) = s
  dropNl s = s

  h _  n NilCh = mreplicate n "\r"
  h nl n (spanCh (== ' ') -> (lengthCh -> k, spanCh (/= '\n') -> (as, Cons nl' cs)))
    | NilCh <- as  = nl <> h nl' n cs
    | True      = mreplicate (n -. k) "\r" <> nl <> mreplicate (k -. n) " " <> mreplicate (k -. n) "\t" <> snd (revSpanCh (== ' ') as) <> h nl' k cs
  h _ _ _ = impossible

indent   :: ISource -> Source
indent (MkISource s_) = g 0 s_
 where
  g i (spanCh (== ' ') -> (sp, spanCh (== '\r') -> (((i -.) . lengthCh -> i'), cs))) = case cs of
    Cons c cs | chars c == "\n" -> c <> g i' cs
    cs   -> mreplicate i' " " <> sp <> f i' cs

  f i (spanCh (\c -> c /= '\n' && c /= '\r' && c /= '\t') -> (s, cs)) = s <> case cs of
    Cons c@(chars -> s) cs
      | s == "\t" -> f (i+1) cs
      | s == "\r" -> f (i-.1) cs
      | s == "\n" -> c <> g i cs
    NilCh | i == 0 -> stringToSource Nil
    NilCh -> impossible --error $ fromString' (show (i, showSource s_)) -- impossible
    _ -> impossible


-----------------------------------------------
--------------- Token data type ---------------
-----------------------------------------------


data Phase
  = Spaced | Stringed | Uncomment | Uncomments | Unspaced | Layout | POp | Desug

data Token (a :: Phase)
  = MkToken_
    Word -- hash/id
    (Cached Source)               -- constraint: not empty, nearby chars are glued
                         --   if (a) then whitespace is allowed
    (Cached (Precedence, Precedence))
  | MkNat_ (Cached Source) Integer
  | MkString_ (Cached Source) String
  deriving (Eq, Ord)

pattern MkNat a b = MkNat_ (MkCached a) b
pattern MkString a b = MkString_ (MkCached a) b
pattern MkToken a b <- MkToken_ _ (MkCached a) b

{-# COMPLETE MkToken, MkNat, MkString #-}

{-
instance Semigroup (Token a) where
  MkToken a (MkCached (l, _)) <> MkToken b (MkCached (_, r))
    = MkToken (a <> b) (MkCached (l, r))
  _ <> _ =
-}
precedence = \case
  MkToken _ p -> getCached p
  _ -> topPrec

isGraphicToken :: Token a -> Bool
isGraphicToken t = isAtom t && case t of
  MkToken (headCh -> c) _  -> isGraphic c
  _ -> False

isUpperToken :: Token a -> Bool
isUpperToken t = isAtom t && case t of
  MkToken (headCh -> c) _  -> isUpper c || c == ':'
  _ -> False

isLowerToken :: Token a -> Bool
isLowerToken t = isAtom t && case t of
  MkToken (headCh -> c) _  -> isLower c || (c /= ':' && isGraphic c)
  _ -> False

showToken = \case
    MkToken cs _ -> cs
    MkNat    s _ -> s
    MkString s _ -> s

{-# noinline mkToken #-}
mkToken cs = topM do
  h <- intHash'' cs
  pure $ MkToken_ h (MkCached cs) $ MkCached $ strPrecedence $ chars cs

mkIntToken n = MkNat (stringToSource $ showInteger n) n

mkToken' cs
  | Just n <- readNat (chars cs) = pure $ MkNat cs n
mkToken' cs = do
    h <- intHash' cs
    pure $ MkToken_ h (MkCached cs) $ MkCached $ strPrecedence $ chars cs

consts' :: List String
consts' =
  [ "_", "View", "Guard", "Dot", "Fail", "noreturn"
  , "Ap"
  , "lookupDict", "superClasses", "SuperClassList", "SuperClassNil", "SuperClassCons"
  , "Bool", "True", "False"
  , "Nat", "ProdNat", "PairNat", "Succ", "SuccOk", "succView", "EqNat", "DecNat", "AddNat", "MulNat", "DivNat", "ModNat"
  , "String", "ProdStr", "PairStr", "Cons", "ConsOk", "consView", "AppendStr", "EqStr", "TakeStr", "DropStr"
  , "Ty", "Arr", "Prod"
  , "Code", "Lam", "App", "Let", "Pair", "Fst", "Snd"
  , "Match", "OBool", "OTrue", "OFalse", "OString", "MkOString", "OEqStr", "ONat", "MkONat", "OEqNat"
  , ">>="
  ] <> map fst precedenceTable_
    <> ["___", "__", "ModuleEnd", "Type", "HPi", "CPi", "IPi", "Pi", "Constr", "Dict", "TopLet", "Let", "Funct", "Variable", "sel", "Term", "Erased", "noret"]
    <> ["app#", "lam#", "fail", "return", "match", "ret", "X"]
    <> ["c#", "r#", "t#", "v#", "m#", "wF#", "wG#", "wS#", "wR#", "wD#", "wH#", "cS#", "cR#", "_t#", "i#", "d#", "ww#", "w#", "'", "z#", "???"]

{-# noinline tokenState #-}
tokenState :: StringMap Word
tokenState = topStringMap \m -> forM_ consts' \s -> insertSM s (neg (intHash s)) m

intHash'' cs = lookupSM s tokenState >>= \case
    Just i -> pure i
    Nothing -> error $ "not predefined: " <> cs
 where
  s = chars cs

intHash' cs = lookupSM s tokenState >>= \case
    Just i -> pure i
    Nothing -> do
      i <- newId
      insertSM s i tokenState
      pure i
 where
  s = chars cs

instance IsString (Token a) where
  fromString' cs = mkToken (fromString' cs)

instance Parse (Token a) where
  parse = parse >=> mkToken'

instance Print (Token a) where
  print = pure . showToken

type OpSeq' a = OpSeq (Token a)

sing :: Token a -> OpSeq' a
sing a@(precedence -> (l, r)) = singOpSeq (l, a, r)

filterOpSeq p = mapOpSeq c where
      c s | p s = sing s
      c _ = mempty
{-
instance IsString (OpSeq' a) where
  fromString' = sing . fromString'
-}


---------------------------------------------
--------------- lex and unlex ---------------
---------------------------------------------


glueChars :: Char -> Char -> Bool
glueChars c d
   = isAlphaNum c && isAlphaNum d
  || isGraphic  c && isGraphic  d
  || c == '{' && d == '-'
  || c == '-' && d == '}'

lex :: ISource -> RefM (List (Token Spaced))
lex = mapM mkToken' . f . unISource
 where
  f NilCh = Nil
  f (groupCh glueChars -> (as, bs)) = as:. f bs

unlex :: List (Token Spaced) -> ISource
unlex = MkISource . mconcat . map showToken

instance Parse (List (Token Spaced)) where
  parse = parse >=> lex

instance Print (List (Token Spaced)) where
  print = pure . unlex >=> print


---------------------------------------------------------
--------------- structure and unstructure ---------------
---------------------------------------------------------


structure   :: List (Token Spaced) -> OpSeq' Spaced
structure = foldMap sing

unstructure :: OpSeq' Spaced -> List (Token Spaced)
unstructure = fromOpSeq

instance Parse (OpSeq' Spaced) where
  parse = parse >=> pure . structure

instance Print (OpSeq' Spaced) where
  print = pure . unstructure >=> print


---------------------------------------------------
--------------- string and unstring ---------------
---------------------------------------------------


string   :: (OpSeq' Spaced) -> (OpSeq' Stringed)
string = \case
  Node2 l a@"\"" (Node2 s b@"\"" r)
    | not (hasNl s), ss <- foldMap showToken $ fromOpSeq s
    -> coerce l <> sing (MkString (showToken a <> ss <> showToken b) (chars ss)) <> string r
  Node2 _ s@"\"" _ -> error' $ print s <&> \r -> "Unterminated string\n" <> r
  a -> coerce a
 where
  hasNl (Node2 _ "\n" _) = True
  hasNl _ = False

unstring :: (OpSeq' Stringed) -> (OpSeq' Spaced)
unstring = coerce -- TODO

instance Parse ((OpSeq' Stringed)) where
  parse = fmap string . parse

instance Print ((OpSeq' Stringed)) where
  print = print . unstring


-----------------------------------------------------
--------------- uncomment and comment ---------------
-----------------------------------------------------


uncomment :: (OpSeq' Stringed) -> (OpSeq' Uncomment)
uncomment = \case
    Node2 (Node2 l "--" c) "\n" r -> coerce l <> comm c <> sing "\v" <> uncomment r
    Node2 l                "\n" r -> coerce l <> sing "\v" <> uncomment r
    a -> coerce a

comment :: (OpSeq' Uncomment) -> (OpSeq' Stringed)
comment = mapOpSeq c  where
  c "\v" = sing "\n"
  c s = sing (coerce s)

instance Parse ((OpSeq' Uncomment)) where
  parse = fmap uncomment . parse

instance Print ((OpSeq' Uncomment)) where
  print = print . comment

comm s = coerce (filterOpSeq (`elem` ["\t", "\r", "\v"]) s)


-------------------------------------------------------
--------------- uncomments and comments ---------------
-------------------------------------------------------


uncomments :: (OpSeq' Uncomment) -> (OpSeq' Uncomments)
uncomments = \case
    Node3 l "{-" c "-}" r -> coerce l <> comm c <> uncomments r
    Node2 _ s@"{-" _ -> error' $ print s <&> \r -> "Unterminated comment\n" <> r
    Node2 _ s@"-}" _ -> error' $ print s <&> \r -> "Unterminated comment\n" <> r
    a -> coerce a

comments :: (OpSeq' Uncomments) -> (OpSeq' Uncomment)
comments = coerce

instance Parse (OpSeq' Uncomments) where
  parse = fmap uncomments . parse

instance Print (OpSeq' Uncomments) where
  print = print . comments


-------------------------------------------------
--------------- unspace and space ---------------
-------------------------------------------------


unspace :: (OpSeq' Uncomments) -> (OpSeq' Unspaced)
unspace = \case
    Node2 l " " r -> coerce l <> unspace r
    a -> coerce a

space :: (OpSeq' Unspaced) -> (OpSeq' Uncomments)
space = error "TODO: implement space"

instance Parse (OpSeq' Unspaced) where
  parse = fmap unspace . parse

instance Print (OpSeq' Unspaced) where
  print = print . space


--------------------------------------
--------------- layout ---------------
--------------------------------------


instance Parse (OpSeq' Layout) where
  parse = fmap layout . parse

instance Print (OpSeq' Layout) where
  print = print . spaceLayout

layout  :: OpSeq' Unspaced -> OpSeq' Layout
layout = g True
   where
    g :: Bool -> OpSeq' Unspaced -> OpSeq' Layout
    g top = \case
      Node2 l "\v" r -> semi top (g top l) (g top r)
      Node3 l "\t" a "\r" r
        | Node2 l "\v" Empty <- l, Node2 l "do" Empty <- l
        -> g top l <> brace True (g True a) <> g top r
        | Node2 l "\v" Empty <- l, Node2 l "where" Empty <- l
        -> g top l <> sing "whereBegin" <> g True a <> sing "whereEnd" <> g top r
        | Node2 l "\v" Empty <- l
        -> g top l <> f a <> g top r
        | True
        -> g top l <> g top a <> g top r
      Node2 _ t@"do"    _ -> error $ "Illegal " <> showToken t
      Node2 a "where" Empty -> g top a <> sing "whereBegin" <> sing "ModuleEnd" <> sing "whereEnd"
      Node2 _ t@"where" _ -> error $ "Illegal " <> showToken t
      a -> coerce a

    f (Node3 Empty "\t" a "\r" Empty) = f a
    f a = g False a

    semi _     a Empty = a
    semi _     Empty a = a
    semi True  a b = a <> sing ";" <> b
    semi False a b = a <> b

    brace _ Empty = Empty
    brace True  a = sing "(" <> a <> sing ")"
    brace False a = a


--------------------

data DocShape a
  = SingleLine a
  | MultiLine a a
  deriving (Eq)

firstLine (SingleLine i)  = i
firstLine (MultiLine i _) = i

lastLine  (SingleLine i)  = i
lastLine  (MultiLine _ i) = i

instance Semigroup a => Semigroup (DocShape a) where
  SingleLine a  <> SingleLine b  = SingleLine (a <> b)
  SingleLine a  <> MultiLine b c = MultiLine (a <> b) c
  MultiLine a b <> SingleLine c  = MultiLine a (b <> c)
  MultiLine a _ <> MultiLine _ d = MultiLine a d

instance Monoid a => Monoid (DocShape a) where
  mempty = SingleLine mempty

--------------------

data Nesting = MkPC (List Word) Word (List Word)

instance Semigroup Nesting where
  MkPC a x Nil      <> MkPC Nil y d      = MkPC a (max x y) d
  MkPC a x Nil      <> MkPC (c:. cs) y d = MkPC (a ++ (max x c):. cs) y d
  MkPC a x (c:. cs) <> MkPC Nil y d      = MkPC a x (d ++ (max y c):. cs)
  MkPC a x (b:. bs) <> MkPC (c:. cs) y d = MkPC a x bs <> MkPC Nil (max b c + 1) Nil <> MkPC cs y d

instance Monoid Nesting where
  mempty = MkPC Nil 0 Nil

--------------------

newtype Length = MkLength Word
  deriving (Eq, Ord)

instance Semigroup Length where
  MkLength a <> MkLength b = MkLength (a + b)

instance Monoid Length where
  mempty = MkLength 0


data Complexity = MkComplexity Nesting Length

instance Semigroup Complexity where
  MkComplexity a b <> MkComplexity a' b' = MkComplexity (a <> a') (b <> b')

instance Monoid Complexity where
  mempty = MkComplexity mempty mempty

maxComplexity :: Complexity -> Bool
maxComplexity (MkComplexity (MkPC a b c) l) = l < MkLength 80 && b < 2 && (null a && all (< 1) c || null c && all (< 2) a)

mkDocShape :: Token a -> DocShape Complexity
mkDocShape "\v" = MultiLine mempty mempty
mkDocShape s    = SingleLine (MkComplexity mempty (MkLength $ lengthCh $ showToken s))

--------------------

data Doc = MkDoc (Maybe (Interval (Token Uncomments))) (DocShape Complexity) (OpSeq' Uncomments)

instance Semigroup Doc where
  MkDoc a b c <> MkDoc a' b' c' = MkDoc (a <> a') (b <> b') (c <> c')

instance Monoid Doc where
  mempty = MkDoc mempty mempty mempty

mkDoc :: (Token Uncomments) -> Doc
mkDoc s = MkDoc (Just $ mkInterval s s) (mkDocShape s) (sing s)

hang1, hang :: Doc -> Doc
hang2 :: Word -> Doc -> Doc

hang1 (MkDoc a b c) = MkDoc a (mk (MkPC Nil 0 [0]) <> b <> mk (MkPC [0] 0 Nil)) c
 where
  mk c = SingleLine (MkComplexity c mempty)

hang2 n (MkDoc a b c) = MkDoc a b (mreplicate n (sing "\t") <> c <> mreplicate n (sing "\r"))

hang (MkDoc a b c)
  | MultiLine{} <- b = hang2 2 (MkDoc a b c)
hang (MkDoc a b c) = MkDoc a b c

sep :: (Complexity -> Bool) -> Doc -> Doc -> Doc
sep w a@(MkDoc ia da _) b@(MkDoc ib db _) = a <> op <> b
 where
  op1
    | Just (MkInterval _ a) <- ia
    , Just (MkInterval b _) <- ib
    , glueChars (lastCh $ showToken a) (headCh $ showToken b)
    || not (a `elem` ["(", "[", "{", "\\"]
         || b `elem` [".", ",", ":", ";", "}", ")", "]"]
           )
    = mkDoc " "
    | otherwise = mempty

  op
    | MkDoc _ s _ <- op1
    , w $ lastLine da <> firstLine s <> firstLine db
    = op1
    | otherwise = mkDoc "\v"

--------------------

seqToDoc :: (Complexity -> Bool) -> OpSeq' Layout -> Doc
seqToDoc w = f1
 where
  (<+>) = sep w

  g tok = mkDoc $ coerce tok

  f1, f2 :: OpSeq' Layout -> Doc
  f1 = \case
    (getSemis -> es@(_:._:._)) -> hang $ mkDoc "do" <> mkDoc "\v" <> foldl1 (<+>) (map ff es)
    Empty ->  mempty
    l := r ->  hang1 $ hang $ g l <+> f2 r
    l :> r ->                 g l <+> f1 r
    (l :< "###" :> Empty) :< r -> f1 l <> f1 r
    l :< r ->                f1 l <+> f1 r

  ff x = hang1 $ hang1 $ hang2 2 $ f1 x

  f2 = \case
    l := r ->  g  l <+> f2 r
    l :> r ->  g  l <+> f1 r
    l :< r ->  f1 l <+> f2 r
    Empty -> impossible

getSemis = \case
  Node2 l ";" r -> l:. getSemis r
  x -> [x]

spaceLayout :: OpSeq' Layout -> OpSeq' Uncomments
spaceLayout x  | MkDoc _ _ a <- seqToDoc maxComplexity x = a


--------------------------------------------
--------------- mixfix names ---------------
--------------------------------------------


data Mixfix a = MkM_ (Cached Arity) (List (Token a))

tokens (MkM_ _ ts) = ts

instance Eq  (Mixfix a) where (==) = (==) `on` tokens
instance Ord (Mixfix a) where compare = compare `on` tokens

pattern MkM a <- MkM_ _ a
  where MkM a =  mkM (MkCached $ arity a) a

mkM :: Cached Arity -> (List (Token a)) -> Mixfix a
mkM ar ts = MkM_ ar ts

{-# COMPLETE MkM #-}

instance IsString (Mixfix a) where
  fromString' t = MkM [fromString' t]
{-
instance Semigroup (Mixfix a) where
  MkM a <> MkM b = MkM (a <> b)
-}

instance IntHash (Mixfix a) where
  intHash (MkM_ _ ts) = intHash $ map intHash ts

instance IntHash (Token a) where
  intHash = \case
    MkToken_ h _ _ -> h
    MkNat_ _ n -> intHash (showInteger n)  -- TODO
    MkString_ _ s -> intHash s

-- strip os = filter (/= "___") os

enrich :: List (Token a) -> List (Token a)
enrich os = g os
 where
  g (o:. os)
    = maybeList "___" (fst (precedence o) /= fst topPrec)
      (o:. f (snd (precedence o) /= snd topPrec) os)
  g Nil = impossible

  f p (o:. os)
    = maybeList "___" (p && fst (precedence o) /= fst topPrec)
      (maybeList "###" (not p && fst (precedence o) == fst topPrec)
      (o:. f (snd (precedence o) /= snd topPrec) os))
  f p Nil = maybeList "___" p Nil

showMixfix :: Mixfix a -> Source
showMixfix (MkM ts) = mconcat $ map showToken $ map (\case "___" -> "_"; a -> a) $ filter (/= "###") $ enrich ts

instance Print (Mixfix a) where
  print = pure . showMixfix

{-
instance IsString (Mixfix a) where
  fromString' = MkM . (:.Nil) . fromString'
-}

pattern NTy    = MkM [":"]
pattern NLetTy = MkM [":",";"]
pattern NExpl  = MkM ["(",":",")"]
pattern NImpl  = MkM ["{",":","}"]

pattern NImport         = MkM ["import"]
pattern NLetImport      = MkM ["import",";"]
pattern NConstructor    = MkM ["constructor"]
pattern NConstructorTy  = MkM ["constructor",":"]
pattern NLetConstructor = MkM ["constructor",":",";"]
pattern NBuiltin        = MkM ["builtin"]
pattern NBuiltinTy      = MkM ["builtin",":"]
pattern NLetBuiltin     = MkM ["builtin",":",";"]
pattern NLetArr         = MkM ["<-",";"]

pattern NClass       = MkM ["class","whereBegin","whereEnd"]
pattern NLetClass    = MkM ["class","whereBegin","whereEnd",";"]
pattern NInstance    = MkM ["instance","whereBegin","whereEnd"]
pattern NLetInstance = MkM ["instance","whereBegin","whereEnd",";"]
pattern NData        = MkM ["data","whereBegin","whereEnd"]
pattern NLetData     = MkM ["data","whereBegin","whereEnd",";"]


pattern NGuard = MkM ["|"]
pattern NEnd   = MkM ["ModuleEnd"]

pattern NEq    = MkM ["="]
pattern NLet   = MkM ["=",";"]
pattern NTEq   = MkM [":","="]
pattern NTLet  = MkM [":","=",";"]
pattern NOEq   = MkM [":="]
pattern NOLet  = MkM [":=",";"]
pattern NOTEq  = MkM [":",":="]
pattern NOTLet = MkM [":",":=",";"]

pattern NLambda= MkM ["\\"]
pattern NLam   = MkM ["\\","->"]
pattern NTLam  = MkM ["\\","(",":",")","->"]
pattern NTHLam = MkM ["\\","{",":","}","->"]
pattern NHLam  = MkM ["\\","{","}","->"]

pattern NSemi  = MkM [";"]
pattern NParens= MkM ["(",")"]
pattern NBraces= MkM ["{","}"]
pattern NEmpty = MkM ["__"]
pattern NAny   = MkM ["_"]

pattern NHole :: Mixfix a
pattern NHole    = MkM ["_"]
pattern NLeftArr = MkM ["<-"]
pattern NArr     = MkM ["->"]
pattern NIArr    = MkM ["~>"]
pattern NView    = MkM ["-->"]
pattern NPi      = MkM ["(",":",")","->"]
pattern NHPi     = MkM ["{",":","}","->"]
pattern NCPi     = MkM ["=>"]
pattern NHArr    = MkM ["{","}","->"]
pattern NRule    = MkM ["==>"]
pattern NLetRule = MkM ["==>",";"]
pattern NDot     = MkM ["[","]"]

instance HasArity (Mixfix t) where
  arity (MkM_ (MkCached a) _) = a
instance HasArity (List (Token i)) where
  arity ["_"] = 0
  arity [t] | isInfix t = 0
  arity os = wordToInt . length . filter (== "___") $ enrich os



------------------------------------------------
--------------- expression trees ---------------
------------------------------------------------


data ExpTree_ b a
  = RVar a
  | RNat_ (Cached Source) Integer
  | RString_ (Cached Source) String
  | EApp Arity (ExpTree_ b a) (ExpTree_ b a)
  | REmbed b
  deriving (Eq)

type ExpTree = ExpTree_ Void

coerceExpTree :: ExpTree_ Void a -> ExpTree_ b a
coerceExpTree = unsafeCoerce

instance HasArity a => HasArity (ExpTree_ b a) where
  arity (RVar a) = arity a
  arity (EApp a _ _) = a
  arity _ = 0

pattern (:@) :: HasArity a => ExpTree_ b a -> ExpTree_ b a -> ExpTree_ b a
pattern f :@ e <- EApp _ f e
  where f :@ e =  EApp (arity f - 1) f e

pattern Apps :: HasArity a => a -> List (ExpTree_ b a) -> ExpTree_ b a
pattern Apps a es <- (getApps Nil -> Just (a, es))
  where Apps a es = foldl (:@) (RVar a) es

getApps es (RVar a) = Just (a, es)
getApps es (f :@ e) = getApps (e:. es) f
getApps _ _ = Nothing


pattern SApps os es <- (dup -> ((== 0) . arity -> True, Apps os es))

pattern a :@@ b <- (dup -> ((<0) . arity -> True, a :@ b))

{-# COMPLETE RVar, (:@), REmbed, RNat_, RString_ #-}

instance (IsString a, HasArity a) => IsString (ExpTree_ b a) where
  fromString' = RVar . fromString'

type ExpTree'_ b a = ExpTree_ b (Mixfix a)
type ExpTree' a = ExpTree (Mixfix a)


-------------------------------------------
--------------- unop and op ---------------
-------------------------------------------


instance Parse (ExpTree' Layout) where
  parse = fmap unop . parse

instance Print (ExpTree' Layout) where
  print = print . op

unop :: OpSeq' Layout -> ExpTree' Layout
unop Empty = RVar NEmpty
unop (topOp -> (os, l, ts, r)) = case os of
  Nil -> RVar NEmpty
  os | not $ operator os -> error $ "Mismatched operator: " <> showMixfix (MkM os)
  ["(",")"] | [t :> Empty] <- ts, isInfix t -> lf $ rf $ RVar $ MkM [t]           -- TODO: implement inverse of this in op
  _ -> lf $ rf $ Apps (MkM os) $ map unop $ fs ts
 where
  f Empty a = a
  f l a = unop l :@ a

  (lf, fs) = if fst (precedence $ head os) == fst topPrec
             then (f l, id)
             else (id, (l :.))
  rf x | snd (precedence $ last os) == snd topPrec, Empty <- r = x
  rf x = x :@ unop r

op :: ExpTree' Layout -> OpSeq' Layout
op = addParens . opt
 where
  opt e = case e of
    RVar NEmpty -> Empty
    Apps (MkM os) args -> alter mempty (enrich os) (map opt args)
    _ -> impossible

  alter acc         Nil      Nil   =        parens acc
  alter acc         Nil  (a:. as)  = alter (parens acc <> a) Nil as
  alter acc ("___":. os) (a:. as)  = alter (       acc <> a) os as
  alter acc ("___":. os)     Nil   = alter         acc       os Nil
  alter acc (o:.     os)     as   = alter   (acc <> sing o) os as

allJoin ((l :< "###" :> _) :< _ :> _) = allJoin l
allJoin (Empty :< _ :> Empty) = True
allJoin _ = False

parens a | allJoin a = a
parens a = sing "<!" <> a <> sing "!>"

addParens :: OpSeq' Layout -> OpSeq' Layout
addParens = flr Nothing Nothing
 where
  flr x y = \case
    Empty -> Empty
    Node3 a@Empty "<!"           b  "!>" Empty | p a b -> flr x y $ a <> b
    Node3 a       "<!" (Empty :< b) "!>" Empty | p a b -> flr x y $ a <> b
    Node3 a       "<!"           b  "!>" Empty -> flr x y $ a <> sing "(" <> b <> sing ")"
    a       :< b                               -> flr x (Just b) a <> gg b
   where
    gg = \case
      (sing -> b) :> c       -> b <> flr (Just b)       y  c
      (sing -> b) := c :< d  -> b <> flr (Just b) (Just d) c <> gg d
      _ -> impossible

    p a b = a > b && maybe True (< a) x && maybe True (< b) x && maybe True (b >) y
{-
isEmpty Empty = True
isEmpty _ = False
-}


-------------------------------------------------
--------------- patch and unpatch ---------------
-------------------------------------------------


instance Parse (ExpTree' POp) where
  parse = fmap (defEnd . patch) . parse

joinAtN i n (Apps (MkM (splitAt i -> (xs, zs)))
                  (splitAt n -> (as, Apps (MkM ys) bs:. cs))
            )
  = Apps (MkM $ xs <> ys <> zs) (as <> bs <> cs)
joinAtN _ _ _ = impossible

xApps :: Mixfix a -> List (ExpTree' a) -> ExpTree' a
xApps a b = norm $ Apps a b

dup a = (a, a)

pattern RApp a b <- a :@@ b
  where RApp a b =  a :@  b

norm r = case r of
  _ | arity r /= 0 -> r
  Apps (MkM ["#"])  [a, _] -> a
  Apps NSemi  [RVar NEmpty, a] -> a
  Apps NSemi  [a, RVar NEmpty] -> a
  _ | Just z <- gg NParens   NTy        -> z
  _ | Just z <- gg NBraces   NTy        -> z
  _ | Just z <- gg NEq       NTy        -> z
  _ | Just z <- gg NOEq      NTy        -> z
  _ | Just z <- gg NLet      NTy        -> z
  _ | Just z <- gg NOLet     NTy        -> z
  _ | Just z <- gg NSemi     NTy        -> z
  _ | Just z <- gg NHArr     NTy        -> z
  _ | Just z <- gg NHLam     NTy        -> z
  _ | Just z <- gg NConstructor NTy     -> z
  _ | Just z <- gg NBuiltin     NTy     -> z
  _ | Just z <- gg NSemi     NEq        -> z
  _ | Just z <- gg NSemi     NTEq       -> z
  _ | Just z <- gg NSemi     NOEq       -> z
  _ | Just z <- gg NSemi     NOTEq      -> z
  _ | Just z <- gg NSemi     NImport    -> z
  _ | Just z <- gg NSemi     NConstructorTy -> z
  _ | Just z <- gg NSemi     NBuiltinTy -> z
  _ | Just z <- gg NSemi     NLeftArr   -> z
  _ | Just z <- gg NSemi     NClass     -> z
  _ | Just z <- gg NSemi     NInstance  -> z
  _ | Just z <- gg NSemi     NData      -> z
  _ | Just z <- gg NSemi     NRule      -> z
  _ | Just z <- gg NLambda   NArr       -> z
  _ | Just z <- gg NLambda   NHArr      -> z
  _ | Just z <- gg NLambda   NPi        -> z
  _ | Just z <- gg NLambda   NHPi       -> z
  _ | Just z <- gg NLam      NExpl      -> z
  _ | Just z <- gg NLam      NImpl      -> z
  _ | Just z <- gg NLam      NBraces    -> z
  _ | Just z <- gg NArr      NExpl      -> z
  _ | Just z <- gg NArr      NImpl      -> z
  _ | Just z <- gg NArr      NBraces    -> z
  Apps NParens [a] -> a
  r -> r
 where
  (tt, as', rr) = case r of
    Apps tt@(MkM as') rr -> (tt, as', rr)
    _ -> undefined
  ii = length $ takeWhile (/= "___") $ filter (/= "###") $ enrich as'

  gg ((== tt) -> True) bs | SApps ((== bs) -> True) _:. _ <- rr = Just $ joinAtN ii 0 r
  gg _ _ = Nothing

patch :: ExpTree' Layout -> ExpTree' POp
patch = \case
  a :@ b -> norm $ patch a :@ patch b
  t -> coerce t

-- TODO: move to separate phase
defEnd :: ExpTree' POp -> ExpTree' POp
defEnd = addEnd . \case
  a :@ b -> defEnd a :@ defEnd b
  t -> t
 where
  addEnd = \case
    e@(SApps l _) | l `elem` [NTy, NEq, NTEq, NOEq, NOTEq, NImport, NConstructorTy, NBuiltinTy, NClass, NInstance, NData] -> xApps NSemi [e, REnd]
    e -> e

instance Print (ExpTree' POp) where
  print = print . unpatch

unpatch  :: ExpTree' POp -> ExpTree' Layout
unpatch = coerce



-------------------------------------------------------
--------------- Raw syntax constructors ---------------
-------------------------------------------------------


class Eq t => IsMixfix t where
  toMixfix   :: t -> Maybe (Mixfix a)
  fromMixfix :: Mixfix a -> t

instance IsMixfix (Mixfix a) where
  toMixfix = Just . coerce
  fromMixfix = coerce

pattern ZName :: IsMixfix a => Mixfix t -> a
pattern ZName ts <- (toMixfix -> Just ts)
  where ZName = fromMixfix

pattern ZApps l es = Apps (ZName l) es

pattern ZVar l = RVar (ZName l)

-- TODO: make it distinct from RApp?
pattern RHApp a b = RApp a (ZVar NBraces :@ b)

zVar l = ZVar (MkM l)

-- GHC bug if no type signature is given
pattern Hole :: (HasArity a, IsMixfix a) => ExpTree_ b a
pattern Hole           = ZVar NHole

pattern Lam    n     e = ZApps NLam   [RVar n,       e]
pattern RLam   n t   e = ZApps NTLam  [RVar n, t,    e]
pattern RHLam  n t   e = ZApps NTHLam [RVar n, t,    e]
pattern RPi    n t   e = ZApps NPi    [RVar n, t,    e]
pattern RHPi   n t   e = ZApps NHPi   [RVar n, t,    e]
pattern RCPi     t   e = ZApps NCPi   [        t,    e]
pattern RIPi     t   e = ZApps NIArr  [        t,    e]
pattern RLet   n t d e = ZApps NTLet  [RVar n, t, d, e]
pattern ROLet  n t d e = ZApps NOTLet [RVar n, t, d, e]
pattern RLetTy n t   e = ZApps NLetTy [RVar n, t,    e]
pattern RConstructor n t e = ZApps NLetConstructor [RVar n, t, e]
pattern RBuiltin     n t e = ZApps NLetBuiltin     [RVar n, t, e]
pattern RRule  a b   e = ZApps NLetRule [a, b, e]
pattern RDot   a       = ZApps NDot   [a]       -- .a   (in lhs)
pattern RView  a b     = ZApps NView  [a, b]
pattern RGuard a b     = ZApps NGuard [a, b]
pattern RImport     n e = ZApps NLetImport      [RVar n, e]
pattern RClass    a b c = ZApps NLetClass    [a, b, c]
pattern RInstance a b c = ZApps NLetInstance [a, b, c]
pattern RData     a b c = ZApps NLetData     [a, b, c]
pattern REnd            = ZApps NEnd Nil
pattern RAnn e t        = ZApps NExpl [e, t]

unGLam = \case
  _ :@@ _ -> Nothing
  ZApps a (RVar n:. es) :@ e | a `elem` [NLam, NHLam, NTLam, NTHLam, NPi, NHPi, NLetTy, NLetConstructor, NLetBuiltin, NTLet, NOTLet] -> Just (ZVar a:. es, n, e)
  _ -> Nothing

pattern GLam :: (HasArity a, IsMixfix a) => List (ExpTree_ b a) -> a -> ExpTree_ b a -> ExpTree_ b a
pattern GLam es n e <- (unGLam -> Just (es, n, e))
  where GLam (ZVar a:. es) n e = ZApps a (RVar n:. es) :@ e
        GLam _ _ _ = impossible

getBIcit = \case
  n@NExpl -> Just n
  n@NImpl -> Just n
  _ -> Nothing

pattern Bind a b c <- Apps (getBIcit -> Just a) [b, c]

getHArr = \case
  n@NLam -> Just n
  n@NArr -> Just n
  _ -> Nothing

pattern Arr  a b c <- Apps (getHArr -> Just a) [b, c]



-------------------------------------------------
--------------- desugar and sugar ---------------
-------------------------------------------------


isBind Bind{} = True
isBind _ = False

desugar :: ExpTree' POp -> RefM (ExpTree' Desug)
desugar e = pure $ coerce $ etr3 $ etr2 $ etr e where

  etr :: ExpTree' POp -> ExpTree' POp
  etr = \case
    Apps l [n :@ m, a, b] | l `elem` [NTLam, NTHLam, NPi, NHPi] -> etr $ xApps l [n, a, xApps l [m, a, b]]
    Apps l [a :@ b, e] | l == NLam || l == NHLam || l == NArr && isBind b || l == NHArr -> etr $ xApps l [a, xApps l [b, e]]
    a :@ b -> etr a :@ etr b
    l -> l

  etr2 :: ExpTree' POp -> ExpTree' POp
  etr2 = \case
    RVar l@NLam  :@ a :@ b -> xApps l [xApps NExpl [etr2 a, RVar NHole], etr2 b]
    RVar l@NHLam :@ a :@ b -> xApps l [xApps NTy   [etr2 a, RVar NHole], etr2 b]
    RVar l@NHArr :@ a :@ b -> xApps l [xApps NTy   [etr2 a, RVar NHole], etr2 b]
    RVar l@NArr  :@ a :@ b -> xApps l [xApps NExpl [RVar NAny, etr2 a], etr2 b]
    RVar l@NLetTy:@ n :@ t :@ (RVar z@NLet :@ n' :@ b :@ m) | n == n'
      -> etr2 $ xApps z [xApps (del 1 1 l) [n', t], b, m]
    RVar l@NLetTy:@ n :@ t :@ (RVar z@NOLet :@ n' :@ b :@ m) | n == n'
      -> etr2 $ xApps z [xApps (del 1 1 l) [n', t], b, m]
    RVar z@NOLet :@ n :@ b :@ m
      | RVar{} <- n -> xApps z [xApps NTy [etr2 n, RVar NHole], etr2 b, etr2 m]
    RVar z@NLet  :@ n :@ b :@ m
      | RVar{} <- n -> xApps z [xApps NTy [etr2 n, RVar NHole], etr2 b, etr2 m]
      | a <- etr2 n -> xApps (del 0 1 z) [xApps NRule [a, etr2 b], etr2 m]
    a :@ b -> etr2 a :@ etr2 b
    l -> l

  etr3 :: ExpTree' POp -> ExpTree' POp
  etr3 = \case
    SApps l es | l `elem` [ NGuard, NDot, NHole, NLetImport, NLetClass, NLetInstance, NLetData, NLetTy, NLetConstructor, NLetBuiltin, NTLet, NOTLet
                          , NPi, NHPi, NCPi, NIArr, NTLam, NTHLam, NBraces, NLetRule, NView, NExpl]
      -> Apps l $ map etr3 es
    SApps NLetArr [a, b, c] -> xApps ">>=" [etr3 b, xApps NTLam [etr3 a, RVar NHole, etr3 c]]
    SApps NSemi [b, c] -> xApps ">>=" [etr3 b, xApps NTLam [RVar NAny, RVar NHole, etr3 c]]
--    SApps NSemi [a, _] -> error' $ print a <&> \r -> "Definition expected\n" <> r
    a :@ b  -> etr3 a :@ etr3 b
    RVar n@(MkM [t]) | isAtom t || isUpperToken t || isLowerToken t   -> RVar n
    e -> error' $ print ({- pprint $ op $ unpatch -} e) <&> \r -> "Expression expected\n" <> r



del i j (MkM (splitAt i -> (as, splitAt j -> (_, bs)))) = MkM $ as <> bs

sugar :: ExpTree' Desug -> ExpTree' POp
sugar = coerce . sug . sug0
 where
  sug0 :: ExpTree' Desug -> ExpTree' Desug
  sug0 = \case
    Apps l@NTLam [RVar n, Hole, b]
      -> Apps (del 1 3 l) [RVar $ coerce n, sug0 b]
    Apps l@NPi [ZVar NAny, a, b]
      -> Apps (del 0 3 l) [sug0 a, sug0 b]
    Apps l@NLetRule [a, b, c]
      -> Apps (del 0 1 l) [Apps (del 1 1 l) [sug0 a, sug0 b], sug0 c]
    Apps l@NTLet [RVar n, Hole, b, c]
      -> Apps (del 0 1 l) [RVar n, sug0 b, sug0 c]
    Apps l@NOTLet [RVar n, Hole, b, c]
      -> Apps (del 0 1 l) [RVar n, sug0 b, sug0 c]
    a :@ b -> sug0 a :@ sug0 b
    a -> coerce a

  sug :: ExpTree' Desug -> ExpTree' Desug
  sug = \case
    Apps l@NArr [a, b]
      -> arrow l (sug a) (sug b)
    Apps l [RVar n, a, b] | l `elem` [NPi, NHPi]
      -> arrow (del 0 3 l) (Apps (del 3 1 l) [RVar n, sug a]) (sug b)
    Apps l@NLam [RVar n, b]
      -> arrow l (RVar n) (sug b)           -- \x (w : t)-> \(y : t) z-> e   ~>  \x (w y: t) z-> e
    Apps l [RVar n, a, b] | l `elem` [NTLam, NTHLam]
      -> arrow (del 1 3 l) (Apps (del 3 1 $ del 0 1 l) [RVar n, sug a]) (sug b)
    a :@ b -> sug a :@ sug b
    a -> a

  arrow :: Mixfix Desug -> ExpTree' Desug -> ExpTree' Desug -> ExpTree' Desug
  arrow arr n (Arr arr' m e) | arr == arr', Just nm <- n +@ m = Apps arr [nm, e]
   where
    a +@ (b :@@ c) | arr == NLam, Just ab <- a +@ b = Just $ ab :@ c
    (Bind pl n t) +@ (Bind pl' m t') | pl == pl', t == t' = Just $ Apps pl [n ++@ m, t]
    a +@ b | arr == NLam || isBind a && isBind b = Just $ a :@ b
    _ +@ _ = Nothing

    n ++@ (a :@ b) = (n ++@ a) :@ b
    n ++@ m = n :@ m
  arrow arr n e = Apps arr [n, e]


instance Parse (ExpTree'_ b Desug) where
  parse = parse >=> desugar
    >=> preprocess{-TODO: do in separate phase-}
    >=> pure . preprocess2{-TODO: do in separate phase-}

preprocess   :: ExpTree' Desug -> RefM (Raw_ a)
preprocess t = coerceExpTree <$> f t  where
    f = \case
      RImport (MkM [m]) e -> print m >>= \m -> importModule m >>= \fm -> f $ fm e
      RVar n -> pure $ RVar n
      a :@ b -> (:@) <$> f a <*> f b
      RNat_ a b -> pure $ RNat_ a b
      RString_ a b -> pure $ RString_ a b

preprocess2 t = f t  where
    f = \case
      RVar (MkM [MkNat s n]) -> RNat_ (MkCached s) n
      RVar (MkM [MkString s n]) -> RString_ (MkCached s) n
      RVar n -> RVar n
      REmbed x -> REmbed x
      a :@ b -> f a :@ f b
      RNat_ a b -> RNat_ a b
      RString_ a b -> RString_ a b

instance Print (ExpTree'_ b Desug) where
  print = print . sugar . unembed

unembed :: ExpTree_ a (Mixfix b) -> ExpTree_ a' (Mixfix b)
unembed = f where
  f = \case
    REmbed _ -> RVar "???"
    RNat_ (MkCached a) b -> RVar $ MkM [MkNat a b]
    RString_ (MkCached a) b -> RVar $ MkM [MkString a b]
    a :@ b -> f a :@ f b
    RVar n -> RVar n



----------------------------------------------
--------------- Name data type ---------------
----------------------------------------------


type NameStr = Mixfix Desug

data Name = MkName
  { nameStr :: NameStr
  , nameId  :: Word
  }

instance HasId Name where getId = nameId

showName = showMixfix . nameStr

instance IsMixfix Name where
  toMixfix (NConst n) = toMixfix n
  toMixfix _ = Nothing
  fromMixfix = NConst . fromMixfix

instance HasArity Name where
  arity = arity . nameStr

isGraphicMixfix (MkM (t:. _)) = isGraphicToken t
isGraphicMixfix _ = False

isConName (nameStr -> MkM [t]) = isUpperToken t
isConName _ = False

isVarName (nameStr -> MkM [t]) = isLowerToken t
isVarName _ = False

-- TODO: remove
neg :: Word -> Word
neg i = i .|. 9223372036854775808

hashNameStr :: NameStr -> Word
hashNameStr = neg . intHash

pattern NConst :: NameStr -> Name
pattern NConst n <- MkName n (isConstName n -> True)
  where NConst n@(MkM [MkToken_ h _ _]) | h >= 9223372036854775808 = MkName n h
        NConst n = MkName n (hashNameStr n)

isConstName (MkM [MkToken_ h _ _]) i = h >= 9223372036854775808 && h == i
isConstName n i = hashNameStr n == i

pattern RNat n <- RNat_ _ n
  where RNat n =  RNat_ (MkCached $ stringToSource $ showInteger n) n

pattern RString n <- RString_ _ n
  where RString n =  RString_ (MkCached $ stringToSource ("\"" <> n <> "\"")) n

mapName f (MkName a b) = MkName (f a) b
rename a = mapName $ const a

instance Eq  Name where (==)    = (==)    `on` nameId
instance Ord Name where compare = compare `on` nameId

instance Print Name where
  print = print . nameStr

instance IsString Name where
  fromString' t = case fromString' t of
    MkNat{}    -> impossible
    MkString{} -> impossible
    n -> NConst $ MkM [n]

mkName :: NameStr -> RefM Name
mkName s = newId <&> MkName s

mkName' s = newId <&> \i -> MkName (addSuffix s $ mkIntToken $ wordToInteger i) i

nameOf :: NameStr -> RefM Name
nameOf n@(MkM [MkToken_ h _ _]) | h >= 9223372036854775808 = pure $ NConst n
nameOf n = mkName n

type Raw_ a = ExpTree_ a NameStr


---------------------------------------------
--------------- import module ---------------
---------------------------------------------


importModule :: Source -> RefM (ExpTree' Desug -> ExpTree' Desug)
importModule m = do
  t <- importFile m
  pure $ include t

include :: ExpTree' Desug -> ExpTree' Desug -> ExpTree' Desug
include t s = f t
   where
    f :: ExpTree' Desug -> ExpTree' Desug
    f = \case
      RLet  n t a b -> RLet  n t a $ f b
      RRule   a b c -> RRule   a b $ f c
      ROLet n t a b -> ROLet n t a $ f b
      RLetTy  n a b -> RLetTy  n a $ f b
      RConstructor n a b -> RConstructor n a $ f b
      RBuiltin     n a b -> RBuiltin     n a $ f b
      RImport   a b -> RImport   a $ f b
      RClass    a b c -> RClass    a b $ f c
      RInstance a b c -> RInstance a b $ f c
      RData     a b c -> RData     a b $ f c
      REnd -> s
      _ -> undefined


-------------------------------------------------
--------------- scope and unscope ---------------
-------------------------------------------------


instance PPrint a => Print (Scoped_ a) where
  print = unscope >=> print

type Scoped_ a = ExpTree_ a Name

unscope :: PPrint a => Scoped_ a -> RefM (ExpTree' Desug)
unscope t = runReader (mempty :: IntMap Name Word, emptyMap :: Map NameStr Word) ff where

  addIndex n i = addSuffix (addSuffix n "_") $ mkIntToken $ wordToInteger i

  ff r = f t where

    f :: PPrint a => Scoped_ a -> RefM (ExpTree' Desug)
    f = \case
      REmbed a -> f $ pprint a
      RVar "Pi"  :@ a :@ Lam n e -> f $ RPi  n a e
      RVar "HPi" :@ a :@ Lam n e -> f $ RHPi n a e
      RVar "CPi" :@ a :@       e -> f $ RCPi   a e
      RVar "IPi" :@ a :@       e -> f $ RIPi   a e
      RVar v@(nameStr -> n) -> do
        k <- asks r (lookupIM v . fst)
        let m = maybe n (addIndex n) k
        pure $ RVar m
      GLam es v a
        | NConst n@"_" <- v -> GLam <$> mapM f es <*> pure n <*> f a
        | n <- nameStr v -> asks r (lookupIM v . fst) >>= \case
          _ -> do
            k <- asks r (lookupMap n . snd)
            let m = maybe n (addIndex n) k
            GLam <$> mapM f es <*> pure m <*> local r (maybe id (insertIM v) k *** insert n (1 + fromMaybe (0 :: Word) k)) (f a)
      a :@ b -> (:@) <$> f a <*> f b
      RNat_ (MkCached a) b -> pure $ RVar $ MkM [MkNat a b]
      RString_ (MkCached a) b -> pure $ RVar $ MkM [MkString a b]

addPrefix :: Token a -> Mixfix a -> Mixfix a
addPrefix s (MkM_ ar a) = mkM ar $ s:. a

addSuffix :: Mixfix a -> Token a -> Mixfix a
addSuffix (MkM_ ar a) s = mkM ar $ a ++ [s]


--------------------------------------
--------------- PPrint ---------------
--------------------------------------

class PPrint a where
  pprint :: a -> Scoped_ Void


instance (PPrint a, PPrint b) => PPrint (a, b) where
  pprint (a, b) = zVar ["(",",",")"] :@ pprint a :@ pprint b

instance PPrint a => PPrint (List a) where
  pprint Nil = zVar ["[","]"]
  pprint as = ZApps (MkM $ ["["] <> replicate (length as -. 1) "," <> ["]"]) $ map pprint as

instance PPrint () where
  pprint () = RVar "Unit"   -- TODO: ZVar ["(",")"], without "_"
{-
instance PPrint Int where
  pprint i = RVar $ fromString' $ showInteger i
-}
instance PPrint Word where
  pprint i = RVar $ fromString' $ showInt i
{-
instance PPrint String where
  pprint s = pprint (fromString' s :: Source)

instance PPrint Char where
  pprint c = pprint (fromString' [c] :: Source)
-}
instance PPrint Source where
  pprint = \case
    NilCh -> res ""
    Cons' c s
      | c == '\n' -> co (r "newline") s
      | c == '\t' -> co (r "begin")   s
      | c == '\r' -> co (r "end")     s
      | c == '\v' -> co (r "nl")      s
      | c == '\"' -> co (r "quote")   s    -- co (res c) s
    (spanCh (\c -> not $ c `elem` ['\n', '\t', '\r', '\"', '\v']) -> (as, bs))
      -> co (res as) bs
   where
    r s = pprintToken $ MkString s (chars s)
    res s = pprintToken $ MkString ("\"" <> s <> "\"") (chars s)
    co a NilCh = a
    co a b = RVar "<>" :@ a :@ pprint b

pprintToken :: Token Desug -> ExpTree Name
pprintToken t = RVar $ MkName (MkM [t]) 0{-TODO?-}

instance PPrint ISource where
  pprint = pprint . unISource

instance PPrint Void where
  pprint = impossible

instance (PPrint a) => PPrint (OpSeq a) where
  pprint Empty = RVar "_"
  pprint (a :> Empty) = pprint a
  pprint (sl :< b) = zVar ["[","]"] :@ foldl (:@) (pprint sl) (f b)  where
    f (b := c :< d) = pprint b:. pprint c:. f d
    f (b :> c) = pprint b:. pprint c:. Nil
    f _ = impossible

instance PPrint (Token a) where
  pprint = \case
    t | precedence t == topPrec -> pprintToken $ coerce t
    t -> pprint $ showToken t

instance PPrint (Mixfix a) where
  pprint (MkM [t]) | precedence t == topPrec = pprint t
  pprint s = pprintToken $ MkString x (chars x) where x = showMixfix s

instance PPrint Name where
  pprint = pprint . nameStr -- RVar ?

instance (Eq a, PPrint a, HasArity a) => PPrint (ExpTree_ b a) where
  pprint = f where
    f = \case
      RVar n     -> pprint n
      REmbed _   -> undefined
      a :@ b     -> RVar "@" :@ f a :@ f b
      RNat_ a b   -> RNat_ a b
      RString_ a b -> RString_ a b


showM a = print a <&> chars

