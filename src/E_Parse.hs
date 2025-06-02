{-# language CPP #-}
module E_Parse
  ( Arity

  , Phase (..), IString, Token, OpSeq

  , ExpTree
    ( Apps, RVar, (:@), Lam, RLam, RHLam, RPi, RHPi, RCPi, RIPi, RLet, ROLet, RLetTy, RConstructor, RBuiltin
    , Hole, RRule, RDot, RApp, RHApp, RView, RGuard
    , RClass, RInstance, RData, RNat, RString, REnd, RAnn, RCase, RCaseOf)
  , zVar, Tokens(..)

  , Mixfix, addPrefix, addSuffix, addIntSuffix, HasArity (..), IsMixfix (..), showMixfix
  , TokenSeq, ExpTree'

  , Name, nameOf, NameStr, nameStr, nameId, mkName, mkName', rename, showName
  , PPrint (pprint)
  ) where

import B_Base


------------------------------------------------------

type Arity = Int

class HasArity a where
  arity :: a -> Arity


-- TODO: remove
negIntHash i = intHash i .|. 9223372036854775808


------------------------------------------------------
--------------- precedence calculation ---------------
------------------------------------------------------


precedenceTableString :: String
precedenceTableString = topM (parseDataFile "precedences")

precedenceTableList :: List (Tup2 String (Either Precedence Precedence))
precedenceTableList = mkTable (lines precedenceTableString) where

  mkTable
    = mconcat
    . numberWith (\p f -> f p) 1
    . reverse
    . map (mconcat . map g . words)

  g s | headStr s == '_' = \p -> T2 (h (tailStr s)) (Left  p) :. Nil
  g s | lastStr s == '_' = \p -> T2 (h (initStr s)) (Right p) :. Nil
  g _ = impossible

  h "BEGIN"   = "\t"
  h "END"     = "\r"
  h "NEWLINE" = "\n"
  h "SPACE"   = " "
  h s         = s

lookupPrec :: String -> Precedences
lookupPrec s = case map snd $ filter ((== s) . fst) precedenceTableList of
  Left l :. Right r :. Nil -> MkPrecedences l r
  Right r :. Left l :. Nil -> MkPrecedences l r
  _ -> impossible

topPrec     = lookupPrec "ALPHA"
graphicPrec = lookupPrec "GRAPHIC"
maxPrec     = lookupPrec "MAXPREC"
minPrec     = lookupPrec "MINPREC"

defaultPrecedences (ConsChar c _) | isGraphic c = graphicPrec
defaultPrecedences _ = topPrec


---------------------------------------------------
--------------- unindent and indent ---------------
---------------------------------------------------


data IString = MkIString String

unIString (MkIString s) = s

instance IsString IString where
  fromString' s = MkIString <$> fromString' s

instance Parse IString where
  parse = parse >=> pure . unindent

instance Print IString where
  print = pure . indent >=> print

unindent :: String -> IString
unindent s = MkIString $ dropNl $ h "\n" 0 $ s <> "\n" where

  dropNl (ConsChar '\n' s) = s
  dropNl s = s

  h _  n NilStr = mreplicate n "\r"
  h nl n (spanStr (== ' ') -> T2 (lengthStr -> k) (spanStr (/= '\n') -> T2 as (ConsStr nl' cs)))
    | NilStr <- as  = nl <> h nl' n cs
    | True      = mreplicate (n -. k) "\r" <> nl <> mreplicate (k -. n) " " <> mreplicate (k -. n) "\t" <> fst (revSpanStr (== ' ') as) <> h nl' k cs
  h _ _ _ = impossible

indent   :: IString -> String
indent (MkIString s_) = g 0 s_  where

  g i (spanStr (== ' ') -> T2 sp (spanStr (== '\r') -> T2 ((i -.) . lengthStr -> i') cs)) = case cs of
    ConsStr c cs | c == "\n" -> c <> g i' cs
    cs   -> mreplicate i' " " <> sp <> f i' cs

  f i (spanStr (\c -> c /= '\n' && c /= '\r' && c /= '\t') -> T2 s cs) = s <> case cs of
    ConsStr c cs
      | c == "\t" -> f (i+1) cs
      | c == "\r" -> f (i-.1) cs
      | c == "\n" -> c <> g i cs
    NilStr | i == 0 -> ""
    NilStr -> impossible
    _ -> impossible


-----------------------------------------------
--------------- Token data type ---------------
-----------------------------------------------

data Phase
  = Spaced | Stringed | Uncomment | Uncomments | Unspaced | Layout | PatchedOp | Desug

data Token (a :: Phase)
  = MkToken TokenInfo String
  | MkLit String               -- TODO: remove?

newLit s = pure (MkLit s)

getLit (MkToken _ s) 
  | allStr isDigit s = Just s
  | ConsChar '"' _ <- s = Just s
  | True = Nothing

pattern MkLit' :: String -> Token a
pattern MkLit' s <- (getLit -> Just s)

instance Tag (Token a) where
  tag MkToken{} = 0
  tag MkLit{}   = 1

instance Ord (Token a) where
  compare (MkToken i _) (MkToken i' _) = compare i i'
  compare (MkLit s)     (MkLit s')     = compare s s'
  compare a b = compareTag a b

showToken = \case
  MkToken _ s -> s
  MkLit     s -> s

data TokenInfo = MkTI Bool{-global-} Word{-id-} Precedences

instance HasPrecedences TokenInfo where
  precedences (MkTI _ _ p) = p

instance HasPrecedences (Token a) where
  precedences (MkToken i _) = precedences i
  precedences _ = topPrec

srcId (MkTI _ i _) = i

instance Ord TokenInfo where compare = compare `on` srcId

instance IsString (Token a) where
  fromString' cs = do
    s <- fromString' cs
    -- traceShow "isString" $ pure s
    parseToken s

parseToken :: String -> RefM (Token a)
parseToken cs
  | allStr isDigit cs = newLit cs
  | True = do
   ti <- lookupSM cs tokenMap >>= \case
    Just i -> pure i
    Nothing -> do
      i <- newId
      let ip = MkTI False i (defaultPrecedences cs)
      insertSM cs ip tokenMap
      pure ip
   pure $ MkToken ti cs

{-# noinline tokenMap #-}
tokenMap :: StringMap TokenInfo
tokenMap = topStringMap \m -> do
  forM_ precedenceTableList \(T2 s lr) -> lookupSM s m >>= \case
    Nothing -> do
      _n <- newId
      insertSM s (MkTI True (negIntHash s) (either (\l -> MkPrecedences l 0) (\r -> MkPrecedences 0 r) lr)) m
    Just (MkTI gl w (MkPrecedences l' r'))
      -> insertSM s (MkTI gl w (either (\l -> MkPrecedences l r') (\r -> MkPrecedences l' r) lr)) m
  do
    let infixr 5 .+
        (.+) :: String -> RefM Tup0 -> RefM Tup0
        s .+ mm = do
          mm
          _n <- newId
          lookupSM s m >>= \case
            Just{} -> error $ "impossible at tokenMap: " <<>> pure s
            _  -> insertSM s (MkTI True (negIntHash s) (defaultPrecedences s)) m

    "_" .+ "View" .+ "Guard" .+ "Dot" .+ "Fail" .+ "noreturn" .+ "Ap"
     .+ "lookupDict" .+ "superClasses" .+ "SuperClassList" .+ "SuperClassNil" .+ "SuperClassCons"
     .+ "Bool" .+ "True" .+ "False" .+ "Nat" .+ "wordToNat" .+ "Word" .+ "ProdWord" .+ "PairWord" .+ "WSuc" .+ "WSucOk"
     .+ "succView" .+ "EqWord" .+ "DecWord" .+ "AddWord" .+ "MulWord" .+ "DivWord" .+ "ModWord"
     .+ "String" .+ "ProdStr" .+ "PairStr" .+ "ConsStr" .+ "ConsOk" .+ "consView" .+ "AppendStr" .+ "EqStr" .+ "TakeStr" .+ "DropStr"
     .+ "Ty" .+ "Arr" .+ "Prod" .+ "Code" .+ "Lam" .+ "App" .+ "Pair" .+ "Fst" .+ "Snd"
     .+ "Match" .+ "OBool" .+ "OTrue" .+ "OFalse" .+ "OString" .+ "MkOString" .+ "OEqStr" .+ "OWord" .+ "MkOWord" .+ "OEqWord"
     .+ "___" .+ "__" .+ "ModuleEnd" .+ "Type" .+ "HPi" .+ "CPi" .+ "IPi" .+ "Pi"
     .+ "Erased" .+ "X" .+ "match" .+ "fail" .+ "TopLet" .+ "Let" .+ "EMBEDDED"
     .+ pure T0

  do
    let infixr 5 .+
        (.+) :: String -> RefM Tup0 -> RefM Tup0
        s .+ mm = do
          mm
          i <- newId
          insertSM s (MkTI False i (defaultPrecedences s)) m

    "c" .+ "h" .+ "w" .+ "v" .+ "q" .+ "i" .+ "s" .+ "d" .+ "t" .+ "z" .+ "m" .+ "a" .+ "l" .+ "caseFun"
     .+ "TODO" .+ "Meta" .+ "noret" .+ "ret" .+ "return" .+ "Term" .+ "Variable" .+ "Funct" .+ "Constr" .+ "Var"
     .+ "sel" .+ "_t" .+ "'" .+ "Dict"
     .+ pure T0


instance Parse (Token a) where
  parse = parse >=> parseToken

instance Print (Token a) where
  print = pure . showToken


isInfix :: Token a -> Bool
isInfix (precedences -> p) = minPrec `less` p && p `less` maxPrec  where

  MkPrecedences a b `less` MkPrecedences c d = a < c && b < d

isAtom :: Token a -> Bool
isAtom t = precedences t == topPrec || isInfix t


type TokenSeq a = OpSeq (Token a)

instance IsString (TokenSeq a) where
  fromString' s = singOpSeq <$> fromString' s


---------------------------------------------
--------------- lex and unlex ---------------
---------------------------------------------


glueChars :: Char -> Char -> Bool
glueChars c d
   = isAlphaNum c && isAlphaNum d
  || isGraphic  c && isGraphic  d
  || c == '{' && d == '-'
  || c == '-' && d == '}'

lex :: IString -> RefM (List (Token Spaced))
lex = mapM parse . f . unIString  where

  f NilStr = Nil
  f (groupStr glueChars -> T2 as bs) = as :. f bs

unlex :: List (Token Spaced) -> IString
unlex = MkIString . mconcat . map showToken

instance Parse (List (Token Spaced)) where
  parse = parse >=> lex

instance Print (List (Token Spaced)) where
  print = pure . unlex >=> print


---------------------------------------------------------
--------------- structure and unstructure ---------------
---------------------------------------------------------


structure :: List (Token Spaced) -> TokenSeq Spaced
structure = foldMap singOpSeq

unstructure :: TokenSeq Spaced -> List (Token Spaced)
unstructure t = appEndo (foldMapOpSeq (\a -> MkEndo (a :.)) t) Nil

instance Parse (TokenSeq Spaced) where
  parse = parse >=> pure . structure

instance Print (TokenSeq Spaced) where
  print = pure . unstructure >=> print


---------------------------------------------------
--------------- string and unstring ---------------
---------------------------------------------------


string :: TokenSeq Spaced -> TokenSeq Stringed
string = \case
  Node2 l a@"\"" (Node2 s b@"\"" r) | not (hasNl s)
    -> coerce l <> singOpSeq (MkLit $ showToken a <> appEndo (foldMapOpSeq (\t -> MkEndo (showToken t <>)) s) (showToken b)) <> string r
  Node2 _ s@"\"" _ -> error $ "Unterminated string\n" <<>> print s
  a -> coerce a
 where
  hasNl (Node2 _ "\n" _) = True
  hasNl _ = False

instance Parse (TokenSeq Stringed) where
  parse = (<$>) string . parse

instance Print (TokenSeq Stringed) where
  print = print . (coerce :: TokenSeq Stringed -> TokenSeq Spaced)


-----------------------------------------------------
--------------- uncomment and comment ---------------
-----------------------------------------------------


uncomment :: TokenSeq Stringed -> TokenSeq Uncomment
uncomment = \case
    Node2 (Node2 l "--" c) "\n" r -> coerce l <> comm c <> "SEMI" <> uncomment r
    Node2 l                "\n" r -> coerce l <> "SEMI" <> uncomment r
    a -> coerce a

comm s = coerce (filterOpSeq (`elem` ("\t" :. "\r" :. "SEMI" :. Nil)) s)

comment :: TokenSeq Uncomment -> TokenSeq Stringed
comment = foldMapOpSeq c  where
  c "SEMI" = "\n"
  c s = singOpSeq (coerce s)

instance Parse (TokenSeq Uncomment) where
  parse = (uncomment <$>) . parse

instance Print (TokenSeq Uncomment) where
  print = print . comment


-------------------------------------------------------
--------------- uncomments and comments ---------------
-------------------------------------------------------


uncomments :: TokenSeq Uncomment -> TokenSeq Uncomments
uncomments = \case
    Node3 l "{-" c "-}" r -> coerce l <> comm c <> uncomments r
    Node2 _ s@"{-" _ -> error $ print s <&> \r -> "Unterminated comment\n" <> r
    Node2 _ s@"-}" _ -> error $ print s <&> \r -> "Unterminated comment\n" <> r
    a -> coerce a

comments :: TokenSeq Uncomments -> TokenSeq Uncomment
comments = coerce

instance Parse (TokenSeq Uncomments) where
  parse = (<$>) uncomments . parse

instance Print (TokenSeq Uncomments) where
  print = print . comments


-------------------------------------------------
--------------- unspace and space ---------------
-------------------------------------------------


unspace :: TokenSeq Uncomments -> TokenSeq Unspaced
unspace = \case
    Node2 l " " r -> coerce l <> unspace r
    a -> coerce a

-- remove immediately nested BEGIN END pairs
-- remove incomplete semicolons candidates
simplify = f  where

  f = \case
    Node2 l s@"SEMI" r -> node2 s (f l) (f r)
    Node3 l s@"\t" a t@"\r" r -> node3 (f l) s (f $ skip a) t (f r)
    Node2 l s r | s == "do" || s == "where" || s == "of" -> f l <> singOpSeq s <> f r
    a -> a

  node2 _ Empty a = a
  node2 _ a Empty = a
  node2 s a b = a <> singOpSeq s <> b

  node3 a _ Empty _ b = a <> b
  node3 a x b y c = a <> singOpSeq x <> b <> singOpSeq y <> c

  skip (Node3 Empty "\t" a "\r" Empty) = skip a
  skip a = a

space :: TokenSeq Unspaced -> TokenSeq Uncomments
space _ = error "TODO: implement space"

instance Parse (TokenSeq Unspaced) where
  parse = (<$>) (simplify . unspace) . parse

instance Print (TokenSeq Unspaced) where
  print = print . space


--------------------------------------
--------------- layout ---------------
--------------------------------------


instance Parse (TokenSeq Layout) where
  parse = (<$>) layout . parse

layout  :: TokenSeq Unspaced -> TokenSeq Layout
layout = snd . g True  where

  g :: Bool{-not inside braces-} -> TokenSeq Unspaced -> Tup2 Bool (TokenSeq Layout)
  g top = \case
    Node2 l "SEMI" r -> T2 False $ coerce l <> semi (g top r)

    Node3 l "\t" a "\r" r -> T2 True $ coerce l <> snd (g False a) <> semi (g top r)

    Node2 l "do"    (Node3 Empty "\t" a "\r" r)
      -> T2 False $ coerce l <>          "(" <> snd (g True a) <>        ")" <> semi (g top r)
    Node2 l "where" (Node3 Empty "\t" a "\r" r)
      -> T2 False $ coerce l <> "whereBegin" <> snd (g True a) <> "whereEnd" <> semi (g top r)
    Node2 l "of"    (Node3 Empty "\t" a "\r" r)
      -> T2 False $ coerce l <>    "ofBegin" <> snd (g True a) <>    "ofEnd" <> semi (g top r)

    -- TODO?
    Node2 a "where" b -> T2 False $ coerce a <> "whereBegin" <> "ModuleEnd" <> "whereEnd" <> semi (g top b)

    Node2 _ t _  | t == "do" || t == "where" || t == "of" -> error $ "Illegal " <<>> print t

    a -> T2 False (coerce a)
   where
    semi (T2 indent b) | not top || indent  = b
    semi (T2 _ b)  = ";" <> b


-------------------------------------------------
--------------- inverse of layout ---------------
-------------------------------------------------


data DocShape a
  = SingleLine a
  | MultiLine a a

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

{-
Nesting is a string of ')' and '(' characters, like ")((())()))()(((())".

Well-balanced substrings are compressed to a number, the maximal depth:
  ")((())()))()(((())"   -->
  ")((1 )1 ))1 (((1 )"   -->
  ")(2     ))1 ((2   "   -->
  ")3       )1 ((2   ".

Next, the left and right parens are split:
  ")3)", 1, "((2"

Add 0-s where a parens has no number :
  "0)3)", 1, "(0(2"

Finally, form lists (the second is reversed):
  [0,3], 1, [2, 0]
-}

{- unoptimized version
data Nesting = MkNesting (List Word) Word (List Word)

instance Semigroup Nesting where
  MkNesting a x Nil      <> MkNesting Nil      y d  = MkNesting a (max x y) d
  MkNesting a x Nil      <> MkNesting (c:. cs) y d  = MkNesting (a ++ max x c :. cs) y d
  MkNesting a x (c:. cs) <> MkNesting Nil      y d  = MkNesting a x (d ++ max y c :. cs)
  MkNesting a x (b:. bs) <> MkNesting (c:. cs) y d  = MkNesting a x bs <> MkNesting Nil (max b c + 1) Nil <> MkNesting cs y d

instance Monoid Nesting where
  mempty = MkNesting Nil 0 Nil

leftNesting  = MkNesting Nil 0 (0 :. Nil)    -- '('
rightNesting = MkNesting (0 :. Nil) 0 Nil    -- ')'

smallNesting (MkNesting a b c) = b < 2 && (null a && all (< 1) c || null c && all (< 2) a)
-}
-- optimized version
data Nesting = MkNesting (List Word) Word Word | Big

mkNesting True a b c = MkNesting a b c
mkNesting _ _ _ _ = Big

instance Semigroup Nesting where
  MkNesting a x 0 <> MkNesting Nil      y d  | xy <- max x y = mkNesting (xy < 2 && null a || d == 0) a xy d
  MkNesting a x 0 <> MkNesting (c:. cs) y d  | xc <- max x c = mkNesting (xc < 2) (a ++ xc :. cs) y d
  MkNesting a x n <> MkNesting Nil      y d  = mkNesting (y == 0) a x (d + n + 1)
  MkNesting a x n <> MkNesting (c:. cs) y d  | c + 1 < 2 = MkNesting a x (n -. 1) <> MkNesting Nil (c + 1) 0 <> MkNesting cs y d
  _               <> _                       = Big

instance Monoid Nesting where
  mempty = MkNesting Nil 0 0

leftNesting  = MkNesting Nil        0 1    -- '('
rightNesting = MkNesting (0 :. Nil) 0 0    -- ')'

smallNesting Big = False
smallNesting _   = True

--------------------

data Length = MkLength Word

instance Ord Length where compare (MkLength a) (MkLength b) = compare a b

instance Semigroup Length where
  MkLength a <> MkLength b = MkLength (a + b)

instance Monoid Length where
  mempty = MkLength 0


data Complexity = MkComplexity Nesting Length

instance Semigroup Complexity where
  MkComplexity a b <> MkComplexity a' b' = MkComplexity (a <> a') (b <> b')

instance Monoid Complexity where
  mempty = MkComplexity mempty mempty

smallComplexity :: Complexity -> Bool
smallComplexity (MkComplexity n l) = l < MkLength 80 && smallNesting n

mkDocShape :: Token Layout -> DocShape Complexity
mkDocShape s
  | s == "SEMI" || s == "\n"  = MultiLine mempty mempty
  | True    = SingleLine (MkComplexity mempty (MkLength $ lengthStr $ showToken s))

--------------------

{- unoptimized version

type DocBuilder = TokenSeq Uncomments

pureDB = singOpSeq

evalDocBuilder = id

mkNl = mkDoc "SEMI"

-}

type DocBuilder = Endo (List (Token Spaced))

pureDB :: Token Spaced -> DocBuilder
pureDB a = MkEndo (a :.)

mkNl = mkDoc "\n"

evalDocBuilder t = appEndo t Nil

instance IsString DocBuilder where
  fromString' s = pureDB <$> fromString' s

-- end of optimized version


data Interval a = MkInterval a a

mkInterval a b = MkInterval a b

instance Semigroup (Interval a) where
  MkInterval a _ <> MkInterval _ b = MkInterval a b


data Doc = MkDoc (Maybe (Interval (Token Layout))) (DocShape Complexity) DocBuilder

instance Semigroup Doc where
  MkDoc a b c <> MkDoc a' b' c' = MkDoc (a <> a') (b <> b') (c <> c')

instance Monoid Doc where
  mempty = MkDoc mempty mempty mempty

mkDoc :: Token Layout -> Doc
mkDoc s = MkDoc (Just $ mkInterval s s) (mkDocShape s) (pureDB $ coerce s)

hang1, hang :: Doc -> Doc
hang2 :: Word -> Doc -> Doc

hang1 (MkDoc a b c) = MkDoc a (mk leftNesting <> b <> mk rightNesting) c where

  mk c = SingleLine (MkComplexity c mempty)

hang2 n (MkDoc a b c) = MkDoc a b (mreplicate n ("\t") <> c <> mreplicate n ("\r"))

hang (MkDoc a b c)
  | MultiLine{} <- b = hang2 2 (MkDoc a b c)
hang (MkDoc a b c) = MkDoc a b c

sep :: (Complexity -> Bool) -> Doc -> Doc -> Doc
sep w a@(MkDoc ia da _) b@(MkDoc ib db _) = a <> op <> b where

  op1
    | Just (MkInterval _ a) <- ia
    , Just (MkInterval b _) <- ib
    , glueChars (lastStr $ showToken a) (headStr $ showToken b)
    || not (a `elem` ("(" :. "[" :. "{" :. "\\" :. Nil)
         || b `elem` ("," :. ";" :. "}" :. ")" :. "]" :. Nil)
           )
    = mkDoc " "
    | True = mempty

  op
    | MkDoc _ s _ <- op1
    , w $ lastLine da <> firstLine s <> firstLine db
    = op1
    | True = mkNl

--------------------

seqToDoc :: (Complexity -> Bool) -> TokenSeq Layout -> Doc
seqToDoc w = f1  where

  (<+>) = sep w

  f1, f2 :: TokenSeq Layout -> Doc
  f1 = \case
    (getSemis -> es@(_:._:._)) -> hang $ mkDoc "do" <> mkNl <> foldl1 (<+>) (map ff es)
    Empty ->  mempty
    l := r ->  hang1 $ hang $ mkDoc l <+> f2 r
    l :> r ->                 mkDoc l <+> f1 r
    (l :< "###" :> Empty) :< r -> f1 l <> f1 r
    l :< r ->                f1 l <+> f1 r

  ff x = hang1 $ hang1 $ hang2 2 $ f1 x

  f2 = \case
    l := r ->  mkDoc  l <+> f2 r
    l :> r ->  mkDoc  l <+> f1 r
    l :< r ->  f1     l <+> f2 r
    Empty -> impossible

getSemis = \case
  Node2 l ";" r -> l:. getSemis r
  x -> x :. Nil

spaceLayout :: TokenSeq Layout -> DocBuilder
spaceLayout x  | MkDoc _ _ a <- seqToDoc smallComplexity x = a

instance Print (TokenSeq Layout) where
  print = print . evalDocBuilder . spaceLayout


--------------------------------------------
--------------- mixfix names ---------------
--------------------------------------------


data Tokens a
  = NilT
  | Token a :! Tokens a

infixr 5 :!

instance Tag (Tokens a) where
  tag NilT     = 0
  tag (_ :! _) = 1

instance Ord (Tokens a) where
  compare (a :! as) (b :! bs) = compare a b &&& lazy (compare as bs)
  compare a b = compareTag a b

instance Semigroup (Tokens a) where
  NilT      <> xs = xs
  (x :! xs) <> ys = x :! (xs <> ys)


isOperator :: Tokens a -> Bool
isOperator = \case
  _ :! NilT -> True
  "if" :! "then" :! "else" :! NilT -> True
  "(" :! ")"    :! NilT -> True
  "{" :! "}"    :! NilT -> True
  "[" :! "]"    :! NilT -> True
  "\\" :! "->"  :! NilT -> True
  "let" :! "in" :! NilT -> True
  "class" :!    "whereBegin" :! "whereEnd" :! NilT -> True
  "instance" :! "whereBegin" :! "whereEnd" :! NilT -> True
  "data" :!     "whereBegin" :! "whereEnd" :! NilT -> True
  "case" :!        "ofBegin" :!    "ofEnd" :! NilT -> True
  _ -> False


splitAt' :: Word -> Tokens a -> Tup2 (Tokens a) (Tokens a)
splitAt' 0 xs   = T2 NilT xs
splitAt' _ NilT = T2 NilT NilT
splitAt' i (x :! xs) | T2 as bs <- splitAt' (i-.1) xs = T2 (x :! as) bs

replicate' :: Word -> Token a -> Tokens a
replicate' 0 _ = NilT
replicate' i t = t :! replicate' (i -. 1) t


instance IntHash (Token a) where
  intHash = \case
    MkToken h _ -> srcId h
    MkLit s -> intHash s

instance HasId (Token a) where
  getId = \case
    MkToken h _ -> srcId h
    _ -> impossible


instance IntHash (Tokens a) where
  intHash = f 0 where
    f acc NilT = acc
    f acc (t :! ts) = f (33 * acc + intHash t) ts



data Mixfix a = MkM_ Arity (Tokens a)

tokens (MkM_ _ ts) = ts

instance Ord (Mixfix a) where compare = compare `on` tokens

pattern MkM a <- MkM_ _ a
  where MkM a =  mkM (arity a) a

pattern MSing a = MkM (a :! NilT)

mkM :: Arity -> Tokens a -> Mixfix a
mkM ar ts = MkM_ ar ts

{-# COMPLETE MkM #-}

{-
instance Semigroup (Mixfix a) where
  MkM a <> MkM b = MkM (a <> b)
-}

instance IntHash (Mixfix a) where
  intHash (MkM (t :! NilT)) = intHash t
  intHash (MkM ts) = intHash ts


instance HasId (Mixfix a) where
  getId (MkM (t :! NilT)) = getId t
  getId m = negIntHash m


-- strip os = filter (/= "___") os

enrich :: Tokens a -> List (Token a)
enrich os = g os where

  g (o:! os)
    = condCons (leftPrec (precedences o) /= leftPrec topPrec) "___"
      (o:. f (rightPrec (precedences o) /= rightPrec topPrec) os)
  g NilT = impossible

  f p (o:! os)
    = condCons (p && leftPrec (precedences o) /= leftPrec topPrec) "___"
      (condCons (not p && leftPrec (precedences o) == leftPrec topPrec) "###"
      (o:. f (rightPrec (precedences o) /= rightPrec topPrec) os))
  f p NilT = condCons p "___" Nil

showMixfix :: Mixfix a -> String
showMixfix (MkM ts) = mconcat $ map showToken $ map (\case "___" -> "_"; a -> a) $ filter (/= "###") $ enrich ts

instance Print (Mixfix a) where
  print = pure . showMixfix

instance IsString (Mixfix a) where
  fromString' s = MSing <$> fromString' s

class Ord t => IsMixfix t where
  fromMixfix :: Mixfix a -> t

instance IsMixfix (Mixfix a) where
  fromMixfix = coerce

instance IsMixfix (ExpTree (Mixfix a)) where
  fromMixfix a = RVar (fromMixfix a) -- <<<

zVar l = RVar (fromMixfix $ MkM l)

cmp l a = fromMixfix (MkM l) == a

#define MM(n, l) pattern n <- (cmp (l) -> True) where n = fromMixfix (MkM (l))

MM(NTy    , ":":!NilT)
MM(NLetTy , ":":!";":!NilT)
MM(NExpl  , "(":!":":!")":!NilT)
MM(NImpl  , "{":!":":!"}":!NilT)

MM(NImport         , "import":!NilT)
MM(NLetImport      , "import":!";":!NilT)
MM(NConstructor    , "constructor":!NilT)
MM(NConstructorTy  , "constructor":!":":!NilT)
MM(NLetConstructor , "constructor":!":":!";":!NilT)
MM(NBuiltin        , "builtin":!NilT)
MM(NBuiltinTy      , "builtin":!":":!NilT)
MM(NLetBuiltin     , "builtin":!":":!";":!NilT)
MM(NLetArr         , "<-":!";":!NilT)

MM(NClass       , "class":!"whereBegin":!"whereEnd":!NilT)
MM(NLetClass    , "class":!"whereBegin":!"whereEnd":!";":!NilT)
MM(NInstance    , "instance":!"whereBegin":!"whereEnd":!NilT)
MM(NLetInstance , "instance":!"whereBegin":!"whereEnd":!";":!NilT)
MM(NData        , "data":!"whereBegin":!"whereEnd":!NilT)
MM(NLetData     , "data":!"whereBegin":!"whereEnd":!";":!NilT)

MM(NCaseOf      , "case":!"ofBegin":!"ofEnd":!NilT)
MM(NCaseArr     , "--->":!NilT)
MM(NCase        , "--->":!";":!NilT)


MM(NGuard , "|":!NilT)
MM(NEnd   , "ModuleEnd":!NilT)

MM(NEq    , "=":!NilT)
MM(NLet   , "=":!";":!NilT)
MM(NTEq   , ":":!"=":!NilT)
MM(NTLet  , ":":!"=":!";":!NilT)
MM(NOEq   , ":=":!NilT)
MM(NOLet  , ":=":!";":!NilT)
MM(NOTEq  , ":":!":=":!NilT)
MM(NOTLet , ":":!":=":!";":!NilT)

MM(NLam   , "\\":!"->":!NilT)
--MM(NTLam  , "\\":!"(":!":":!")":!"->":!NilT)

MM(NTLam, "\\":!"(":!":":!")":!"->":!NilT)

MM(NTHLam , "\\":!"{":!":":!"}":!"->":!NilT)
MM(NHLam  , "\\":!"{":!"}":!"->":!NilT)

MM(NSemi  , ";":!NilT)
MM(NParens, "(":!")":!NilT)
MM(NBraces, "{":!"}":!NilT)
MM(NEmpty , "__":!NilT)
MM(NAny   , "_":!NilT)

MM(NHole    , "_":!NilT)
MM(NLeftArr , "<-":!NilT)
MM(NArr     , "->":!NilT)
MM(NIArr    , "~>":!NilT)
MM(NView    , "-->":!NilT)
MM(NPi      , "(":!":":!")":!"->":!NilT)
MM(NHPi     , "{":!":":!"}":!"->":!NilT)
MM(NCPi     , "=>":!NilT)
MM(NHArr    , "{":!"}":!"->":!NilT)
MM(NRule    , "==>":!NilT)
MM(NLetRule , "==>":!";":!NilT)
MM(NDot     , "[":!"]":!NilT)

instance HasArity (Mixfix t) where
  arity (MkM_ a _) = a

instance HasArity (Tokens i) where
  arity ("_" :! NilT) = 0
  arity (t :! NilT) | isInfix t = 0
  arity os = wordToInt . length . filter (== "___") $ enrich os



------------------------------------------------
--------------- expression trees ---------------
------------------------------------------------


data ExpTree a
  = RVar a
  | RNat_ String Word
  | RString_ String String
  | EApp Arity (ExpTree a) (ExpTree a)
{-
pattern TNat_ s n <- MkLit s@(readWord -> Just n)
  where TNat_ s _  = MkLit s

pattern RNat_ :: String -> Word -> ExpTree (Mixfix a)
pattern RNat_ s n = RVar (MSing (TNat_ s n))
-}
instance Tag (ExpTree a) where
  tag RNat_{} = 1
  tag RString_{} = 2
  tag RVar{} = 0
  tag EApp{} = 3

instance Ord a => Ord (ExpTree a) where
  compare (RNat_ _ a) (RNat_ _ a') = compare a a'
  compare (RString_ _ a) (RString_ _ a') = compare a a'
  compare (RVar a) (RVar a') = compare a a'
  compare (EApp _ a b) (EApp _ a' b') = compare a a' &&& lazy (compare b b')
  compare a b = compareTag a b

instance Functor ExpTree where
  (<$>) _ (RNat_ a b) = RNat_ a b
  (<$>) _ (RString_ a b) = RString_ a b
  (<$>) f (RVar a) = RVar (f a)
  (<$>) f (EApp ar a b) = EApp ar ((<$>) f a) ((<$>) f b)

instance HasArity a => HasArity (ExpTree a) where
  arity (RVar a) = arity a
  arity (EApp a _ _) = a
  arity _ = 0

pattern (:@) :: HasArity a => ExpTree a -> ExpTree a -> ExpTree a
pattern f :@ e <- EApp _ f e
  where f :@ e =  EApp (arity f - 1) f e

pattern Apps :: HasArity a => a -> List (ExpTree a) -> ExpTree a
pattern Apps a es <- (getApps Nil -> Just (T2 a es))
  where Apps a es = foldl (:@) (RVar a) es

getApps es (RVar a) = Just (T2 a es)
getApps es (f :@ e) = getApps (e:. es) f
getApps _ _ = Nothing


pattern Saturated a <- (dup -> T2 ((== 0) . arity -> True) a)

pattern a :@@ b <- (dup -> T2 ((<0) . arity -> True) (a :@ b))

{-# COMPLETE RVar, (:@), RNat_, RString_ #-}

instance (IsString a) => IsString (ExpTree a) where
  fromString' s = RVar <$> fromString' s

type ExpTree' a = ExpTree (Mixfix a)


-------------------------------------------
--------------- unop and op ---------------
-------------------------------------------


instance Parse (ExpTree' Layout) where
  parse = (<$>) unop . parse

instance Print (ExpTree' Layout) where
  print = print . op

fromListTokens Nil = NilT
fromListTokens (a :. b) = a :! fromListTokens b

unop :: TokenSeq Layout -> ExpTree' Layout
unop Empty = RVar NEmpty
unop (topOp -> T4 (fromListTokens -> os) l ts r) = case os of
  NilT -> RVar NEmpty
  os | not $ isOperator os -> error $ "Mismatched operator: " <<>> print (MkM os)
  "(" :! ")" :! NilT | (t :> Empty) :. Nil <- ts, isInfix t -> lf $ rf $ RVar $ MSing t           -- TODO: implement inverse of this in op
  _ -> lf $ rf $ Apps (MkM os) $ map unop $ fs ts
 where
  f Empty a = a
  f l a = unop l :@ a

  head_os = case os of
    x :! _ -> x
    _      -> impossible

  last xs = case xs of
    x :! NilT -> x
    _ :! xs -> last xs
    _ -> impossible

  T2 lf fs = case leftPrec (precedences $ head_os) == leftPrec topPrec of
             True  -> T2 (f l) id
             False -> T2 id (l :.)
  rf x | rightPrec (precedences (last os)) == rightPrec topPrec, Empty <- r = x
  rf x = x :@ unop r

op :: ExpTree' Layout -> TokenSeq Layout
op = removeSuperfluousParens . opt  where

  opt e = case e of
    NEmpty -> Empty
    Apps (MkM os) args -> alter mempty (enrich os) (map opt args)
    RNat{}    -> impossible
    RString{} -> impossible
    _ -> impossible

  alter acc         Nil      Nil   =        parens acc
  alter acc         Nil  (a:. as)  = alter (parens acc <> a) Nil as
  alter acc ("___":. os) (a:. as)  = alter (       acc <> a) os as
  alter acc ("___":. os)     Nil   = alter         acc       os Nil
  alter acc (o:.     os)     as    = alter   (acc <> singOpSeq o) os as

allJoin ((l :< "###" :> _) :< _ :> _) = allJoin l
allJoin (Empty :< _ :> Empty) = True
allJoin _ = False

parens a | allJoin a = a
parens a = "<!" <> a <> "!>"

removeSuperfluousParens :: TokenSeq Layout -> TokenSeq Layout
removeSuperfluousParens = flr Nothing Nothing  where

  flr x y = \case
    Empty -> Empty
    Node3 a@Empty "<!"           b  "!>" Empty | p a b -> flr x y $ a <> b
    Node3 a       "<!" (Empty :< b) "!>" Empty | p a b -> flr x y $ a <> b
    Node3 a       "<!"           b  "!>" Empty -> flr x y $ a <> "(" <> b <> ")"
    a       :< b                               -> flr x (Just b) a <> gg b
   where
    gg = \case
      (singOpSeq -> b) :> c       -> b <> flr (Just b)       y  c
      (singOpSeq -> b) := c :< d  -> b <> flr (Just b) (Just d) c <> gg d
      _ -> impossible

    p a b = a > b && maybe True (< a) x && maybe True (< b) x && maybe True (b >) y
{-
isEmpty Empty = True
isEmpty _ = False
-}


-------------------------------------------------
--------------- patch and unpatch ---------------
-------------------------------------------------


instance Parse (ExpTree' PatchedOp) where
  parse = (<$>) (defEnd . patch) . parse

joinAtN i n (Apps (MkM (splitAt' i -> T2 xs zs))
                  (splitAt n -> T2 as (Apps (MkM ys) bs:. cs))
            )
  = Apps (MkM $ xs <> ys <> zs) (as <> bs <> cs)
joinAtN _ _ _ = impossible

infixl 9 .@

dup a = T2 a a

pattern RApp a b <- a :@@ b
  where RApp a b =  a :@  b

a .@ b = norm (a :@ b)

norm r = case r of
  _ | arity r /= 0 -> r
  "#" :@ a :@ _ -> a
  NSemi :@ NEmpty :@ a -> a
  NSemi :@ a :@ NEmpty -> a
  _ | Apps tt@(MkM as') (Saturated (Apps bs' _) :. _) <- r
    , match <- \a b -> a == tt && b == bs'
    ,  match NConstructor NTy                      -- 
    || match NBuiltin  NTy
    || match NParens   NTy           --   (_:_)
    || match NBraces   NTy           --   {_:_}
    || match NEq       NTy           --   _:_=_
    || match NOEq      NTy           --   _:_:=_
    || match NLet      NTy           --   (_:_)=_;_   ~~>  _:_=_;_
    || match NSemi     NEq           --   (_=_);_
    || match NOLet     NTy           --   (_:_):=_;_
    || match NHArr     NTy
    || match NHLam     NTy
    || match NSemi     NTy           --   (_:_);_
    || match NSemi     NTEq      
    || match NSemi     NOEq      
    || match NSemi     NOTEq     
    || match NSemi     NImport   
    || match NSemi     NConstructorTy
    || match NSemi     NBuiltinTy
    || match NSemi     NLeftArr  
    || match NSemi     NClass    
    || match NSemi     NInstance 
    || match NSemi     NData     
    || match NSemi     NRule     
    || match NSemi     NCaseArr  
    || match NLam      NExpl         --
    || match NLam      NImpl         --    \({_:_})->_   ~>   \{_:_}->_
    || match NLam      NBraces       --    \({_})->_     ~>   \{_}->_
    || match NArr      NExpl         --     
    || match NArr      NImpl         --     ({_:_})->_   ~>    {_:_}->_
    || match NArr      NBraces
    , ii <- length $ takeWhile (/= "___") $ filter (/= "###") $ enrich as'
    -> joinAtN ii 0 r
  NParens :@ a -> a
  r -> r

patch :: ExpTree' Layout -> ExpTree' PatchedOp
patch = \case
  a :@ b -> patch a .@ patch b
  t -> coerce t

-- TODO: move to separate phase
defEnd :: ExpTree' PatchedOp -> ExpTree' PatchedOp
defEnd = addEnd . \case
  a :@ b -> defEnd a :@ defEnd b
  t -> t
 where
  addEnd = \case
    e@(Saturated (Apps l _)) | l `elem` (NTy :. NEq :. NTEq :. NOEq :. NOTEq :. NImport :. NConstructorTy :. NBuiltinTy :. NClass :. NInstance :. NData :. NCaseArr :. Nil)
      -> NSemi :@ e .@ REnd
    e -> e

instance Print (ExpTree' PatchedOp) where
  print = print . unpatch

unpatch  :: ExpTree' PatchedOp -> ExpTree' Layout
unpatch = coerce



-------------------------------------------------------
--------------- Raw syntax constructors ---------------
-------------------------------------------------------


-- TODO: make it distinct from RApp?
pattern RHApp a b = RApp a (RVar NBraces :@ b)

pattern Hole           = RVar NHole

pattern Lam    n     e = RVar NLam   :@ RVar n :@       e
pattern RLam   n t   e = RVar NTLam  :@ RVar n :@ t :@    e
pattern RHLam  n t   e = RVar NTHLam :@ RVar n :@ t :@    e
pattern RPi    n t   e = RVar NPi    :@ RVar n :@ t :@    e
pattern RHPi   n t   e = RVar NHPi   :@ RVar n :@ t :@    e
pattern RCPi     t   e = RVar NCPi   :@         t :@    e
pattern RIPi     t   e = RVar NIArr  :@         t :@    e
pattern RLet   n t d e = RVar NTLet  :@ RVar n :@ t :@ d :@ e
pattern ROLet  n t d e = RVar NOTLet :@ RVar n :@ t :@ d :@ e
pattern RLetTy n t   e = RVar NLetTy :@ RVar n :@ t :@    e
pattern RConstructor n t e = RVar NLetConstructor :@ RVar n :@ t :@ e
pattern RBuiltin     n t e = RVar NLetBuiltin     :@ RVar n :@ t :@ e
pattern RRule  a b   e = RVar NLetRule :@ a :@ b :@ e
pattern RDot   a       = RVar NDot   :@ a       -- .a   (in lhs)
pattern RView  a b     = RVar NView  :@ a :@ b
pattern RGuard a b     = RVar NGuard :@ a :@ b
pattern RImport     n e = RVar NLetImport      :@ RVar n :@ e
pattern RClass    a b c = RVar NLetClass    :@ a :@ b :@ c
pattern RInstance a b c = RVar NLetInstance :@ a :@ b :@ c
pattern RData     a b c = RVar NLetData     :@ a :@ b :@ c
pattern RCase     a b c = RVar NCase        :@ a :@ b :@ c
pattern RCaseOf   a b   = RVar NCaseOf      :@ a :@ b
pattern REnd            = RVar NEnd
pattern RAnn e t        = RVar NExpl :@ e :@ t

unGLam = \case
  _ :@@ _ -> Nothing
  Apps a (RVar n:. es) :@ e
    | a `elem` (NLam :. NHLam :. NTLam :. NTHLam :. NPi :. NHPi :. NLetTy :. NLetConstructor :. NLetBuiltin :. NTLet :. NOTLet :. Nil)
    -> Just (T3 (RVar a:. es) n e)
  _ -> Nothing

pattern GLam :: (HasArity a, IsMixfix a) => List (ExpTree a) -> a -> ExpTree a -> ExpTree a
pattern GLam es n e <- (unGLam -> Just (T3 es n e))
  where GLam (RVar a:. es) n e = Apps a (RVar n:. es) :@ e
        GLam _ _ _ = impossible

getBIcit = \case
  n@NExpl -> Just n
  n@NImpl -> Just n
  _ -> Nothing

pattern Bind a b c <- RVar (getBIcit -> Just a) :@ b :@ c

getHArr = \case
  n@NLam -> Just n
  n@NArr -> Just n
  _ -> Nothing

pattern Arr  a b c <- RVar (getHArr -> Just a) :@ b :@ c



---------------------------------------------
--------------- import module ---------------
---------------------------------------------


importModule :: String -> RefM (ExpTree' Desug -> ExpTree' Desug)
importModule f = parseDataFile (f <> ".csip") <&> include

include :: ExpTree' Desug -> ExpTree' Desug -> ExpTree' Desug
include t s = f t  where

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
    x -> error $ "include: " <<>> print x


-------------------------------------------------
--------------- desugar and sugar ---------------
-------------------------------------------------


isBind Bind{} = True
isBind _ = False

desugar :: ExpTree' PatchedOp -> RefM (ExpTree' Desug)
desugar e = pure $ coerce $ etr3 $ etr2 $ etr e where

  etr :: ExpTree' PatchedOp -> ExpTree' PatchedOp
  etr = \case
    l :@ (n :@ m) :@ a :@ b | l `elem` (NTLam :. NTHLam :. NPi :. NHPi :. Nil) -> etr $ l :@ n :@ a .@ (l :@ m :@ a .@ b)
    l :@ (a :@ b) :@ e | l == NLam || l == NHLam || l == NArr && isBind b || l == NHArr -> etr $ l :@ a .@ (l :@ b .@ e)
    a :@ b -> etr a :@ etr b
    l -> l

  etr2 :: ExpTree' PatchedOp -> ExpTree' PatchedOp
  etr2 = \case
    l@NLam  :@ a :@ b -> l :@ (NExpl :@ etr2 a .@ NHole) .@ etr2 b
    l@NHLam :@ a :@ b -> l :@ (NTy   :@ etr2 a .@ NHole) .@ etr2 b
    l@NHArr :@ a :@ b -> l :@ (NTy   :@ etr2 a .@ NHole) .@ etr2 b
    l@NArr  :@ a :@ b -> l :@ (NExpl :@ NAny .@ etr2 a) .@ etr2 b
    l@NLetTy:@ n :@ t :@ (z@NLet :@ n' :@ b :@ m) | n == n'
      -> etr2 $ z :@ (del 1 1 l :@ n' .@ t) :@ b .@ m
    l@NLetTy:@ n :@ t :@ (z@NOLet :@ n' :@ b :@ m) | n == n'
      -> etr2 $ z :@ (del 1 1 l :@ n' .@ t) :@ b .@ m
    z@NOLet :@ n :@ b :@ m
      | RVar{} <- n -> z :@ (NTy :@ etr2 n .@ NHole) :@ etr2 b .@ etr2 m
    z@NLet  :@ n :@ b :@ m
      | RVar{} <- n -> z :@ (NTy :@ etr2 n .@ NHole) :@ etr2 b .@ etr2 m
      | a <- etr2 n -> del 0 1 z :@ (NRule :@ a .@ etr2 b) .@ etr2 m
    a :@ b -> etr2 a :@ etr2 b
    l -> l

  etr3 :: ExpTree' PatchedOp -> ExpTree' PatchedOp
  etr3 = \case
    Saturated (Apps l es) | l `elem`
         (NGuard :. NDot :. NHole :. NLetImport :. NLetClass :. NLetInstance :. NLetData :. NLetTy :. NLetConstructor :. NLetBuiltin :. NTLet :. NOTLet
         :. NPi :. NHPi :. NCPi :. NIArr :. NTLam :. NTHLam :. NBraces :. NLetRule :. NView :. NExpl :. NCaseOf :. NCase :. Nil)
      -> Apps l $ map etr3 es
    NLetArr :@ a :@ b :@ c -> ">>=" :@ etr3 b .@ (NTLam :@ etr3 a :@ NHole .@ etr3 c)
    NSemi :@ b :@ c -> ">>=" :@ etr3 b .@ (NTLam :@ NAny :@ NHole .@ etr3 c)
--    NSemi :@ a :@ _ -> error $ print a <&> \r -> "Definition expected\n" <> r
    a :@ b  -> etr3 a :@ etr3 b
    n@(RVar (MSing t)) | isAtom t   -> n
    e -> error $ print ({- pprint $ op $ unpatch -} e) <&> \r -> "Expression expected\n" <> r



del i j (RVar (MkM (splitAt' i -> T2 as (splitAt' j -> T2 _ bs)))) = RVar $ MkM $ as <> bs
del _ _ _ = impossible

sugar :: ExpTree' Desug -> ExpTree' PatchedOp
sugar = coerce . sug . sug0  where

  sug0 :: ExpTree' Desug -> ExpTree' Desug
  sug0 = \case
    l@NTLam :@ RVar n :@ Hole :@ b
      -> del 1 3 l :@ RVar (coerce n) :@ sug0 b
    l@NPi :@ NAny :@ a :@ b
      -> del 0 3 l :@ sug0 a :@ sug0 b
    l@NLetRule :@ a :@ b :@ c
      -> del 0 1 l :@ (del 1 1 l :@ sug0 a :@ sug0 b) :@ sug0 c
    l@NTLet :@ RVar n :@ Hole :@ b :@ c
      -> del 0 1 l :@ RVar n :@ sug0 b :@ sug0 c
    l@NOTLet :@ RVar n :@ Hole :@ b :@ c
      -> del 0 1 l :@ RVar n :@ sug0 b :@ sug0 c
    a :@ b -> sug0 a :@ sug0 b
    a -> coerce a

  sug :: ExpTree' Desug -> ExpTree' Desug
  sug = \case
    l@NArr :@ a :@ b
      -> arrow l (sug a) (sug b)
    l :@ RVar n :@ a :@ b | l `elem` (NPi :. NHPi :. Nil)
      -> arrow (del 0 3 l) (del 3 1 l :@ RVar n :@ sug a) (sug b)
    l@NLam :@ RVar n :@ b
      -> arrow l (RVar n) (sug b)           -- \x (w : t)-> \(y : t) z-> e   ~>  \x (w y: t) z-> e
    l :@ RVar n :@ a :@ b | l `elem` (NTLam :. NTHLam :. Nil)
      -> arrow (del 1 3 l) (del 3 1 (del 0 1 l) :@ RVar n :@ sug a) (sug b)
    a :@ b -> sug a :@ sug b
    a -> a

  arrow :: ExpTree' Desug -> ExpTree' Desug -> ExpTree' Desug -> ExpTree' Desug
  arrow arr n (Arr arr' m e) | arr == RVar arr', Just nm <- n +@ m = arr :@ nm :@ e  where

    a +@ (b :@@ c) | arr == NLam, Just ab <- a +@ b = Just $ ab :@ c
    Bind pl n t +@ Bind pl' m t' | pl == pl', t == t' = Just $ RVar pl :@ (n ++@ m) :@ t
    a +@ b | arr == NLam || isBind a && isBind b = Just $ a :@ b
    _ +@ _ = Nothing

    n ++@ (a :@ b) = (n ++@ a) :@ b
    n ++@ m = n :@ m
  arrow arr n e = arr :@ n :@ e


instance Parse (ExpTree' Desug) where
  parse = parse >=> desugar
    >=> preprocess{-TODO: do in separate phase-}
    >=> pure . preprocess2{-TODO: do in separate phase-}

preprocess   :: ExpTree' Desug -> RefM (ExpTree' Desug)
preprocess t = f t  where
    f = \case
      RImport (MSing m) e -> print m >>= \m -> importModule m >>= \fm -> f $ fm e
      RNat_ a b -> pure $ RNat_ a b
      RString_ a b -> pure $ RString_ a b
      RVar n -> pure $ RVar n
      a :@ b -> (:@) <$> f a <*> f b

preprocess2 t = f t  where
    f = \case
      RNat_ a b -> RNat_ a b
      RString_ a b -> RString_ a b
      RVar (MSing (MkLit s@(readWord -> Just n))) -> RNat_ s n
      RVar (MSing (MkLit s@(getString -> Just n))) -> RString_ s n
      RVar n -> RVar n
      a :@ b -> f a :@ f b

getString (ConsChar '"' s) = Just (initStr s)
getString _ = Nothing

instance Print (ExpTree' Desug) where
  print = print . sugar . unembed

unembed :: ExpTree' a -> ExpTree' a
unembed = f where
  f = \case
    RNat_    a _ -> RVar $ MSing (MkLit a)
    RString_ a _ -> RVar $ MSing (MkLit a)
    a :@ b -> f a :@ f b
    RVar n -> RVar n


----------------------------------------------

pattern RNat n <- RNat_ _ n
  where RNat n =  RNat_ (showWord n) n

pattern RString n <- RString_ _ n
  where RString n =  RString_ ("\"" <> n <> "\"") n

addPrefix :: Token a -> Mixfix a -> Mixfix a
addPrefix s (MkM_ ar a) = mkM ar (s :! a)

addSuffix :: Mixfix a -> Token a -> Mixfix a
addSuffix (MkM_ ar a) s = mkM ar $ a <> (s :! NilT)

notDigitEnd (MkM (MkToken _ s :! NilT)) | ConsChar d _ <- revTakeStr 1 s = not $ isDigit d
notDigitEnd _ = False


----------------------------------------------
--------------- Name data type ---------------
----------------------------------------------


type NameStr = Mixfix Desug

data Name = MkName NameStr Word

nameStr (MkName n _) = n
nameId  (MkName _ w) = w

instance HasId Name where getId = nameId

showName = showMixfix . nameStr

instance IsMixfix Name where
  fromMixfix (fromMixfix -> n) = MkName n (getId n)

instance HasArity Name where
  arity = arity . nameStr


rename a (MkName _ b) = MkName a b

instance Ord Name where compare = compare `on` nameId

instance Print Name where
  print = print . nameStr

instance IsString Name where
  fromString' t = fromString' t <&> \case
    MkLit{}    -> impossible
    n -> fromMixfix $ MSing n

-- TODO: rename to newName
mkName :: NameStr -> RefM Name
mkName s = newId <&> MkName s

mkName' s = mkName s <&> \n -> rename (addIntSuffix (nameStr n) $ nameId n) n

addIntSuffix a n = addSuffix a $ MkLit (showWord n)

nameOf :: NameStr -> RefM Name
nameOf n@(MSing (MkToken (MkTI global h _) _)) | global = pure $ MkName n h
nameOf n = mkName n


-------------------------------------------------
--------------- scope and unscope ---------------
-------------------------------------------------


instance Print (ExpTree Name) where
  print = unscope >=> print

unscope :: ExpTree Name -> RefM (ExpTree' Desug)
unscope t = runReader (T2 (mempty :: IntMap Name Word) (emptyMap :: Map NameStr Word)) ff where

  addIndex n Nothing = nameStr n
  addIndex (nameStr -> n) (Just i) = addIntSuffix (case notDigitEnd n of True -> n; False -> addSuffix n "_") i

  ff r = f t where

    f :: ExpTree Name -> RefM (ExpTree' Desug)
    f = \case
      RVar "Pi"  :@ a :@ Lam n e -> f $ RPi  n a e
      RVar "HPi" :@ a :@ Lam n e -> f $ RHPi n a e
      RVar "CPi" :@ a :@       e -> f $ RCPi   a e
      RVar "IPi" :@ a :@       e -> f $ RIPi   a e
      RNat_    a b -> pure $ RNat_ a b
      RString_ a b -> pure $ RString_ a b
      RVar v -> do
        k <- asks r (lookupIM v . fst)
        let m = addIndex v k
        pure $ RVar m
      GLam es v a
        | n@"_" <- v -> GLam <$> mapM f es <*> pure (nameStr n) <*> f a
        | n <- nameStr v -> asks r (lookupIM v . fst) >>= \case
          _ -> do
            k <- asks r (lookupMap n . snd)
            let m = addIndex v k
            GLam <$> mapM f es <*> pure m <*> local r (maybe id (insertIM v) k *** insertMap n (1 + fromMaybe' 0 k)) (f a)
      a :@ b -> (:@) <$> f a <*> f b



--------------------------------------
--------------- PPrint ---------------
--------------------------------------

class PPrint a where
  pprint :: a -> ExpTree Name


instance (PPrint a, PPrint b) => PPrint (Tup2 a b) where
  pprint (T2 a b) = zVar ("(" :! "," :! ")" :! NilT) :@ pprint a :@ pprint b

instance PPrint a => PPrint (List a) where
  pprint Nil = zVar ("[":!"]":!NilT)
  pprint as = Apps (fromMixfix $ MkM $ "[" :! replicate' (length as -. 1) "," <> ("]" :! NilT)) $ map pprint as

instance PPrint Tup0 where
  pprint T0 = RVar "Unit"   -- TODO: zVar ["(",")"], without "_"

instance PPrint Word where
  pprint i = RNat i

instance PPrint String where
  pprint = \case
    NilStr -> res ""
    ConsChar c s
      | c == '\n' -> co (r "newline") s
      | c == '\t' -> co (r "begin")   s
      | c == '\r' -> co (r "end")     s
      | c == '\"' -> co (r "quote")   s    -- co (res c) s
    (spanStr (\c -> not $ c `elem` ('\n' :. '\t' :. '\r' :. '\"' :. Nil)) -> T2 as bs)
      -> co (res as) bs
   where
    r s = pprintStr s
    res s = pprintStr ("\"" <> s <> "\"")
    co a NilStr = a
    co a b = "<>" :@ a :@ pprint b

pprintStr t = RString_ t t

instance PPrint IString where
  pprint = pprint . unIString

instance PPrint Void where
  pprint = impossible

instance (PPrint a) => PPrint (OpSeq a) where
  pprint Empty = "_"
  pprint (a :> Empty) = pprint a
  pprint (sl :< b) = zVar ("[":!"]":!NilT) :@ foldl (:@) (pprint sl) (f b)  where
    f (b := c :< d) = pprint b:. pprint c:. f d
    f (b :> c) = pprint b:. pprint c:. Nil
    f _ = impossible

instance PPrint (Token a) where
  pprint = \case
    MkLit s -> pprintStr s
    t | precedences t == topPrec -> RVar $ fromMixfix $ MSing $ coerce t
    t -> pprint $ showToken t

instance PPrint (Mixfix a) where
  pprint (MSing t) | precedences t == topPrec = pprint t
  pprint s = pprintStr $ showMixfix s

instance PPrint Name where
  pprint = RVar

instance (Ord a, PPrint a, HasArity a) => PPrint (ExpTree a) where
  pprint = f where
    f = \case
      RNat_ a b   -> RNat_ a b
      RString_ a b -> RString_ a b
      RVar n     -> pprint n
      a :@ b     -> RVar "@" :@ f a :@ f b
