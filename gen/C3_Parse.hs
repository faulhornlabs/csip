
{-# LINE 1 "src/C3_Parse.hs" #-}
module C3_Parse
  ( IString, unIString
  , OpSeq, NameSeq
  , ExpTree (RVar, (:@), RApp, Apps, EApp, Saturated), ExpTree', (<@>), Raw, Scoped
  ) where

import B_Base
import C1_Name
import C2_NameLiterals


--------------- unindent and indent ---------------

data IString = MkIString String

unIString (MkIString s) = s

unindent :: String -> IString
unindent s = MkIString $ dropNl $ h "\n" 0 $ s <> "\n" where

  dropNl (ConsChar '\n' s) = s
  dropNl s = s

  h _  n NilStr = mreplicate n "\r"
  h nl n (spanStr (== ' ') -> T2 (lengthStr -> k) (spanStr (/= '\n') -> T2 as (ConsStr nl' cs)))
    | NilStr <- as  = nl <> h nl' n cs
    | True      = mreplicate (n - k) "\r" <> nl <> mreplicate (k - n) " " <> mreplicate (k - n) "\t" <> fst (revSpanStr (== ' ') as) <> h nl' k cs
  h _ _ _ =  (impossible "src/C3_Parse.hs" 28)

indent   :: IString -> String
indent (MkIString s_) = g 0 s_  where

  g i (spanStr (== ' ') -> T2 sp (spanStr (== '\r') -> T2 ((i -) . lengthStr -> i') cs)) = case cs of
    ConsStr c cs | c == "\n" -> c <> g i' cs
    cs   -> mreplicate i' " " <> sp <> f i' cs

  f i (spanStr (\c -> c /= '\n' && c /= '\r' && c /= '\t') -> T2 s cs) = s <> case cs of
    ConsStr c cs
      | c == "\t" -> f (i+1) cs
      | c == "\r" -> f (i-1) cs
      | c == "\n" -> c <> g i cs
    NilStr | i == 0 -> ""
    _ ->       (impossible "src/C3_Parse.hs" 43)

instance Parse IString where  parse = parse >=> pure . unindent
instance Print IString where  print = pure . indent >=> print


--------------- lex and unlex ---------------

glueChars :: Char -> Char -> Bool
glueChars c d
   = isAlphaNum c && isAlphaNum d
  || isGraphic  c && isGraphic  d
  || c == '{' && d == '-'
  || c == '-' && d == '}'

lex :: IString -> IO (List (Name Spaced))
lex = runMem . mapM newName . f . unIString  where

  f NilStr = Nil
  f (groupStr glueChars -> T2 as bs) = as :. f bs

unlex :: List (Name Spaced) -> IString
unlex = MkIString . mconcat . map showName

instance Parse (List (Name Spaced)) where  parse = parse >=> lex
instance Print (List (Name Spaced)) where  print = pure . unlex >=> print


--------------- structure and unstructure ---------------

type NameSeq a = OpSeq (Name a)

instance IsName (NameSeq a) where
  fromName a = singOpSeq (fromName a)
  eqName a (Node2 Empty b Empty) = eqName a b
  eqName _ _                     = False

structure :: List (Name Spaced) -> NameSeq Spaced
structure = foldMap singOpSeq

unstructure :: NameSeq Spaced -> List (Name Spaced)
unstructure t = appEndo (foldMapOpSeq (\a -> MkEndo (a :.)) t) Nil

instance Parse (NameSeq Spaced) where  parse = parse >=> pure . structure
instance Print (NameSeq Spaced) where  print = pure . unstructure >=> print


--------------- string and unstring ---------------

string :: NameSeq Spaced -> Mem (NameSeq Stringed)
string = \case
  Node2 l a@N0 (Node2 s b@N0 r) | not (hasNl s)
    -> pure (coerce l) <> (singOpSeq <$> newName (showName a <> appEndo (foldMapOpSeq (\t -> MkEndo (showName t <>)) s) (showName b))) <> string r
  Node2 _ s@N0 _ -> fail $ "Unterminated string\n" <> print s
  a -> pure $ coerce a
 where
  hasNl (Node2 _ N1 _) = True
  hasNl _ = False

instance Parse (NameSeq Stringed) where  parse = parse >=> runMem . string
instance Print (NameSeq Stringed) where  print = print . (coerce :: NameSeq Stringed -> NameSeq Spaced)


--------------- uncomment and comment ---------------

uncomment :: NameSeq Stringed -> NameSeq Uncomment
uncomment = \case
  Node2 (Node2 l N2 c) N1 r -> coerce l <> comm c <> N3 <> uncomment r
  Node2 l                 N1 r -> coerce l <> N3 <> uncomment r
  a -> coerce a

comm s = coerce (filterOpSeq (\x -> x == N4 || x == N5 || x == N3) s)

comment :: NameSeq Uncomment -> NameSeq Stringed
comment = foldMapOpSeq c  where
  c N3 = singOpSeq N1
  c s = singOpSeq (coerce s)

instance Parse (NameSeq Uncomment) where  parse = (uncomment <$>) . parse
instance Print (NameSeq Uncomment) where  print = print . comment


--------------- uncomments and comments ---------------

uncomments :: NameSeq Uncomment -> NameSeq Uncomments
uncomments = \case
    Node3 l N6 c N7 r -> coerce l <> comm c <> uncomments r
    Node2 _ s@N6 _ -> error $ print s <&> \r -> "Unterminated comment\n" <> r
    Node2 _ s@N7 _ -> error $ print s <&> \r -> "Unterminated comment\n" <> r
    a -> coerce a

comments :: NameSeq Uncomments -> NameSeq Uncomment
comments = coerce

instance Parse (NameSeq Uncomments) where  parse = (<$>) uncomments . parse
instance Print (NameSeq Uncomments) where  print = print . comments


--------------- unspace and space ---------------

unspace :: NameSeq Uncomments -> NameSeq Unspaced
unspace = \case
    Node2 l N8 r -> coerce l <> unspace r
    a -> coerce a

-- remove immediately nested BEGIN END pairs
-- remove incomplete semicolons candidates
simplify = f  where

  f = \case
    Node2 l s@N3 r -> node2 s (f l) (f r)
    Node3 l s@N4 a t@N5 r -> node3 (f l) s (f $ skip a) t (f r)
    Node2 l s r | s == N9 || s == N10 || s == N11 -> f l <> singOpSeq s <> f r
    a -> a

  node2 _ Empty a = a
  node2 _ a Empty = a
  node2 s a b = a <> singOpSeq s <> b

  node3 a _ Empty _ b = a <> b
  node3 a x b y c = a <> singOpSeq x <> b <> singOpSeq y <> c

  skip (Node3 Empty N4 a N5 Empty) = skip a
  skip a = a

space :: NameSeq Unspaced -> NameSeq Uncomments
space _ = error "TODO: implement space"

instance Parse (NameSeq Unspaced) where  parse = (<$>) (simplify . unspace) . parse
instance Print (NameSeq Unspaced) where  print = print . space


--------------- layout ---------------

layout  :: NameSeq Unspaced -> NameSeq Layout
layout = snd . g True  where

  g :: Bool{-not inside braces-} -> NameSeq Unspaced -> Tup2 Bool (NameSeq Layout)
  g top = \case
    Node2 l N3 r -> T2 False $ coerce l <> semi (g top r)

    Node3 l N4 a N5 r -> T2 True $ coerce l <> snd (g False a) <> semi (g top r)

    Node2 l N9    (Node3 Empty N4 a N5 r)
      -> T2 False $ coerce l <>     N12 <> snd (g True a) <>  N13 <> semi (g top r)
    Node2 l N10 (Node3 Empty N4 a N5 r)
      -> T2 False $ coerce l <>  N14 <> N15 <> snd (g True a) <>  N16 <> semi (g top r)
    Node2 l N11    (Node3 Empty N4 a N5 r)
      -> T2 False $ coerce l <>  N17    <> N18    <> snd (g True a) <>     N19 <> semi (g top r)

    -- TODO?
    Node2 a N10 b -> T2 False $ coerce a <> N14 <> N15 <> N20 <> N16 <> semi (g top b)

    Node2 _ t _  | t == N9 || t == N10 || t == N11 -> error $ "Illegal " <> print t

    a -> T2 False (coerce a)
   where
    semi (T2 indent b) | not top || indent  = b
    semi (T2 _ b)  = N21 <> b


spaceLayout :: NameSeq Layout -> IString
spaceLayout = MkIString . evalDoc . ff1  where

  mk = mkDoc . showName

  infixr 3 <+>
  (<+>) = sepDoc glue

  glue a b
    =  glueChars a b
    || not (a == '(' || a == '[' || a == '{' || a == '\\' || b == ',' || b == ';' || b == '}' || b == ')' || b == ']')

  ff1 :: NameSeq Layout -> Doc
  ff1 = \case
    Empty -> mempty
    (getSemis -> e :. es@(_:._)) -> hangDoc $ mk N9 <> nlDoc <> foldl (<+>) (ff e) (map ff es)
    Node2 a x b -> ff1 a <+> mk x <+> ff1 b
    Node3 a x b y c -> ff1 a <+> hh (mk x <+> ff1 b <+> mk y <+> ff1 c)

  hh = hangDoc1 . hangDoc

  ff x = hangDoc1 $ hangDoc1 $ hangDoc2 2 $ ff1 x

  getSemis = \case
    Node2 l N21 r -> l:. getSemis r
    x -> x :. Nil

instance Parse (NameSeq Layout) where  parse = (<$>) layout . parse
instance Print (NameSeq Layout) where  print = print . spaceLayout


--------------- expression trees ---------------

data ExpTree a
  = RVar a
  | EApp Arity (ExpTree a) (ExpTree a)

type Raw = ExpTree NameStr
type Scoped = ExpTree SName


instance Tag (ExpTree a) where
  tag RVar{} = 0
  tag EApp{} = 1

instance Ord a => Ord (ExpTree a) where
  compare (RVar a) (RVar a') = compare a a'
  compare (EApp _ a b) (EApp _ a' b') = compare a a' &&& lazy (compare b b')
  compare a b = compareTag a b

instance IsName a => IsName (ExpTree a) where
  fromName a = RVar (fromName a)
  eqName a (RVar b) = eqName a b
  eqName _ _        = False

instance HasArity a => HasArity (ExpTree a) where
  arity (RVar a) = arity a
  arity (EApp a _ _) = a

pattern (:@) :: HasArity a => ExpTree a -> ExpTree a -> ExpTree a
pattern f :@ e <- EApp _ f e
  where f :@ e =  EApp (arity f - 1) f e

{-# COMPLETE RVar, (:@) #-}

a <@> b = (:@) <$> a <*> b

getApps es (RVar a) = T2 a es
getApps es (f :@ e) = getApps (e:. es) f

pattern Apps :: HasArity a => a -> List (ExpTree a) -> ExpTree a
pattern Apps a es <- (getApps Nil -> T2 a es)
  where Apps a es = foldl (:@) (RVar a) es

{-# COMPLETE Apps #-}

pattern Saturated a <- (dup -> T2 ((== 1) . arity -> True) a)

pattern RApp a b <- (dup -> T2 ((< 1) . arity -> True) (a :@ b))
  where RApp a b =  a :@  b


type ExpTree' a = ExpTree (Name a)
