module B8_Doc
  ( Doc, mkDoc, nlDoc, hangDoc, hangDoc1, hangDoc2, sepDoc, evalDoc
  ) where

import B1_Basic
import B2_String

-------------------------------

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
  MkNesting a x n <> MkNesting (c:. cs) y d  | c + 1 < 2 = MkNesting a x (n - 1) <> MkNesting Nil (c + 1) 0 <> MkNesting cs y d
  _               <> _                       = Big

instance Monoid Nesting where
  mempty = MkNesting Nil 0 0

leftNesting  = MkNesting Nil        0 1    -- '('
rightNesting = MkNesting (0 :. Nil) 0 0    -- ')'

smallNesting Big = False
smallNesting _   = True

--------------------

data Length = MkLength Word

instance Ord       Length where  compare (MkLength a) (MkLength b) = compare a b
instance Semigroup Length where  MkLength a <> MkLength b = MkLength (a + b)
instance Monoid    Length where  mempty = MkLength 0

data Complexity = MkComplexity Nesting Length

instance Semigroup Complexity where  MkComplexity a b <> MkComplexity a' b' = MkComplexity (a <> a') (b <> b')
instance Monoid    Complexity where  mempty = MkComplexity mempty mempty

smallComplexity :: Complexity -> Bool
smallComplexity (MkComplexity n l) = l < MkLength 80 && smallNesting n

mkNlDocShape :: DocShape Complexity
mkNlDocShape = MultiLine mempty mempty

mkDocShape :: String -> DocShape Complexity
mkDocShape s = SingleLine (MkComplexity mempty (MkLength $ lengthStr s))

--------------------

type DocBuilder = Endo String

pureDB :: String -> DocBuilder
pureDB a = MkEndo (a <>)

evalDocBuilder t = appEndo t ""

-- end of optimized version


-----------------------

data Interval a = MkInterval a a

instance Semigroup (Interval a) where  MkInterval a _ <> MkInterval _ b = MkInterval a b

-----------------------

data Doc = MkDoc (Maybe (Interval Char)) (DocShape Complexity) DocBuilder

instance Semigroup Doc where  MkDoc a b c <> MkDoc a' b' c' = MkDoc (a <> a') (b <> b') (c <> c')
instance Monoid    Doc where  mempty = MkDoc mempty mempty mempty

evalDoc :: Doc -> String
evalDoc (MkDoc _ _ b) = evalDocBuilder b

mkDoc s | ConsChar a _ <- s, SnocChar _ b <- s = MkDoc (Just $ MkInterval a b) (mkDocShape s) (pureDB s)
        | True = mempty

nlDoc = MkDoc (Just $ MkInterval '\n' '\n') mkNlDocShape (pureDB "\n")

hangDoc1, hangDoc :: Doc -> Doc
hangDoc2 :: Word -> Doc -> Doc

hangDoc1 (MkDoc a b c) = MkDoc a (mk leftNesting <> b <> mk rightNesting) c where

  mk c = SingleLine (MkComplexity c mempty)

hangDoc2 n (MkDoc a b c) = MkDoc a b (mreplicate n ("\t") <> c <> mreplicate n ("\r"))

hangDoc (MkDoc a b c)
  | MultiLine{} <- b = hangDoc2 2 (MkDoc a b c)
hangDoc (MkDoc a b c) = MkDoc a b c

nullComplexity (SingleLine (MkComplexity _ (MkLength 0))) = True
nullComplexity _ = False

sepDoc :: (Char -> Char -> Bool) -> Doc -> Doc -> Doc
sepDoc glue a@(MkDoc ia da _) b@(MkDoc ib db _) = a <> op <> b where

  op1
    | Just (MkInterval _ a) <- ia
    , Just (MkInterval b _) <- ib
    , glue a b
    = mkDoc " "
    | True = mempty

  op
    | MkDoc _ s _ <- op1
    , nullComplexity da || nullComplexity db || smallComplexity (lastLine da <> firstLine s <> firstLine db)
    = op1
    | True = nlDoc
