module B2_String
  ( HasId (getId)

  , String (NilStr, ConsStr, ConsChar)
  , mkString, mkFileString
  , showLoc, appendLoc, stripSource
  , lengthStr, stringToList, stripSuffix
  , splitAtStr, revSplitAtStr, spanStr, revSpanStr, takeStr, revTakeStr, dropStr, revDropStr
  , nullStr, groupStr, allStr
  , unlines, lines, words, renameString
  , showWord, readWord
  , hashString

  , Color, black, red, green, yellow, blue, magenta, cyan, white
  , invertColors, background, foreground
  , lengthANSI, fixANSI
  , toPreludeString
  ) where

import B0_Builtins
import B1_Basic


-------------------

class HasId k where
  getId :: k -> Word

instance HasId Word where
  getId i = i

----------------------------------------

data Handler = MkHandler Word String

instance HasId Handler where getId (MkHandler i _) = i
instance Ord Handler where compare = compare `on` getId


data StringSource
  = FileSource Handler
  | StringSource String
  | NoSource

instance Tag StringSource where
  tag FileSource{} = 0
  tag StringSource{} = 1
  tag NoSource{} = 2

instance Ord StringSource where
  FileSource a   `compare` FileSource b   = a `compare` b
  StringSource a `compare` StringSource b = a `compare` b
  a              `compare` b              = compareTag a b


data CharCtx = MkCtx StringSource CharArray

stringSource (MkCtx s _) = s

instance Ord CharCtx where compare = compare `on` stringSource

indexCtx (MkCtx _ v) i = readCharArray v i


----------------------------------------

data String
  = NilStr
  | ConsS {-# UNPACK #-} Word {-# UNPACK #-} Word CharCtx String

consS a b c (ConsS a' b' c' s)
  | b == a', eqFS c c' = ConsS a b' c s
consS a b c s = ConsS a b c s

eqFS (stringSource -> FileSource a) (stringSource -> FileSource b) = a == b
eqFS _ _ = False

instance Semigroup String where
  NilStr <> s = s
  ConsS a b c s <> s' = consS a b c (s <> s')

instance Monoid String where
  mempty = NilStr

stringToList :: String -> List Char
stringToList s = go s  where
  go NilStr = Nil
  go (ConsS i j c s) = (indexCtx c <$> enumFromTo i j) ++ go s

instance Ord String where
  compare = compare `on` stringToList

instance IntHash String where
  intHash = intHash . stringToList

----------------------------------------

lengthStr = f 0 where
   f acc NilStr = acc
   f acc (ConsS i j _ s) = f (acc + (j -. i)) s

nullStr NilStr = True
nullStr _ = False


----------------------------------------

allStr p s = all p (stringToList s)

toPreludeString :: String -> PreludeString
toPreludeString s = foldr consPrelude nilPrelude (stringToList s)

readWord :: String -> Maybe Word
readWord (stringToList -> cs)
  | all isDigit cs = Just (foldl (\i c -> 10*i + digitToWord c) 0 cs)
  | True = Nothing


----------------------------------------

replaceSource _ NilStr = NilStr
replaceSource x (ConsS a b (MkCtx _ v) s) = ConsS a b (MkCtx x v) (replaceSource x s)

stripSource :: String -> String
stripSource = replaceSource NoSource

renameString :: String -> String -> String
renameString a s = replaceSource (StringSource s) a


----------------------------------------

mkLocString_ :: StringSource -> CharArray -> String
mkLocString_ _ v | lengthCharArray v == 0 = NilStr
mkLocString_ n v = ConsS 0 (lengthCharArray v) (MkCtx n v) NilStr

mkString :: CharArray -> String
mkString s = mkLocString_ NoSource s

fromString :: PreludeString -> String
fromString cs = mkString $ fromPreludeString cs

mkFileString n s i = mkLocString_ (FileSource $ MkHandler i n) s


----------------------------------------

groupCh_ :: (Word -> Char -> Char -> Bool) -> String -> Tup2 String String
groupCh_ p ss = f' ss  where

  f' NilStr = T2 NilStr NilStr
  f' (ConsS i j c ss) = g (indexCtx c i) (i+1)  where
    g l x | x == j, T2 as bs <- f (j -. i) l ss = T2 (ConsS i j c as) bs
          | l' <- indexCtx c x, p (x -. i) l l' = g l' (x+1)
          | True = T2 (ConsS i x c NilStr) (ConsS x j c ss)

  f _ _ NilStr = T2 NilStr NilStr
  f offs l s@(ConsS i j c ss) = g l i  where
    g l x | x == j, T2 as bs <- f (offs + j -. i) l ss = T2 (ConsS i j c as) bs
          | l' <- indexCtx c x, p (offs + x -. i) l l' = g l' (x+1)
          | x == i    = T2 NilStr s
          | True = T2 (ConsS i x c NilStr) (ConsS x j c ss)

spanCh_ :: (Word -> Char -> Bool) -> String -> Tup2 String String
spanCh_ p ss = f 0 ss  where

  f _ NilStr = T2 NilStr NilStr
  f offs s@(ConsS i j c ss) = g i  where
    g x | x == j, T2 as bs <- f (offs + j -. i) ss = T2 (ConsS i j c as) bs
        | p (offs + x -. i) (indexCtx c x) = g (x+1)
        | x == i    = T2 NilStr s
        | True = T2 (ConsS i x c NilStr) (ConsS x j c ss)

reverseS = f NilStr where
  f acc NilStr = acc
  f acc (ConsS a b c s) = f (ConsS a b c acc) s

revSpanCh_ :: (Word -> Char -> Bool) -> String -> Tup2 String String
revSpanCh_ p ss | T2 as bs <- f 0 (reverseS ss) = T2 (reverseS bs) (reverseS as)  where

  f _ NilStr = T2 NilStr NilStr
  f offs s@(ConsS j i c ss) = g i  where
    g x | x == j, T2 as bs <- f (offs + i -. j) ss = T2 (ConsS j i c as) bs
        | p (offs + i -. x) (indexCtx c (x-.1)) = g (x-.1)
        | x == i    = T2 NilStr s
        | True = T2 (ConsS x i c NilStr) (ConsS j x c ss)

spanStr, revSpanStr :: (Char -> Bool) -> String -> Tup2 String String
spanStr p = spanCh_ \_ -> p
revSpanStr p = revSpanCh_ \_ -> p

splitAtStr, revSplitAtStr :: Word -> String -> Tup2 String String
splitAtStr n = spanCh_ \i _ -> i < n
revSplitAtStr n = revSpanCh_ \i _ -> i < n

takeStr, dropStr, revTakeStr, revDropStr :: Word -> String -> String
takeStr    n = fst . splitAtStr    n
dropStr    n = snd . splitAtStr    n
revTakeStr n = snd . revSplitAtStr n
revDropStr n = fst . revSplitAtStr n

groupStr p = groupCh_ \_ -> p

stripSuffix a b
  | T2 b1 b2 <- revSplitAtStr (lengthStr a) b, a == b2 = Just b1
  | True = Nothing


----------------------------------------

wordToDigit :: Word -> String
wordToDigit 0 = "0"
wordToDigit 1 = "1"
wordToDigit 2 = "2"
wordToDigit 3 = "3"
wordToDigit 4 = "4"
wordToDigit 5 = "5"
wordToDigit 6 = "6"
wordToDigit 7 = "7"
wordToDigit 8 = "8"
wordToDigit 9 = "9"
wordToDigit _ = ""

showWord :: Word -> String
showWord i | i == 0 = wordToDigit i
showWord i = g mempty (div i 10) (mod i 10)
 where
  g acc 0 0 = acc
  g acc q r = g (wordToDigit r <> acc) (div q 10) (mod q 10)

unlines :: List String -> String
unlines xs = mconcat (map (<> "\n") xs)


----------------------------------------

getConsStr (ConsS i j ctx ss)
  | j == i + 1 = Just (T2 (ConsS i j ctx NilStr) ss)
  | True  = Just (T2 (ConsS i (i+1) ctx NilStr) (ConsS (i+1) j ctx ss))
getConsStr _ = Nothing

pattern ConsStr :: String -> String -> String
pattern ConsStr c s <- (getConsStr -> Just (T2 c s))

{-# COMPLETE ConsStr,  NilStr #-}

getConsChar (ConsS i j ctx ss)
  | j == i + 1 = Just (T2 (indexCtx ctx i) ss)
  | True  = Just (T2 (indexCtx ctx i) (ConsS (i+1) j ctx ss))
getConsChar _ = Nothing

pattern ConsChar :: Char -> String -> String
pattern ConsChar c s <- (getConsChar -> Just (T2 c s))

{-# COMPLETE ConsChar, NilStr #-}


----------------------------------------

words :: String -> List String
words (spanStr isSpace -> T2 _ bs) = g bs where
  g NilStr = Nil
  g (spanStr (not . isSpace) -> T2 as bs) = as :. words bs

lines :: String -> List String
lines (spanStr (/= '\n') -> T2 as xs) = as :. h xs  where
  h (ConsChar '\n' xs) = lines xs
  h _ = Nil


----------------------------------------

meld :: String -> String
meld s = f (len s) s  where

  len NilStr = 0 :: Word
  len (ConsS _ _ _ s) = 1 + len s

  drop 0 s = s
  drop i (ConsS _ _ _ s) = drop (i-.1) s
  drop _ s = s

  f 0 _ = NilStr
  f 1 (ConsS _ _ (MkCtx NoSource _) _) = NilStr
  f 1 (ConsS _ _ (MkCtx (StringSource s) _) _) = meld s
  f 1 (ConsS a b c _) = ConsS a b c NilStr
  f l s | i <- l `div` 2 = f i s `merge` f (l -. i) (drop i s)

  merge :: String -> String -> String
  merge NilStr s = s
  merge s NilStr = s
  merge so@(ConsS a b c s) so'@(ConsS a' b' c' s') = compareCase c c'
    (ConsS a b c (merge s so'))
    (case T0 of
      _ | b < a' -> ConsS a b c (merge s so')
        | b' < a -> ConsS a' b' c' (merge so s')
        | True -> consS (min a a') (max b b') c (merge s s')
    )
    (ConsS a' b' c' (merge so s'))

showLoc :: String -> String
showLoc s = splitFiles (meld s)
 where
  splitFiles s@(ConsS _ _ (MkCtx (FileSource h@(MkHandler _ fn)) v) _)
    = matchT2 (splitFile h s) \is rest -> title fn <> hh v is <> splitFiles rest
  splitFiles _ = mempty

  splitFile h (ConsS a b (MkCtx (FileSource h') _) s)
    | h' == h = matchT2 (splitFile h s) \is rest -> T2 (a :. b :. is) rest
  splitFile _ s = T2 Nil s

  diffs is = zipWith (-.) is (0 :. is)

  splits Nil s = s .+ \_ -> Nil
  splits (i :. is) s = matchT2 (splitAtStr i s) \as bs -> as .+ splits is bs

  ((lines -> as) .+ b) i = numberWith T2 i as :. b (i + length as -. 1)

  hh v is = mconcat . mapHead (hrest 0) (hrest 2) . everyNth 2 $ splits (diffs is) (mkString v) 1

  hrest k (as :. bs :. Nil) = takes k 2 as <> unlines' (mapHead (highlight . snd) highlightLine bs)
  hrest k (as :. _) = takes k 0 as
  hrest _ _ = mempty

  takes i j (splitAt i -> T2 a (revSplitAt j -> T2 b c))
    = unlines' $ mapHead snd number a
       ++ condCons (not $ null b) dots (map number c)

  title f = invertColors (foreground green $ " " <> f <> " ") <> nl
  number (T2 n s) = foreground green (showWord n <> " | ") <> s
  dots = foreground green "..."
  highlight s = background blue s
  highlightLine (T2 i s) = number (T2 i (highlight s))
  nl = "\n"

  unlines' = mconcat . intersperse nl

  mapHead _ _ Nil = Nil
  mapHead f g (a :. as) = f a :. map g as


appendLoc s = stripSource s <> "\n" <> showLoc s


-----------------------------------------------


data Word128 = MkWord128 Word Word

hashString :: String -> String
hashString s = f v2 <> f v1 where

  f = mconcat . map char . base 11
  MkWord128 v1 v2 = hash (stringToList s)

  hash :: List Char -> Word128
  hash = foldl (\h c -> add (ord c) (mul 33 h)) (MkWord128 0 5381)   -- djb2

  mul t (MkWord128 a b) = mulWordCarry t b \c tb -> MkWord128 (t * a + c) tb
  add t (MkWord128 a b) = addWordCarry t b \c tb -> MkWord128 (    a + c) tb

  base :: Word -> Word -> List Word
  base 0 _ = Nil
  base n i = (i .&. 63) :. base (n-.1) (shiftR i 6)

  char i = takeStr 1 $ dropStr i "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"


----------------------------------------------- Colored String

data Color = MkColor String String

black   = MkColor "\ESCa" "\ESCA"
red     = MkColor "\ESCb" "\ESCB"
green   = MkColor "\ESCc" "\ESCC"
yellow  = MkColor "\ESCd" "\ESCD"
blue    = MkColor "\ESCe" "\ESCE"
magenta = MkColor "\ESCf" "\ESCF"
cyan    = MkColor "\ESCg" "\ESCG"
white   = MkColor "\ESCh" "\ESCH"

endsgr i s = i <> s <> "\ESC|"

invertColors             = endsgr "\ESC#"
foreground (MkColor n _) = endsgr n
background (MkColor _ n) = endsgr n

lengthANSI :: String -> Word
lengthANSI s = f 0 $ stringToList s where

  f acc = \case
    '\ESC' :. _ :. cs -> f acc cs
    _ :. cs -> f (acc + 1) cs
    Nil -> acc

fixANSI :: String -> String
fixANSI cs = f (T4 0 39 49 False :. Nil) cs where

  f :: List (Tup4 Word Word Word Bool) -> String -> String
  f as@(T4 a x y z :. bs) (ConsChar '\ESC' (ConsChar i cs))
    | i == '|'         = sgr a (f bs cs)
    | i == '#'         = sgr (if z then 27 else 7) (f (T4 (if z then 7 else 27) x y (not z) :. as) cs)
    | 'a' <= i, i <= 'h', j <- charToWord i -. 67 = sgr j (f (T4 x j y z :. as) cs)
    | 'A' <= i, i <= 'H', j <- charToWord i -. 25 = sgr j (f (T4 y x j z :. as) cs)
  f as (ConsStr s@"\ESC" cs) = s <> f as cs
  f _  NilStr = mempty
  f as (spanStr (/= '\ESC') -> T2 bs cs) = bs <> f as cs

  sgr a b = "\ESC[" <> showWord a <> "m" <> b

