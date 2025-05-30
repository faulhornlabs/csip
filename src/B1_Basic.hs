module B1_Basic
  ( on, ($), (.), flip, id

  , Semigroup, (<>), (<<>>), Monoid, mempty, mconcat, mreplicate
  , Endo (MkEndo), appEndo

  , Functor ((<$>)), (<&>), Applicative (pure, (<*>))
  , Monad, (>>=), (>>), join, (>=>), (=<<), forM, forM_, foldM

  , Bool (True, False), (&&), (||), not

  , Char, ord, digitToWord
  , isUpper, isLower, isDigit, isGraphic, isAlphaNum, isSpace

  , List (Nil, (:.))
  , nub, (++), drop, dropWhile, take, takeWhile, filter
  , map, replicate, reverse, span, splitAt, revSplitAt, zip, zipWith, unzip, groupBy
  , intercalate, intersperse, stripPrefix, tails, everyNth, distribute

  , Maybe (Just, Nothing), maybe, fromMaybe, fromMaybe', maybeToList, listToMaybe, isJust, isNothing
  , firstJust

  , Void, Either (Left, Right), either

  , Tag (tag), compareTag
  , Ordering (LT, EQ, GT), (&&&)
  , Ord (compare), (==), (/=), (<=), (>=), (<), (>), max, min

  , Int, Word, intToWord, wordToInt, enumFromTo, numberWith

  , Num ((+), fromWord), fromInteger, Mul ((*)), Minus ((-)), Diff ((-.))
  , Natural (div, mod)
  , Bits (shiftR, shiftL, (.&.), (.|.)), even

  , Tup0 (T0), Tup2 (T2), Tup3 (T3), Tup4 (T4), Tup5 (T5)
  , fst, snd, uncurry, matchT2
  , (***), first, second

  , foldMap, foldr, foldl, null, length, elem, sum, all, and, any, or
  , mapM_, sequence, mapM, condCons, guard, lookupList

  , Interval (MkInterval), mkInterval

  , IntHash (intHash)
  ) where

import B0_Builtins


---------------------------------------- Fixities

infixl 9 ***
infixr 9 .
infixl 7 *, `mod`, `div`, .&.
infixl 6 +, -, -.
infixr 6 <>, <<>>
infixl 5 .|.
infixr 5 ++, :.
infix  4 /=, ==, >, >=, <, <=
infixl 4 <$>, <*>
infixr 3 &&, &&&
infixr 2 ||
infixl 1 <&>, >>=, >>
infixr 1 >=>, =<<
infixr 0 $


---------------------------------------- Semigroup, Monoid

class Semigroup a where
  (<>) :: a -> a -> a

a <<>> b = (<>) <$> a <*> b

class Semigroup a => Monoid a where
  mempty :: a

mconcat = foldr (<>) mempty

foldMap f = foldr (\a b -> f a <> b) mempty

mreplicate n a = mconcat (replicate n a)

data Endo a = MkEndo (a -> a)

appEndo (MkEndo f) = f

instance Semigroup (Endo a) where
  MkEndo f <> MkEndo g = MkEndo (f . g)

instance Monoid (Endo a) where
  mempty = MkEndo id


---------------------------------------- Functor, Applicative, Monad

class Functor m where
  (<$>) :: (a -> b) -> m a -> m b

m <&> f = f <$> m

class Functor m => Applicative m where
  pure  :: a -> m a
  (<*>) :: m (a -> b) -> m a -> m b

class Applicative m => Monad m where
  (>>=) :: m a -> (a -> m b) -> m b

(>>) :: Monad m => m a -> m b -> m b
a >> b = a >>= \_ -> b

f =<< m = m >>= f

mapM _ Nil = pure Nil
mapM f (x :. xs) = f x >>= \x -> mapM f xs <&> (:.) x

mapM_ _ Nil = pure T0
mapM_ f (x :. xs) = f x >> mapM_ f xs

sequence Nil = pure Nil
sequence (x :. xs) = x >>= \x -> sequence xs <&> (:.) x

forM  a b = mapM  b a

forM_ a b = mapM_ b a

f >=> g = \x -> f x >>= g

foldM :: Monad m => (b -> a -> m b) -> b -> List a -> m b
foldM f a l = foldl (\a b -> a >>= \a -> f a b) (pure a) l

join m = m >>= \x -> x


---------------------------------------- Functions

id = \x -> x

flip f = \x y -> f y x

f . g = \x -> f (g x)

f $ x = f x

on f g = \x y -> f (g x) (g y)

instance Semigroup a => Semigroup (b -> a) where
  (f <> g) x = f x <> g x

instance Monoid a => Monoid (b -> a) where
  mempty _ = mempty

instance Functor ((->) a) where
  (<$>) f g x = f (g x)

instance Applicative ((->) a) where
  pure x _ = x
  (f <*> g) x = f x (g x)


---------------------------------------- List


data List a = Nil | a :. List a

instance Tag (List a) where
  tag Nil      = 0
  tag (_ :. _) = 1

instance Ord a => Ord (List a) where
  compare (a :. as) (b :. bs) = compare a b &&& lazy (compare as bs)
  compare a b = compareTag a b

instance Semigroup (List a) where
  (<>) = (++)

instance Monoid (List a) where
  mempty = Nil

instance Functor List where
  (<$>) = map

concatMap _ Nil = Nil
concatMap f (a :. b) = f a ++ concatMap f b

instance Applicative List where
  pure x = x :. Nil
  fs <*> xs = concatMap (\f -> map f xs) fs

instance Monad List where
  m >>= f = concatMap f m

tails Nil = Nil :. Nil
tails ys@(_ :. xs) = ys :. tails xs

intersperse :: a -> List a -> List a
intersperse _ Nil = Nil
intersperse _ xs@(_ :. Nil) = xs
intersperse x (a :. as) = a :. x :. intersperse x as

intercalate :: List a -> List (List a) -> List a
intercalate xs xss = mconcat (intersperse xs xss)

reverse = f Nil where
  f acc Nil = acc
  f acc (x :. xs) = f (x :. acc) xs

foldr _ n Nil = n
foldr f n (a :. b) = f a (foldr f n b)

foldl _ n Nil = n
foldl f n (a :. b) = foldl f (f n a) b

(x :. xs) ++ ys = x :. (xs ++ ys)
Nil       ++ ys = ys

map _ Nil = Nil
map f (x :. xs) = f x :. map f xs

numberWith :: (Word -> a -> b) -> Word -> List a -> List b
numberWith _ _ Nil = Nil
numberWith f i (x :. xs) = f i x :. numberWith f (i+1) xs


guard :: Bool -> List Tup0
guard True = T0 :. Nil
guard _    = Nil

everyNth _ Nil = Nil
everyNth i as = take i as :. everyNth i (drop i as)

distribute :: Word -> Word -> List Word
distribute parts i = zipWith (-.) is (0 :. is) where
  is = enumFromTo 1 (parts + 1) <&> \j -> (j * i -. 1) `div` parts + 1

revSplitAt n xs = splitAt (length xs -. n) xs


------------------------------------------------ Void

data Void

instance Ord Void where compare ~_ ~_ = EQ


---------------------------------------- Tuples

instance Semigroup Tup0 where
  _ <> _ = T0

instance Monoid Tup0 where
  mempty = T0


data Tup2 a b = T2 a b

instance (Ord a, Ord b) => Ord (Tup2 a b) where
  T2 a b `compare` T2 a' b' = compare a a' &&& lazy (compare b b')

instance (Semigroup a, Semigroup b) => Semigroup (Tup2 a b) where
  T2 a b <> T2 a' b' = T2 (a <> a') (b <> b')

instance (Monoid a, Monoid b) => Monoid (Tup2 a b) where
  mempty = T2 mempty mempty

fst (T2 a _) = a

snd (T2 _ b) = b

uncurry f = \(T2 a b) -> f a b

first f = \(T2 a b) -> T2 (f a) b

second f = \(T2 a b) -> T2 a (f b)

f *** g = \(T2 a b) -> T2 (f a) (g b)

matchT2 (T2 a b) f = f a b

zipWith f (x :. xs) (y :. ys) = f x y :. zipWith f xs ys
zipWith _ _ _ = Nil

zip = zipWith T2

unzip Nil = T2 Nil Nil
unzip (T2 x y :. xs) | T2 a b <- unzip xs = T2 (x :. a) (y :. b)


data Tup3 a b c = T3 a b c

instance (Semigroup a, Semigroup b, Semigroup c) => Semigroup (Tup3 a b c) where
  T3 a b c <> T3 a' b' c' = T3 (a <> a') (b <> b') (c <> c')

instance (Monoid a, Monoid b, Monoid c) => Monoid (Tup3 a b c) where
  mempty = T3 mempty mempty mempty

data Tup4 a b c d = T4 a b c d

data Tup5 a b c d e = T5 a b c d e


---------------------------------------- Bool

not True = False
not False = True

(&&), (||) :: Bool -> {-Lazy-}Bool -> Bool
False && ~_ = False
True  && b  = b

True  || ~_ = True
False || b  = b

and = foldr (&&) True
or  = foldr (||) False

any p (x:. xs) = p x || any p xs
any _ _ = False

all p (x:. xs) = p x && all p xs
all _ _ = True

takeWhile p (x :. xs) | p x = x :. takeWhile p xs
takeWhile _ _ = Nil

dropWhile p (x :. xs) | p x = dropWhile p xs
dropWhile _ xs = xs

span p (x :. xs) | p x, T2 as bs <- span p xs = T2 (x :. as) bs
span _ xs = T2 Nil xs

null Nil = True
null _   = False



---------------------------------------- Eq

condCons :: Bool -> {-Lazy-}a -> List a -> List a
condCons False _ bs =      bs
condCons _     a bs = a :. bs

filter _ Nil = Nil
filter p (x :. xs) = condCons (p x) x (filter p xs)

groupBy _ Nil = Nil
groupBy f xs | T2 as bs <- g xs = as:. groupBy f bs
 where
  g Nil = T2 Nil Nil
  g (x:. xs) | T2 as bs <- h x xs = T2 (x:. as) bs

  h _ Nil = T2 Nil Nil
  h x (y:. ys)
    | f x y, T2 as bs <- h y ys = T2 (y:. as) bs
  h _ (y:. ys) = T2 Nil (y:. ys)

nub Nil = Nil
nub (x:. xs) = x:. nub (filter (/= x) xs)


lookupList _ Nil = Nothing
lookupList a (T2 b c :. _) | a == b = Just c
lookupList a (_ :. bs) = lookupList a bs

elem _ Nil = False
elem a (b :. _) | a == b = True
elem a (_ :. bs) = elem a bs

stripPrefix :: Ord a => List a -> List a -> Maybe (List a)
stripPrefix Nil xs = Just xs
stripPrefix (a :. as) (b :. bs) | a == b = stripPrefix as bs
stripPrefix _ _ = Nothing


---------------------------------------- Ord

data Ordering = EQ | LT | GT

class Ord a where
  compare :: a -> a -> Ordering

instance Ord Char where compare a b = compare (charToWord a) (charToWord b)
instance Ord Word where
  compare a b | eqWord a b = EQ
              | ltWord a b = LT
              | True       = GT

instance Ord Tup0 where compare _ _ = EQ


class Tag a where tag :: a -> Word

compareTag a b = compare (tag a) (tag b)

(&&&) :: Ordering -> Lazy Ordering -> Ordering
LT &&& _ = LT
EQ &&& x = force x
GT &&& _ = GT

a <  b = case compare a b of LT -> True ; EQ -> False; GT -> False
a <= b = case compare a b of LT -> True ; EQ -> True ; GT -> False
a >  b = case compare a b of LT -> False; EQ -> False; GT -> True
a >= b = case compare a b of LT -> False; EQ -> True ; GT -> True
a == b = case compare a b of LT -> False; EQ -> True ; GT -> False
a /= b = case compare a b of LT -> True ; EQ -> False; GT -> True

max a b | a < b = b
max a _ = a

min a b | a > b = b
min a _ = a


---------------------------------------- Maybe

data Maybe a = Nothing | Just a

instance Tag (Maybe a) where
  tag Nothing = 0
  tag Just{}  = 1

instance Ord a => Ord (Maybe a) where
  compare (Just a) (Just b) = compare a b
  compare a b = compareTag a b

maybeToList (Just x) = x :. Nil
maybeToList _ = Nil

listToMaybe (x :. _) = Just x
listToMaybe _ = Nothing

isJust Just{} = True
isJust _ = False

isNothing Nothing{} = True
isNothing _ = False

fromMaybe :: Lazy a -> Maybe a -> a
fromMaybe _ (Just a) = a
fromMaybe a _ = force a

fromMaybe' _ (Just a) = a
fromMaybe' a _ = a

maybe :: {-Lazy-}a -> (b -> a) -> Maybe b -> a
maybe _ b (Just c) = b c
maybe a  _ _ = a

firstJust :: Maybe a -> {-Lazy-}Maybe a -> Maybe a
firstJust Nothing x = x
firstJust x       _ = x

instance Semigroup a => Semigroup (Maybe a) where
  Nothing <> a       = a
  a       <> Nothing = a
  Just a  <> Just b  = Just (a <> b)

instance Semigroup a => Monoid (Maybe a) where
  mempty = Nothing

instance Functor Maybe where
  _ <$> Nothing = Nothing
  f <$> Just a  = Just (f a)

instance Applicative Maybe where
  pure = Just
  fs <*> xs = fs >>= \f -> f <$> xs

instance Monad Maybe where
  Nothing >>= _ = Nothing
  Just a  >>= f = f a


---------------------------------------- Either

data Either a b = Left a | Right b

either f g e = case e of
  Left  a -> f a
  Right b -> g b


---------------------------------------- Char

ord = charToWord

digitToWord c = ord c -. ord '0'

isSpace, isUpper, isLower, isDigit, isGraphic, isAlphaNum :: Char -> Bool

isSpace ' '  = True
isSpace '\n' = True
isSpace _    = False

isUpper c = 'A' <= c && c <= 'Z'
isLower c = 'a' <= c && c <= 'z'
isDigit c = '0' <= c && c <= '9'

isGraphic c = c == '!' || c == '#'  || c == '$' || c == '%' || c == '&'
           || c == '*' || c == '+'  || c == '-' || c == '.' || c == '/'
           || c == ':' || c == '<'  || c == '=' || c == '>' || c == '?'
           || c == '@' || c == '\\' || c == '^' || c == '|' || c == '~'

isAlphaNum c
  = isLower c || isUpper c || isDigit c || c == '_' || c == '\''


-----------------------------------------------

data Interval a = MkInterval a a

mkInterval a b = MkInterval a b

instance Semigroup (Interval a) where
  MkInterval a _ <> MkInterval _ b = MkInterval a b


---------------------------------------- Num

class Num a where
  (+) :: a -> a -> a
  fromWord :: Word -> a

class Num a => Mul a where
  (*) :: a -> a -> a

fromInteger = fromWord . integerToWord

sum = foldr (+) 0

class Num a => Diff a where
  (-.) :: a -> a -> a

class Num a => Bits a where
  (.&.)  :: a -> a -> a
  (.|.)  :: a -> a -> a
  shiftL :: a -> Word -> a
  shiftR :: a -> Word -> a

class Num a => Natural a where
  div :: a -> a -> a
  mod :: a -> a -> a

class Num a => Minus a where
  (-) :: a -> a -> a

even n = n .&. 1 == 0


---------------------------------------- Word

instance Num Word where
  (+) = addWord
  fromWord x = x

instance Mul Word where
  (*) = mulWord

instance Bits Word where
  (.&.) = andWord
  (.|.) = orWord
  shiftL = shiftLWord
  shiftR = shiftRWord

instance Natural Word where
  div = divWord
  mod = modWord

instance Diff Word where
  a -. b | b > a = 0
  a -. b = subWord a b

length :: List a -> Word
length = f 0 where
  f i Nil = i
  f i (_ :. x) = f (i+1) x

replicate :: Word -> a -> List a
replicate 0 _ = Nil
replicate i x = x :. replicate (i-.1) x

take, drop :: Word -> List a -> List a
take 0 _   = Nil
take _ Nil = Nil
take i (x :. xs) = x :. take (i-.1) xs

drop 0 xs  = xs
drop _ Nil = Nil
drop i (_ :. xs) = drop (i-.1) xs

splitAt :: Word -> List a -> Tup2 (List a) (List a)
splitAt 0 xs  = T2 Nil xs
splitAt _ Nil = T2 Nil Nil
splitAt i (x :. xs) | T2 as bs <- splitAt (i-.1) xs = T2 (x :. as) bs

enumFromTo :: Word -> Word -> List Word
enumFromTo a b | a >= b = Nil
enumFromTo a b = a :. enumFromTo (a+1) b


---------------------------------------- Int

data Int = MkInt Word

intToWord :: Int -> Word
intToWord (MkInt a) = a

wordToInt :: Word -> Int
wordToInt a = MkInt a

instance Num Int where
  MkInt a + MkInt b = MkInt (a + b)
  fromWord = wordToInt

instance Minus Int where
  MkInt a - MkInt b = MkInt (subWord a b)

instance Ord Int where
  compare a b = compare (intToWord a + 9223372036854775808) (intToWord b + 9223372036854775808)


------------------------------------------------ IntHash

class IntHash a where
  intHash :: a -> Word

instance IntHash Word where
  intHash x = x

instance IntHash Char where
  intHash = ord

instance IntHash a => IntHash (List a) where
  intHash xs
    = foldl (\h c -> 33*h + c) 5381 (map intHash xs)   -- djb2
