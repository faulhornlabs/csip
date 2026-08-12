module B1_Basic
  ( on, ($), (.), flip, id
  , Semigroup, (<>), Monoid, mempty, mconcat, mreplicate, Endo (MkEndo), appEndo
  , Functor, (<$>), (<&>)
  , Monad, pure, (>>=), (<*>), (>>), (>=>), (=<<), forM, forM_, foldM, filterM
  , Bool (True, False), (&&), (||), not
  , Char, isUpper, isLower, isDigit, isGraphic, isAlphaNum, isSpace
  , List (Nil, INil, (:.)), nub, (++), drop, take, takeWhile, filter
  , map, replicate, reverse, splitAt, revSplitAt, zipWith, intersperse, everyNth, distribute
  , Maybe (Just, Nothing), maybe, fromMaybe, fromMaybe', isJust, firstJust, last, (!!)
  , Either (Left, Right), either
  , Tag, tag, compareTag, Ordering (LT, EQ, GT), (&&&), Ord, compare, (==), (/=), (<=), (>=), (<), (>), max, min
  , Word, enumFromTo, numberWith, (+), fromInteger, (*), (-), even, HasId (getId), (===)
  , Tup0 (T0), Tup2 (T2), Tup3 (T3), Tup4 (T4), fst, snd, dup, first, second
  , foldMap, foldr, foldr1, foldl, null, length, all, mapM, condCons, guard, lookupList
  ) where

import B0_Builtins


---------------------------------------- Fixities

infixl 9 !!
infixr 9 .
infixl 7 *
infixl 6 +, -
infixr 6 <>
infixr 5 ++, :.
infix  4 /=, ==, >, >=, <, <=, ===
infixl 4 <$>, <*>
infixr 3 &&, &&&
infixr 2 ||
infixl 1 <&>, >>=, >>
infixr 1 >=>, =<<
infixr 0 $


---------------------------------------- Semigroup, Monoid

class Semigroup a where
  (<>) :: a -> a -> a

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


---------------------------------------- Functor, Monad

class Functor m where
  (<$>) :: (a -> b) -> m a -> m b

m <&> f = f <$> m


class Functor m => Monad m where
  pure  :: a -> m a
  (>>=) :: m a -> (a -> m b) -> m b

(<*>) :: Monad m => m (a -> b) -> m a -> m b
f <*> x = f >>= \f -> f <$> x

a >> b  = a >>= \_ -> b
f =<< m = m >>= f
f >=> g = \x -> f x >>= g

mapM _ Nil = pure Nil
mapM f (x :. xs) = f x >>= \x -> mapM f xs <&> (:.) x

forM a b = mapM b a

forM_ Nil _ = pure T0
forM_ (x :. xs) f = f x >> forM_ xs f

filterM :: Monad m => (a -> m Bool) -> List a -> m (List a)
filterM _ Nil = pure Nil
filterM p (a :. b) = p a >>= \case
  True -> (a :.) <$> filterM p b
  False -> filterM p b

foldM :: Monad m => (b -> a -> m b) -> b -> List a -> m b
foldM f a l = foldl (\a b -> a >>= \a -> f a b) (pure a) l


---------------------------------------- Functions

id     = \x -> x
flip f = \x y -> f y x
f . g  = \x -> f (g x)
f $ x  = f x
on f g = \x y -> f (g x) (g y)


---------------------------------------- List


data List a = Nil | a :. List a

pattern INil :: List a
pattern INil <- _
  where INil =  Nil

{-# COMPLETE INil #-}

instance Tag (List a) where
  tag Nil      = 0
  tag (_ :. _) = 1

instance Ord a => Ord (List a) where
  compare (a :. as) (b :. bs) = compare a b &&& lazy (compare as bs)
  compare a b = compareTag a b

instance Semigroup (List a) where  (<>) = (++)
instance Monoid    (List a) where  mempty = Nil
instance Functor    List    where  (<$>) = map

concatMap _ Nil = Nil
concatMap f (a :. b) = f a ++ concatMap f b

instance Monad List where
  pure x = x :. Nil
  m >>= f = concatMap f m

intersperse :: a -> List a -> List a
intersperse _ Nil = Nil
intersperse _ xs@(_ :. Nil) = xs
intersperse x (a :. as) = a :. x :. intersperse x as

reverse = f Nil where
  f acc Nil = acc
  f acc (x :. xs) = f (x :. acc) xs

foldr _ n Nil = n
foldr f n (a :. b) = f a (foldr f n b)

foldr1 :: (a -> a -> a) -> a -> List a -> a
foldr1 _ n Nil = n
foldr1 f n (b :. bs) = f n (foldr1 f b bs)

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
distribute parts i = zipWith (-) is (0 :. is) where
  is = enumFromTo 1 (parts + 1) <&> \j -> (j * i - 1) `div` parts + 1

revSplitAt n xs = splitAt (length xs - n) xs


---------------------------------------- Tuples

data Tup2 a b = T2 a b
data Tup3 a b c = T3 a b c
data Tup4 a b c d = T4 a b c d

fst (T2 a _) = a
snd (T2 _ b) = b

first  f = \(T2 a b) -> T2 (f a) b
second f = \(T2 a b) -> T2 a (f b)

dup a = T2 a a

zipWith f (x :. xs) (y :. ys) = f x y :. zipWith f xs ys
zipWith _ _ _ = Nil


---------------------------------------- Bool

not True = False
not False = True

(&&), (||) :: Bool -> {-lazy-}Bool -> Bool
False && ~_ = False
True  && b  = b

True  || ~_ = True
False || b  = b

all p (x:. xs) = p x && all p xs
all _ _ = True

takeWhile p (x :. xs) | p x = x :. takeWhile p xs
takeWhile _ _ = Nil

null Nil = True
null _   = False

condCons :: Bool -> {-not lazy!-}a -> List a -> List a
condCons False _ bs =      bs
condCons _     a bs = a :. bs

filter _ Nil = Nil
filter p (x :. xs) = condCons (p x) x (filter p xs)


---------------------------------------- Ord

data Ordering = EQ | LT | GT

class Ord a where compare :: a -> a -> Ordering

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

lookupList _ Nil = Nothing
lookupList a (T2 b c :. _) | a == b = Just c
lookupList a (_ :. bs) = lookupList a bs


---------------------------------------- Maybe

data Maybe a = Nothing | Just a

instance Tag (Maybe a) where
  tag Nothing = 0
  tag Just{}  = 1

instance Ord a => Ord (Maybe a) where
  compare (Just a) (Just b) = compare a b
  compare a b = compareTag a b

isJust Just{} = True
isJust _      = False

fromMaybe :: Lazy a -> Maybe a -> a
fromMaybe _ (Just a) = a
fromMaybe a _        = force a

fromMaybe' _ (Just a) = a
fromMaybe' a _        = a

maybe :: {-not lazy!-}a -> (b -> a) -> Maybe b -> a
maybe _ b (Just c) = b c
maybe a _ _        = a

firstJust :: Maybe a -> {-not lazy!-}Maybe a -> Maybe a
firstJust Nothing x = x
firstJust x       _ = x

last :: List a -> Maybe a
last (x :. Nil) = Just x
last (_ :. xs) = last xs
last _ = Nothing

(!!) :: List a -> Word -> Maybe a
(x :. _)  !! 0 = Just x
(_ :. xs) !! i = xs !! (i - 1)
_         !! _ = Nothing

instance Semigroup a => Semigroup (Maybe a) where
  Nothing <> a       = a
  a       <> Nothing = a
  Just a  <> Just b  = Just (a <> b)

instance Semigroup a => Monoid (Maybe a) where
  mempty = Nothing

instance Functor Maybe where
  _ <$> Nothing = Nothing
  f <$> Just a  = Just (f a)


---------------------------------------- Either

data Either a b = Left a | Right b

either f g = \case
  Left  a -> f a
  Right b -> g b


---------------------------------------- Char

instance Ord Char where compare a b = compare (ord a) (ord b)

isSpace, isUpper, isLower, isDigit, isGraphic, isAlphaNum :: Char -> Bool

isSpace c = c == ' ' || c == '\n'
isUpper c = 'A' <= c && c <= 'Z'
isLower c = 'a' <= c && c <= 'z'
isDigit c = '0' <= c && c <= '9'

isAlphaNum c = isLower c || isUpper c || isDigit c || c == '_' || c == '\''

isGraphic c = c == '!' || c == '#'  || c == '$' || c == '%' || c == '&'
           || c == '*' || c == '+'  || c == '-' || c == '.' || c == '/'
           || c == ':' || c == '<'  || c == '=' || c == '>' || c == '?'
           || c == '@' || c == '\\' || c == '^' || c == '|' || c == '~'


---------------------------------------- Word

instance Ord Word where
  compare a b | eqWord a b = EQ
              | ltWord a b = LT
              | True       = GT

fromInteger = integerToWord

(+) = addWord
(*) = mulWord

even n = andWord n 1 == 0

a - b | b > a = 0
a - b = subWord a b

length :: List a -> Word
length = f 0 where
  f i Nil = i
  f i (_ :. x) = f (i+1) x

replicate :: Word -> a -> List a
replicate 0 _ = Nil
replicate i x = x :. replicate (i-1) x

take, drop :: Word -> List a -> List a
take 0 _   = Nil
take _ Nil = Nil
take i (x :. xs) = x :. take (i-1) xs

drop 0 xs  = xs
drop _ Nil = Nil
drop i (_ :. xs) = drop (i-1) xs

splitAt :: Word -> List a -> Tup2 (List a) (List a)
splitAt 0 xs  = T2 Nil xs
splitAt _ Nil = T2 Nil Nil
splitAt i (x :. xs) | T2 as bs <- splitAt (i-1) xs = T2 (x :. as) bs

enumFromTo :: Word -> Word -> List Word
enumFromTo a b | a >= b = Nil
enumFromTo a b = a :. enumFromTo (a+1) b

----------------

class HasId a where
  getId :: a -> Word

instance HasId Word where
  getId i = i

(===) :: HasId a => a -> a -> Bool
a === b = getId a == getId b

nub Nil = Nil
nub (x:. xs) = x :. nub (filter (not . (=== x)) xs)
