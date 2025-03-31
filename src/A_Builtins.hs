module A_Builtins
  ( on, ($), (.), const, flip, id

  , seq
  , String
  , Int, Word, Integer, intToInteger, integerToInt, intToWord, wordToInt
  , fromInteger
  , Bool (True, False), (&&), (||), not, ifThenElse
  , fst, snd, uncurry
  , enumFromTo

  , Char, ord, chr, digitToInt

  , List, pattern Nil
  , nub, init, last, (!!), (++), drop, dropWhile, take, takeWhile, filter
  , map, replicate, reverse, span, splitAt, zip, zipWith, unzip, groupBy
  , intercalate, intersperse, stripPrefix, tails

  , Maybe (Just, Nothing), maybe, fromMaybe, maybeToList, listToMaybe, isJust

  , Either (Left, Right), either

  , IsString, fromString, unlines, lines, words

  , Eq ((==)), (/=)
  , Ordering (LT, EQ, GT)
  , Ord, compare, (<=), (>=), (<), (>), max, min
  , Num, (+), (-), (*), negate
  , div, mod, shiftR, shiftL, (.&.), (.|.), even
  , Show (show)
  , readInt

  , Semigroup, (<>)
  , Monoid, mempty, mconcat

  , Functor (fmap), (<$>), (<&>)

  , pure, (<*>)

  , Tup0, pattern T0, Tup2, pattern T2, Tup3, pattern T3, Tup4, pattern T4
  , (***), first, second

  , when, (>>=), (>>), join, (>=>), (<=<), (=<<), forM, forM_, foldM
  , fail

  , foldMap, foldr, foldl, foldl1, null, length, elem, maximum, minimum, sum, all, and, any, or
  , concat, concatMap, mapM_
  , sequence, mapM

  , coerce


  , lookup, IO, FilePath, readFile
  , IOArray, UArray, unsafeRead, unsafeWrite, unsafeAt, unsafeNewArray_, numElements, listArray

  , IORef, newIORef, readIORef, writeIORef

  , Typeable, Proxy
  , KnownNat, Nat, SomeNat (SomeNat), someNatVal
  , Exception, catch, throwIO

  , unsafePerformIO

  , HasCallStack, callStack, getCallStack, SrcLoc(..)

  , finally

  , getArgs

  , hReady, hFlush, hSetEcho, BufferMode(..), hSetBuffering, hIsTerminalDevice, stdin, stdout

  , die

  , versionBranch

  , writeFile, getChar, putChar

  , doesFileExist, doesDirectoryExist, getTemporaryDirectory
  , listDirectory, createDirectoryIfMissing, removeDirectoryRecursive

  , getDataDir, getDataFileName, version
  ) where

import Prelude
  ( IO, Char, Int, Word, Integer
  , Bool (..)
  , Eq, (==)
  , Ordering (..)
  , Ord, compare
  , Show, show
  )
import qualified Data.Bits as P (shiftR, shiftL, (.&.), (.|.))
import qualified Prelude
  ( (*), (+), (-), fromInteger, negate, (>>=), (>>), pure, fmap, fromIntegral, undefined, fail, mod, div
  , Maybe (..)
  )
import Data.Char (ord, chr)
import Data.Typeable (Typeable, Proxy)
import GHC.TypeLits (KnownNat, Nat, SomeNat (SomeNat))
import qualified GHC.TypeLits as P (someNatVal)
import Data.Coerce (coerce)
import Data.Array.Base
  (UArray, unsafeRead, unsafeWrite, unsafeAt, unsafeNewArray_, numElements, listArray)
import Data.Array.IO
  (IOArray)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.Version (versionBranch)
import Control.Exception (Exception, catch, throwIO, finally)
import System.Environment (getArgs)
import System.IO
  ( hReady, hFlush, hSetEcho, BufferMode(..), hSetBuffering, hIsTerminalDevice
  , stdin, stdout, getChar, putChar, readFile, writeFile)
import System.IO.Unsafe (unsafePerformIO)
import System.Exit (die)
import System.Directory
  ( doesFileExist, doesDirectoryExist, getTemporaryDirectory, listDirectory
  , createDirectoryIfMissing, removeDirectoryRecursive)
import GHC.Stack (HasCallStack, callStack, getCallStack, SrcLoc(..))

import Paths_csip (getDataDir, getDataFileName, version)

---------------------------------------- Fixities

infixl 9 ***
infixl 9 !!
infixr 9 .
infixl 7 *, `mod`, `div`, .&.
infixl 6 +, -
infixr 6 <>
infixl 5 .|.
infixr 5 ++, :.
infix  4 /=, {- ==, -} >, >=, <, <=
infixl 4 <$>, <*>
infixr 3 &&
infixr 2 ||
infixl 1 <&>, >>=, >>
infixr 1 <=<, >=>, =<<
infixr 0 $

---------------------------------------- Semigroup, Monoid

class Semigroup a where
  (<>) :: a -> a -> a

class Semigroup a => Monoid a where
  mempty :: a

mconcat = foldr (<>) mempty

foldMap f = foldr (\ ~a ~b -> f a <> b) mempty


---------------------------------------- Functor, Applicative, Monad

class Functor m where
  fmap :: (a -> b) -> m a -> m b

(<$>) = fmap

m <&> f = f <$> m

class Functor m => Applicative m where
  pure :: a -> m a
  (<*>) :: m (a -> b) -> m a -> m b

class Applicative m => Monad m where
  (>>=) :: m a -> (a -> m b) -> m b
  (>>)  :: m a -> m b -> m b
  a >> b = a >>= \_ -> b

f =<< m = m >>= f

mapM _ Nil = pure Nil
mapM f (x :. ~xs) = f x >>= \x -> mapM f xs <&> (:.) x

mapM_ _ Nil = pure T0
mapM_ f (x :. ~xs) = f x >> mapM_ f xs

sequence Nil = pure Nil
sequence (x :. ~xs) = x >>= \x -> sequence xs <&> (:.) x
{-
sequence_ Nil = pure T0
sequence_ (x :. ~xs) = x >> sequence_ xs
-}

forM a b = mapM b a
forM_ a b = mapM_ b a
(f >=> g) x = f x >>= g
a <=< b = b >=> a

foldM :: Monad m => (b -> a -> m b) -> b -> List a -> m b
foldM f a l = foldl (\a b -> a >>= \a -> f a b) (pure a) l

join m = m >>= \x -> x

when False ~_ = pure ()
when _ m = m


class Monad m => MonadFail m where
  fail :: String -> m a


---------------------------------------- Functions

id = \x -> x

const x = \ ~_ -> x

flip f = \x y -> f y x

f . g = \x -> f (g x)

f $ ~x = f x

on f g = \x y -> f (g x) (g y)

seq _a b = b

undefined = Prelude.undefined

instance Semigroup a => Semigroup (b -> a) where
  (f <> g) x = f x <> g x

instance Monoid a => Monoid (b -> a) where
  mempty ~_ = mempty

instance Functor ((->) a) where
  fmap f g x = f (g x)

instance Applicative ((->) a) where
  pure x ~_ = x
  (f <*> g) x = f x (g x)


---------------------------------------- List

{-
data List a = a :. List a | Nil
-}

type List = []

pattern Nil = []

{-# COMPLETE Nil, (:) #-}

pattern (:.) :: a -> List a -> List a
pattern x :. xs <- ~x : ~xs
  where ~x :. ~xs = x : xs

{-# COMPLETE Nil, (:.) #-}

{-
fromList' :: [a] -> List a
fromList' [] = Nil
fromList' (x: xs) = x :. fromList' xs
-}

instance Semigroup (List a) where
  (<>) = (++)

instance Monoid (List a) where
  mempty = Nil
{-
instance Functor List where
  fmap = map

instance Applicative List where
  pure x = x :. Nil
  fs <*> xs = fs >>= \f -> fmap f xs

instance Monad List where
  ~m >>= f = concatMap f m
-}
singleton ~x = x :. Nil

intersperse :: a -> List a -> List a
intersperse ~_ Nil = Nil
intersperse ~_ xs@(~_ :. Nil) = xs
intersperse ~x (~a :. ~as) = a :. x :. intersperse x as

intercalate :: List a -> List (List a) -> List a
intercalate xs xss = concat (intersperse xs xss)

{-
head (a :. ~_) = a
-}

init (~_ :. Nil) = Nil
init (~x :. xs) = x :. init xs
init _ = undefined

last (~x :. Nil) = x
last (~_ :. xs) = last xs
last _ = undefined

reverse = f Nil where
  f acc Nil = acc
  f acc (~x :. xs) = f (x :. acc) xs

tails Nil = Nil :. Nil
tails ys@(_: ~xs) = ys: tails xs


foldr _ ~n Nil = n
foldr f ~n (~a :. ~b) = f a (foldr f n b)

foldl _ n Nil = n
foldl f n (a :. b) = foldl f (f n a) b

foldl1 f (x :. xs) = foldl f x xs
foldl1 _ _ = undefined

{-
scanl f ~n ~xs = n :. case xs of
  Nil -> Nil
  ~a :. ~b -> scanl f (f n a) b
-}

xs ++ ~ys = foldr (:.) ys xs

concat = foldr (++) Nil

map f = foldr (\ ~x ~y -> f x :. y) Nil

concatMap _ Nil = Nil
concatMap f (~a :. ~b) = f a ++ concatMap f b


---------------------------------------- Tuples

{-
data Tup0 = T0
-}

type Tup0 = ()
pattern T0 = ()
{-# COMPLETE T0 #-}

instance Semigroup Tup0 where
  _ <> _ = T0

instance Monoid Tup0 where
  mempty = T0



{-
data Tup2 a b = T2 a b
-}

type Tup2 a b = (a, b)
pattern T2 a b <- (~a, ~b)
  where T2 ~a ~b = (a, b)
{-# COMPLETE T2 #-}

instance (Semigroup a, Semigroup b) => Semigroup (Tup2 a b) where
  T2 a b <> T2 a' b' = T2 (a <> a') (b <> b')

instance (Monoid a, Monoid b) => Monoid (Tup2 a b) where
  mempty = T2 mempty mempty

fst (T2 a ~_) = a

snd (T2 ~_ b) = b

uncurry f = \(T2 ~a ~b) -> f a b

first f = \(T2 ~a ~b) -> T2 (f a) b

second f = \(T2 ~a ~b) -> T2 a (f b)

f *** g = \(T2 ~a ~b) -> T2 (f a) (g b)

zipWith f (~x :. ~xs) (~y :. ~ys) = f x y :. zipWith f xs ys
zipWith _ _ _ = Nil

zip = zipWith T2

unzip Nil = T2 Nil Nil
unzip (~(T2 ~x ~y) :. ~xs) | T2 ~a ~b <- unzip xs = T2 (x :. a) (y :. b)



{-
data Tup3 a b c = T3 a b c
data Tup4 a b c d = T4 a b c d
data Tup5 a b c d e = T5 a b c d e
data Tup6 a b c d e f = T6 a b c d e f
-}

type Tup3 a b c = (a, b, c)
pattern T3 a b c = (a, b, c)
{-# COMPLETE T3 #-}
type Tup4 a b c d = (a, b, c, d)
pattern T4 a b c d = (a, b, c, d)
{-# COMPLETE T4 #-}

instance (Semigroup a, Semigroup b, Semigroup c) => Semigroup (Tup3 a b c) where
  T3 a b c <> T3 a' b' c' = T3 (a <> a') (b <> b') (c <> c')

instance (Monoid a, Monoid b, Monoid c) => Monoid (Tup3 a b c) where
  mempty = T3 mempty mempty mempty


---------------------------------------- Bool

{-
data Bool = False | True
-}

ifThenElse True ~a ~_ = a
ifThenElse _    ~_ ~b = b

not True = False
not False = True

False && ~_ = False
True  && b = b

True || ~_ = True
False || b = b

and = foldr (&&) True
or  = foldr (||) False

any p (x:. ~xs) = p x || any p xs
any _ _ = False

all p (x:. ~xs) = p x && all p xs
all _ _ = True

takeWhile p (x :. ~xs) | p x = x :. takeWhile p xs
takeWhile _ _ = Nil

dropWhile p (x :. ~xs) | p x = dropWhile p xs
dropWhile _ xs = xs

span p (x :. xs) | p x, T2 as bs <- span p xs = T2 (x :. as) bs
span _ xs = T2 Nil xs

null Nil = True
null _ = False



---------------------------------------- Eq

a /= b = not (a == b)


filter _ Nil = Nil
filter p (x :. ~xs) = case p x of False -> filter p xs; True -> x :. filter p xs

groupBy _ Nil = Nil
groupBy f xs | (as, ~bs) <- g xs = as: groupBy f bs
 where
  g Nil = (Nil, Nil)
  g (x: ~xs) | (as, ~bs) <- h x xs = (x: as, bs)

  h _ Nil = (Nil, Nil)
  h x (y: ~ys)
    | f x y, (as, ~bs) <- h y ys = (y: as, bs)
    | True = (Nil, y: ys)

nub Nil = Nil
nub (x: ~xs) = x: nub (filter (/= x) xs)

lookup _ Nil = Nothing
lookup a (T2 b ~c :. ~_) | a == b = Just c
lookup a (_ :. bs) = lookup a bs

elem _ Nil = False
elem a (b :. ~_) | a == b = True
elem a (_ :. bs) = elem a bs

stripPrefix :: Eq a => List a -> List a -> Maybe (List a)
stripPrefix Nil ~xs = Just xs
stripPrefix (a :. ~as) (b :. ~bs) | a == b = stripPrefix as bs
stripPrefix _ _ = Nothing



---------------------------------------- Ord

a < b = compare a b == LT
a > b = compare a b == GT
a <= b = not (a > b)
a >= b = not (a < b)

max a b | a < b = b
        | True  = a
min a b | a > b = b
        | True  = a

maximum = foldl1 max
minimum = foldl1 min


---------------------------------------- Maybe

data Maybe a = Nothing | Just a
  deriving (Eq, Ord)

maybeToList (Just x) = x : Nil
maybeToList _ = Nil

listToMaybe (x : _) = Just x
listToMaybe _ = Nothing

isJust Just{} = True
isJust _ = False

fromMaybe ~_ (Just a) = a
fromMaybe a _ = a

maybe ~_ b (Just c) = b c
maybe a _ _ = a

instance Semigroup a => Semigroup (Maybe a) where
  Nothing <> a = a
  a <> Nothing = a
  Just a <> Just b = Just (a <> b)

instance Semigroup a => Monoid (Maybe a) where
  mempty = Nothing

instance Functor Maybe where
  fmap _ Nothing = Nothing
  fmap f (Just a) = Just (f a)

instance Applicative Maybe where
  pure = Just
  fs <*> xs = fs >>= \f -> fmap f xs

instance Monad Maybe where
  Nothing >>= _ = Nothing
  Just a >>= f = f a


---------------------------------------- Either

data Either a b = Left a | Right b
  deriving (Eq, Ord)

either f g e = case e of
  Left  a -> f a
  Right b -> g b


---------------------------------------- Char

digitToInt c = ord c - ord '0'


---------------------------------------- String

type String = List Char
type FilePath = String


class IsString a where
  fromString :: String -> a

instance IsString String where
  fromString = id



{-
showInt :: Int -> String
showInt i
  | True <- i ==. 0 = '0' :. Nil
  | True <- i < 0   = '-' :. f (negate i)
  | T0 <- T0   = f i
 where
  f i = g Nil (quot i 10) (rem i 10)
  g acc 0 0 = acc
  g acc q r = g (chr (48 + r) :. acc) (quot q 10) (rem q 10)
-}
readInt :: String -> Int
--readInt ('-' :. Nil) = 0
readInt ('0' :. Nil) = 0
readInt cs = f 0 cs where
  f acc Nil = acc
  f acc (c :. cs) = f (10 * acc + ord c - 48) cs

unlines xs = concat $ map (++ "\n") xs

words = g where
  g Nil = Nil
  g (' ' :. xs) = g xs
  g (x :. xs) = h (singleton x) xs

  h acc Nil = reverse acc :. Nil
  h acc (' ' :. ~xs) = reverse acc :. g xs
  h acc (x :. ~xs) = h (x :. acc) xs

lines = h Nil where
  h acc Nil = reverse acc :. Nil
  h acc ('\n' :. ~xs) = reverse acc :. h Nil xs
  h acc (x :. ~xs) = h (x :. acc) xs


---------------------------------------- Num

class Num a where
  (+) :: a -> a -> a
  (-) :: a -> a -> a
  (*) :: a -> a -> a
  negate :: a -> a
  fromInteger :: Integer -> a

sum = foldr (+) 0


class Num a => Integral a where
  div :: a -> a -> a
  mod :: a -> a -> a
  (.&.) :: a -> a -> a
  (.|.) :: a -> a -> a
  shiftL :: a -> Int -> a
  shiftR :: a -> Int -> a

even n = n .&. 1 == 0

---------------------------------------- Int

instance Num Int where
  (+) = (Prelude.+)
  (-) = (Prelude.-)
  (*) = (Prelude.*)
  negate = Prelude.negate
  fromInteger = Prelude.fromInteger

instance Integral Int where
  div = Prelude.div
  mod = Prelude.mod
  (.&.) = (P..&.)
  (.|.) = (P..|.)
  shiftL = P.shiftL
  shiftR = P.shiftR

length :: List a -> Int
length = f 0 where
  f i Nil = i
  f i (~_ :. x) = f (i+1) x

replicate :: Int -> a -> List a
replicate i ~_ | i <= 0 = Nil
replicate i ~x = x :. replicate (i-1) x

take :: Int -> List a -> List a
take i _ | True <- i <= 0 = Nil
take _ Nil = Nil
take i (~x :. ~xs) = x :. take (i-1) xs

drop :: Int -> List a -> List a
drop i xs | True <- i <= 0 = xs
drop _ Nil = Nil
drop i (~_ :. ~xs) = drop (i-1) xs

splitAt :: Int -> List a -> Tup2 (List a) (List a)
splitAt i xs | True <- i <= 0 = T2 Nil xs
splitAt _ Nil = T2 Nil Nil
splitAt i (~x :. ~xs) | T2 as bs <- splitAt (i-1) xs = T2 (x :. as) bs

enumFromTo :: Int -> Int -> List Int
enumFromTo a b | a > b = Nil
enumFromTo a b = a :. enumFromTo (a+1) b

(!!) :: List a -> Int -> a
(x :. ~_) !! 0 = x
(_ :. xs) !! i = xs !! (i-1)
_ !! _ = undefined



---------------------------------------- Word

intToWord :: Int -> Word
intToWord = Prelude.fromIntegral

wordToInt :: Word -> Int
wordToInt = Prelude.fromIntegral

instance Num Word where
  (+) = (Prelude.+)
  (-) = (Prelude.-)
  (*) = (Prelude.*)
  negate = Prelude.negate
  fromInteger = Prelude.fromInteger

instance Integral Word where
  div = Prelude.div
  mod = Prelude.mod
  (.&.) = (P..&.)
  (.|.) = (P..|.)
  shiftL = P.shiftL
  shiftR = P.shiftR

---------------------------------------- Integer

intToInteger :: Int -> Integer
intToInteger = Prelude.fromIntegral

integerToInt :: Integer -> Int
integerToInt = Prelude.fromIntegral

instance Num Integer where
  (+) = (Prelude.+)
  (-) = (Prelude.-)
  (*) = (Prelude.*)
  negate = Prelude.negate
  fromInteger = Prelude.fromInteger

instance Integral Integer where
  div = Prelude.div
  mod = Prelude.mod
  (.&.) = (P..&.)
  (.|.) = (P..|.)
  shiftL = P.shiftL
  shiftR = P.shiftR


---------------------------------------- IO

instance Functor IO where
  fmap = Prelude.fmap

instance Applicative IO where
  pure = Prelude.pure
  fs <*> xs = fs >>= \f -> fmap f xs

instance Monad IO where
  (>>=) = (Prelude.>>=)
  (>>) = (Prelude.>>)

instance MonadFail IO where
  fail = Prelude.fail

instance Semigroup a => Semigroup (IO a) where
  m <> n = (<>) <$> m <*> n


----------------------------------------

someNatVal :: Int -> SomeNat
someNatVal i = case P.someNatVal (intToInteger i) of
  Prelude.Just x -> x
  _ -> undefined
