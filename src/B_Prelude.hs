module B_Prelude
  ( on, ($), (.), const, flip, id

  , seq
  , String
  , Int, showInt, showInteger
  , Word, Integer, {- intToInteger, integerToInt, -} wordToInteger, integerToWord, intToWord, wordToInt
  , Word128, wordToWord128, word128ToWord
  , fromInteger
  , Bool, pattern True, otherwise, pattern False, (&&), (||), not, ifThenElse
  , fst, snd, uncurry
  , enumFromTo

  , Char, ord, chr, digitToInt

  , List, pattern Nil, pattern (:.)
  , nub, init, last, (!!), (++), drop, dropWhile, take, takeWhile, filter
  , map, replicate, reverse, span, splitAt, zip, zipWith, unzip, groupBy
  , intercalate, intersperse, stripPrefix, tails

  , Maybe (Just, Nothing), maybe, fromMaybe, maybeToList, listToMaybe, isJust, isNothing

  , Either (Left, Right), either

  , IsString, fromString', fromString, unlines, lines, words

  , Eq ((==)), (/=)
  , Ordering, pattern LT, pattern EQ, pattern GT
  , Ord, compare, (<=), (>=), (<), (>), max, min
  , Num, (+), (-), (*), (-.)
  , div, mod, shiftR, shiftL, (.&.), (.|.), even
--  , Show, show
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


  , IO, FilePath, readFile
  , IOArray, CharArray, unsafeRead, unsafeWrite, unsafeAt, unsafeNewArray_, numElements, listArray

  , IORef, newIORef, readIORef, writeIORef

  , HasCallStack, callStack

  , finally

  , getArgs

  , hReady, hFlush, hSetEcho, BufferMode, noBuffering, lineBuffering, hSetBuffering, hIsTerminalDevice, stdin, stdout

  , die

  , versionBranch

  , writeFile, getChar, putChar

  , doesFileExist, doesDirectoryExist, getTemporaryDirectory
  , listDirectory, createDirectoryIfMissing, removeDirectoryRecursive

  , getDataDir, getDataFileName

--  , fromList, fromListN, toList
  , throwIO', catch'

------------------------

  , maybeList, stringToSource, guard, lookupList
  , stripSuffix
  , firstJust


  , Interval (MkInterval), mkInterval
  , Cached (MkCached, getCached)         -- newtype with trivial Eq, Ord instances

  , mreplicate

  , head, tail, fromJust
  , isUpper, isLower, isDigit, isGraphic, isAlphaNum

  , Source (Cons, Cons', NilCh)
  , lengthCh, spanCh, groupCh, splitAtCh, takeCh, dropCh, revSpanCh, revTakeCh, revDropCh, lastCh, headCh, readNat
  , chars
  , Print (print)
  , Parse (parse)
  , source

  , RefM, Ref, newRef, readRef, writeRef, modifyRef, stateRef
  , top_
  , topM, topRef, reset

  -- monad transformer alternatives
  , State,  runState,  evalState, gets, modify, topState
  , Reader, runReader, asks, local, topReader
  , Writer, runWriter, tell, listenAll
  , Except, runExcept, throwError, catchError

  , newId

  , pattern CSI
  , invert, background, foreground, black, red, green, yellow, blue, magenta, cyan, white
  , clearScreen, setCursorPosition, setCursorHPosition, cursorUp, cursorDown, cursorForward, cursorBack
  , showCursor, hideCursor, fixANSI
  , lengthANSI

  , mainException
  , tag
  , impossible, undefined, error, error', errorM, assert, assertM

  , traceShow, (<<>>)

  , IntHash (intHash)
  , importFile

  , Void

  , numberWith
  , fromListN, fromList, toList
  , showSource


  ) where

import Prelude
  ( Eq, (==)
  , Ord, compare
  , otherwise
  )

import A_Builtins hiding (Cons)
import qualified A_Builtins as B


---------------------------------------- Fixities

infixl 9 ***
infixl 9 !!
infixr 9 .
infixl 7 *, `mod`, `div`, .&.
infixl 6 +, -, -.
infixr 6 <>, <<>>
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

a <<>> b = (<>) <$> a <*> b

class Semigroup a => Monoid a where
  mempty :: a

mconcat = foldr (<>) mempty

foldMap f = foldr (\ a ~b -> f a <> b) mempty


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

class IsList l where
  type Item l

  fromList :: [Item l] -> l
  toList   :: l -> [Item l]

  fromListN :: Int -> [Item l] -> l
  fromListN _ = fromList
{-
  nil :: l
  isNil :: l -> Bool

  cons :: Item l -> l -> l
  unCons :: l -> Maybe (Item l, l)
-}

instance IsList [a] where
  type Item [a] = a
  fromList x = x
  toList x = x

instance IsList (List a) where
  type Item (List a) = a

  fromList = fl
  toList = tl

pattern (:.) :: a -> List a -> List a
pattern x :. xs <- B.Cons x ~xs
  where x :. ~xs = B.Cons x xs

{-# COMPLETE Nil, (:.) #-}

instance Semigroup (List a) where
  (<>) = (++)

instance Monoid (List a) where
  mempty = Nil

instance Functor List where
  fmap = map

instance Applicative List where
  pure = singleton
  fs <*> xs = concatMap (\f -> map f xs) fs

instance Monad List where
  m >>= f = concatMap f m

head :: HasCallStack => List a -> a
head (a:. _) = a
head _ = impossible

tail :: HasCallStack => List a -> List a
tail (_:. as) = as
tail _ = impossible

singleton x = x :. Nil

intersperse :: a -> List a -> List a
intersperse _ Nil = Nil
intersperse _ xs@(_ :. Nil) = xs
intersperse x (a :. ~as) = a :. x :. intersperse x as

intercalate :: List a -> List (List a) -> List a
intercalate xs xss = concat (intersperse xs xss)

{-
head (a :. ~_) = a
-}

init (_ :. Nil) = Nil
init (x :. xs) = x :. init xs
init _ = undefined

last (x :. Nil) = x
last (_ :. xs) = last xs
last _ = undefined

reverse = f Nil where
  f acc Nil = acc
  f acc (x :. xs) = f (x :. acc) xs

tails Nil = Nil :. Nil
tails ys@(_ :. ~xs) = ys :. tails xs


foldr _ ~n Nil = n
foldr f ~n (a :. ~b) = f a (foldr f n b)

foldl _ n Nil = n
foldl f n (a :. b) = foldl f (f n a) b

foldl1 f (x :. xs) = foldl f x xs
foldl1 _ _ = undefined

{-
scanl f ~n ~xs = n :. case xs of
  Nil -> Nil
  a :. ~b -> scanl f (f n a) b
-}

-- xs ++ ~ys = foldr (:.) ys xs
(x :. ~xs) ++ ~ys = x :. (xs ++ ys)
Nil ++ ys = ys

concat = foldr (++) Nil

--map f = foldr (\ x ~y -> f x :. y) Nil
map _ Nil = Nil
map f (x :. ~xs) = f x :. map f xs

concatMap _ Nil = Nil
concatMap f (a :. ~b) = f a ++ concatMap f b

numberWith :: (Word -> a -> b) -> Word -> List a -> List b
numberWith _ _ Nil = Nil
numberWith f i (~x :. ~xs) = f i x :. numberWith f (i+1) xs


------------------------------------------------ Void

data Void

instance Eq  Void where (==) = impossible
instance Ord Void where compare = impossible


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

zipWith f (x :. ~xs) (y :. ~ys) = f x y :. zipWith f xs ys
zipWith _ _ _ = Nil

zip = zipWith T2

unzip Nil = T2 Nil Nil
unzip (T2 ~x ~y :. ~xs) | T2 ~a ~b <- unzip xs = T2 (x :. a) (y :. b)



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
groupBy f xs | (as, ~bs) <- g xs = as:. groupBy f bs
 where
  g Nil = (Nil, Nil)
  g (x:. ~xs) | (as, ~bs) <- h x xs = (x:. as, bs)

  h _ Nil = (Nil, Nil)
  h x (y:. ~ys)
    | f x y, (as, ~bs) <- h y ys = (y:. as, bs)
  h _ (y:. ~ys) = (Nil, y:. ys)

nub Nil = Nil
nub (x:. ~xs) = x:. nub (filter (/= x) xs)
{-
nubBy _ Nil = Nil
nubBy f (x:. ~xs) = x:. nub (filter (\y -> f x /= f y) xs)
-}

lookupList _ Nil = Nothing
lookupList a (T2 b ~c :. ~_) | a == b = Just c
lookupList a (_ :. bs) = lookupList a bs

elem _ Nil = False
elem a (b :. ~_) | a == b = True
elem a (_ :. bs) = elem a bs

stripPrefix :: Eq a => List a -> List a -> Maybe (List a)
stripPrefix Nil ~xs = Just xs
stripPrefix (a :. ~as) (b :. ~bs) | a == b = stripPrefix as bs
stripPrefix _ _ = Nothing

maybeList a True bs = a :. bs
maybeList _ _ bs = bs

stripSuffix a b = fmap reverse (stripPrefix (reverse a) (reverse b))


---------------------------------------- Ord
{-
class Eq a => Ord a where
  compare :: a -> a -> Ordering
-}

a < b = compare a b == LT
a > b = compare a b == GT
a <= b = not (a > b)
a >= b = not (a < b)

max a b | a < b = b
max a _ = a
min a b | a > b = b
min a _ = a

maximum = foldl1 max
minimum = foldl1 min


---------------------------------------- Maybe

data Maybe a = Nothing | Just a
  deriving (Eq, Ord)
{-
instance Ord a => Ord (Maybe a) where
  compare Nothing Nothing = EQ
  compare Nothing _ = LT
  compare _ Nothing = GT
  compare (Just a) (Just b) = compare a b
-}
maybeToList (Just x) = x :. Nil
maybeToList _ = Nil

listToMaybe (x :. _) = Just x
listToMaybe _ = Nothing

isJust Just{} = True
isJust _ = False

isNothing Nothing{} = True
isNothing _ = False

fromJust :: HasCallStack => Maybe a -> a
fromJust (Just a) = a
fromJust _ = impossible

fromMaybe ~_ (Just a) = a
fromMaybe a _ = a

maybe ~_ b (Just c) = b c
maybe a _ _ = a

firstJust :: Maybe a -> Maybe a -> Maybe a
firstJust Nothing x = x
firstJust x _ = x

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
{-
instance (Ord a, Ord b) => Ord (Either a b) where
  Left a `compare` Left b = compare a b
  Left{} `compare` _      = LT
  _      `compare` Left{} = GT
  Right a `compare` Right b = compare a b
-}
either f g e = case e of
  Left  a -> f a
  Right b -> g b


---------------------------------------- Char

ord = charToWord

chr = wordToChar

digitToInt c = ord c -. ord '0'

isUpper, isLower, isDigit, isGraphic, isAlphaNum :: Char -> Bool

isUpper c = 'A' <= c && c <= 'Z'
isLower c = 'a' <= c && c <= 'z'
isDigit c = '0' <= c && c <= '9'

isGraphic c = c `elem`
  [ '!',  '#','$','%','&',  '*','+'
  , '-','.','/',  ':',  '<','=','>','?','@'
  , '\\',  '^',  '|',  '~']

isAlphaNum c
  = isLower c || isUpper c || isDigit c || c == '_' || c == '\''


---------------------------------------- String

class IsString a where
  fromString' :: String -> a

fromString :: IsString a => [Char] -> a
fromString cs = fromString' (fl cs)

instance IsString String where
  fromString' s = s

instance IsString [Char] where
  fromString' s = tl s


showInt :: Word -> String
showInt i | i == 0 = '0' :. Nil
showInt i = f i
 where
  f i = g Nil (div i 10) (mod i 10)
  g acc 0 0 = acc
  g acc q r = g (chr (48 + r) :. acc) (div q 10) (mod q 10)

showInteger :: Integer -> String
showInteger i | i == 0 = '0' :. Nil
showInteger i = f i
 where
  f i = g Nil (div i 10) (mod i 10)
  g acc 0 0 = acc
  g acc q r = g (chr (48 + integerToWord r) :. acc) (div q 10) (mod q 10)

readInt :: String -> Word
readInt ('0' :. Nil) = 0
readInt cs = f 0 cs where
  f acc Nil = acc
  f acc (c :. cs) = f (10 * acc + ord c -. 48) cs

unlines xs = concat (map (++ ('\n' :. Nil)) xs)

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


-----------------------------------------------

newtype Cached a = MkCached {getCached :: a}

instance Eq   (Cached a) where _ == _ = True
instance Ord  (Cached a) where compare _ _ = EQ


-----------------------------------------------

data Interval a = MkInterval a a
  deriving (Eq)

mkInterval a b = MkInterval a b

instance Semigroup (Interval a) where
  MkInterval a _ <> MkInterval _ b = MkInterval a b


---------------------------------------- Num

class Num a where
  (+) :: a -> a -> a
  (*) :: a -> a -> a
  fromInteger :: Integer -> a

sum = foldr (+) 0

class Num a => Diff a where
  (-.) :: a -> a -> a

class Num a => Bits a where
  (.&.) :: a -> a -> a
  (.|.) :: a -> a -> a
  shiftL :: a -> Int -> a
  shiftR :: a -> Int -> a

class (Bits a, Ord a) => Natural a where
  div :: a -> a -> a
  mod :: a -> a -> a

class Num a => Minus a where
  (-) :: a -> a -> a

even n = n .&. 1 == 0


---------------------------------------- Word

instance Num Word where
  (+) = addWord
  (*) = mulWord
  fromInteger = integerToWord

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

take :: Word -> List a -> List a
take 0 ~_ = Nil
take _ Nil = Nil
take i (x :. ~xs) = x :. take (i-.1) xs

drop :: Word -> List a -> List a
drop 0 xs = xs
drop _ Nil = Nil
drop i (_ :. ~xs) = drop (i-.1) xs

splitAt :: Word -> List a -> Tup2 (List a) (List a)
splitAt 0 ~xs = T2 Nil xs
splitAt _ Nil = T2 Nil Nil
splitAt i (x :. ~xs) | T2 as bs <- splitAt (i-.1) xs = T2 (x :. as) bs

enumFromTo :: Word -> Word -> List Word
enumFromTo a b | a >= b = Nil
enumFromTo a b = a :. enumFromTo (a+1) b

(!!) :: List a -> Word -> a
(x :. ~_) !! 0 = x
(_ :. xs) !! i = xs !! (i-.1)
_ !! _ = undefined


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

instance IntHash Source where
  intHash = intHash . chars


---------------------------------------- Int

instance Num Int where
  (+) = addInt
  (*) = mulInt
  fromInteger = integerToInt

instance Minus Int where
  (-) = subInt


---------------------------------------- Word128

newtype Word128 = MkW128 Integer{-TODO-}
  deriving (Eq, Ord)

wordToWord128 :: Word -> Word128
wordToWord128 w = MkW128 (wordToInteger w)

word128ToWord :: Word128 -> Word
word128ToWord (MkW128 w) = integerToWord w

mkW128 :: Integer -> Word128
mkW128 i = MkW128 (i .&. 340282366920938463463374607431768211455)

instance Num Word128 where
  MkW128 x + MkW128 y = mkW128 (x + y)
  MkW128 x * MkW128 y = mkW128 (x * y)
  fromInteger = mkW128

instance Bits Word128 where
  (.&.) = undefined
  (.|.) = undefined
  shiftL = undefined
  shiftR = undefined

instance Natural Word128 where
  MkW128 x `div` MkW128 y = MkW128 (x `div` y)
  MkW128 x `mod` MkW128 y = MkW128 (x `mod` y)


---------------------------------------- Integer

{- TODO
data Integer
  = SmallInt Int
  | BigInt Integer Int
-}

instance Num Integer where
  (+) = addInteger
  (*) = mulInteger
  fromInteger = id

instance Diff Integer where
  a -. b | b > a = 0
  a -. b = subInteger a b

instance Bits Integer where
  (.&.) = andInteger
  (.|.) = orInteger
  shiftL = shiftLInteger
  shiftR = shiftRInteger

-- TODO: remove
instance Natural Integer where
  div = divInteger
  mod = modInteger

readNat :: String -> Maybe Integer
readNat cs
  | all isDigit cs = Just (foldl (\i c -> 10*i + wordToInteger (digitToInt c)) 0 cs)
  | otherwise = Nothing


---------------------------------------- IO

instance Functor IO where
  fmap f m = m >>= \x -> pure (f x)

instance Applicative IO where
  pure = pureIO
  fs <*> xs = fs >>= \f -> fmap f xs

instance Monad IO where
  (>>=) = bindIO
  (>>) = bindIO'

instance MonadFail IO where
  fail = failIO

instance Semigroup a => Semigroup (IO a) where
  m <> n = m >>= \x -> n >>= \y -> pure (x <> y)


-------------------------------------------------- RefM

-- restricted IO
type RefM = IO

-- use with {-# noinline #-}
-- only on top level
-- without ad-hoc polimorphysm
topM :: RefM a -> a
topM = unsafePerformIO

instance IsString a => IsString (RefM a) where
  fromString' s = pure (fromString' s)


-------------------------------------------------- Ref

newtype Ref a = MkRef (IORef a)

newRef :: a -> RefM (Ref a)
newRef a = MkRef <$> newIORef a

readRef  :: Ref a -> RefM a
readRef (MkRef r) = readIORef r

writeRef :: Ref a -> a -> RefM ()
writeRef (MkRef r) a = writeIORef r a

modifyRef :: Ref a -> (a -> a) -> RefM ()
modifyRef r f = readRef r >>= writeRef r . f

stateRef :: Ref a -> (a -> (a, b)) -> RefM b
stateRef r f = do
  a_ <- readRef r
  let (a, b) = f a_
  writeRef r a
  pure b


---------------------------------------------

{-# noinline idRef #-}
idRef :: Ref Word
idRef = topRef 0

newId :: RefM Word
newId = stateRef idRef \i -> (i+1, i)


--------------------------------------------------

{-# noinline resetRef #-}
resetRef :: Ref (RefM ())
resetRef = topM (newRef (pure ()))

-- use with {-# noinline #-}
-- only on top level
-- without ad-hoc polimorphysm
topRef :: a -> Ref a
topRef a = topRef_ (pure a)

topRef_ :: RefM a -> Ref a
topRef_ mx = top_ do
  r <- newRef =<< mx
  pure (r, mx >>= writeRef r)

top_ :: RefM (a, RefM ()) -> a
top_ mx = topM do
  (r, reset) <- mx
  () <- modifyRef resetRef \m -> m >> reset
  pure r

reset :: RefM ()
reset = join (readRef resetRef)


-------------------------------------------------- State

newtype State a = MkState (Ref a)

newState :: a -> RefM (State a)
newState a = MkState <$> newRef a

topState :: RefM a -> State a
topState a = MkState (topRef_ a)

runState :: a -> (State a -> RefM b) -> RefM (b, a)
runState a cont = do
  s@(MkState r) <- newState a
  b <- cont s
  a <- readRef r
  pure (b, a)

evalState :: a -> (State a -> RefM b) -> RefM b
evalState s f = fst <$> runState s f

gets :: State a -> (a -> b) -> RefM b
gets (MkState r) f = readRef r <&> f

modify :: State a -> (a -> a) -> RefM ()
modify (MkState r) f = modifyRef r f


----------------------------------------------- Reader

newtype Reader a = MkReader (Ref a)

newReader :: a -> RefM (Reader a)
newReader a = MkReader <$> newRef a

topReader :: RefM a -> Reader a
topReader a = MkReader (topRef_ a)

runReader :: a -> (Reader a -> RefM b) -> RefM b
runReader a cont = newReader a >>= cont

asks :: Reader a -> (a -> b) -> RefM b
asks (MkReader r) f = readRef r <&> f

local :: Reader r -> (r -> r) -> RefM a -> RefM a
local (MkReader st) f m = do
  r <- readRef st
  writeRef st (f r)
  a <- m
  writeRef st r
  pure a
{-
localInv :: Reader r -> (r -> r) -> (r -> r) -> RefM a -> RefM a
localInv (MkReader st) f g m = do
  modifyRef st f
  a <- m
  modifyRef st g
  pure a
-}

----------------------------------------------- Writer

newtype Writer a = MkWriter (Ref a)

newWriter :: Monoid w => RefM (Writer w)
newWriter = MkWriter <$> newRef mempty

listenAll :: (Monoid w) => Writer w -> RefM a -> RefM (a, w)
listenAll (MkWriter st) m = do
  r <- readRef st
  writeRef st mempty
  a <- m
  r2 <- readRef st
  writeRef st r
  pure (a, r2)

runWriter :: (Monoid w) => (Writer w -> RefM a) -> RefM (a, w)
runWriter cont = do
  w <- newWriter
  listenAll w (cont w)

tell :: (Semigroup w) => Writer w -> w -> RefM ()
tell (MkWriter st) x = modify (MkState st) (x <>)


----------------------------------------------- Except

data Except e = MkExcept Word

{-# noinline exceptCounter #-}
exceptCounter :: Ref Word
exceptCounter = topM (newRef 0)    -- TODO: reset for local newExcept calls

newExcept :: RefM (Except e)
newExcept = MkExcept <$> (stateRef exceptCounter \i -> (i+1, i))

throwError :: (HasCallStack, Print e) => Except e -> e -> RefM a
throwError (MkExcept p) e
  = print e >>= \s -> throwIO' p e ("\n" <> showSource s)

catchError :: Except e -> (e -> RefM a) -> RefM a -> RefM a
catchError (MkExcept p) f ~g = catch' p f g

runExcept :: (Except e -> RefM a) -> RefM (Either e a)
runExcept f = do
  e <- newExcept
  catchError e (pure . Left) (Right <$> f e)


----------------------------------------------- ANSI String

stripANSI :: String -> String
stripANSI = f
 where
  f = \case
    '\ESC':. '[':. cs -> f (skip cs)
    c:. cs -> c:. f cs
    Nil -> Nil

  skip = drop 1 . dropWhile (\c -> isDigit c || c `elem` [';','?'])

lengthANSI :: String -> Word
lengthANSI = length . stripANSI

csi :: (IsString a, Monoid a) => List Word -> a -> a
csi args code = "\ESC[" <> mconcat (intersperse ";" (map (fromString' . showInt) args)) <> code

clearScreen = csi [2] "J"
setCursorHPosition n = csi [n + 1] "G"
setCursorPosition n m = csi [n + 1, m + 1] "H"
cursorUp      n = csi [n] "A"
cursorDown    n = csi [n] "B"
cursorForward n = csi [n] "C"
cursorBack    n = csi [n] "D"

hideCursor = csi Nil "?25l"
showCursor = csi Nil "?25h"

sgr args = csi args "m"
background_ n = sgr [n + 40]
foreground_ n = sgr [n + 30]
normal = 9  -- color

invert s = sgr [7] <> s <> sgr [27]
background n s = background_ n <> s <> background_ normal

foreground :: (IsString s, Monoid s) => Word -> s -> s
foreground n s = foreground_ n <> s <> foreground_ normal

black = 0
red = 1
green = 2
yellow = 3
blue = 4
magenta = 5
cyan = 6
white = 7

pattern SGR is s = CSI is 'm' s

fixANSI = f [0] [0] where
  f (_:. a:. as) bs (SGR [39] cs) = SGR [a] (f (a:. as) bs cs)
  f as (_:. b:. bs) (SGR [49] cs) = SGR [b] (f as (b:. bs) cs)
  f as bs (SGR [i] cs)
    | 30 <= i, i <= 37 = SGR [i] (f (i:. as) bs cs)
    | 40 <= i, i <= 47 = SGR [i] (f as (i:. bs) cs)
  f as bs (c:. cs) = c:. f as bs cs
  f _  _  Nil = Nil

getCSI ('\ESC':. '[':. cs) = f "" Nil cs
 where
  f i is (c:. cs) = case c of
    ';'           -> f "" (i:. is) cs
    c | isDigit c -> f (c:. i) is cs
    c             -> Just (reverse (map (readInt . reverse) (i:. is)), c, cs)
  f _ _ _ = Nothing
getCSI _ = Nothing

pattern CSI :: List Word -> Char -> String -> String
pattern CSI is c cs <- (getCSI -> Just (is, c, cs))
  where CSI is c cs =  "\ESC[" ++ mconcat (intersperse ";" (map showInt is)) ++ c:. cs


----------------------------------------------- Source

data Handler = MkHandler {fileId :: Word, fileName :: String}

instance Eq  Handler where (==) = (==) `on` fileId
instance Ord Handler where compare = compare `on` fileId

mkHandler :: FilePath -> RefM Handler
mkHandler s = do
  i <- newId
  pure (MkHandler i s)

source :: (Parse a) => String -> String -> RefM a
source n s = do
  p <- mkHandler n
  parse (source_ (Just p) s)

type Vec = CharArray

lengthVec :: Vec -> Word
lengthVec = numElements

indexVec :: Vec -> Word -> Char
indexVec = unsafeAt


data CharCtx = MkCtx (Maybe Handler) Vec

instance Eq CharCtx where
  MkCtx (Just h) _ == MkCtx (Just h') _ = h == h'
  _ == _ = False

data Source
  = NilS
  | ConsS {-# UNPACK #-} Word {-# UNPACK #-} Word CharCtx Source

instance Semigroup Source where
  NilS <> s = s
  ConsS a b c s <> s' = consS a b c (s <> s')

consS a b c (ConsS a' b' c' s)
  | b == a', c == c' = ConsS a b' c s
consS a b c s = ConsS a b c s

instance Monoid Source where
  mempty = NilS

reverseS = f NilS where
  f acc NilS = acc
  f acc (ConsS a b c s) = f (ConsS a b c acc) s

meld :: Source -> Source
meld s = f (len s) s  where

  len NilS = 0 :: Word
  len (ConsS _ _ _ s) = 1 + len s

  drop 0 s = s
  drop i (ConsS _ _ _ s) = drop (i-.1) s
  drop _ _ = impossible

  f 0 _ = NilS
  f 1 (ConsS _ _ (MkCtx Nothing _) _) = NilS
  f 1 (ConsS a b c _) = ConsS a b c NilS
  f l s | i <- l `div` 2 = f i s `merge` f (l -. i) (drop i s)

  merge :: Source -> Source -> Source
  merge NilS s = s
  merge s NilS = s
  merge so@(ConsS a b c s) so'@(ConsS a' b' c' s') = case cmp c c' of
    LT -> ConsS a b c (merge s so')
    GT -> ConsS a' b' c' (merge so s')
    EQ
      | b < a' -> ConsS a b c (merge s so')
      | b' < a -> ConsS a' b' c' (merge so s')
      | otherwise -> consS (min a a') (max b b') c (merge s s')

  cmp (MkCtx (Just h) _) (MkCtx (Just h') _) = compare h h'
  cmp _ _ = impossible

{-# INLINE chars #-}
chars :: Source -> String
chars NilS = Nil
chars (ConsS i j (MkCtx _ v) s) = (indexVec v <$> enumFromTo i j) ++ chars s


indexCtx (MkCtx _ v) i = indexVec v i

pattern Cons :: Source -> Source -> Source
pattern Cons c s <- (getCons -> Just (c, s))

pattern Cons' :: Char -> Source -> Source
pattern Cons' c s <- (getCons' -> Just (c, s))

pattern NilCh :: Source
pattern NilCh <- (getNil -> True)

{-# COMPLETE Cons, NilCh #-}
{-# COMPLETE Cons', NilCh #-}

getNil NilS = True
getNil _ = False

getCons (ConsS i j ctx ss)
  | j == i + 1 = Just (ConsS i j ctx NilS, ss)
  | True  = Just (ConsS i (i+1) ctx NilS, ConsS (i+1) j ctx ss)
getCons _ = Nothing

getCons' (ConsS i j ctx ss)
  | j == i + 1 = Just (indexCtx ctx i, ss)
  | True  = Just (indexCtx ctx i, ConsS (i+1) j ctx ss)
getCons' _ = Nothing

spanCh, revSpanCh :: (Char -> Bool) -> Source -> (Source, Source)
spanCh p = spanCh_ \_ -> p
revSpanCh p = revSpanCh_ \_ -> p

splitAtCh :: Word -> Source -> (Source, Source)
splitAtCh n = spanCh_ \i _ -> i < n

takeCh, dropCh, revTakeCh, revDropCh :: Word -> Source -> Source
takeCh n = fst . splitAtCh n
dropCh n = snd . splitAtCh n
revTakeCh n = fst . revSpanCh_ \i _ -> i < n
revDropCh n = snd . revSpanCh_ \i _ -> i < n

groupCh p = groupCh_ \_ -> p

groupCh_ :: (Word -> Char -> Char -> Bool) -> Source -> (Source, Source)
groupCh_ p ss = f' ss
 where
  f' NilS = (NilS, NilS)
  f' (ConsS i j c@(MkCtx _ v) ss) = g (indexVec v i) (i+1)
   where
    g l x
      | x == j, (as, bs) <- f (j -. i) l ss = (ConsS i j c as, bs)
      | l' <- indexVec v x, p (x -. i) l l' = g l' (x+1)
    g _ x = (ConsS i x c NilS, ConsS x j c ss)

  f _ _ NilS = (NilS, NilS)
  f offs l s@(ConsS i j c@(MkCtx _ v) ss) = g l i
   where
    g l x
      | x == j, (as, bs) <- f (offs + j -. i) l ss = (ConsS i j c as, bs)
      | l' <- indexVec v x, p (offs + x -. i) l l' = g l' (x+1)
      | x == i    = (NilS, s)
    g _ x = (ConsS i x c NilS, ConsS x j c ss)

spanCh_ :: (Word -> Char -> Bool) -> Source -> (Source, Source)
spanCh_ p ss = f 0 ss
 where
  f _ NilS = (NilS, NilS)
  f offs s@(ConsS i j c@(MkCtx _ v) ss) = g i
   where
    g x
      | x == j, (as, bs) <- f (offs + j -. i) ss = (ConsS i j c as, bs)
      | p (offs + x -. i) (indexVec v x) = g (x+1)
      | x == i    = (NilS, s)
    g x = (ConsS i x c NilS, ConsS x j c ss)

revSpanCh_ :: (Word -> Char -> Bool) -> Source -> (Source, Source)
revSpanCh_ p ss | (as, bs) <- f 0 (reverseS ss) = (reverseS as, reverseS bs)
 where
  f _ NilS = (NilS, NilS)
  f offs s@(ConsS j i c@(MkCtx _ v) ss) = g i
   where
    g x
      | x == j, (as, bs) <- f (offs + i -. j) ss = (ConsS j i c as, bs)
      | p (offs + i -. x) (indexVec v (x-.1)) = g (x-.1)
      | x == i    = (NilS, s)
    g x = (ConsS x i c NilS, ConsS j x c ss)

--lengthCh = length . chars
lengthCh = f 0 where
   f acc NilS = acc
   f acc (ConsS i j _ s) = f (acc + (j -. i)) s

lastCh   = last   . chars
headCh   = head   . chars

mreplicate n a = mconcat (replicate n a)

showSource s = chars s <> "\n" <> showLoc s

stringToSource = source_ Nothing

instance IsString Source where
  fromString' = stringToSource

source_ :: Maybe Handler -> String -> Source
source_ _ Nil = NilS
source_ n s = let (l, v) = listArray s in ConsS 0 l (MkCtx n v) NilS


guard :: Bool -> List ()
guard True = [()]
guard _ = []

showLoc_ :: Source -> List (String, String)
showLoc_ s = split (meld s)
 where
  split NilS = Nil
  split s@(ConsS _ _ (MkCtx (Just h) v) _) | (as, rest) <- go s = (fileName h, h_ (v, as)):. split rest
   where
    go (ConsS a b (MkCtx (Just h') _) s)
      | h' == h, (is, rest) <- go s = ((a, b):. is, rest)
    go s = (Nil, s)
  split _ = impossible

  h1 (v, is) = ff 0 (is >>= \(i, j) -> enumFromTo i j)
   where
    ff i _ | i == lengthVec v = Nil
    ff i (j :. js) | i == j = (True, indexVec v i):. ff (i+1) js
    ff i js = (False, indexVec v i):. ff (i+1) js

  lines :: List (a, Char) -> List (List (a, Char))
  lines Nil = Nil
  lines (span ((/= '\n') . snd) -> (as, bs)) = as:. case bs of
    Nil -> Nil
    [_] -> Nil:. Nil
    _:. bs -> lines bs

  groupOn :: Eq b => List (b, c) -> List (b, List c)
  groupOn = map (\as -> (fst (head as), map snd as)) . groupBy ((==) `on` fst)

  h_ = hh
    . map groupOn
    . lines
    . h1

  hh :: List (List (Bool, String)) -> String
  hh ss = (intercalate "\n" . map h2 . groupOn . zip (widen 1 mask)) s2
   where
    s2 :: List String
    s2 = numberWith gb 1 ss
    mask = map ga ss

  widen i bs = (take (length bs) . map (or . take (2*i + 1)) . tails) (replicate i False <> bs)

  h2 (True, s) = intercalate "\n" s
  h2 (False, _) = foreground green "..."

  ga Nil = False
  ga [(False, _)] = False
  ga _ = True

  gb :: Word -> List (Bool, String) -> String
  gb n s = foreground green (showInt n <> " | ") <> concat (map g s)  where
    g (True, s) = background blue s
    g (_, s) = s

showLoc :: Source -> String
showLoc s = intercalate "\n" (showLoc_ s <&> \(f, x) -> invert (foreground green $ " " <> f <> " ") <> "\n" <> x)


------------------------------------------------

importFile :: Parse a => Source -> RefM a
importFile f = do
  d <- getDataDir
  s <- readFile (d <> "/" <> chars f <> ".csip")
  source (chars f) s


-----------------------------------------------

class Print a where
  print :: a -> RefM Source

instance Print Source where
  print = pure

instance Print String where
  print = pure . stringToSource
{-
instance Print Int where
  print = print . show
-}
instance Print Word where
  print = print . showInt

instance Print Void where
  print = impossible

-----------------------------------------------

class Parse a where
  parse :: Source -> RefM a

instance Parse Source where
  parse = pure

instance Parse String where
  parse = pure . chars



----------------------------------------------- main exception

data MainException
  = MkMainException Source
  | MkTag (RefM Source) MainException

instance Print MainException where
  print = \case
    MkMainException s -> pure s
    MkTag _ r@MkTag{} -> print r
    MkTag s r -> s >>= \s -> print r <&> \r -> stringToSource (showSource r <> showLoc s)

{-# noinline mainException #-}
mainException :: Except MainException
mainException = topM newExcept

errorM_ :: HasCallStack => Bool -> Source -> RefM a
errorM_ cs s = throwError mainException (MkMainException (if cs then s <> "\n" <> stringToSource callStack else s))

errorM :: HasCallStack => Source -> RefM a
errorM = errorM_ False

error' :: HasCallStack => IO Source -> a
error' s = unsafePerformIO (s >>= errorM_ False)

error :: HasCallStack => Source -> a
error s = error' (pure s)

undefined :: HasCallStack => a
undefined = unsafePerformIO (errorM_ True "TODO")

impossible :: HasCallStack => a
impossible = unsafePerformIO (errorM_ True "impossible")

assert :: HasCallStack => Bool -> a -> a
-- assert False = error "assertion failed"
assert ~_ = id

assertM :: HasCallStack => Bool -> RefM ()
-- assertM False = errorM "assertion failed"
assertM ~_ = pure ()

tag :: Print s => s -> RefM a -> RefM a
tag s = catchError mainException (throwError mainException . MkTag (print s))

traceShow :: String -> RefM String -> RefM ()
--traceShow ~s m {- | s `elem` ["1","2","3","4","5","6","7"] -} = m >>= \s -> traceM s
traceShow ~_ ~_ = pure ()



