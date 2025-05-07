module B_Prelude
  ( on, ($), (.), const, flip, id

  , Semigroup, (<>), (<<>>)
  , Monoid, mempty, mconcat, mreplicate

  , Functor, fmap, (<$>), (<&>)
  , pure, (<*>)

  , Monad, when, (>>=), (>>), join, (>=>), (<=<), (=<<), forM, forM_, foldM
  , MonadFail, fail

  , Bool, pattern True, pattern False, otherwise, (&&), (||), not, ifThenElse

  , Char, ord, chr, digitToInt
  , isUpper, isLower, isDigit, isGraphic, isAlphaNum

  , List (Nil, (:.))
  , head, tail
  , nub, init, last, (!!), (++), drop, dropWhile, take, takeWhile, filter
  , map, replicate, reverse, span, splitAt, zip, zipWith, unzip, groupBy
  , intercalate, intersperse, stripPrefix, tails

  , Maybe (Just, Nothing), maybe, fromMaybe, maybeToList, listToMaybe, isJust, isNothing
  , fromJust, firstJust

  , Void
  , Either (Left, Right), either

  , Eq, (==), (/=)
  , Ordering, pattern LT, pattern EQ, pattern GT, Ord, compare, (<=), (>=), (<), (>), max, min

  , Int, showInt, showInteger, readInt, readNat
  , Word, Integer, wordToInteger, integerToWord, intToWord, wordToInt
  , Word128, wordToWord128, word128ToWord
  , enumFromTo, numberWith

  , Num ((+), (*), fromInteger)
  , Minus ((-))
  , Diff ((-.))
  , Natural (div, mod)
  , Bits (shiftR, shiftL, (.&.), (.|.)), even

  , Tup0 (T0), Tup2 (T2), Tup3 (T3), Tup4 (T4), Tup5 (T5)
  , fst, snd, uncurry
  , (***), first, second

  , foldMap, foldr, foldl, foldl1, null, length, elem, maximum, minimum, sum, all, and, any, or
  , concat, concatMap, mapM_, sequence, mapM
  , condCons, guard, lookupList

  , Interval (MkInterval), mkInterval
  , Cached (MkCached, getCached)         -- newtype with trivial Eq, Ord instances

  , String (NilStr, ConsStr, ConsChar)
  , mkString, mkLocString, appendLoc, charStr, lengthStr, stringToList, stripSuffix
  , splitAtStr, revSplitAtStr, spanStr, revSpanStr, takeStr, revTakeStr, dropStr, revDropStr
  , nullStr, tailStr, initStr, replicateStr, groupStr, lastStr, headStr
  , unlines, lines, words

  , Print (print)
  , Parse (parse)
  , IsString (fromString'), fromString

  , Color, black, red, green, yellow, blue, magenta, cyan, white
  , invertColors, background, foreground
  , lengthANSI, fixANSI

  , IntHash (intHash)

  , RefM, Ref, newRef, readRef, writeRef, modifyRef, stateRef
  , top_  -- TODO: rename
  , topM, topRef, reset

  -- monad transformer alternatives
  , State,  runState,  evalState, gets, modify, topState
  , Reader, runReader, asks, local, localInv, topReader
  , Writer, runWriter, tell
  , Except, runExcept, throwError, catchError

  , newId

  , mainException, tagError
  , impossible, undefined, error, errorM
  , traceShow

  , coerce

  , HasCallStack

  ) where

import Prelude (Eq, (==), Ord, compare, otherwise)

import A_Builtins hiding (Cons, String, FilePath, stringToList, listToString)
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

foldMap f = foldr (\a b -> f a <> b) mempty


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

(>>) :: Monad m => m a -> m b -> m b
a >> b = a >>= \_ -> b

f =<< m = m >>= f

mapM _ Nil = pure Nil
mapM f (x :. xs) = f x >>= \x -> mapM f xs <&> (:.) x

mapM_ _ Nil = pure T0
mapM_ f (x :. xs) = f x >> mapM_ f xs

sequence Nil = pure Nil
sequence (x :. xs) = x >>= \x -> sequence xs <&> (:.) x
{-
sequence_ Nil = pure T0
sequence_ (x :. xs) = x >> sequence_ xs
-}

forM  a b = mapM  b a

forM_ a b = mapM_ b a

f >=> g = \x -> f x >>= g

a <=< b = b >=> a

foldM :: Monad m => (b -> a -> m b) -> b -> List a -> m b
foldM f a l = foldl (\a b -> a >>= \a -> f a b) (pure a) l

join m = m >>= \x -> x

when :: Applicative m => Bool -> m Tup0 -> m Tup0
when False ~_ = pure T0
when _      m = m


class Monad m => MonadFail m where
  fail :: String -> m a


---------------------------------------- Functions

id = \x -> x

const x = \ ~_ -> x

flip f = \x y -> f y x

f . g = \x -> f (g x)

f $ ~x = f x

on f g = \x y -> f (g x) (g y)

instance Semigroup a => Semigroup (b -> a) where
  (f <> g) x = f x <> g x

instance Monoid a => Monoid (b -> a) where
  mempty _ = mempty

instance Functor ((->) a) where
  fmap f g x = f (g x)

instance Applicative ((->) a) where
  pure x _ = x
  (f <*> g) x = f x (g x)


---------------------------------------- List

pattern (:.) :: a -> List a -> List a
pattern x :. xs = B.Cons x xs

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

tails Nil = Nil :. Nil
tails ys@(_ :. xs) = ys :. tails xs

singleton x = x :. Nil

intersperse :: a -> List a -> List a
intersperse _ Nil = Nil
intersperse _ xs@(_ :. Nil) = xs
intersperse x (a :. as) = a :. x :. intersperse x as

intercalate :: List a -> List (List a) -> List a
intercalate xs xss = concat (intersperse xs xss)

init (_ :. Nil) = Nil
init (x :. xs) = x :. init xs
init _ = impossible

last (x :. Nil) = x
last (_ :. xs) = last xs
last _ = impossible

reverse = f Nil where
  f acc Nil = acc
  f acc (x :. xs) = f (x :. acc) xs


foldr _ n Nil = n
foldr f n (a :. b) = f a (foldr f n b)

foldl _ n Nil = n
foldl f n (a :. b) = foldl f (f n a) b

foldl1 f (x :. xs) = foldl f x xs
foldl1 _ _ = impossible

(x :. xs) ++ ys = x :. (xs ++ ys)
Nil       ++ ys = ys

concat = foldr (++) Nil

map _ Nil = Nil
map f (x :. xs) = f x :. map f xs

concatMap _ Nil = Nil
concatMap f (a :. b) = f a ++ concatMap f b

numberWith :: (Word -> a -> b) -> Word -> List a -> List b
numberWith _ _ Nil = Nil
numberWith f i (x :. xs) = f i x :. numberWith f (i+1) xs


mreplicate n a = mconcat (replicate n a)

guard :: Bool -> List Tup0
guard True = T0 :. Nil
guard _ = Nil

everyNth _ Nil = Nil
everyNth i as = take i as :. everyNth i (drop i as)

mapHead _ _ Nil = Nil
mapHead f g (a :. as) = f a :. map g as

revSplitAt n xs = splitAt (length xs -. n) xs


------------------------------------------------ Void

data Void

instance Eq  Void where (==) = impossible
instance Ord Void where compare = impossible


---------------------------------------- Tuples

instance Semigroup Tup0 where
  _ <> _ = T0

instance Monoid Tup0 where
  mempty = T0


data Tup2 a b = T2 a b
  deriving (Eq, Ord)

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

{-
data Bool = False | True
-}

ifThenElse True a ~_ = a
ifThenElse _    ~_ b = b

not True = False
not False = True

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

a /= b = not (a == b)


condCons False ~_ bs =      bs
condCons _      a bs = a :. bs

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
{-
nubBy _ Nil = Nil
nubBy f (x:. xs) = x:. nub (filter (\y -> f x /= f y) xs)
-}

lookupList _ Nil = Nothing
lookupList a (T2 b c :. _) | a == b = Just c
lookupList a (_ :. bs) = lookupList a bs

elem _ Nil = False
elem a (b :. _) | a == b = True
elem a (_ :. bs) = elem a bs

stripPrefix :: Eq a => List a -> List a -> Maybe (List a)
stripPrefix Nil xs = Just xs
stripPrefix (a :. as) (b :. bs) | a == b = stripPrefix as bs
stripPrefix _ _ = Nothing


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
maybe a ~_ _ = a

firstJust :: Maybe a -> Maybe a -> Maybe a
firstJust Nothing x = x
firstJust x ~_ = x

instance Semigroup a => Semigroup (Maybe a) where
  Nothing <> a       = a
  a       <> Nothing = a
  Just a  <> Just b  = Just (a <> b)

instance Semigroup a => Monoid (Maybe a) where
  mempty = Nothing

instance Functor Maybe where
  fmap _ Nothing  = Nothing
  fmap f (Just a) = Just (f a)

instance Applicative Maybe where
  pure = Just
  fs <*> xs = fs >>= \f -> fmap f xs

instance Monad Maybe where
  Nothing >>= _ = Nothing
  Just a  >>= f = f a


---------------------------------------- Either

data Either a b = Left a | Right b
  deriving (Eq, Ord)

either f g e = case e of
  Left  a -> f a
  Right b -> g b


---------------------------------------- Char

ord = charToWord

chr = wordToChar

digitToInt c = ord c -. ord '0'

isSpace, isUpper, isLower, isDigit, isGraphic, isAlphaNum :: Char -> Bool

isSpace ' '  = True
isSpace '\n' = True
isSpace _    = False

isUpper c = 'A' <= c && c <= 'Z'
isLower c = 'a' <= c && c <= 'z'
isDigit c = '0' <= c && c <= '9'

isGraphic c = c `elem`
  ( '!' :. '#' :. '$' :. '%' :. '&' :. '*' :. '+'
   :. '-' :. '.' :. '/' :. ':' :. '<' :. '=' :. '>' :. '?' :. '@'
   :. '\\' :. '^' :. '|' :. '~' :. Nil)

isAlphaNum c
  = isLower c || isUpper c || isDigit c || c == '_' || c == '\''


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
take 0 _   = Nil
take _ Nil = Nil
take i (x :. xs) = x :. take (i-.1) xs

drop :: Word -> List a -> List a
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

(!!) :: List a -> Word -> a
(x :. _)  !! 0 = x
(_ :. xs) !! i = xs !! (i-.1)
_         !! _ = impossible


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

instance IntHash String where
  intHash = intHash . stringToList


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

instance Natural Integer where
  div = divInteger
  mod = modInteger


---------------------------------------- IO

instance Functor IO where
  fmap f m = m >>= \x -> pure (f x)

instance Applicative IO where
  pure = pureIO
  fs <*> xs = fs >>= \f -> fmap f xs

instance Monad IO where
  (>>=) = bindIO

instance MonadFail IO where
  fail s = failIO (fromString' s)

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

writeRef :: Ref a -> a -> RefM Tup0
writeRef (MkRef r) a = writeIORef r a

modifyRef :: Ref a -> (a -> a) -> RefM Tup0
modifyRef r f = readRef r >>= writeRef r . f

stateRef :: Ref a -> (a -> Tup2 a b) -> RefM b
stateRef r f = do
  a_ <- readRef r
  let T2 a b = f a_
  writeRef r a
  pure b


---------------------------------------------

{-# noinline idRef #-}
idRef :: Ref Word
idRef = topRef 0

newId :: RefM Word
newId = stateRef idRef \i -> T2 (i+1) i


--------------------------------------------------

{-# noinline resetRef #-}
resetRef :: Ref (RefM Tup0)
resetRef = topM (newRef (pure T0))

-- use with {-# noinline #-}
-- only on top level
-- without ad-hoc polimorphysm
topRef :: a -> Ref a
topRef a = topRef_ (pure a)

topRef_ :: RefM a -> Ref a
topRef_ mx = top_ do
  r <- newRef =<< mx
  pure (T2 r (mx >>= writeRef r))

top_ :: RefM (Tup2 a (RefM Tup0)) -> a
top_ mx = topM do
  T2 r reset <- mx
  T0 <- modifyRef resetRef \m -> m >> reset
  pure r

reset :: RefM Tup0
reset = join (readRef resetRef)


-------------------------------------------------- State

newtype State a = MkState (Ref a)

newState :: a -> RefM (State a)
newState a = MkState <$> newRef a

topState :: RefM a -> State a
topState a = MkState (topRef_ a)

runState :: a -> (State a -> RefM b) -> RefM (Tup2 b a)
runState a cont = do
  s@(MkState r) <- newState a
  b <- cont s
  a <- readRef r
  pure (T2 b a)

evalState :: a -> (State a -> RefM b) -> RefM b
evalState s f = fst <$> runState s f

gets :: State a -> (a -> b) -> RefM b
gets (MkState r) f = readRef r <&> f

modify :: State a -> (a -> a) -> RefM Tup0
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

localInv :: Reader r -> (r -> r) -> (r -> r) -> RefM a -> RefM a
localInv (MkReader st) f g m = do
  modifyRef st f
  a <- m
  modifyRef st g
  pure a


----------------------------------------------- Writer

newtype Writer a = MkWriter (Ref a)

newWriter :: Monoid w => RefM (Writer w)
newWriter = MkWriter <$> newRef mempty
{-
listenAll :: (Monoid w) => Writer w -> RefM a -> RefM (Tup2 a w)
listenAll (MkWriter st) m = do
  r <- readRef st
  writeRef st mempty
  a <- m
  r2 <- readRef st
  writeRef st r
  pure (T2 a r2)
-}
runWriter :: (Monoid w) => (Writer w -> RefM a) -> RefM (Tup2 a w)
runWriter cont = do
  w@(MkWriter st) <- newWriter
  a <- cont w
  r <- readRef st
  pure (T2 a r)

tell :: (Semigroup w) => Writer w -> w -> RefM Tup0
tell (MkWriter st) x = modify (MkState st) (x <>)


----------------------------------------------- Except

data Except e = MkExcept Word

{-# noinline exceptCounter #-}
exceptCounter :: Ref Word
exceptCounter = topM (newRef 0)    -- TODO: reset for local newExcept calls

newExcept :: RefM (Except e)
newExcept = MkExcept <$> (stateRef exceptCounter \i -> T2 (i+1) i)

throwError :: Except e -> e -> RefM a
throwError (MkExcept p) e = throwIO' p e

catchError :: Except e -> (e -> RefM a) -> RefM a -> RefM a
catchError (MkExcept p) f ~g = catch' p f g

runExcept :: (Except e -> RefM a) -> RefM (Either e a)
runExcept f = do
  e <- newExcept
  catchError e (pure . Left) (Right <$> f e)


---------------------------------------- String

stringToList :: String -> List Char
stringToList s = go s  where
  go NilS = Nil
  go (ConsS i j c s) = (indexCtx c <$> enumFromTo i j) ++ go s

instance Eq String where
  (==) = (==) `on` stringToList

instance Ord String where
  compare = compare `on` stringToList

replicateStr :: Word -> Char -> String
replicateStr n c = mreplicate n $ charStr c

charsStr :: B.String
charsStr = B.listToString $ map wordToChar $ enumFromTo 0 128

charStr :: Char -> String
charStr (charToWord -> i) | i < 128 = ConsS i (i+1) (MkCtx Nothing charsStr) NilS
charStr c = mkString $ B.listToString (c :. Nil)

showInt :: Word -> String
showInt i | i == 0 = charStr '0'
showInt i = g mempty (div i 10) (mod i 10)
 where
  g acc 0 0 = acc
  g acc q r = g (charStr (chr (48 + r)) <> acc) (div q 10) (mod q 10)

showInteger :: Integer -> String
showInteger i | i == 0 = charStr '0'
showInteger i = g mempty (div i 10) (mod i 10)
 where
  g acc 0 0 = acc
  g acc q r = g (charStr (chr $ 48 + integerToWord r) <> acc) (div q 10) (mod q 10)

readInt :: String -> Word
readInt (stringToList -> ('0' :. Nil)) = 0
readInt (stringToList -> cs) = f 0 cs where
  f acc Nil = acc
  f acc (c :. cs) = f (10 * acc + ord c -. 48) cs

readNat :: String -> Maybe Integer
readNat (stringToList -> cs)
  | all isDigit cs = Just (foldl (\i c -> 10*i + wordToInteger (digitToInt c)) 0 cs)
  | otherwise = Nothing

unlines :: List String -> String
unlines xs = mconcat (map (<> "\n") xs)

words :: String -> List String
words (spanStr isSpace -> T2 _ bs) = g bs where
  g NilStr = Nil
  g (spanStr (not . isSpace) -> T2 as bs) = as :. words bs

lines :: String -> List String
lines (spanStr (/= '\n') -> T2 as xs) = as :. h xs  where
  h (ConsChar '\n' xs) = lines xs
  h _ = Nil

stripSuffix a b
  | T2 b1 b2 <- revSplitAtStr (lengthStr a) b
  , a == b2
  = Just b1
  | otherwise = Nothing


class IsString a where
  fromString' :: String -> a

fromString :: IsString a => [Char] -> a
fromString cs = fromString' (mkString $ fromPreludeString cs)

instance IsString String where
  fromString' s = s

instance IsString B.String where
  fromString' (stringToList -> s) = B.listToString s

instance IsString [Char] where
  fromString' (stringToList -> s) = toList s

instance IsString (List Char) where
  fromString' (stringToList -> s) = s



----------------------------------------------- String

type FilePath = String

data Handler = MkHandler {fileId :: Word, fileName :: FilePath}

instance Eq  Handler where (==) = (==) `on` fileId
instance Ord Handler where compare = compare `on` fileId

mkLocString_ :: Maybe Handler -> B.String -> String
mkLocString_ _ v | lengthString v == 0 = NilS
mkLocString_ n v = ConsS 0 (lengthString v) (MkCtx n v) NilS

mkString :: B.String -> String
mkString s = mkLocString_ Nothing s

mkHandler :: FilePath -> RefM Handler
mkHandler s = do
  i <- newId
  pure (MkHandler i s)

mkLocString :: (Parse a) => FilePath -> B.String -> RefM a
mkLocString n s = do
  p <- mkHandler n
  parse (mkLocString_ (Just p) s)


data CharCtx = MkCtx (Maybe Handler) B.String

instance Eq CharCtx where
  MkCtx (Just h) _ == MkCtx (Just h') _ = h == h'
  _ == _ = False

data String
  = NilS
  | ConsS {-# UNPACK #-} Word {-# UNPACK #-} Word CharCtx String

instance Semigroup String where
  NilS <> s = s
  ConsS a b c s <> s' = consS a b c (s <> s')

consS a b c (ConsS a' b' c' s)
  | b == a', c == c' = ConsS a b' c s
consS a b c s = ConsS a b c s

instance Monoid String where
  mempty = NilS

stripSource :: String -> String
stripSource NilS = NilS
stripSource (ConsS a b (MkCtx _ v) s) = ConsS a b (MkCtx Nothing v) (stripSource s)


indexCtx (MkCtx _ v) i = unsafeAt v i

pattern NilStr :: String
pattern NilStr <- (getNil -> True)

pattern ConsStr :: String -> String -> String
pattern ConsStr c s <- (getConsStr -> Just (T2 c s))

pattern ConsChar :: Char -> String -> String
pattern ConsChar c s <- (getConsChar -> Just (T2 c s))

{-# COMPLETE ConsStr,  NilStr #-}
{-# COMPLETE ConsChar, NilStr #-}

getNil NilS = True
getNil _ = False

getConsStr (ConsS i j ctx ss)
  | j == i + 1 = Just (T2 (ConsS i j ctx NilS) ss)
  | True  = Just (T2 (ConsS i (i+1) ctx NilS) (ConsS (i+1) j ctx ss))
getConsStr _ = Nothing

getConsChar (ConsS i j ctx ss)
  | j == i + 1 = Just (T2 (indexCtx ctx i) ss)
  | True  = Just (T2 (indexCtx ctx i) (ConsS (i+1) j ctx ss))
getConsChar _ = Nothing

spanStr, revSpanStr :: (Char -> Bool) -> String -> Tup2 String String
spanStr p = spanCh_ \_ -> p
revSpanStr p = revSpanCh_ \_ -> p

splitAtStr, revSplitAtStr :: Word -> String -> Tup2 String String
takeStr, dropStr, revTakeStr, revDropStr :: Word -> String -> String

splitAtStr n = spanCh_ \i _ -> i < n
takeStr n = fst . splitAtStr n
dropStr n = snd . splitAtStr n

revSplitAtStr n = revSpanCh_ \i _ -> i < n
revTakeStr n = snd . revSplitAtStr n
revDropStr n = fst . revSplitAtStr n

groupStr p = groupCh_ \_ -> p

groupCh_ :: (Word -> Char -> Char -> Bool) -> String -> Tup2 String String
groupCh_ p ss = f' ss
 where
  f' NilS = T2 NilS NilS
  f' (ConsS i j c ss) = g (indexCtx c i) (i+1)
   where
    g l x
      | x == j, T2 as bs <- f (j -. i) l ss = T2 (ConsS i j c as) bs
      | l' <- indexCtx c x, p (x -. i) l l' = g l' (x+1)
    g _ x = T2 (ConsS i x c NilS) (ConsS x j c ss)

  f _ _ NilS = T2 NilS NilS
  f offs l s@(ConsS i j c ss) = g l i
   where
    g l x
      | x == j, T2 as bs <- f (offs + j -. i) l ss = T2 (ConsS i j c as) bs
      | l' <- indexCtx c x, p (offs + x -. i) l l' = g l' (x+1)
      | x == i    = T2 NilS s
    g _ x = T2 (ConsS i x c NilS) (ConsS x j c ss)

spanCh_ :: (Word -> Char -> Bool) -> String -> Tup2 String String
spanCh_ p ss = f 0 ss
 where
  f _ NilS = T2 NilS NilS
  f offs s@(ConsS i j c ss) = g i
   where
    g x
      | x == j, T2 as bs <- f (offs + j -. i) ss = T2 (ConsS i j c as) bs
      | p (offs + x -. i) (indexCtx c x) = g (x+1)
      | x == i    = T2 NilS s
    g x = T2 (ConsS i x c NilS) (ConsS x j c ss)

reverseS = f NilS where
  f acc NilS = acc
  f acc (ConsS a b c s) = f (ConsS a b c acc) s

revSpanCh_ :: (Word -> Char -> Bool) -> String -> Tup2 String String
revSpanCh_ p ss | T2 as bs <- f 0 (reverseS ss) = T2 (reverseS bs) (reverseS as)
 where
  f _ NilS = T2 NilS NilS
  f offs s@(ConsS j i c ss) = g i
   where
    g x
      | x == j, T2 as bs <- f (offs + i -. j) ss = T2 (ConsS j i c as) bs
      | p (offs + i -. x) (indexCtx c (x-.1)) = g (x-.1)
      | x == i    = T2 NilS s
    g x = T2 (ConsS x i c NilS) (ConsS j x c ss)

lengthStr = f 0 where
   f acc NilS = acc
   f acc (ConsS i j _ s) = f (acc + (j -. i)) s

nullStr NilS = True
nullStr _ = False

headStr (ConsChar c _) = c
headStr _ = impossible

tailStr (ConsChar _ s) = s
tailStr _ = impossible

-- TODO: optimize
lastStr s = case snd (revSplitAtStr 1 s) of
  ConsChar c _ -> c
  _ -> impossible

initStr NilStr = impossible
initStr s = fst (revSplitAtStr 1 s)

appendLoc s = stripSource s <> "\n" <> showLoc s


meld :: String -> String
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

  merge :: String -> String -> String
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


showLoc :: String -> String
showLoc s = splitFiles (meld s)
 where
  splitFiles NilS = mempty
  splitFiles s@(ConsS _ _ (MkCtx (Just h) v) _)
    = matchT2 (splitFile h s) \is rest -> title (fileName h) <> hh v is <> splitFiles rest
  splitFiles _ = impossible

  splitFile h (ConsS a b (MkCtx (Just h') _) s)
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
  number (T2 n s) = foreground green (showInt n <> " | ") <> s
  dots = foreground green "..."
  highlight s = background blue s
  highlightLine (T2 i s) = number (T2 i (highlight s))
  nl = "\n"

  unlines' = mconcat . intersperse nl


----------------------------------------------- Colored String

data Color = MkColor Word

black   = MkColor 0
red     = MkColor 1
green   = MkColor 2
yellow  = MkColor 3
blue    = MkColor 4
magenta = MkColor 5
cyan    = MkColor 6
white   = MkColor 7

endsgr i s = sgr i <> s <> sgr (MkColor 1)
 where
  sgr (MkColor a) = "\ESC" <> charStr (wordToChar a)

invertColors = endsgr (MkColor 7)
foreground (MkColor n) = endsgr (MkColor $ n + 30)
background (MkColor n) = endsgr (MkColor $ n + 40)

lengthANSI :: String -> Word
lengthANSI s = f 0 $ stringToList s
 where
  f acc = \case
    '\ESC' :. _ :. cs -> f acc cs
    _ :. cs -> f (acc + 1) cs
    Nil -> acc

fixANSI :: String -> String
fixANSI cs = f (T2 0 (T3 39 49 False) :. Nil) cs
 where
  f as@(T2 a (T3 x y z) :. bs) (ConsChar '\ESC' (ConsChar (charToWord -> i) cs))
    | i == 1           = sgr a (f bs cs)
    | i == 7           = sgr i (f (T2 (if z then 7 else 27) (T3 x y (not z)):. as) cs)
    | 30 <= i, i <= 37 = sgr i (f (T2 x (T3 i y z):. as) cs)
    | 40 <= i, i <= 47 = sgr i (f (T2 y (T3 x i z):. as) cs)
  f _  NilStr = mempty
  f as (spanStr (/= '\ESC') -> T2 bs cs) = bs <> f as cs

  sgr a b = "\ESC[" <> showInt a <> "m" <> b


-----------------------------------------------

class Print a where
  print :: a -> RefM String

instance Print String where
  print = pure

instance Print Word where
  print = print . showInt

instance Print Void where
  print = impossible


-----------------------------------------------

class Parse a where
  parse :: String -> RefM a

instance Parse String where
  parse = pure


----------------------------------------------- main exception

data MainException
  = MkMainException (RefM String)
  | MkTag (RefM String) MainException

instance Print MainException where
  print = \case
    MkMainException s -> s
    MkTag _ r@MkTag{} -> print r
    MkTag s r -> s >>= \s -> print r <&> \r -> (stripSource r <> "\n" <> showLoc s)

{-# noinline mainException #-}
mainException :: Except MainException
mainException = topM newExcept

errorM_ :: HasCallStack => Bool -> RefM String -> RefM a
errorM_ cs ~s = throwError mainException (MkMainException (if cs then s <<>> "\n" <<>> pure (mkString callStack) else s))

errorM :: HasCallStack => RefM String -> RefM a
errorM = errorM_ False

error :: HasCallStack => RefM String -> a
error ~s = unsafePerformIO (errorM_ False s)

undefined :: HasCallStack => a
undefined = unsafePerformIO (errorM_ True "TODO")

impossible :: HasCallStack => a
impossible = unsafePerformIO (errorM_ True "impossible")
{-
assert :: HasCallStack => Bool -> a -> a
-- assert False = error "assertion failed"
assert ~_ = id

assertM :: HasCallStack => Bool -> RefM Tup0
-- assertM False = errorM "assertion failed"
assertM ~_ = pure T0
-}
tagError :: Print s => s -> RefM a -> RefM a
tagError ~s = catchError mainException (throwError mainException . MkTag (print s))

traceShow :: String -> RefM String -> RefM Tup0
--traceShow ~s m  | s `elem` [{-"56", "57"-} "1","2","3","4","5","6","7"] = m >>= \s -> mapM_ putChar (stringToList s) >> putChar '\n'
traceShow ~_ ~_ = pure T0



