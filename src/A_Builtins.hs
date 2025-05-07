module A_Builtins where

import qualified Prelude as P
import qualified Data.Bits as P
import qualified Data.Char as P
import qualified Data.String as P
import qualified Data.IORef as P
import qualified Data.Version as P
import qualified Data.Array.Base as P
import qualified Data.Array.IO as P
import qualified Data.Typeable as P
import qualified Data.Coerce as P
import qualified Control.Exception as P
import qualified System.IO as P
import qualified System.Exit as P
import qualified System.Directory as P
import qualified System.Environment as P
import qualified System.IO.Unsafe as P
import qualified GHC.Base as P
import qualified GHC.Stack as P
import qualified GHC.TypeLits as P
import qualified Unsafe.Coerce as P
import qualified Paths_csip as P


-------------------------------------------------- Word

type Word = P.Word

andWord, orWord, addWord, mulWord, subWord, divWord, modWord :: Word -> Word -> Word
andWord a b = (P..&.) a b
orWord  a b = (P..|.) a b
addWord a b = (P.+) a b
mulWord a b = (P.*) a b
subWord a b = (P.-) a b
divWord a b = P.div a b
modWord a b = P.mod a b

shiftRWord, shiftLWord :: Word -> Int -> Word
shiftRWord a b = P.shiftR a b
shiftLWord a b = P.shiftL a b


-------------------------------------------------- Int

type Int = P.Int

intToWord :: Int -> Word
intToWord a = P.fromIntegral a

wordToInt :: Word -> Int
wordToInt a = P.fromIntegral a

andInt, orInt, addInt, mulInt, subInt :: Int -> Int -> Int
addInt a b = (P.+) a b
mulInt a b = (P.*) a b
subInt a b = (P.-) a b
andInt a b = (P..&.) a b
orInt  a b = (P..|.) a b

shiftRInt, shiftLInt :: Int -> Int -> Int
shiftRInt a b = P.shiftR a b
shiftLInt a b = P.shiftL a b


-------------------------------------------------- Char

type Char = P.Char

charToWord :: Char -> Word
charToWord c = intToWord (P.ord c)

wordToChar :: Word -> Char
wordToChar w = P.chr (wordToInt w)


-------------------------------------------------- Integer

type Integer = P.Integer

integerToInt :: Integer -> Int
integerToInt a = P.fromIntegral a

wordToInteger :: Word -> Integer
wordToInteger a = P.fromIntegral a

integerToWord :: Integer -> Word
integerToWord a = P.fromIntegral a

andInteger, orInteger, addInteger, mulInteger, subInteger, divInteger, modInteger :: Integer -> Integer -> Integer
andInteger a b = (P..&.) a b
orInteger  a b = (P..|.) a b
addInteger a b = (P.+) a b
mulInteger a b = (P.*) a b
subInteger a b = (P.-) a b
divInteger a b = P.div a b
modInteger a b = P.mod a b

shiftRInteger, shiftLInteger :: Integer -> Int -> Integer
shiftRInteger a b = P.shiftR a b
shiftLInteger a b = P.shiftL a b


-------------------------------------------------- Bool

type Bool = P.Bool

pattern False = P.False
pattern True  = P.True

{-# COMPLETE False, True #-}

--type Eq = P.Eq
--(==) = (P.==)


-------------------------------------------------- Ordering

type Ordering = P.Ordering

pattern EQ = P.EQ
pattern LT = P.LT
pattern GT = P.GT

{-# COMPLETE EQ, LT, GT #-}

--type Ord = P.Ord
--compare = P.compare


-------------------------------------------------- List

data List a = Nil | Cons a (List a)
  deriving (P.Eq, P.Ord, P.Show)

fromList :: [a] -> List a
fromList (a: as) = Cons a (fromList as)
fromList _ = Nil

toList :: List a -> [a]
toList (Cons a as) = a: toList as
toList Nil = []


-------------------------------------------------- String

newtype String = MkStr (P.UArray Int Char)
  deriving (P.Eq, P.Ord, P.Show)

unsafeAt :: String -> Word -> Char
unsafeAt (MkStr v) i = P.unsafeAt v (wordToInt i)

lengthString :: String -> Word
lengthString (MkStr v) = intToWord (P.numElements v)

emptyString :: String
emptyString = MkStr (P.listArray (0, P.negate 1) [])
 where
  fromInteger = P.fromInteger

listToString :: List Char -> String
listToString Nil = emptyString
listToString (toList -> es) = MkStr (P.listArray (0, P.length es P.- 1) es)
 where
  fromInteger = P.fromInteger

stringToList :: String -> List Char
stringToList s = go 0 (lengthString s) where
  fromInteger = P.fromInteger

  go i j | i P.== j = Nil
  go i j = Cons (unsafeAt s i) (go (i P.+ 1) j)

fromPreludeString :: P.String -> String
fromPreludeString s = listToString (fromList s)

toPreludeString :: String -> P.String
toPreludeString s = toList (stringToList s)


-------------------------------------------------- Tup0

data Tup0 = T0
  deriving (P.Eq, P.Ord)


-------------------------------------------------- IO

type IO = P.IO

pureIO :: a -> IO a
pureIO a = P.pure a

bindIO :: IO a -> (a -> IO b) -> IO b
bindIO a f = a P.>>= f

failIO :: String -> IO a
failIO s = P.fail (toPreludeString s)

finally :: IO a -> IO b -> IO a
finally a b = P.finally a b

unsafePerformIO :: IO a -> a
unsafePerformIO a = P.unsafePerformIO a

void :: IO a -> IO Tup0
void m = m P.>> P.pure T0


-------------------------------------------------- IORef

type IORef = P.IORef

newIORef :: a -> IO (IORef a)
newIORef a = P.newIORef a

readIORef :: IORef a -> IO a
readIORef r = P.readIORef r

writeIORef :: IORef a -> a -> IO Tup0
writeIORef r a = void (P.writeIORef r a)


-------------------------------------------------- IOArray

type IOArray = P.IOArray Word

-- size /= 0
unsafeNewArray_ :: Word -> IO (IOArray e)
unsafeNewArray_ s = P.unsafeNewArray_ (0, s P.- 1)
 where
  fromInteger = P.fromInteger

unsafeRead :: IOArray e -> Word -> IO e
unsafeRead ar i = P.unsafeRead ar (wordToInt i)

unsafeWrite :: IOArray e -> Word -> e -> IO Tup0
unsafeWrite ar i e = void (P.unsafeWrite ar (wordToInt i) e)


-------------------------------------------------- exceptions

-- internal
data GException (i :: P.Nat) = MkGException P.Any

-- internal
instance P.Show (GException i) where
  show (MkGException _) = "<<exception>>"
    where fromString = P.fromString

-- internal
instance P.KnownNat i => P.Exception (GException i)

-- internal
someNatVal :: Word -> P.SomeNat
someNatVal i = case P.someNatVal (wordToInteger i) of
  P.Just x -> x
  _ -> P.undefined

throwIO' :: Word -> e -> IO a
throwIO' (someNatVal -> P.SomeNat p) e = P.throwIO (mk p e)
 where
  mk :: P.Proxy i -> e -> GException i
  mk _ e = MkGException (P.unsafeCoerce e)

catch' :: Word -> (e -> IO a) -> IO a -> IO a
catch' (someNatVal -> P.SomeNat p) f ~g
  = P.catch (g P.>>= \a -> a `P.seq` P.pure a) (fun p f)
 where
  fun :: P.Proxy i -> (e -> IO a) -> GException i -> IO a
  fun _ f (MkGException x) = f (P.unsafeCoerce x)


-------------------------------------------------- callstack

type HasCallStack = P.HasCallStack

callStack :: HasCallStack => String
callStack = fromPreludeString (printCallStack (P.getCallStack P.callStack))
 where
  fromString = P.fromString
  (<>) = (P.<>)
  printCallStack cs@(_:_) | (name, loc) <- P.last cs
    = "  " <> name <> " called at "
     <> P.srcLocModule loc <> ":" <> P.show (P.srcLocStartLine loc) <> ":" <> P.show (P.srcLocStartCol loc)
  printCallStack _ = "<empty callstack>"


-------------------------------------------------- program I/O

versionBranch :: List Word
versionBranch = fromList (P.map intToWord (P.versionBranch P.version))

getArgs :: IO (List String)
getArgs = P.fmap (fromList P.. P.fmap fromPreludeString) P.getArgs

die :: String -> IO a
die s = P.die (toPreludeString s)


-------------------------------------------------- terminal I/O

getChar :: IO Char
getChar = P.getChar

putChar :: Char -> IO Tup0
putChar c = void (P.putChar c)


-------------------------------------------------- terminal I/O

type Handle = P.Handle

stdin, stdout :: Handle
stdin = P.stdin
stdout = P.stdout

hReady :: Handle -> IO Bool
hReady = P.hReady

hIsTerminalDevice :: Handle -> IO Bool
hIsTerminalDevice = P.hIsTerminalDevice

hFlush :: Handle -> IO Tup0
hFlush h = void (P.hFlush h)

hSetEcho :: Handle -> Bool -> IO Tup0
hSetEcho h b = void (P.hSetEcho h b)

type BufferMode = P.BufferMode

noBuffering, lineBuffering :: BufferMode
noBuffering = P.NoBuffering
lineBuffering = P.LineBuffering

hSetBuffering :: Handle -> BufferMode -> IO Tup0
hSetBuffering h b = void (P.hSetBuffering h b)


-------------------------------------------------- file I/O

type FilePath = String

readFile :: FilePath -> IO String
readFile f = P.fmap fromPreludeString (P.readFile (toPreludeString f))

writeFile :: FilePath -> String -> IO Tup0
writeFile f s = void (P.writeFile (toPreludeString f) (toPreludeString s))

doesFileExist, doesDirectoryExist :: FilePath -> IO Bool
doesFileExist f = P.doesFileExist (toPreludeString f)
doesDirectoryExist f = P.doesDirectoryExist (toPreludeString f)

getTemporaryDirectory, getDataDir :: IO FilePath
getTemporaryDirectory = P.fmap fromPreludeString P.getTemporaryDirectory
getDataDir = P.fmap fromPreludeString P.getDataDir

getDataFileName :: FilePath -> IO FilePath
getDataFileName f = P.fmap fromPreludeString (P.getDataFileName (toPreludeString f))

createDirectoryIfMissing :: Bool -> FilePath -> IO Tup0
createDirectoryIfMissing b f = void (P.createDirectoryIfMissing b (toPreludeString f))

removeDirectoryRecursive :: FilePath -> IO Tup0
removeDirectoryRecursive f = void (P.removeDirectoryRecursive (toPreludeString f))

listDirectory :: FilePath -> IO (List FilePath)
listDirectory f = P.fmap (fromList P.. P.fmap fromPreludeString) (P.listDirectory (toPreludeString f))


-------------------------------------------------- misc

coerce a = P.coerce a

