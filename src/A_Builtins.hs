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
andWord = (P..&.)
orWord  = (P..|.)
addWord = (P.+)
mulWord = (P.*)
subWord = (P.-)
divWord = P.div
modWord = P.mod

shiftRWord, shiftLWord :: Word -> Int -> Word
shiftRWord = P.shiftR
shiftLWord = P.shiftL


-------------------------------------------------- Int

type Int = P.Int

intToWord :: Int -> Word
intToWord = P.fromIntegral

wordToInt :: Word -> Int
wordToInt = P.fromIntegral

andInt, orInt, addInt, mulInt, subInt :: Int -> Int -> Int
addInt = (P.+)
mulInt = (P.*)
subInt = (P.-)
andInt = (P..&.)
orInt = (P..|.)

shiftRInt, shiftLInt :: Int -> Int -> Int
shiftRInt = P.shiftR
shiftLInt = P.shiftL


-------------------------------------------------- Char

type Char = P.Char

charToWord :: Char -> Word
charToWord c = intToWord (P.ord c)

wordToChar :: Word -> Char
wordToChar w = P.chr (wordToInt w)


-------------------------------------------------- Integer

type Integer = P.Integer

integerToInt :: Integer -> Int
integerToInt = P.fromIntegral

wordToInteger :: Word -> Integer
wordToInteger = P.fromIntegral

integerToWord :: Integer -> Word
integerToWord = P.fromIntegral

andInteger, orInteger, addInteger, mulInteger, subInteger, divInteger, modInteger :: Integer -> Integer -> Integer
andInteger = (P..&.)
orInteger = (P..|.)
addInteger = (P.+)
mulInteger = (P.*)
subInteger = (P.-)
divInteger = P.div
modInteger = P.mod

shiftRInteger, shiftLInteger :: Integer -> Int -> Integer
shiftRInteger = P.shiftR
shiftLInteger = P.shiftL


-------------------------------------------------- Bool

type Bool = P.Bool

pattern False = P.False
pattern True = P.True

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

data List a = Nil | Cons a ~(List a)
  deriving (P.Eq, P.Ord, P.Show)

fl :: [a] -> List a
fl (a: ~as) = Cons a (fl as)
fl _ = Nil

tl :: List a -> [a]
tl (Cons a ~as) = a: tl as
tl Nil = []  where
  fromListN _ x = x


-------------------------------------------------- String

type String = P.UArray Word Char

unsafeAt :: String -> Word -> Char
unsafeAt v i = P.unsafeAt v (wordToInt i)

numElements :: String -> Word
numElements v = intToWord (P.numElements v)

nullString :: String
nullString = P.unsafeCoerce (P.listArray (0, P.negate 1) [] :: P.UArray Int Char)
 where
  fromInteger = P.fromInteger
  fromListN _ x = x

listToString :: List Char -> String
listToString Nil = nullString
listToString (tl -> es) = P.listArray (0, intToWord (P.length es P.- 1)) es
 where
  fromInteger = P.fromInteger

stringToList :: String -> List Char
stringToList s = go 0 (numElements s) where
  fromInteger = P.fromInteger

  go i j | i P.== j = Nil
  go i j = Cons (unsafeAt s i) (go (i P.+ 1) j)

fromPreludeString :: P.String -> String
fromPreludeString s = listToString (fl s)

toPreludeString :: String -> P.String
toPreludeString s = tl (stringToList s)


-------------------------------------------------- IO

type IO = P.IO

pureIO :: a -> IO a
pureIO = P.pure

bindIO :: IO a -> (a -> IO b) -> IO b
bindIO = (P.>>=)

bindIO' :: IO a -> IO b -> IO b
bindIO' = (P.>>)

failIO :: String -> IO a
failIO s = P.fail (toPreludeString s)

finally :: IO a -> IO b -> IO a
finally = P.finally

unsafePerformIO :: IO a -> a
unsafePerformIO = P.unsafePerformIO


-------------------------------------------------- IORef

type IORef = P.IORef

newIORef :: a -> IO (IORef a)
newIORef = P.newIORef

readIORef :: IORef a -> IO a
readIORef = P.readIORef

writeIORef :: IORef a -> a -> IO ()
writeIORef = P.writeIORef


-------------------------------------------------- IOArray

type IOArray = P.IOArray Word

unsafeNewArray_ :: Word -> IO (IOArray e)
unsafeNewArray_ s = P.unsafeNewArray_ (0, s P.- 1)   -- TODO: s /= 0
 where
  fromInteger = P.fromInteger

unsafeRead :: IOArray e -> Word -> IO e
unsafeRead ar i = P.unsafeRead ar (wordToInt i)

unsafeWrite :: IOArray e -> Word -> e -> IO ()
unsafeWrite ar i e = P.unsafeWrite ar (wordToInt i) e


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
versionBranch = fl (P.map intToWord (P.versionBranch P.version))

getArgs :: IO (List String)
getArgs = P.fmap (fl P.. P.fmap fromPreludeString) P.getArgs

die :: String -> IO a
die s = P.die (toPreludeString s)


-------------------------------------------------- terminal I/O

getChar :: IO Char
getChar = P.getChar

putChar :: Char -> IO ()
putChar = P.putChar


-------------------------------------------------- terminal I/O

type Handle = P.Handle

stdin, stdout :: Handle
stdin = P.stdin
stdout = P.stdout

hReady :: Handle -> IO Bool
hReady = P.hReady

hIsTerminalDevice :: Handle -> IO Bool
hIsTerminalDevice = P.hIsTerminalDevice

hFlush :: Handle -> IO ()
hFlush = P.hFlush

hSetEcho :: Handle -> Bool -> IO ()
hSetEcho = P.hSetEcho

type BufferMode = P.BufferMode

noBuffering, lineBuffering :: BufferMode
noBuffering = P.NoBuffering
lineBuffering = P.LineBuffering

hSetBuffering :: Handle -> BufferMode -> IO ()
hSetBuffering = P.hSetBuffering


-------------------------------------------------- file I/O

type FilePath = String

readFile :: FilePath -> IO String
readFile f = P.fmap fromPreludeString (P.readFile (toPreludeString f))

writeFile :: FilePath -> String -> IO ()
writeFile f s = P.writeFile (toPreludeString f) (toPreludeString s)

doesFileExist, doesDirectoryExist :: FilePath -> IO Bool
doesFileExist f = P.doesFileExist (toPreludeString f)
doesDirectoryExist f = P.doesDirectoryExist (toPreludeString f)

getTemporaryDirectory, getDataDir :: IO FilePath
getTemporaryDirectory = P.fmap fromPreludeString P.getTemporaryDirectory
getDataDir = P.fmap fromPreludeString P.getDataDir

getDataFileName :: FilePath -> IO FilePath
getDataFileName f = P.fmap fromPreludeString (P.getDataFileName (toPreludeString f))

createDirectoryIfMissing :: Bool -> FilePath -> IO ()
createDirectoryIfMissing b f = P.createDirectoryIfMissing b (toPreludeString f)

removeDirectoryRecursive :: FilePath -> IO ()
removeDirectoryRecursive f = P.removeDirectoryRecursive (toPreludeString f)

listDirectory :: FilePath -> IO (List FilePath)
listDirectory f = P.fmap (fl P.. P.fmap fromPreludeString) (P.listDirectory (toPreludeString f))


-------------------------------------------------- misc

coerce = P.coerce

