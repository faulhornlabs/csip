{-# language MagicHash, UnboxedTuples #-}
module B0_Builtins
  ( Word, andWord, orWord, addWord, mulWord, subWord, divWord, modWord, shiftRWord, shiftLWord
  , addWordCarry, mulWordCarry, compareWord
  , CharArray, readCharArray, lengthCharArray
  , Tup0 (T0)
  , RefM, pureRefM, bindRefM, unsafePerformRefM
  , throwRefM, catchRefM
  , Ref, newRef, readRef, writeRef
  , Array, newArray, readArray, writeArray
  , Prog (..), runProg, readFileRaw, getDataDirRaw
  , HasCallStack, callStackRaw, coerce

  , Char, charToWord
  , Bool (True, False)
  , integerToWord
  , PreludeList, nilPrelude, consPrelude, foldrPrelude
  , PreludeString, fromPreludeString
  ) where

import Prelude
import Data.String
import Data.IORef
import Data.Typeable
import Data.Coerce
import Control.Exception
import Control.Monad.ST
import System.Exit
import System.Environment
import System.IO
import System.IO.Error
import System.IO.Unsafe
import GHC.Base hiding (compareWord)
import GHC.Num
import GHC.ST
import GHC.IOArray
import GHC.Stack
import GHC.TypeLits
import Unsafe.Coerce
import Paths_csip


-------------------------------------------------- Word

andWord, orWord, addWord, mulWord, subWord, divWord, modWord, shiftRWord, shiftLWord :: Word -> Word -> Word
andWord    (W# a) (W# b) = W# (and#       a b)
orWord     (W# a) (W# b) = W# (or#        a b)
addWord    (W# a) (W# b) = W# (plusWord#  a b)
mulWord    (W# a) (W# b) = W# (timesWord# a b)
subWord    (W# a) (W# b) = W# (minusWord# a b)
divWord    (W# a) (W# b) = W# (quotWord#  a b)
modWord    (W# a) (W# b) = W# (remWord#   a b)
shiftRWord (W# a) (W# b) = W# (uncheckedShiftRL# a (word2Int# b))
shiftLWord (W# a) (W# b) = W# (uncheckedShiftL#  a (word2Int# b))

addWordCarry :: Word -> Word -> (Word -> Word -> a) -> a
addWordCarry (W# a) (W# b) cont = case plusWord2# a b of
  (# a, b #) -> cont (W# a) (W# b)

mulWordCarry :: Word -> Word -> (Word -> Word -> a) -> a
mulWordCarry (W# a) (W# b) cont = case timesWord2# a b of
  (# a, b #) -> cont (W# a) (W# b)

compareWord :: Word -> Word -> a -> a -> a -> a
compareWord (W# a) (W# b) ~lt ~eq ~gt = case compareWord# a b of LT -> lt; EQ -> eq; GT -> gt

-------------------------------------------------- Char

charToWord :: Char -> Word
charToWord (C# c#) = W# (int2Word# (ord# c#))


--------------------------------------------------

type PreludeList a = [a]

nilPrelude = []
consPrelude a b = a: b

foldrPrelude :: (a -> b -> b) -> b -> PreludeList a -> b
foldrPrelude c n (a: as) = c a (foldrPrelude c n as)
foldrPrelude _ n [] = n

type PreludeString = PreludeList Char


-------------------------------------------------- CharArray

data CharArray = MkCharArray ByteArray#

readCharArray :: CharArray -> Word -> Char
readCharArray (MkCharArray v#) (W# w#) = C# (indexWideCharArray# v# (word2Int# w#))

lengthCharArray :: CharArray -> Word
lengthCharArray (MkCharArray v#) = W# (uncheckedShiftRL# (int2Word# (sizeofByteArray# v#)) 2#)

emptyCharArray :: CharArray
emptyCharArray = runST $
  ST \s# -> case newByteArray# 0# s# of
    (# s#, marr# #) -> case unsafeFreezeByteArray# marr# s# of
      (# s#, arr# #) -> (# s#, MkCharArray arr# #)

fromPreludeString :: PreludeString -> CharArray
fromPreludeString [] = emptyCharArray
fromPreludeString cs = runST $
  ST \s# -> case length cs of
    I# l# -> case newByteArray# (l# *# 4#) s# of
      (# s#, marr# #) -> let
          go (C# c# : cs) i# s# = go cs (i# +# 1#) (writeWideCharArray# marr# i# c# s#)
          go [] _ s# = case unsafeFreezeByteArray# marr# s# of
            (# s#, arr# #) -> (# s#, MkCharArray arr# #)
        in go cs 0# s#


-------------------------------------------------- Tup0

data Tup0 = T0


-------------------------------------------------- RefM

type RefM = IO

pureRefM :: a -> RefM a
pureRefM a = pure a

bindRefM :: RefM a -> (a -> RefM b) -> RefM b
bindRefM a f = a >>= f

unsafePerformRefM :: RefM a -> a
unsafePerformRefM a = unsafePerformIO a


-------------------------------------------------- Ref

type Ref = IORef

newRef :: a -> RefM (Ref a)
newRef a = newIORef a

readRef :: Ref a -> RefM a
readRef r = readIORef r

writeRef :: Ref a -> a -> RefM Tup0
writeRef r a = writeIORef r a >> pure T0


-------------------------------------------------- Array

type Array = IOArray Word

-- size is (input + 1)
newArray :: Word -> e -> RefM (Array e)
newArray s e = newIOArray (0, s) e

readArray :: Array e -> Word -> RefM e
readArray ar i = unsafeReadIOArray ar (fromIntegral i)

writeArray :: Array e -> Word -> e -> RefM Tup0
writeArray ar i e = unsafeWriteIOArray ar (fromIntegral i) e >> pure T0


-------------------------------------------------- exceptions

data GException (i :: Nat) = MkGException Any

instance Show (GException i) where show _ = "<<exception>>"

instance KnownNat i => Exception (GException i)

throwRefM :: Word -> e -> RefM a
throwRefM w e = case someNatVal (fromIntegral w) of
  Just (SomeNat p) -> throwIO (mk p)
  _ -> undefined
 where
  mk :: Proxy i -> GException i
  mk _ = MkGException (unsafeCoerce e)

catchRefM :: Word -> (e -> RefM a) -> RefM a -> RefM a
catchRefM w f ~g = case someNatVal (fromIntegral w) of
  Just (SomeNat p) -> catch (g >>= \a -> pure a) (fun p f)
  _ -> undefined
 where
  fun :: Proxy i -> (e -> RefM a) -> GException i -> RefM a
  fun _ f (MkGException x) = f (unsafeCoerce x)


-------------------------------------------------- callstack

callStackRaw :: HasCallStack => PreludeString
callStackRaw = printCallStack (getCallStack callStack)
 where
  printCallStack cs@(_:_) | (name, loc) <- last cs
    = "  " ++ name ++ " called at "
     ++ srcLocModule loc ++ ":" ++ show (srcLocStartLine loc) ++ ":" ++ show (srcLocStartCol loc)
  printCallStack _ = "<empty callstack>"


-------------------------------------------------- I/O

data Prog
  = ProgEnd
  | Die PreludeString
  | GetArgs (PreludeList PreludeString -> Prog)

  | PutStr PreludeString ~Prog
  | GetChar (Char -> Prog)
  | PresentationMode ~Prog ~Prog
  | GetTerminalSize (Word -> Word -> Prog)

  | ReadFile PreludeString ~Prog (PreludeString -> Prog)
  | WriteFile PreludeString PreludeString ~Prog
  | GetTemporaryDir (PreludeString -> Prog)

  | forall a. Do (RefM a) (a -> Prog)

  | forall e a. CatchError Word (e -> (a -> Prog) -> Prog) ((a -> Prog) -> Prog) (a -> Prog)


runProg :: Prog -> IO ()
runProg m = do
  hSetBuffering stdin  NoBuffering
  hSetBuffering stdout LineBuffering
  _ <- go m
  pure ()
 where
  putStr' s = putStr s >> hFlush stdout

  go :: Prog -> RefM Tup0
  go = \case

    ProgEnd   -> pure T0
    Die s     -> die s
    GetArgs f -> getArgs >>= go . f

    GetChar f  -> getChar >>= go . f
    PutStr s m -> putStr' s >> go m

    ReadFile f fail cont -> tryIOError (readFileRaw f) >>= \case
      Left _  -> go fail
      Right s -> go (cont s)
 
    WriteFile f s c -> do
      writeFile f s
      go c

    Do m f -> m >>= go . f

    GetTemporaryDir cont -> do
      t <- lookupEnv "TMPDIR"
      go $ cont $ maybe "/tmp" id t

    PresentationMode m c -> do
      -- hide cursor, turn on bracketed paste mode, enable alternative screen buffer, turn line wrap off
      putStr "\ESC[?25l\ESC[?2004h\ESC[?1049h\ESC[?7l"
      hSetEcho stdin False
      go m `finally` do
        hSetEcho stdin True
        putStr "\ESC[?7h\ESC[?1049l\ESC[?2004l\ESC[?25h"
        go c

    GetTerminalSize ret -> hIsTerminalDevice stdout >>= \case
      False -> go def
      True -> do
        putStr' "\ESC7\ESC[10000;10000H" -- save cursor, set cursor position
        r <- try 3
        putStr' "\ESC8" -- restore cursor
        go r
     where
      try :: Int -> IO Prog
      try 0 = pure def
      try i = do
        clearStdin
        putStr' "\ESC[6n"
        skip '\ESC' $ skip '[' $ getInt 0 ';' \as -> getInt 0 'R' \bs -> pure (ret bs as)
       where
        clearStdin = hReady stdin >>= \case
          True  -> getChar >> clearStdin
          False -> pure ()

        skip c m = getChar >>= \c' -> case c' == c of True -> m; False -> try (i - 1)

        getInt acc end cont = getChar >>= \case
          c | c == end  -> cont acc
          c | '0' <= c, c <= '9' -> getInt (10 * acc + (charToWord c - 48)) end cont
          _ -> try (i - 1)

      ~def = ret 119 31

    CatchError w fail m ok -> do
      r <- newIORef $ unsafeCoerce False
      let cont x = Do (writeIORef r $ unsafeCoerce x) \_ -> ProgEnd
      _ <- catchRefM w (\e -> go $ fail e cont) (go $ m cont)
      x <- readIORef r
      go $ ok $ unsafeCoerce x


-------------------------------------------------- I/O in RefM

readFileRaw :: PreludeString -> RefM PreludeString
readFileRaw f = readFile f

getDataDirRaw :: RefM PreludeString
getDataDirRaw = getDataDir
