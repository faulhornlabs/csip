{-# language MagicHash, UnboxedTuples #-}
module B0_Builtins
  ( Word, andWord, orWord, addWord, mulWord, subWord, divWord, modWord, shiftRWord, shiftLWord
  , addWordCarry, mulWordCarry, eqWord, ltWord
  , CharArray, readCharArray, lengthCharArray
  , RefM, pureRefM, bindRefM, unsafePerformRefM
  , throwRefM, catchRefM
  , Ref, newRef, readRef, writeRef
  , Array, newArray, readArray, writeArray
  , Prog (..), runProg, readFileRaw, getDataDirRaw
  , HasCallStack, callStackRaw

  , Tup0 (T0)
  , Lazy, lazy, force
  , Char, charToWord
  , Bool (True, False)
  , integerToWord
  , PreludeList, nilPrelude, consPrelude, foldrPrelude
  , PreludeString, fromPreludeString
  , coerce
  ) where

import Prelude
import Data.Coerce
import Control.Exception
import System.Exit
import System.Environment
import System.IO
import System.IO.Error
import qualified GHC.Base as P (lazy)
import GHC.Base hiding (lazy)
import GHC.Num
import GHC.Stack
import Unsafe.Coerce
import Paths_csip

--import Data.Typeable
--import GHC.TypeLits


-------------------------------------------------- Tup0

data Tup0 = T0


-------------------------------------------------- laziness

data Lazy a = MkLazy (Tup0 -> a)

lazy :: a -> Lazy a
lazy ~a = MkLazy \_ -> a

force :: Lazy a -> a
force (MkLazy f) = f T0


--------------------------------------------------

type PreludeList a = [a]

nilPrelude = []
consPrelude a b = a: b

foldrPrelude :: (a -> b -> b) -> b -> PreludeList a -> b
foldrPrelude c n (a: as) = c a (foldrPrelude c n as)
foldrPrelude _ n [] = n

type PreludeString = [Char]

fromString s = s


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


-------------------------------------------------- Char

charToWord :: Char -> Word
charToWord (C# c#) = W# (int2Word# (ord# c#))


-------------------------------------------------- CharArray

data CharArray = MkCharArray ByteArray#

readCharArray :: CharArray -> Word -> Char
readCharArray (MkCharArray v#) (W# w#) = C# (indexWideCharArray# v# (word2Int# w#))

lengthCharArray :: CharArray -> Word
lengthCharArray (MkCharArray v#) = W# (uncheckedShiftRL# (int2Word# (sizeofByteArray# v#)) 2#)

emptyCharArray :: CharArray
emptyCharArray = runRW#
  \s# -> case newByteArray# 0# s# of
    (# s#, marr# #) -> case unsafeFreezeByteArray# marr# s# of
      (# _, arr# #) -> MkCharArray arr#

fromPreludeString :: PreludeString -> CharArray
fromPreludeString [] = emptyCharArray
fromPreludeString cs = runRW#
  \s# -> case length cs of
    I# l# -> case newByteArray# (l# *# 4#) s# of
      (# s#, marr# #) -> let
          go (C# c# : cs) i# s# = go cs (i# +# 1#) (writeWideCharArray# marr# i# c# s#)
          go [] _ s# = case unsafeFreezeByteArray# marr# s# of
            (# _, arr# #) -> MkCharArray arr#
        in go cs 0# s#


-------------------------------------------------- RefM

data RefM a = MkRefM (State# RealWorld -> (# State# RealWorld, a #))

unRefM (MkRefM f) = f

refMToIO (MkRefM f) = IO f
ioToRefM (IO f) = MkRefM f

pureRefM :: a -> RefM a
pureRefM a = MkRefM \s -> (# s, a #)

bindRefM :: RefM a -> (a -> RefM b) -> RefM b
bindRefM (MkRefM a) f = MkRefM \s -> case a s of (# s, b #) -> unRefM (f b) s

unsafePerformRefM :: RefM a -> a
unsafePerformRefM (MkRefM m) = case runRW# m of (# _, a #) -> P.lazy a


-------------------------------------------------- Ref

data Ref a = MkRef (MutVar# RealWorld a)

newRef :: a -> RefM (Ref a)
newRef a = MkRefM \s# -> case newMutVar# a s# of
  (# s#, arr# #) -> (# s#, MkRef arr# #)

readRef :: Ref a -> RefM a
readRef (MkRef arr#) = MkRefM \s# -> readMutVar# arr# s#

writeRef :: Ref a -> a -> RefM Tup0
writeRef (MkRef arr#) e = MkRefM \s# -> (# writeMutVar# arr# e s#, T0 #)


-------------------------------------------------- Array

data Array a = MkArray (MutableArray# RealWorld a)

newArray :: Word -> e -> RefM (Array e)
newArray (W# n#) def = MkRefM \s# -> case newArray# (word2Int# n#) def s# of
  (# s#, arr# #) -> (# s#, MkArray arr# #)

readArray :: Array e -> Word -> RefM e
readArray (MkArray arr#) (W# i#) = MkRefM \s# -> readArray# arr# (word2Int# i#) s#

writeArray :: Array e -> Word -> e -> RefM Tup0
writeArray (MkArray arr#) (W# i#) e = MkRefM \s# -> (# writeArray# arr# (word2Int# i#) e s#, T0 #)


-------------------------------------------------- exceptions
{-
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

catchRefM :: Word -> (e -> RefM a) -> Lazy (RefM a) -> RefM a
catchRefM w f g = case someNatVal (fromIntegral w) of
  Just (SomeNat p) -> catch (force g >>= \a -> pure a) (fun p f)
  _ -> undefined
 where
  fun :: Proxy i -> (e -> RefM a) -> GException i -> RefM a
  fun _ f (MkGException x) = f (unsafeCoerce x)
-}
data Exception = MkException Word Any

throwRefM :: Word -> e -> RefM a
throwRefM w e = MkRefM \s# -> raiseIO# (MkException w (unsafeCoerce e)) s#

catchRefM :: Word -> (e -> RefM a) -> Lazy (RefM a) -> RefM a
catchRefM w f g = MkRefM \s# -> catch# io handler s#  where
  io s# = case (bindRefM (force g) \a -> pureRefM a) of MkRefM f -> f s#
  handler e@(MkException w' c)
    | w' == w = unRefM (f (unsafeCoerce c))
    | True    = raiseIO# e



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

  | PutStr PreludeString (Lazy Prog)
  | GetChar (Char -> Prog)
  | PresentationMode (Lazy Prog) (Lazy Prog)
  | GetTerminalSize (Lazy Prog) (Word -> Word -> Prog)

  | ReadFile PreludeString (Lazy Prog) (PreludeString -> Prog)
  | WriteFile PreludeString PreludeString (Lazy Prog)
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

  go :: Prog -> IO Tup0
  go = \case

    ProgEnd   -> pure T0
    Die s     -> die s
    GetArgs f -> getArgs >>= go . f

    GetChar f  -> getChar >>= go . f
    PutStr s m -> putStr' s >> go (force m)

    ReadFile f fail cont -> tryIOError (openFile f ReadMode >>= hGetContents) >>= \case
      Left _  -> go (force fail)
      Right s -> go (cont s)
 
    WriteFile f s c -> do
      writeFile f s
      go (force c)

    Do m f -> refMToIO m >>= go . f

    GetTemporaryDir cont -> do
      t <- lookupEnv "TMPDIR"
      go $ cont $ maybe "/tmp" id t

    PresentationMode m c -> do
      -- hide cursor, turn on bracketed paste mode, enable alternative screen buffer, turn line wrap off
      putStr "\ESC[?25l\ESC[?2004h\ESC[?1049h\ESC[?7l"
      hSetEcho stdin False
      go (force m) `finally` do
        hSetEcho stdin True
        putStr "\ESC[?7h\ESC[?1049l\ESC[?2004l\ESC[?25h"
        go (force c)

    GetTerminalSize def ret -> hIsTerminalDevice stdout >>= \case
      False -> go (force def)
      True -> do
        putStr' "\ESC7\ESC[10000;10000H" -- save cursor, set cursor position
        r <- try 3
        putStr' "\ESC8" -- restore cursor
        go r
     where
      try :: Int -> IO Prog
      try 0 = pure (force def)
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

    CatchError w fail m ok -> do
      r <- refMToIO $ newRef $ unsafeCoerce False
      let cont x = Do (writeRef r $ unsafeCoerce x) \_ -> ProgEnd
      _ <- refMToIO $ catchRefM w (\e -> ioToRefM $ go $ fail e cont) (lazy (ioToRefM $ go $ m cont))
      x <- refMToIO $ readRef r
      go $ ok $ unsafeCoerce x


-------------------------------------------------- I/O in RefM

readFileRaw :: PreludeString -> RefM PreludeString
readFileRaw f = ioToRefM (readFile f)

getDataDirRaw :: RefM PreludeString
getDataDirRaw = ioToRefM getDataDir
