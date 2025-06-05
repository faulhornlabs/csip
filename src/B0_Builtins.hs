{-# language MagicHash, UnboxedTuples, ForeignFunctionInterface #-}
module B0_Builtins
  ( Word, andWord, orWord, addWord, mulWord, subWord, divWord, modWord, shiftRWord, shiftLWord
  , addWordCarry, mulWordCarry, eqWord, ltWord
  , CharArray, readCharArray, lengthCharArray
  , RefM, pureRefM, bindRefM, unsafePerformRefM
  , throwRefM, catchRefM
  , Ref, newRef, readRef, writeRef
  , Array, newArray, readArray, writeArray
  , Prog (..), runProg, readFileRaw, getDataDirRaw, putStrRefM
  , HasCallStack, callStackRaw

  , Tup0 (T0)
  , Lazy, lazy, force
  , Char, charToWord
  , Bool (True, False)
  , integerToWord
  , nilPrelude, consPrelude, foldrPrelude
  , PreludeString, fromPreludeString
  , coerce
  ) where

import Prelude hiding (mapM)
import Control.Exception
import Data.Coerce
import System.Exit (exitFailure)
import Foreign hiding (newArray)
--import Foreign.Ptr
import Foreign.C.Types
import Foreign.C.String
import qualified GHC.Base as P (lazy)
import GHC.Base hiding (lazy)
import GHC.Num (integerToWord)
import GHC.Word
import GHC.Stack
--import GHC.Storable
import GHC.Exts (Ptr (..))
import Unsafe.Coerce
import Paths_csip


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
readCharArray (MkCharArray v#) (W# w#) = C# (indexCharArray# v# (word2Int# w#))

lengthCharArray :: CharArray -> Word
lengthCharArray (MkCharArray v#) = W# (int2Word# (sizeofByteArray# v#))

runRW :: (State# RealWorld -> (# State# RealWorld, a #)) -> a
runRW f = case runRW# f of
  (# _, a #) -> a

{-# noinline emptyCharArray #-}
emptyCharArray :: CharArray
emptyCharArray = runRW
  \s# -> case newByteArray# 0# s# of
    (# s#, marr# #) -> case unsafeFreezeByteArray# marr# s# of
      (# s, arr# #) -> (# s, MkCharArray arr# #)

fromPreludeString :: PreludeString -> CharArray
fromPreludeString [] = emptyCharArray
fromPreludeString cs = runRW
  \s# -> case length cs of
    I# l# -> case newByteArray# l# s# of
      (# s#, marr# #) -> let
          go (C# c# : cs) i# s# = go cs (i# +# 1#) (writeCharArray# marr# i# c# s#)
          go [] _ s# = case unsafeFreezeByteArray# marr# s# of
            (# s, arr# #) -> (# s, MkCharArray arr# #)
        in go cs 0# s#

peekCStringLen' :: CStringLen -> IO CharArray
peekCStringLen' (Ptr adr#, I# l#) = IO
    \s# -> case newByteArray# l# s# of
      (# s#, marr# #) -> let
          go i# s# | isTrue# (i# ==# l#) = case unsafeFreezeByteArray# marr# s# of
            (# s#, arr# #) -> (# s#, MkCharArray arr# #)
          go i# s# = case readWord8OffAddr# adr# i# s# of
            (# s#, w# #) -> go (i# +# 1#) (writeCharArray# marr# i# (chr# (word2Int# (word8ToWord# w#))) s#)
        in go 0# s#

peekCString' :: CString -> IO CharArray
peekCString' cs = do
  l <- lengthCString cs
  peekCStringLen' (cs, l)

lengthCString (Ptr adr#) = IO
    \s# -> let
          go i# s# = case readInt8OffAddr# adr# i# s# of
            (# s#, w# #)
              | isTrue# (int8ToInt# w# ==# 0#) -> (# s#, I# i# #)
              | True -> go (i# +# 1#) s#
        in go 0# s#


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

{- does not work with -O2

data Exception = MkException Word Any

throwRefM :: Word -> e -> RefM a
throwRefM w e = MkRefM \s# -> raiseIO# (MkException w (unsafeCoerce e)) s#

catchRefM :: Word -> (e -> RefM a) -> Lazy (RefM a) -> RefM a
catchRefM w f g = MkRefM \s# -> catch# io handler s#  where

  io s# = case (bindRefM (force g) \a -> pureRefM a) of MkRefM f -> f s#

  handler e@(MkException w' c) s
    | w' == w = unRefM (f (unsafeCoerce c)) s
    | True    = raiseIO# e s

finally :: IO a -> IO b -> IO a
finally (IO io) end = IO \s -> case catch# io handler s of
   (# s, a #) -> case unIO end s of
     (# s, _ #) -> (# s, a #)
 where
  handler e s = case unIO end s of
     (# s, _ #) -> raiseIO# e s

-}

data GException = MkGException Word Any

instance Show GException where show _ = "<<exception>>"

instance Exception GException

throwRefM :: Word -> e -> RefM a
throwRefM w e = ioToRefM $ throwIO (MkGException w (unsafeCoerce e))

catchRefM :: Word -> (e -> RefM a) -> Lazy (RefM a) -> RefM a
catchRefM w f g = ioToRefM $ catch (refMToIO (force g) >>= \a -> pure a) handler
 where
  handler e@(MkGException w' v)
    | w' == w = refMToIO $ f (unsafeCoerce v)
    | True    = throwIO e


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
  | GetArgs (PreludeList CharArray -> Prog)

  | PutStr PreludeString (Lazy Prog)
  | GetChar (Char -> Prog)
  | PresentationMode (Lazy Prog) (Lazy Prog)
  | GetTerminalSize (Lazy Prog) (Word -> Word -> Prog)

  | ReadFile PreludeString (Lazy Prog) (CharArray -> Prog)
  | WriteFile PreludeString PreludeString (Lazy Prog)
  | GetTemporaryDir (CharArray -> Prog)

  | forall a. Do (RefM a) (a -> Prog)

  | forall e a. CatchError Word (e -> (a -> Prog) -> Prog) ((a -> Prog) -> Prog) (a -> Prog)


runProg :: Prog -> IO ()
runProg m = do
  stdin_NoBuffering ioerror do
  stdout_LineBuffering ioerror do
  _ <- go m
  pure ()
 where
  go :: Prog -> IO Tup0
  go = \case

    ProgEnd   -> pure T0
    Die s     -> putStr' s ioerror exitFailure
    GetArgs f -> getArgs >>= go . f

    GetChar f  -> getChar' >>= go . f
    PutStr s m -> putStr' s ioerror (go (force m))

    ReadFile f fail cont -> readF f (go (force fail)) \s -> go (cont s)
 
    WriteFile f s c -> writeF f s ioerror (go (force c))

    Do m f -> refMToIO m >>= go . f

    GetTemporaryDir cont -> do
      t <- lookupEnv "TMPDIR"
      go $ cont $ maybe (fromPreludeString "/tmp") id t

    PresentationMode m c -> do
      -- hide cursor, turn on bracketed paste mode, enable alternative screen buffer, turn line wrap off
      putStr' "\ESC[?25l\ESC[?2004h\ESC[?1049h\ESC[?7l" ioerror do
      setEcho 0{-stdin-} False
      go (force m) `finally` do
        setEcho 0{-stdin-} True
        putStr' "\ESC[?7h\ESC[?1049l\ESC[?2004l\ESC[?25h" ioerror do
        pure ()
      go (force c)

    GetTerminalSize def ret -> termSize (go (force def)) \w h -> go (ret w h)

    CatchError w fail m ok -> do
      r <- refMToIO $ newRef $ unsafeCoerce False
      let cont x = Do (writeRef r $ unsafeCoerce x) \_ -> ProgEnd
      _ <- refMToIO $ catchRefM w (\e -> ioToRefM $ go $ fail e cont) (lazy (ioToRefM $ go $ m cont))
      x <- refMToIO $ readRef r
      go $ ok $ unsafeCoerce x


-------------------------------------------------- I/O in RefM

readFileRaw :: PreludeString -> RefM CharArray
readFileRaw f = ioToRefM (readF f ioerror pure)

getDataDirRaw :: RefM PreludeString
getDataDirRaw = ioToRefM getDataDir

--------------------------------------------------

-- type Addr = Ptr () --MkAddr Addr#

{-
data Addr = MkAddr Addr#

nullAddr :: Addr
nullAddr = MkAddr nullAddr#

instance Storable Addr where
  sizeOf _ = 8
  alignment _ = 8
  peekElemOff a b = readPtrOffPtr (castPtr a) b >>= \(Ptr a) -> pure (MkAddr a)
  pokeElemOff a b (MkAddr x) = writePtrOffPtr (castPtr a) b (Ptr x)
-}
--------------------------------------------------

foreign import ccall unsafe "stdio.h fopen"        fopen     :: CString -> CString -> IO (Ptr CFile)
foreign import ccall unsafe "stdio.h fread"        fread     :: CString -> Int -> Int -> Ptr CFile -> IO Int
foreign import ccall unsafe "stdio.h fwrite"       fwrite    :: CString -> Int -> Int -> Ptr CFile -> IO Int
foreign import ccall unsafe "stdio.h fseek"        fseek     :: Ptr CFile -> Word -> Word -> IO Int
foreign import ccall unsafe "stdio.h ftell"        ftell     :: Ptr CFile -> IO Int
foreign import ccall unsafe "getstdout"            stdoutPtr :: IO (Ptr CFile)
foreign import ccall unsafe "getstdin"             stdinPtr  :: IO (Ptr CFile)
foreign import ccall unsafe "stdio.h fclose"       fclose    :: Ptr CFile -> IO Int
foreign import ccall unsafe "stdio.h fflush"       fflush    :: Ptr CFile -> IO Int
foreign import ccall unsafe "stdio.h getchar"      getChar'  :: IO Char
foreign import ccall unsafe "stdio.h setvbuf"      setvbuf   :: Ptr CFile -> Ptr Word8 -> CInt -> CSize -> IO Int
foreign import ccall unsafe "sys/ioctl.h ioctl"    ioctl     :: Int -> Int -> Ptr Word8 -> IO Int
foreign import ccall unsafe "getProgArgv"          getProgArgv :: Ptr CInt -> Ptr (Ptr CString) -> IO ()
foreign import ccall unsafe "getenv"               c_getenv  :: CString -> IO (Ptr CChar)
foreign import ccall unsafe "termios.h tcgetattr"  tcgetattr :: Int -> Ptr Int32 -> IO Int
foreign import ccall unsafe "termios.h tcsetattr"  tcsetattr :: Int -> Int -> Ptr Int32 -> IO Int
foreign import ccall unsafe "HsBase.h __hscore_sizeof_termios"  sizeof_termios :: Int


--------------------------------------------------

ioerror = exitFailure

guardErr :: IO a -> Bool -> IO a -> IO a
guardErr _ True next = next
guardErr def _ _ = def

notErr :: IO a -> IO Int -> IO a -> IO a
notErr def m next = m >>= \i -> guardErr def (i == 0) next

notNull :: IO a -> IO (Ptr b) -> (Ptr b -> IO a) -> IO a
notNull def m next = m >>= \p -> guardErr def (p /= nullPtr) (next p)

--------------------------------------------------

set True  m x = x .|. m
set False m x = x .&. complement m

type Termios = Int32

with_termios :: IO () -> Int -> (Ptr Termios -> IO ()) -> IO ()
with_termios err fd m = do
  allocaBytes sizeof_termios \ptr -> do
  notErr err (tcgetattr fd ptr) do
  m ptr
  notErr err (tcsetattr fd 0{-TCSANOW-} ptr) do
  pure ()

set_c_lflag :: Ptr Termios -> Int32 -> Bool -> IO ()
set_c_lflag ptr mask b = do
  let c_lflag = plusPtr ptr 12 :: Ptr Int32
  x <- peek c_lflag
  poke c_lflag (set b mask x)

setEcho :: Int -> Bool -> IO ()
setEcho fd b = with_termios ioerror fd \ptr -> set_c_lflag ptr 8{-ECHO-} b

stdin_NoBuffering err ok = do
  -- man termios
  with_termios err 0{-stdin-} \ptr -> do
    set_c_lflag ptr 2{-ICANON-} False
    let p = plusPtr ptr 17{-c_cc-}
    poke (plusPtr p 6{-VMIN-}  :: Ptr Word8) 1
    poke (plusPtr p 5{-VTIME-} :: Ptr Word8) 0
  sin <- stdinPtr
  notErr err (setvbuf sin nullPtr 2{-_IONBF-} 0) do
  ok

stdout_LineBuffering err ok = do
  sout <- stdoutPtr
  notErr err (setvbuf sout nullPtr 1{-_IOLBF-} 10000) do
  ok

termSize err ok = do
  allocaBytes 8 \ptr -> do
  notErr err (ioctl 1{-STDOUT_FILENO-} 0x5413{-TIOCGWINSZ-} ptr) do
  W16# h <- peekByteOff ptr 0
  W16# w <- peekByteOff ptr 2
  ok (W# (word16ToWord# w)) (W# (word16ToWord# h))

readF :: String -> IO a -> (CharArray -> IO a) -> IO a
readF n err ok = do
  fn <- newCString n
  notNull err (fopen fn (Ptr "r"#)) \f -> do
  let err' = fclose f >> err
  notErr  err' (fseek f 0 2 {- SEEK_END -}) do
  len <- ftell f
  notErr err' (fseek f 0 0 {- SEEK_SET -}) do
  allocaBytes len $ \s -> do
  len' <- fread s 1 len f
  notErr err (fclose f) do
  guardErr err (len' == len) do
  peekCStringLen' (s, len) >>= ok

writeF :: String -> String -> IO a -> IO a -> IO a
writeF n s_ err ok = do
  fn <- newCString n
  notNull err (fopen fn (Ptr "w"#)) \f -> do
  -- let err' = fclose f >> err
  newCStringLen s_ >>= \(s, len) -> do
  len' <- fwrite s 1 len f
  notErr err (fclose f) do
  guardErr err (len' == len) do
  ok

putStrRefM :: PreludeString -> RefM Tup0
putStrRefM s = ioToRefM $ putStr' s ioerror (pure T0)

putStr' s_ err ok = do
  f <- stdoutPtr
  newCStringLen s_ >>= \(s, len) -> do
  len' <- fwrite s 1 len f
  guardErr err (len' == len) do
  notErr err (fflush f) do
  ok

getArgs :: IO (PreludeList CharArray)
getArgs =
  alloca \p_argc ->
  alloca \p_argv -> do
  getProgArgv p_argc p_argv
  p    <- fromIntegral <$> peek p_argc
  argv <- peek p_argv
  peekArray (p - 1) (advancePtr argv 1) >>= mapM peekCString'

lookupEnv name =
  withCString name \s -> do
  litstring <- c_getenv s
  case litstring /= nullPtr of
    True -> Just <$> peekCString' litstring
    False -> return Nothing
