{-# language UnboxedTuples, ForeignFunctionInterface #-}
module B0_Builtins
  ( Word, andWord, orWord, addWord, mulWord, subWord, div, mod, shiftR, shiftL
  , addWordCarry, mulWordCarry, eqWord, ltWord
  , CharArray, readCharArray, lengthCharArray
  , Mem, pureMem, bindMem, unsafePerformMem
  , throwMem, catchMem
  , Ref, newRef, readRef, writeRef
  , Array, newArray_, newArray, readArray, writeArray
  , Prog (..), runProg, putStrMem

  , Tup0 (T0)
  , Lazy, lazy, force
  , Char, ord
  , Bool (True, False)
  , integerToWord
  , nilPrelude, consPrelude, foldrPrelude
  , PreludeString, fromPreludeString
  , coerce
  , Addr#, addrToCharArray
  ) where

import Prelude hiding (mapM, div, mod)
import Control.Exception
import Data.Coerce
import System.Exit (exitFailure)
import Foreign hiding (newArray, shiftL, shiftR)
--import Foreign.Ptr
import Foreign.C.Types
import Foreign.C.String
import qualified GHC.Base as P (lazy)
import GHC.Base hiding (lazy, ord)
import GHC.Num (integerToWord)
--import GHC.Storable
import GHC.Exts (Ptr (..))
import Unsafe.Coerce


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

andWord, orWord, addWord, mulWord, subWord, div, mod, shiftR, shiftL :: Word -> Word -> Word
andWord    (W# a) (W# b) = W# (and#       a b)
orWord     (W# a) (W# b) = W# (or#        a b)
addWord    (W# a) (W# b) = W# (plusWord#  a b)
mulWord    (W# a) (W# b) = W# (timesWord# a b)
subWord    (W# a) (W# b) = W# (minusWord# a b)
div        (W# a) (W# b) = W# (quotWord#  a b)
mod        (W# a) (W# b) = W# (remWord#   a b)
shiftR     (W# a) (W# b) = W# (uncheckedShiftRL# a (word2Int# b))
shiftL     (W# a) (W# b) = W# (uncheckedShiftL#  a (word2Int# b))

addWordCarry :: Word -> Word -> (Word -> Word -> a) -> a
addWordCarry (W# a) (W# b) cont = case plusWord2# a b of
  (# a, b #) -> cont (W# a) (W# b)

mulWordCarry :: Word -> Word -> (Word -> Word -> a) -> a
mulWordCarry (W# a) (W# b) cont = case timesWord2# a b of
  (# a, b #) -> cont (W# a) (W# b)


-------------------------------------------------- Char

ord :: Char -> Word
ord (C# c) = W# (int2Word# (ord# c))


-------------------------------------------------- CharArray

data CharArray = MkCharArray ByteArray#

readCharArray :: CharArray -> Word -> Char
readCharArray (MkCharArray v) (W# w) = C# (indexCharArray# v (word2Int# w))

lengthCharArray :: CharArray -> Word
lengthCharArray (MkCharArray v) = W# (int2Word# (sizeofByteArray# v))

runRW :: (State# RealWorld -> (# State# RealWorld, a #)) -> a
runRW f = case runRW# f of
  (# _, a #) -> a

{-# noinline emptyCharArray #-}
emptyCharArray :: CharArray
emptyCharArray = runRW
  \s -> case newByteArray# 0# s of
    (# s, marr #) -> case unsafeFreezeByteArray# marr s of
      (# s, arr #) -> (# s, MkCharArray arr #)

fromPreludeString :: PreludeString -> CharArray
fromPreludeString [] = emptyCharArray
fromPreludeString cs = runRW
  \s -> case length cs of
    I# l -> case newByteArray# l s of
      (# s, marr #) -> let
          go (C# c : cs) i s = go cs (i +# 1#) (writeCharArray# marr i c s)
          go [] _ s = case unsafeFreezeByteArray# marr s of
            (# s, arr #) -> (# s, MkCharArray arr #)
        in go cs 0# s

lengthCString (Ptr adr) = IO \s -> let
    go i s = case readInt8OffAddr# adr i s of
      (# s, w #)
        | isTrue# (int8ToInt# w ==# 0#) -> (# s, I# i #)
        | True -> go (i +# 1#) s
  in go 0# s

peekCStringLen' :: CStringLen -> IO CharArray
peekCStringLen' (Ptr adr, I# l) = IO
  \s -> case newByteArray# l s of
    (# s, marr #) -> let
        go i s | isTrue# (i ==# l) = case unsafeFreezeByteArray# marr s of
          (# s, arr #) -> (# s, MkCharArray arr #)
        go i s = case readWord8OffAddr# adr i s of
          (# s, w #) -> go (i +# 1#) (writeCharArray# marr i (chr# (word2Int# (word8ToWord# w))) s)
      in go 0# s

peekCString' :: CString -> IO CharArray
peekCString' cs = do
  l <- lengthCString cs
  peekCStringLen' (cs, l)

addrToCharArray :: Addr# -> Mem CharArray
addrToCharArray adr = ioToMem $ peekCString' (Ptr adr)


-------------------------------------------------- Mem

data Mem a = MkMem (State# RealWorld -> (# State# RealWorld, a #))

unMem (MkMem f) = f

memToIO (MkMem f) = IO f
ioToMem (IO f) = MkMem f

pureMem :: a -> Mem a
pureMem a = MkMem \s -> (# s, a #)

bindMem :: Mem a -> (a -> Mem b) -> Mem b
bindMem (MkMem a) f = MkMem \s -> case a s of (# s, b #) -> unMem (f b) s

unsafePerformMem :: Mem a -> a
unsafePerformMem (MkMem m) = case runRW# m of (# _, a #) -> P.lazy a


-------------------------------------------------- Ref

data Ref a = MkRef (MutVar# RealWorld a)

newRef :: a -> Mem (Ref a)
newRef a = MkMem \s -> case newMutVar# a s of
  (# s, arr #) -> (# s, MkRef arr #)

readRef :: Ref a -> Mem a
readRef (MkRef arr) = MkMem \s -> readMutVar# arr s

writeRef :: Ref a -> a -> Mem Tup0
writeRef (MkRef arr) e = MkMem \s -> (# writeMutVar# arr e s, T0 #)


-------------------------------------------------- Array

data Array a = MkArray (MutableArray# RealWorld a)

newArray :: Word -> e -> Mem (Array e)
newArray (W# n#) def = MkMem \s -> case newArray# (word2Int# n#) def s of
  (# s, arr #) -> (# s, MkArray arr #)

newArray_ :: Word -> Mem (Array e)
newArray_ w = bindMem (newArray w (unsafeCoerce () :: Any)) (pureMem . unsafeCoerce)

readArray :: Array e -> Word -> Mem e
readArray (MkArray arr) (W# i) = MkMem \s -> readArray# arr (word2Int# i) s

writeArray :: Array e -> Word -> e -> Mem Tup0
writeArray (MkArray arr) (W# i) e = MkMem \s -> (# writeArray# arr (word2Int# i) e s, T0 #)

-------------------------------------------------- exceptions

{- does not work with -O2

data Exception = MkException Word Any

throwMem :: Word -> e -> Mem a
throwMem w e = MkMem \s -> raiseIO# (MkException w (unsafeCoerce e)) s

catchMem :: Word -> (e -> Mem a) -> Lazy (Mem a) -> Mem a
catchMem w f g = MkMem \s -> catch# io handler s  where

  io s = case (bindMem (force g) \a -> pureMem a) of MkMem f -> f s

  handler e@(MkException w' c) s
    | w' == w = unMem (f (unsafeCoerce c)) s
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

throwMem :: Word -> e -> Mem a
throwMem w e = ioToMem $ throwIO (MkGException w (unsafeCoerce e))

catchMem :: Word -> (e -> Mem a) -> Lazy (Mem a) -> Mem a
catchMem w f g = ioToMem $ catch (memToIO (force g) >>= \a -> pure a) handler
 where
  handler e@(MkGException w' v)
    | w' == w = memToIO $ f (unsafeCoerce v)
    | True    = throwIO e


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
  | forall a. Do (Mem a) (a -> Prog)
  | forall e a. CatchError Word (e -> (a -> Prog) -> Prog) ((a -> Prog) -> Prog) (a -> Prog)


runProg :: Prog -> IO ()
runProg m = do
  setbuffering
  _ <- go m
  pure ()
 where
  go :: Prog -> IO Tup0
  go = \case

    ProgEnd    -> pure T0
    Die s      -> putStr' s exitFailure
    GetArgs f  -> getArgs >>= go . f
    GetChar f  -> getChar' >>= go . f
    PutStr s m -> putStr' s (go (force m))
    ReadFile f fail cont -> readF f (go (force fail)) \s -> go (cont s)
    WriteFile f s c -> writeF f s (go (force c))
    Do m f     -> memToIO m >>= go . f

    GetTemporaryDir cont -> do
      t <- lookupEnv "TMPDIR"
      tmp <- memToIO $ addrToCharArray "/tmp"#
      go $ cont $ maybe tmp id t

    PresentationMode m c -> do
      setterm
      _ <- go (force m) `finally` resetterm
      go (force c)

    GetTerminalSize def ret -> termSize (go (force def)) \w h -> go (ret w h)

    CatchError w fail m ok -> do
      r <- memToIO $ newRef $ unsafeCoerce False
      let cont x = Do (writeRef r $ unsafeCoerce x) \_ -> ProgEnd
      _ <- memToIO $ catchMem w (\e -> ioToMem $ go $ fail e cont) (lazy (ioToMem $ go $ m cont))
      x <- memToIO $ readRef r
      go $ ok $ unsafeCoerce x


--------------------------------------------------

foreign import ccall unsafe "fopen"                fopen        :: CString -> CString -> IO (Ptr CFile)
foreign import ccall unsafe "fread"                fread        :: CString -> Int -> Int -> Ptr CFile -> IO Int
foreign import ccall unsafe "fwrite"               fwrite       :: CString -> Int -> Int -> Ptr CFile -> IO Int
foreign import ccall unsafe "fseek"                fseek        :: Ptr CFile -> Word -> Word -> IO Int
foreign import ccall unsafe "ftell"                ftell        :: Ptr CFile -> IO Int
foreign import ccall unsafe "getstdout"            stdoutPtr    :: IO (Ptr CFile)
foreign import ccall unsafe "fclose"               fclose       :: Ptr CFile -> IO Int
foreign import ccall unsafe "fflush"               fflush       :: Ptr CFile -> IO Int
foreign import ccall unsafe "getProgArgv"          getProgArgv  :: Ptr CInt -> Ptr (Ptr CString) -> IO ()
foreign import ccall unsafe "getenv"               c_getenv     :: CString -> IO (Ptr CChar)
foreign import ccall unsafe "setbuffering"         setbuffering :: IO ()
foreign import ccall unsafe "getachar"             getChar'     :: IO Char
foreign import ccall unsafe "setterm"              setterm      :: IO ()
foreign import ccall unsafe "resetterm"            resetterm    :: IO ()
foreign import ccall unsafe "termsize"             termsize     :: IO Word

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

termSize err ok = do
  wh <- termsize
  case wh of
    0 -> err
    _ -> ok (shiftR wh 32) (wh .&. 0xffffffff)

readF :: String -> IO a -> (CharArray -> IO a) -> IO a
readF n err ok = do
  fn <- newCString n
  notNull err (fopen fn (Ptr "r"#)) \f -> do
  let err' = fclose f >> err
  notErr err' (fseek f 0 2 {- SEEK_END -}) do
  len <- ftell f
  notErr err' (fseek f 0 0 {- SEEK_SET -}) do
  allocaBytes len $ \s -> do
  len' <- fread s 1 len f
  notErr err (fclose f) do
  guardErr err (len' == len) do
  peekCStringLen' (s, len) >>= ok

writeF :: String -> String -> IO a -> IO a
writeF n s_ ok = do
  fn <- newCString n
  notNull ioerror (fopen fn (Ptr "w"#)) \f -> do
  newCStringLen s_ >>= \(s, len) -> do
  len' <- fwrite s 1 len f
  notErr ioerror (fclose f) do
  guardErr ioerror (len' == len) do
  ok

-- only for debugging
putStrMem :: PreludeString -> Mem Tup0
putStrMem s = ioToMem $ putStr' s (pure T0)

putStr' s_ ok = do
  f <- stdoutPtr
  newCStringLen s_ >>= \(s, len) -> do
  len' <- fwrite s 1 len f
  guardErr ioerror (len' == len) do
  notErr ioerror (fflush f) do
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
