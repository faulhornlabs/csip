module B3_Mem
  ( Mem

  , Ref, newRef, readRef, writeRef, modifyRef, stateRef

  -- monad transformer alternatives
  , State,  runState,  evalState, gets, modify, topState
  , Reader, runReader, asks, local, localInv, topReader
  , Writer, runWriter, tell, topWriter
  , Except (..), runExcept, throwError, catchError, newExcept

  , Print (print)
  , newString

  , topMem
  , Reset, reset, topMemReset, topRef_, topRef

  , MonadFail (fail)
  , error, impossible, undefined
  , traceShow
  , MainException, mainException, tagError
  ) where

import B0_Builtins
import B1_Basic
import B2_String


-------------------------------------------------- Mem

instance Functor Mem where
  (<$>) f m = m >>= \x -> pure (f x)

instance Monad Mem where
  pure  = pureMem
  (>>=) = bindMem

instance Semigroup a => Semigroup (Mem a) where
  m <> n = m >>= \x -> n >>= \y -> pure (x <> y)

instance IsString a => IsString (Mem a) where
  fromString s = pure (fromString s)


-------------------------------------------------- Ref

modifyRef :: Ref a -> (a -> a) -> Mem Tup0
modifyRef r f = readRef r >>= writeRef r . f

stateRef :: Ref a -> (a -> Tup2 a b) -> Mem b
stateRef r f = do
  a_ <- readRef r
  let T2 a b = f a_
  writeRef r a
  pure b


---------------------------------------------

-- use with {-# noinline #-}
-- only on top level
-- without ad-hoc polimorphysm
topMem :: Mem a -> a
topMem = unsafePerformMem


-------------------------------------------------- State

data State a = MkState (Ref a)

newState :: a -> Mem (State a)
newState a = MkState <$> newRef a

runState :: a -> (State a -> Mem b) -> Mem (Tup2 b a)
runState a cont = do
  s@(MkState r) <- newState a
  b <- cont s
  a <- readRef r
  pure (T2 b a)

evalState :: a -> (State a -> Mem b) -> Mem b
evalState s f = fst <$> runState s f

gets :: State a -> (a -> b) -> Mem b
gets (MkState r) f = readRef r <&> f

modify :: State a -> (a -> a) -> Mem Tup0
modify (MkState r) f = modifyRef r f


----------------------------------------------- Reader

data Reader a = MkReader (Ref a)

newReader :: a -> Mem (Reader a)
newReader a = MkReader <$> newRef a

runReader :: a -> (Reader a -> Mem b) -> Mem b
runReader a cont = newReader a >>= cont

asks :: Reader a -> (a -> b) -> Mem b
asks (MkReader r) f = readRef r <&> f

local :: Reader r -> (r -> r) -> Mem a -> Mem a
local (MkReader st) f m = do
  r <- readRef st
  writeRef st (f r)
  a <- m
  writeRef st r
  pure a

localInv :: Reader r -> (r -> r) -> (r -> r) -> Mem a -> Mem a
localInv (MkReader st) f g m = do
  modifyRef st f
  a <- m
  modifyRef st g
  pure a


----------------------------------------------- Writer

data Writer a = MkWriter (Ref a)

newWriter :: Monoid w => Mem (Writer w)
newWriter = MkWriter <$> newRef mempty

runWriter :: Monoid w => (Writer w -> Mem a) -> Mem (Tup2 a w)
runWriter cont = do
  w@(MkWriter st) <- newWriter
  a <- cont w
  r <- readRef st
  pure (T2 a r)

tell :: Monoid w => Writer w -> w -> Mem Tup0
tell (MkWriter st) x = modify (MkState st) (x <>)


----------------------------------------------- Except

data Except e = MkExcept Word

{-# noinline exceptCounter #-}
exceptCounter :: Ref Word
exceptCounter = topMem (newRef 0)

newExcept :: Mem (Except e)
newExcept = MkExcept <$> (stateRef exceptCounter \i -> T2 (i+1) i)

runExcept :: (Except e -> Mem a) -> Mem (Either e a)
runExcept f = do
  e <- newExcept
  catchError e (pure . Left) (lazy (Right <$> f e))

throwError :: Except e -> e -> Mem a
throwError (MkExcept p) e = throwMem p e

catchError :: Except e -> (e -> Mem a) -> Lazy (Mem a) -> Mem a
catchError (MkExcept p) f g = catchMem p f g


-----------------------------------------------

class Print a where
  print :: a -> Mem String

instance Print String where  print = pure
instance Print Word   where  print = print . showWord

newString :: Addr# -> Mem String
newString a = addrToCharArray a <&> mkString


--------------------------------------------------

type Reset = Ref (Mem Tup0)

reset :: Reset -> Mem Tup0
reset r = readRef r >>= \m -> m

-----------------

topMemReset :: Reset -> Mem (Tup2 a (Mem Tup0)) -> a
topMemReset mr mx = topMem do
  T2 r reset <- mx
  T0 <- modifyRef mr \m -> m >> reset
  pure r

topRef_ :: Reset -> Mem a -> Ref a
topRef_ mr mx = topMemReset mr do
  r <- newRef =<< mx
  pure (T2 r (mx >>= writeRef r))

-- use with {-# noinline #-}
-- only on top level
-- without ad-hoc polimorphysm
topRef :: Reset -> a -> Ref a
topRef r a = topRef_ r (pure a)

topState :: Reset -> Mem a -> State a
topState r a = MkState (topRef_ r a)

topReader :: Reset -> Mem a -> Reader a
topReader r a = MkReader (topRef_ r a)

topWriter :: Reset -> Mem a -> Writer a
topWriter r a = MkWriter (topRef_ r a)


--------------------------------------------------

class MonadFail m where
  fail :: Mem String -> m a


----------------------------------------------- main exception

data MainException
  = MkMainException (Mem String)
  | MkTag (Mem String) MainException

instance Print MainException where
  print = \case
    MkMainException s -> s
    MkTag s (MkMainException r) -> (\s r -> stripSource r <> "\n" <> showLoc s) <$> s <*> r
    MkTag _ r -> print r

{-# noinline mainException #-}
mainException :: Except MainException
mainException = topMem newExcept

tagError :: Print s => s -> Lazy (Mem a) -> Mem a
tagError s m = catchError mainException (throwError mainException . MkTag (print s)) m

instance MonadFail Mem where
  fail s = throwError mainException (MkMainException s)

{-# noinline error #-}
error :: Mem String -> a
error s = topMem (fail s)

undefined :: String -> Word -> a
undefined f l = error $ "TODO at " <> pure f <> ":" <> print l

impossible :: String -> Word -> a
impossible f l = error $ "impossible called at " <> pure f <> ":" <> print l

traceShow :: String -> Mem String -> Mem Tup0
--traceShow s m  | s == "" --elem s $ "hash" :. Nil -- [{-"56", "57"-} "1","2","3","4","5","6","7"]
--  = m >>= \s -> putStrMem (toPreludeString (fixANSI s)) >> putStrMem "\n"
traceShow _ _ = pure T0

