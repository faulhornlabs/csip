module B3_RefM
  ( RefM

  , Ref, newRef, readRef, writeRef, modifyRef, stateRef

  -- monad transformer alternatives
  , State,  runState,  evalState, gets, modify, topState
  , Reader, runReader, asks, local, localInv, topReader
  , Writer, runWriter, tell
  , Except (..), runExcept, throwError, catchError, newExcept

  , Print (print)
  , Parse (parse)
  , IsString (fromString'), fromString

  , topM
  , Reset, reset
  , mainReset, topMReset, topRef_, topRef
  , newId
  , mkLocString
  ) where

import B0_Builtins
import B1_Basic
import B2_String


-------------------------------------------------- RefM

instance Functor RefM where
  (<$>) f m = m >>= \x -> pure (f x)

instance Applicative RefM where
  pure = pureRefM
  fs <*> xs = fs >>= \f -> (<$>) f xs

instance Monad RefM where
  (>>=) = bindRefM

instance Semigroup a => Semigroup (RefM a) where
  m <> n = m >>= \x -> n >>= \y -> pure (x <> y)

instance IsString a => IsString (RefM a) where
  fromString' s = pure (fromString' s)


-------------------------------------------------- Ref

modifyRef :: Ref a -> (a -> a) -> RefM Tup0
modifyRef r f = readRef r >>= writeRef r . f

stateRef :: Ref a -> (a -> Tup2 a b) -> RefM b
stateRef r f = do
  a_ <- readRef r
  let T2 a b = f a_
  writeRef r a
  pure b


---------------------------------------------

-- use with {-# noinline #-}
-- only on top level
-- without ad-hoc polimorphysm
topM :: RefM a -> a
topM = unsafePerformRefM


-------------------------------------------------- State

data State a = MkState (Ref a)

fail = 0  -- needed for GHC 9.10

newState :: a -> RefM (State a)
newState a = MkState <$> newRef a

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

data Reader a = MkReader (Ref a)

newReader :: a -> RefM (Reader a)
newReader a = MkReader <$> newRef a

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

data Writer a = MkWriter (Ref a)

newWriter :: Monoid w => RefM (Writer w)
newWriter = MkWriter <$> newRef mempty

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
exceptCounter = topM (newRef 0)

newExcept :: RefM (Except e)
newExcept = MkExcept <$> (stateRef exceptCounter \i -> T2 (i+1) i)

throwError :: Except e -> e -> RefM a
throwError (MkExcept p) e = throwRefM p e

catchError :: Except e -> (e -> RefM a) -> Lazy (RefM a) -> RefM a
catchError (MkExcept p) f g = catchRefM p f g

runExcept :: (Except e -> RefM a) -> RefM (Either e a)
runExcept f = do
  e <- newExcept
  catchError e (pure . Left) (lazy (Right <$> f e))


-----------------------------------------------

class Print a where
  print :: a -> RefM String

instance Print String where
  print = pure

instance Print Word where
  print = print . showWord

instance Print Void where
  print ~_ = pure mempty


class Parse a where
  parse :: String -> RefM a

instance Parse String where
  parse = pure


class IsString a where
  fromString' :: String -> RefM a

instance IsString String where
  fromString' s = pure s

-- needed for ghci
instance IsString PreludeString where
  fromString' s = pure $ toPreludeString s

{-# noinline fromString #-}
fromString :: IsString a => PreludeString -> a
fromString cs = topM $ fromString' (mkString $ fromPreludeString cs)


--------------------------------------------------

type Reset = Ref (RefM Tup0)

reset :: Reset -> RefM Tup0
reset r = join (readRef r)

-----------------

{-# noinline mainReset #-}
mainReset :: Reset
mainReset = topM (newRef (pure T0))

topMReset :: RefM (Tup2 a (RefM Tup0)) -> a
topMReset mx = topM do
  T2 r reset <- mx
  T0 <- modifyRef mainReset \m -> m >> reset
  pure r

topRef_ :: RefM a -> Ref a
topRef_ mx = topMReset do
  r <- newRef =<< mx
  pure (T2 r (mx >>= writeRef r))

-- use with {-# noinline #-}
-- only on top level
-- without ad-hoc polimorphysm
topRef :: a -> Ref a
topRef a = topRef_ (pure a)

topState :: RefM a -> State a
topState a = MkState (topRef_ a)

topReader :: RefM a -> Reader a
topReader a = MkReader (topRef_ a)


---------------------------------------------

{-# noinline idRef #-}
idRef :: Ref Word
idRef = topRef 0

newId :: RefM Word
newId = stateRef idRef \i -> T2 (i+1) i

mkLocString :: (Parse a) => String -> CharArray -> RefM a
mkLocString n s = newId <&> mkFileString n s >>= parse



