{-# language CPP #-}
module M1_Base
  ( module M0_Prelude

  , Sum (MkSum, getSum)
  , Interval (MkInterval), mkInterval
  , Cached (MkCached, getCached)         -- newtype with trivial Eq, Ord, Show instances

  , pattern Reverse

  , mreplicate

  , head, tail, fromJust
  , isUpper, isLower, isDigit, isGraphic, isAlphaNum

  , Source (Cons, Nil)
  , lengthCh, spanCh, splitAtCh, takeCh, dropCh, revSpanCh, revTakeCh, revDropCh, lastCh, headCh, readNat
  , chars
  , Print (print)
  , Parse (parse)
  , source

  , RefM, Ref, newRef, readRef, writeRef, modifyRef, stateRef
  , topM, topRef, reset

  -- monad transformer alternatives
  , State,  runState,  evalState, gets, modify
  , Reader, runReader, asks, local, topReader
  , Writer, runWriter, tell, listenAll
  , Except, runExcept, throwError, catchError

  -- linearly used IntMap alternative
  , LMap, Key, emptyL, newKey, insertL, lookupL

  , newId

  , pattern CSI
  , invert, background, foreground, black, red, green, yellow, blue, magenta, cyan, white
  , clearScreen, setCursorPosition, setCursorHPosition, cursorUp, cursorDown, cursorForward, cursorBack
  , showCursor, hideCursor, fixANSI
  , lengthANSI

  , mainException
  , tag
  , impossible, undefined, error, error', errorM, assert, assertM

  , walk, downUp, topDown, bottomUp

  , precedenceTableString

  , traceShow, (<<>>)

  , IntHash (intHash)
  , importFile

  , Void
  , HasId(getId)
  , IntMap, readIM, insertIM, lookupIM, fromListIM, sizeIM, toListIM, singletonIM, assocsIM, unionWithIM, nullIM
  , walkIM, downUpIM, topDownIM, bottomUpIM
  , IntSet, singletonIS, memberIS, insertIS, deleteIS, fromListIS, toListIS, nullIS
  , nubIS
  )
 where

-----------------------------------------------

import Prelude (IO, FilePath)
import Prelude as IO (readFile)

import Data.Char (digitToInt)
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Array.IArray as Arr
import qualified Data.Array.Unboxed as Arr
import qualified Data.Array.Base as Arr

import Data.IORef (IORef, newIORef, readIORef, writeIORef, modifyIORef', atomicModifyIORef')
import Data.Typeable (Typeable, Proxy)
import qualified Control.Exception as Excpetion (Exception, catch, throwIO)
import GHC.TypeLits (KnownNat, Nat, SomeNat (SomeNat), someNatVal)
import System.IO.Unsafe (unsafePerformIO)
import GHC.Stack (HasCallStack, callStack, getCallStack, SrcLoc(..))

import Paths_csip
import M0_Prelude

-----------------------------------------------

newtype Cached a = MkCached {getCached :: a}

instance Eq   (Cached a) where _ == _ = True
instance Ord  (Cached a) where compare _ _ = EQ
instance Show (Cached a) where show _ = ""


-----------------------------------------------

newtype Sum a = MkSum {getSum :: a}
  deriving (Eq, Ord, Num)

instance Num a => Semigroup (Sum a) where
  (<>) = (+)

instance Num a => Monoid (Sum a) where
  mempty = 0

instance Show a => Show (Sum a) where
  show = show . getSum

-----------------------------------------------

newtype Interval a b = MkInterval (a, b)
  deriving (Eq, Show)

mkInterval a b = MkInterval (a, b)

instance Semigroup (Interval a b) where
  MkInterval (a, _) <> MkInterval (_, b) = MkInterval (a, b)

-----------------------------------------------

pattern Reverse a <- (reverse -> a)
  where Reverse a =  reverse a

-----------------------------------------------

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


-----------------------------------------------

data Handler = MkHandler {fileId :: Int, fileName :: String}

instance Eq  Handler where (==) = (==) `on` fileId
instance Ord Handler where compare = compare `on` fileId

mkHandler :: FilePath -> RefM Handler
mkHandler s = do
  i <- newId
  pure $ MkHandler i s


class Parse a where
  parse :: Source -> RefM a

instance Parse Source where
  parse = pure

instance Parse String where
  parse = pure . chars


source :: (Parse a) => String -> String -> RefM a
source n s = do
  p <- mkHandler n
  parse $ source_ (Just p) s  

type Vec = Arr.UArray Int Char

vecFromList :: String -> Vec
vecFromList s = Arr.listArray (0, length s - 1) s

lengthVec :: Vec -> Int
lengthVec = Arr.numElements

{-# inline indexVec #-}
indexVec :: Vec -> Int -> Char
indexVec = Arr.unsafeAt


data CharCtx = MkCtx (Maybe Handler) Vec

newtype Source = MkSource [(Int, Int, CharCtx)]
  deriving (Semigroup, Monoid)

{-# INLINE chars #-}
chars :: Source -> [Char]
chars (MkSource s) = [indexVec v k | (i, j, MkCtx _ v) <- s, k <- [i..j-1]]

instance Eq  Source  where
  {-# INLINE (==) #-}
--  (==) = (==) `on` chars       -- GHC can not optimize this?
  MkSource sa == MkSource sb = go sa sb  where
    go [] [] = True
    go ((ia, ja, MkCtx _ va): as) ((ib, jb, MkCtx _ vb): bs) = go' ia ja va as ib jb vb bs
    go _ _ = False

    go' ia ja va as ib jb vb bs
      | ja == ia, (ia, ja, MkCtx _ va): as <- as  = go' ia ja va as ib jb vb bs
      | ja == ia, [] <- as, jb == ib, [] <- bs  = True
      | ja == ia, [] <- as  = False
      | jb == ib, (ib, jb, MkCtx _ vb): bs <- bs  = go' ia ja va as ib jb vb bs
      | jb == ib, [] <- bs  = False
      | otherwise = indexVec va ia == indexVec vb ib && go' (ia+1) ja va as (ib+1) jb vb bs

instance Ord Source where compare = compare `on` chars

pattern Cons :: Source -> Source -> Source
pattern Cons c s <- (getCons -> Just (c, s))

pattern Nil :: Source
pattern Nil = ""

{-# COMPLETE Cons, Nil #-}

getCons (MkSource ((i, j, ctx): ss))
  | j == i + 1 = Just (MkSource [(i, j, ctx)], MkSource ss)
  | otherwise  = Just (MkSource [(i, i+1, ctx)], MkSource $ (i+1, j, ctx): ss)
getCons _ = Nothing

spanCh, revSpanCh :: (Char -> Bool) -> Source -> (Source, Source)
spanCh p = spanCh_ \_ -> p
revSpanCh p = revSpanCh_ \_ -> p

splitAtCh :: Int -> Source -> (Source, Source)
splitAtCh n = spanCh_ \i _ -> i < n

takeCh, dropCh, revTakeCh, revDropCh :: Int -> Source -> Source
takeCh n = fst . splitAtCh n
dropCh n = snd . splitAtCh n
revTakeCh n = fst . revSpanCh_ \i _ -> i < n
revDropCh n = snd . revSpanCh_ \i _ -> i < n

spanCh_ :: (Int -> Char -> Bool) -> Source -> (Source, Source)
spanCh_ p (MkSource ss) | (as, bs) <- f 0 ss = (MkSource as, MkSource bs)
 where
  f _ [] = ([], [])
  f offs (s@(i, j, c@(MkCtx _ v)): ss) = g i
   where
    g x
      | x == j, (as, bs) <- f (offs + j - i) ss = (s: as, bs)
      | p (offs + x - i) (indexVec v x) = g (x+1)
      | x == i    = ([], s: ss)
      | otherwise = ([(i, x, c)], (x, j, c): ss)

revSpanCh_ :: (Int -> Char -> Bool) -> Source -> (Source, Source)
revSpanCh_ p (MkSource ss) | (as, bs) <- f 0 $ reverse ss = (MkSource $ reverse as, MkSource $ reverse bs)
 where
  f _ [] = ([], [])
  f offs (s@(j, i, c@(MkCtx _ v)): ss) = g i
   where
    g x
      | x == j, (as, bs) <- f (offs + i - j) ss = (s: as, bs)
      | p (offs + i - x) (indexVec v (x-1)) = g (x-1)
      | x == i    = ([], s: ss)
      | otherwise = ([(x, i, c)], (j, x, c): ss)

--lengthCh = length . chars
lengthCh (MkSource as) = sum [j - i | (i, j, _) <- as]

lastCh   = last   . chars
headCh   = head   . chars

mreplicate n a = mconcat $ replicate n a

readNat :: Source -> Maybe Integer
readNat (chars -> cs)
  | all isDigit cs = Just $ foldl (\i c -> 10*i + fromIntegral (digitToInt c)) 0 cs
  | otherwise = Nothing

instance Show Source where
  show s = chars s <> "\n" <> showLoc s

instance IsString Source where
  fromString = source_ Nothing

source_ :: Maybe Handler -> String -> Source
source_ _ [] = MkSource []
source_ n s = MkSource [(0, lengthVec v, MkCtx n v)]
    where v = vecFromList s


showLoc_ :: Source -> [(String, String)]
showLoc_ (MkSource cs)
  = [f p v [(i, j) | (i, j, MkCtx (Just p') _) <- cs, p' == p] | (p, v) <- ps]
 where
  ps = assocs $ mconcat [singleton p v | (_, _, MkCtx (Just p) v) <- cs]

  f hand v is = (fileName hand, h [(i `IS.member` s, indexVec v i) | i <- [0.. lengthVec v - 1]])
   where
    s = mconcat [IS.singleton k | (i, j) <- is, k <- [i..j-1]]

  lines :: [(a, Char)] -> [[(a, Char)]]
  lines [] = []
  lines (span ((/= '\n') . snd) -> (as, bs)) = as: case bs of
    [] -> []
    [_] -> []: []
    _: bs -> lines bs

  groupOn :: Eq b => [(b, c)] -> [(b, [c])]
  groupOn = map (\as -> (fst (head as), map snd as)) . groupBy ((==) `on` fst)

  h = hh
    . map groupOn
    . lines

  hh :: [[(Bool, String)]] -> String
  hh ss = intercalate "\n" $ map h2 $ groupOn $ zip (widen 1 mask) s2
   where
    s2 = map gb $ zip [1 :: Int ..] ss
    mask = map ga ss

  widen i bs = take (length bs) $ map (or . take (2*i + 1)) $ tails $ replicate i False <> bs

  h2 (True, s) = intercalate "\n" s
  h2 (False, _) = foreground green "..."

  ga [] = False
  ga [(False, _)] = False
  ga _ = True

  gb (n, s) = foreground green (show n <> " | ") <> concat (map g s)  where
    g (True, s) = background blue s
    g (_, s) = s

showLoc :: Source -> String
showLoc s = concat $ intersperse "\n" [invert (foreground green $ " " <> f <> " ") <> "\n" <> x | (f, x) <- showLoc_ s]

-----------------------------

stripANSI :: String -> String
stripANSI = f
 where
  f = \case
    '\ESC': '[': cs -> f (skip cs)
    c: cs -> c: f cs
    [] -> []

  skip = drop 1 . dropWhile (\c -> isDigit c || c `elem` [';','?'])

lengthANSI :: String -> Int
lengthANSI = length . stripANSI

csi :: (IsString a, Monoid a) => [Int] -> a -> a
csi args code = "\ESC[" <> mconcat (intersperse ";" $ map (fromString . show) args) <> code

clearScreen = csi [2] "J"
setCursorHPosition n = csi [n + 1] "G"
setCursorPosition n m = csi [n + 1, m + 1] "H"
cursorUp      n = csi [n] "A"
cursorDown    n = csi [n] "B"
cursorForward n = csi [n] "C"
cursorBack    n = csi [n] "D"

hideCursor = csi [] "?25l"
showCursor = csi [] "?25h"

sgr args = csi args "m"
background_ n = sgr [n + 40]
foreground_ n = sgr [n + 30]
normal = 9  -- color

invert s = sgr [7] <> s <> sgr [27]
background n s = background_ n <> s <> background_ normal
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
  f (_: a: as) bs (SGR [39] cs) = SGR [a] $ f (a: as) bs cs
  f as (_: b: bs) (SGR [49] cs) = SGR [b] $ f as (b: bs) cs
  f as bs (SGR [i] cs)
    | 30 <= i, i <= 37 = SGR [i] $ f (i: as) bs cs
    | 40 <= i, i <= 47 = SGR [i] $ f as (i: bs) cs
  f as bs (c: cs) = c: f as bs cs
  f _  _  [] = []

getCSI ('\ESC': '[': cs) = f "" [] cs
 where
  f i is (c: cs) = case c of
    ';'           -> f "" (i: is) cs
    c | isDigit c -> f (c: i) is cs
    c             -> Just (reverse $ map (read . reverse) $ i: is, c, cs)
  f _ _ _ = Nothing
getCSI _ = Nothing

pattern CSI :: [Int] -> Char -> String -> String
pattern CSI is c cs <- (getCSI -> Just (is, c, cs))
  where CSI is c cs =  "\ESC[" ++ mconcat (intersperse ";" $ map show is) ++ c: cs


------------------------------

class Print a where
  print :: a -> RefM Source

instance Print Source where
  print = pure

instance Print String where
  print = pure . fromString

instance Print Int where
  print = print . show

instance Print Void where
  print = impossible

--------------------------------------------------

-- use with {-# noinline #-}
-- only on top level
-- without ad-hoc polimorphysm
topM :: RefM a -> a
topM = unsafePerformIO

{-# noinline resetRef #-}
resetRef :: Ref (RefM ())
resetRef = topM $ newRef $ pure ()

-- use with {-# noinline #-}
-- only on top level
-- without ad-hoc polimorphysm
topRef :: a -> Ref a
topRef a = topRef_ (pure a)

topRef_ :: RefM a -> Ref a
topRef_ mx = topM do
  r <- newRef =<< mx
  () <- modifyRef resetRef \m -> m >> mx >>= writeRef r
  pure r

reset :: RefM ()
reset = join $ readRef resetRef



--------------------------------------------------

newtype Ref a = MkRef (IORef a)

type RefM = IO

newRef :: a -> RefM (Ref a)
newRef a = MkRef <$> newIORef a

readRef  :: Ref a -> RefM a
readRef (MkRef r) = readIORef r

writeRef :: Ref a -> a -> RefM ()
writeRef (MkRef r) a = writeIORef r a

modifyRef :: Ref a -> (a -> a) -> RefM ()
modifyRef (MkRef r) f = modifyIORef' r f

stateRef :: Ref a -> (a -> (a, b)) -> RefM b
stateRef (MkRef r) f = atomicModifyIORef' r f

-------------------------------------------------- efficient linear maps

emptyL  :: RefM (LMap a)
newKey  :: LMap a -> a -> RefM (Key a)
insertL :: LMap a -> Key a -> a -> RefM ()
lookupL :: LMap a -> Key a -> RefM a

{-
newtype LMap a = MkLMap (Ref (IM.IntMap a))

newtype Key a = MkKey Int

emptyL = withRef mempty $ pure . MkLMap

newKey (MkLMap r) a = stateRef r \m ->
  let i = maybe 0 ((+1) . fst . fst) (IM.maxViewWithKey m)
  in (IM.insert i a m, MkKey i)

insertL (MkLMap r) (MkKey i) a = modifyRef r $ IM.insert i a

lookupL (MkLMap r) (MkKey j) = stateRef r \m -> (m, m IM.! j)
-}

newtype LMap a = MkLMap ()

newtype Key a = MkKey (Ref a)

emptyL = pure $ MkLMap ()

newKey _ a = MkKey <$> newRef a

insertL _ (MkKey i) a = writeRef i a

lookupL _ (MkKey j) = readRef j


--------------------------------------------------

newtype State a = MkState (Ref a)

newState :: a -> RefM (State a)
newState a = MkState <$> newRef a

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

----------------

newtype Reader a = MkReader (Ref a)

newReader :: a -> RefM (Reader a)
newReader a = MkReader <$> newRef a

topReader :: RefM a -> Reader a
topReader a = MkReader $ topRef_ a

runReader :: a -> (Reader a -> RefM b) -> RefM b
runReader a cont = newReader a >>= cont

asks :: Reader a -> (a -> b) -> RefM b
asks (MkReader r) f = readRef r <&> f

local :: Reader r -> (r -> r) -> RefM a -> RefM a
local (MkReader st) f m = do
  r <- readRef st
  writeRef st $! f r
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
----------------

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
  listenAll w $ cont w

tell :: (Semigroup w) => Writer w -> w -> RefM ()
tell (MkWriter st) x = modify (MkState st) (x <>)


----------------

data Except e = {- Typeable e => -} MkExcept SomeNat

{-# noinline exceptCounter #-}
exceptCounter :: Ref Int
exceptCounter = topM $ newRef 0    -- TODO: reset for local newExcept calls

newExcept :: Typeable e => RefM (Except e)
newExcept = do
  i <- stateRef exceptCounter \i -> (i+1, i)
  pure $ MkExcept $ fromJust $ someNatVal $ fromIntegral i

throwError :: (HasCallStack, Typeable e, Print e) => Except e -> e -> RefM a
throwError (MkExcept (SomeNat p)) e
  = print e >>= \s -> Excpetion.throwIO (mk p e s)
 where
  mk :: Proxy i -> e -> Source -> GException e i
  mk _ e s = MkGException e s

catchError :: Typeable e => Except e -> (e -> RefM a) -> RefM a -> RefM a
catchError (MkExcept (SomeNat p)) f g
  = Excpetion.catch (g >>= \a -> a `seq` pure a) (fun p f)
 where
  fun :: Proxy i -> (e -> RefM a) -> GException e i -> RefM a
  fun _ f (MkGException x _) = f x

runExcept :: (Typeable e) => (Except e -> RefM a) -> RefM (Either e a)
runExcept f = do
  e <- newExcept
  catchError e (pure . Left) (Right <$> f e)

----

data GException e (i :: Nat)
  = MkGException e Source

instance Show (GException e i) where
  show (MkGException _ s) = "\n" <> show s

instance (KnownNat i, Typeable e) => Excpetion.Exception (GException e i)


---------------------------------------------

{-# noinline idRef #-}
idRef :: Ref Int
idRef = topRef 0

newId :: RefM Int
newId = stateRef idRef \i -> (i+1, i)


---------------------------------------------

data MainException
  = MkMainException Source
  | MkTag (RefM Source) MainException

instance Print MainException where
  print = \case
    MkMainException s -> pure s
    MkTag _ r@MkTag{} -> print r
    MkTag s r -> s >>= \s -> print r <&> \r -> fromString (show r) <> fromString (showLoc s)

instance Show MainException where
  show r = unsafePerformIO $ print r <&> show

{-# noinline mainException #-}
mainException :: Except MainException
mainException = topM newExcept

printCallStack cs@(_:_) | (name, loc) <- last cs
  = "  " <> name <> " called at "
   <> srcLocModule loc <> ":" <> show (srcLocStartLine loc) <> ":" <> show (srcLocStartCol loc)
printCallStack _ = "<empty callstack>"

errorM_ :: HasCallStack => Bool -> Source -> RefM a
errorM_ cs s = throwError mainException $ MkMainException
  $ if cs then s <> "\n" <> fromString (printCallStack $ getCallStack callStack) else s

errorM :: HasCallStack => Source -> RefM a
errorM = errorM_ False

error' :: HasCallStack => IO Source -> a
error' s = unsafePerformIO $ s >>= errorM_ False

error :: HasCallStack => Source -> a
error s = error' $ pure s

undefined :: HasCallStack => a
undefined = unsafePerformIO $ errorM_ True "TODO"

impossible :: HasCallStack => a
impossible = unsafePerformIO $ errorM_ True "impossible"

assert :: HasCallStack => Bool -> a -> a
#ifdef DEBUG
assert False = error "assertion failed"
#endif
assert _ = id

assertM :: HasCallStack => Bool -> RefM ()
#ifdef DEBUG
assertM False = errorM "assertion failed"
#endif
assertM _ = pure ()

------------------

head :: HasCallStack => [a] -> a
head (a: _) = a
head _ = impossible

tail :: HasCallStack => [a] -> [a]
tail (_: as) = as
tail _ = impossible

fromJust :: HasCallStack => Maybe a -> a
fromJust (Just a) = a
fromJust _ = impossible

---------- TODO: move to Parse with SPrint

tag :: Print s => s -> RefM a -> RefM a
tag s = catchError mainException (throwError mainException . MkTag (print s))

------------------------------------------------- graph algorithms

-- top-down & bottom-up  graph walking;  sharing and cycle friendly
walk
  :: Ord a
  => (a -> RefM (b, [a]))              -- down
  -> (a -> b -> RefM b)                -- shared try
  -> (a -> b -> [(a, b)] -> RefM b)
  -> [a]
  -> RefM (Map a b)
walk children  down up xs = fmap snd $ runState mempty go where
  go st = walk (Left <$> xs)  where
    walk [] = pure ()
    walk (Left v: ts) = gets st (lookup v) >>= \case
      Nothing -> do
        (r, ch) <- children v
        modify st $ insert v r
        walk $ map Left ch ++ Right (v, ch): ts
      Just r -> do
        r' <- down v r
        modify st $ insert v r'
        walk ts
    walk (Right (e, ch): ts) = do
      m <- gets st (fromJust . lookup e)
      ms <- forM ch \v -> gets st (fromJust . lookup v)
      r <- up e m $ zip ch ms
      modify st $ insert e r
      walk ts

downUp
  :: Ord a
  => (a -> RefM (b, [a]))              -- down
  -> (a -> b -> [(a, c)] -> RefM c)
  -> [a]
  -> RefM (Map a c)
downUp down up as = walk down' (\_ -> pure) up' as <&> fmap g
 where
  down' a = down a <&> first Left
  up' a (Left b) cs = fmap Right $ up a b $ map (second g) cs
  up' _ _ _ = impossible
  g (Right c) = c
  g _ = impossible

topDown
  :: Ord a
  => (a -> RefM (b, [a]))
  -> [a]
  -> RefM (Map a b)
topDown down
  = walk down (\_ -> pure) (\_ b _ -> pure b)

bottomUp
  :: Ord a
  => b
  -> (a -> RefM [a])
  -> (a -> [(a, b)] -> RefM b)
  -> a
  -> RefM (Map a b)
bottomUp init children up x
  = walk (\v -> (,) init <$> children v) (\_ -> pure) (\a _ b -> up a b) [x]

------------------------------------------------- graph algorithms

-- top-down & bottom-up  graph walking;  sharing and cycle friendly
walkIM
  :: HasId a
  => (a -> RefM (b, [a]))              -- down
  -> (a -> b -> RefM b)                -- shared try
  -> (a -> b -> [(a, b)] -> RefM b)
  -> [a]
  -> RefM (IntMap a b)
walkIM children  down up xs = fmap snd $ runState mempty go where
  go st = walk (Left <$> xs)  where
    walk [] = pure ()
    walk (Left v: ts) = gets st (lookupIM v) >>= \case
      Nothing -> do
        (r, ch) <- children v
        modify st $ insertIM v r
        walk $ map Left ch ++ Right (v, ch): ts
      Just r -> do
        r' <- down v r
        modify st $ insertIM v r'
        walk ts
    walk (Right (e, ch): ts) = do
      m <- gets st (readIM e)
      ms <- forM ch \v -> gets st (readIM v)
      r <- up e m $ zip ch ms
      modify st $ insertIM e r
      walk ts

downUpIM
  :: HasId a
  => (a -> RefM (b, [a]))              -- down
  -> (a -> b -> [(a, c)] -> RefM c)
  -> [a]
  -> RefM (IntMap a c)
downUpIM down up as = walkIM down' (\_ -> pure) up' as <&> fmap g
 where
  down' a = down a <&> first Left
  up' a (Left b) cs = fmap Right $ up a b $ map (second g) cs
  up' _ _ _ = impossible
  g (Right c) = c
  g _ = impossible

topDownIM
  :: HasId a
  => (a -> RefM (b, [a]))
  -> [a]
  -> RefM (IntMap a b)
topDownIM down
  = walkIM down (\_ -> pure) (\_ b _ -> pure b)

bottomUpIM
  :: HasId a
  => b
  -> (a -> RefM [a])
  -> (a -> [(a, b)] -> RefM b)
  -> a
  -> RefM (IntMap a b)
bottomUpIM init children up x
  = walkIM (\v -> (,) init <$> children v) (\_ -> pure) (\a _ b -> up a b) [x]


----------------------------------------

importFile :: Parse a => Source -> RefM a
importFile f = do
  d <- getDataDir
  s <- IO.readFile $ d <> "/" <> chars f <> ".csip"
  source (chars f) s

precedenceTableString :: String
precedenceTableString = unsafePerformIO do
  f <- getDataFileName "precedences"
  IO.readFile f

traceShow :: String -> RefM String -> RefM ()
--traceShow s m {- | s `elem` ["1","2","3","4","5","6","7"] -} = m >>= \s -> traceM s
traceShow _ _ = pure ()

a <<>> b = (<>) <$> a <*> b

instance IsString a => IsString (RefM a) where
  fromString s = pure $ fromString s


class IntHash a where
  intHash :: a -> Int  -- always negative

instance IntHash String where
  intHash
    = foldl (\h c -> 33*h + ord c) 5381   -- djb2

instance IntHash Source where
  intHash = intHash . chars

data Void

instance Eq  Void where (==) = impossible
instance Ord Void where compare = impossible


-------------------------------------------------- IntMaps

class HasId k where
  getId :: k -> Int

instance HasId Int where
  getId i = i

-----

newtype IntMap k a = MkIM (IM.IntMap (k, a))
  deriving (Semigroup, Monoid)

instance HasId k => Functor (IntMap k) where
  fmap f (MkIM m) = MkIM $ fmap (second f) m

readIM :: (HasCallStack, HasId k) => k -> IntMap a b -> b
readIM a (MkIM m) = snd $ fromMaybe (error "elem not in map") $ IM.lookup (getId a) m

insertIM :: HasId k => k -> a -> IntMap k a -> IntMap k a
insertIM a b (MkIM m) = MkIM $ IM.insert (getId a) (a, b) m

lookupIM a (MkIM m) = fmap snd $ IM.lookup (getId a) m

sizeIM (MkIM m) = IM.size m

fromListIM xs = MkIM $ IM.fromList [(getId a, p) | p@(a, _) <- xs]

toListIM :: IntMap a b -> [b]
toListIM (MkIM m) = map snd $ toList m

assocsIM :: IntMap a b -> [(a, b)]
assocsIM (MkIM m) = toList m

singletonIM a b = MkIM $ IM.singleton (getId a) (a, b)

nullIM (MkIM m) = IM.null m

unionWithIM :: HasId a => (b -> b -> b) -> IntMap a b -> IntMap a b -> IntMap a b
unionWithIM f (MkIM a) (MkIM b) = MkIM $ IM.unionWith (\(a, x) (_, y) -> (a, f x y)) a b

-----

newtype IntSet a = MkIS (IM.IntMap a)
  deriving (Semigroup, Monoid, Eq, Ord)

insertIS :: HasId k => k -> IntSet k -> IntSet k
insertIS a (MkIS m) = MkIS $ IM.insert (getId a) a m

singletonIS a = MkIS $ IM.singleton (getId a) a

nullIS (MkIS m) = IM.null m

memberIS :: HasId a => a -> IntSet a -> Bool
memberIS a (MkIS m) = IM.member (getId a) m

deleteIS a (MkIS m) = MkIS $ IM.delete (getId a) m

fromListIS xs = MkIS $ IM.fromList [(getId a, a) | a <- xs]

toListIS :: IntSet a -> [a]
toListIS (MkIS m) = toList m

nubIS :: HasId a => [a] -> [a]
nubIS = f mempty  where
  f _ [] = []
  f s (x: xs)
    | memberIS x s = f s xs
    | otherwise    = x: f (insertIS x s) xs


