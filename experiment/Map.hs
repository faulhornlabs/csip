{-# language LambdaCase, ViewPatterns, PatternSynonyms, BlockArguments #-}
-- {-# OPTIONS_GHC -Wall #-}

import Data.Functor
import Data.Maybe
import Data.Bits
import Data.Char
import Control.Applicative
import GHC.IOArray
import Text.Show.Pretty

---------- Maps

{-
data Map a b = E | N a b (Map a b)
  deriving Show

emptyMap :: Map a b
emptyMap = E

lookupMap :: Eq a => a -> Map a b -> Maybe b
lookupMap a = \case
  E                    -> Nothing
  N a' b r | a == a'   -> Just b
           | otherwise -> lookupMap a r

insertMap :: Eq a => a -> b -> Map a b -> Map a b
insertMap = N

fromListMap :: Eq a => [(a , b)] -> Map a b
fromListMap = foldl (\m (a, b) -> insertMap a b m) emptyMap
-}
----------------

{-
--data Map a b = E | N a b (Map a b)
--  deriving Show

data Map a b = E | N (Map a b) a b (Map a b)
  deriving Show

emptyMap :: Map a b
emptyMap = E

lookupMap :: Ord a => a -> Map a b -> Maybe b
lookupMap a = \case
  E                    -> Nothing
  N l a' b r | a == a' -> Just b
             | a <  a' -> lookupMap a l
             | a >  a' -> lookupMap a r

insertMap :: Ord a => a -> b -> Map a b -> Map a b
insertMap a b = \case
  E                     ->  N E                 a  b  E
  N l a' b' r | a == a' ->  N l                 a  b  r
              | a <  a' ->  N (insertMap a b l) a' b' r
              | a >  a' ->  N l                 a' b' (insertMap a b r)

fromListMap :: Ord a => [(a , b)] -> Map a b
fromListMap = foldl (\m (a, b) -> insertMap a b m) emptyMap
-}
----------------

data Colour = R | B
  deriving Show

data Map a b = E | N Colour (Map a b) a b (Map a b)
  deriving Show

emptyMap :: Map a b
emptyMap = E

lookupMap :: Ord a => a -> Map a b -> Maybe b
lookupMap a = \case
  E                      -> Nothing
  N _ l a' b r | a == a' -> Just b
               | a <  a' -> lookupMap a l
               | a >  a' -> lookupMap a r

-- by Chris Okasaki, 1999
insertMap :: Ord a => a -> b -> Map a b -> Map a b
insertMap a b t  =  blacken (f t) where

  f = \case
    E                        ->  n R E     a  b  E
    N c l a' b' r | a == a'  ->  n c l     a  b  r
                  | a <  a'  ->  n c (f l) a' b' r
                  | a >  a'  ->  n c l     a' b' (f r)

  blacken (N _ l a b r) =  N B l a b r
  blacken t = t

  n :: Colour -> Map a b -> a -> b -> Map a b -> Map a b
  n B (N R (N R x a b y) a' b' z) a'' b'' v = N R (N B x a b y) a' b' (N B z a'' b'' v)
  n B (N R x a b (N R y a' b' z)) a'' b'' v = N R (N B x a b y) a' b' (N B z a'' b'' v)
  n B x a b (N R (N R y a' b' z) a'' b'' v) = N R (N B x a b y) a' b' (N B z a'' b'' v)
  n B x a b (N R y a' b' (N R z a'' b'' v)) = N R (N B x a b y) a' b' (N B z a'' b'' v)
  n c l a b r                               = N c l a b r

fromListMap :: Ord a => [(a , b)] -> Map a b
fromListMap = foldl (\m (a, b) -> insertMap a b m) emptyMap


------------------------------------------------ IntMap

half :: Int -> Int
half i = shiftR i 1

data IntMap a
  = Empty
  | Zero a                      -- image of 0
  | Node (IntMap a) (IntMap a)  -- image of even and odd elements
  deriving Show

emptyIM :: IntMap a
emptyIM = Empty

getNode :: IntMap a -> (IntMap a, IntMap a)
getNode = \case
  Empty    -> (Empty,  Empty)
  Zero a   -> (Zero a, Empty)
  Node l r -> (l, r)

pattern ENode l r <- (getNode -> (l, r))
  where ENode Empty    Empty = Empty
        ENode (Zero a) Empty = Zero a
        ENode l        r     = Node l r

{-# COMPLETE ENode #-}

lookupIM :: Int -> IntMap a -> Maybe a
lookupIM 0 (Zero a) = Just a
lookupIM i (Node l r) | even i = lookupIM (half i) l
                      | odd  i = lookupIM (half i) r
lookupIM _ _ = Nothing

insertIM :: Int -> a -> IntMap a -> IntMap a
insertIM 0 a Empty    = Zero a
insertIM 0 a (Zero _) = Zero a
insertIM i a (ENode l r) | even i = ENode (insertIM (half i) a l) r
                         | odd  i = ENode l (insertIM (half i) a r)

deleteIM :: Int -> IntMap a -> IntMap a
deleteIM i (Node l r) | even i = ENode (deleteIM (half i) l) r
                      | odd  i = ENode l (deleteIM (half i) r)
deleteIM 0 _ = Empty
deleteIM _ l = l

fromListIM :: [(Int , a)] -> IntMap a
fromListIM = foldl (\m (i, a) -> insertIM i a m) Empty



----------------------------------------------- IntSet

newtype IntSet = MkIS Integer
  deriving Show

instance Semigroup IntSet where
  MkIS a <> MkIS b = MkIS (a .|. b)

instance Monoid IntSet where
  mempty = MkIS 0

singletonIS :: Int -> IntSet
singletonIS i = MkIS $ shiftL 1 i

memberIS w (MkIS i) = i .&. (shiftL 1 w) /= 0

toListIS :: IntSet -> [Int]
toListIS (MkIS i) = f 0 i where
  f _ 0 = []
  f k i = (if odd i then (k:) else id) $ f (k+1) (shiftR i 1)


----------------------------------------------- StringMap

itemsMask = 127 :: Int

hashString (c: _cs) = ord c .&. itemsMask
hashString _ = 0

data HItem a
  = NilH
  | YesH a
  | ConsH Char (HItem a) (HItem a)

consH _ NilH b = b
consH c a    b = ConsH c a b

data StringMap a = MkSM (IOArray Int (HItem a))

newStringMap :: IO (StringMap a)
newStringMap = MkSM <$> newIOArray (0, itemsMask) NilH

lookupSM_ :: String -> StringMap a -> IO (HItem a)
lookupSM_ s (MkSM hm) | h <- hashString s = readIOArray hm h <&> f s  where

  f s@[] = \case
    ConsH _ _ t -> f s t
    z -> z
  f s@(c: cs) = \case
    ConsH c' a b
      | c' == c -> f cs a
      | True    -> f s b
    _ -> NilH

lookupSM :: String -> StringMap a -> IO (Maybe a)
lookupSM s sm = lookupSM_ s sm <&> \case
  YesH a -> Just a
  NilH   -> Nothing
  _       -> error "impossible"

updateSM :: String -> HItem a -> StringMap a -> IO ()
updateSM s x (MkSM hm) | h <- hashString s = do
    t <- readIOArray hm h
    writeIOArray hm h $ ins s t
   where
    ins s@[] = \case
      ConsH c a b -> ConsH c a (ins s b)
      _ -> x
    ins s@(c: cs) = \case
      ConsH c' a b
        | c' == c -> consH c' (ins cs a) b
        | True    -> ConsH c' a (ins s b)
      z -> ConsH c (ins cs NilH) z

insertSM :: String -> a -> StringMap a -> IO ()
insertSM s a sm = updateSM s (YesH a) sm

deleteSM :: String -> StringMap a -> IO ()
deleteSM s sm = updateSM s NilH sm

----------------------------------------------------

data Vector a
  = Nil
  | Snoc (Vector (a, a)) (Maybe a)
  deriving Show

emptyV :: Vector a
emptyV = Nil

lengthV :: Vector a -> Int
lengthV = \case
  Nil      -> 0
  Snoc v m -> 2 * lengthV v + maybe 0 (const 1) m

snoc :: Vector a -> a -> Vector a
snoc v a = case v of
  Nil             -> Snoc Nil (Just a)
  Snoc v Nothing  -> Snoc v (Just a)
  Snoc v (Just e) -> Snoc (snoc v (e, a)) Nothing

listToVec :: [a] -> Vector a
listToVec as = foldr (flip snoc) emptyV (reverse as)

-- Lens style getter/setter for Vector
updateA :: Alternative m => Int -> (a -> m a) -> Vector a -> m (Vector a)
updateA i f v = case v of

  Nil -> empty

  Snoc v Nothing ->
    Snoc <$> updateA (i `div` 2) (\(x, y) -> if even i then (,) x <$> f y else (,) <$> f x <*> pure y) v <*> pure Nothing

  Snoc v (Just e)
    | i == 0 -> Snoc v . Just <$> f e
    | i >  0 ->
       Snoc <$> updateA (i' `div` 2) (\(x, y) -> if even i' then (,) x <$> f y else (,) <$> f x <*> pure y) v <*> pure (Just e)
   where
    i' = i-1

data ConstMaybe a b = No | Yes a

instance Functor (ConstMaybe a) where
  fmap f No      = No
  fmap f (Yes a) = Yes a

instance Applicative (ConstMaybe a) where
  pure _ = No

  Yes f <*> _ = Yes f
  No    <*> _ = No

instance Alternative (ConstMaybe a) where
  empty = No

  No <|> m = m
  m  <|> _ = m

getYes (Yes x) = Just x
getYes _  = Nothing

lookupV :: Int -> Vector a -> Maybe a
lookupV i v = getYes (updateA i Yes v)

updateV :: Int -> a -> Vector a -> Maybe (Vector a)
updateV i a v = updateA i (\_ -> Just a) v
