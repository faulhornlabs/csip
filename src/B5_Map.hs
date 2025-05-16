module B5_Map
  ( Map, emptyMap, insertMap, lookupMap
  , walk, downUp, topDown, bottomUp
  ) where

import B1_Basic
import B3_RefM
import B4_Partial

----------

data Colour = R | B

data Map a b = E | N {-# UNPACK #-} Colour (Map a b) a b (Map a b)

instance Functor (Map a) where
  _ <$> E = E
  f <$> N c l a b r = N c ((<$>) f l) a (f b) ((<$>) f r)

insertMap :: Ord a => a -> b -> Map a b -> Map a b
insertMap a a' t  =  blacken (f t) where
  f (N c l b b' r)
      | a <  b     =  n c (f l) b b' r
      | a >  b     =  n c l     b b' (f r)
  f (N c l _ _  r) =  n c l     a a' r
  f E              =  n R E     a a' E

lookupMap :: Ord a => a -> Map a b -> Maybe b
lookupMap a = \case
  E                    -> Nothing
  N _ l b _ r | a <  b -> lookupMap a l
              | a >  b -> lookupMap a r
  N _ _ _ c _          -> Just c

blacken (N _ l a b r) =  N B l a b r
blacken t = t

n :: Colour -> Map a b -> a -> b -> Map a b -> Map a b
n B (N R (N R x a a' y) b b' z) c c' v = N R (N B x a a' y) b b' (N B z c c' v)
n B (N R x a a' (N R y b b' z)) c c' v = N R (N B x a a' y) b b' (N B z c c' v)
n B x a a' (N R (N R y b b' z) c c' v) = N R (N B x a a' y) b b' (N B z c c' v)
n B x a a' (N R y b b' (N R z c c' v)) = N R (N B x a a' y) b b' (N B z c c' v)
n c l a a' r                           = N c l a a' r

emptyMap = E


------------------------------------------------- graph algorithms

-- top-down & bottom-up  graph walking;  sharing and cycle friendly
walk
  :: Ord a
  => (a -> RefM (Tup2 b (List a)))              -- down
  -> (a -> b -> RefM b)                -- shared try
  -> (a -> b -> List (Tup2 a b) -> RefM b)
  -> List a
  -> RefM (Map a b)
walk children  down up xs = (<$>) snd (runState emptyMap go) where
  go st = walk (map Left xs)  where
    walk Nil = pure T0
    walk (Left v:. ts) = gets st (lookupMap v) >>= \case
      Nothing -> do
        T2 r ch <- children v
        modify st (insertMap v r)
        walk (map Left ch ++ Right (T2 v ch) :. ts)
      Just r -> do
        r' <- down v r
        modify st (insertMap v r')
        walk ts
    walk (Right (T2 e ch):. ts) = do
      m <- gets st (fromJust . lookupMap e)
      ms <- forM ch \v -> gets st (fromJust . lookupMap v)
      r <- up e m (zip ch ms)
      modify st (insertMap e r)
      walk ts

downUp
  :: Ord a
  => (a -> RefM (Tup2 b (List a)))              -- down
  -> (a -> b -> List (Tup2 a c) -> RefM c)
  -> List a
  -> RefM (Map a c)
downUp down up as = walk down' (\_ -> pure) up' as <&> (<$>) g
 where
  down' a = down a <&> first Left
  up' a (Left b) cs = (<$>) Right (up a b (map (second g) cs))
  up' _ _ _ = impossible
  g (Right c) = c
  g _ = impossible

topDown
  :: Ord a
  => (a -> RefM (Tup2 b (List a)))
  -> List a
  -> RefM (Map a b)
topDown down
  = walk down (\_ -> pure) (\_ b _ -> pure b)

bottomUp
  :: Ord a
  => b
  -> (a -> RefM (List a))
  -> (a -> List (Tup2 a b) -> RefM b)
  -> a
  -> RefM (Map a b)
bottomUp init children up x
  = walk (\v -> T2 init <$> children v) (\_ -> pure) (\a _ b -> up a b) (x :. Nil)
