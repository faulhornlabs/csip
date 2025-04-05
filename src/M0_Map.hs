module M0_Map
  ( Map, insert, emptyMap, fromListMap, lookupMap, assocsMap
  , sort
  , walk, downUp, topDown, bottomUp
  ) where

import B_Prelude

fromListMap l = foldr (uncurry insert) emptyMap l

emptyMap = E

----------

data Colour = R | B

data Map a b = E | N {-# UNPACK #-} Colour (Map a b) a b (Map a b)

instance Functor (Map a) where
  fmap f = \case
    E -> E
    N c l a b r -> N c (fmap f l) a (f b) (fmap f r)

insert :: Ord a => a -> b -> Map a b -> Map a b
insert a a' t  =  blacken (f t) where
    f (N c l b b' r)
        | a <  b    =  n c (f l) b b' r
        | a >  b    =  n c l     b b' (f r)
    f (N c l _ _  r)
                    =  n c l     a a' r
    f E             =  n R E     a a' E

lookupMap :: Ord a => a -> Map a b -> Maybe b
lookupMap a = \case
  E -> Nothing
  N _ l b _ r
    | a <  b    -> lookupMap a l
    | a >  b    -> lookupMap a r
  N _ _ _ c _   -> Just c

blacken (N _ l a b r) =  N B l a b r
blacken t = t

n :: Colour -> Map a b -> a -> b -> Map a b -> Map a b
n B (N R (N R x a a' y) b b' z) c c' v = N R (N B x a a' y) b b' (N B z c c' v)
n B (N R x a a' (N R y b b' z)) c c' v = N R (N B x a a' y) b b' (N B z c c' v)
n B x a a' (N R (N R y b b' z) c c' v) = N R (N B x a a' y) b b' (N B z c c' v)
n B x a a' (N R y b b' (N R z c c' v)) = N R (N B x a a' y) b b' (N B z c c' v)
n c l a a' r                           = N c l a a' r

assocsMap :: Map a b -> List (a, b)
assocsMap t = f Nil t  where
    f acc E = acc
    f acc (N _ l a b r) = f ((a, b):. f acc r) l


sort = map fst . assocsMap . fromListMap . map (\a -> (a, ()))


------------------------------------------------- graph algorithms

-- top-down & bottom-up  graph walking;  sharing and cycle friendly
walk
  :: Ord a
  => (a -> RefM (b, List a))              -- down
  -> (a -> b -> RefM b)                -- shared try
  -> (a -> b -> List (a, b) -> RefM b)
  -> List a
  -> RefM (Map a b)
walk children  down up xs = fmap snd (runState emptyMap go) where
  go st = walk (map Left xs)  where
    walk Nil = pure ()
    walk (Left v:. ts) = gets st (lookupMap v) >>= \case
      Nothing -> do
        (r, ch) <- children v
        modify st (insert v r)
        walk (map Left ch ++ Right (v, ch):. ts)
      Just r -> do
        r' <- down v r
        modify st (insert v r')
        walk ts
    walk (Right (e, ch):. ts) = do
      m <- gets st (fromJust . lookupMap e)
      ms <- forM ch \v -> gets st (fromJust . lookupMap v)
      r <- up e m (zip ch ms)
      modify st (insert e r)
      walk ts

downUp
  :: Ord a
  => (a -> RefM (b, List a))              -- down
  -> (a -> b -> List (a, c) -> RefM c)
  -> List a
  -> RefM (Map a c)
downUp down up as = walk down' (\_ -> pure) up' as <&> fmap g
 where
  down' a = down a <&> first Left
  up' a (Left b) cs = fmap Right (up a b (map (second g) cs))
  up' _ _ _ = impossible
  g (Right c) = c
  g _ = impossible

topDown
  :: Ord a
  => (a -> RefM (b, List a))
  -> List a
  -> RefM (Map a b)
topDown down
  = walk down (\_ -> pure) (\_ b _ -> pure b)

bottomUp
  :: Ord a
  => b
  -> (a -> RefM (List a))
  -> (a -> List (a, b) -> RefM b)
  -> a
  -> RefM (Map a b)
bottomUp init children up x
  = walk (\v -> (,) init <$> children v) (\_ -> pure) (\a _ b -> up a b) (x :. Nil)

