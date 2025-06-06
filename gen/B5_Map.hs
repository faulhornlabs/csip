
{-# LINE 1 "src/B5_Map.hs" #-}
module B5_Map
  ( Map, emptyMap, insertMap, lookupMap
  , IntMap, emptyIM, insertIM, lookupIM, fromListIM, deleteIM
  , IntSet, emptyIS, insertIS, memberIS, deleteIS
  , BitSet, singletonBS, toListBS, memberBS
  , walkIM, downUpIM
  , StringMap, lookupSM, insertSM, deleteSM, newStringMap, topStringMap
  ) where

import B0_Builtins
import B1_Basic
import B2_String
import B3_Mem

---------- Maps   -- TODO: remove

data Colour = R | B

data Map a b = E | N Colour (Map a b) a b (Map a b)

emptyMap = E

lookupMap :: Ord a => a -> Map a b -> Maybe b
lookupMap a = \case
  E                   -> Nothing
  N _ l b _ r | a < b -> lookupMap a l
              | b < a -> lookupMap a r
  N _ _ _ c _         -> Just c

insertMap :: Ord a => a -> b -> Map a b -> Map a b
insertMap a a' t  =  blacken (f t) where
  f (N c l b b' r)
      | a < b      =  n c (f l) b b' r
      | b < a      =  n c l     b b' (f r)
  f (N c l _ _  r) =  n c l     a a' r
  f E              =  n R E     a a' E

  blacken (N _ l a b r) =  N B l a b r
  blacken t = t

  n :: Colour -> Map a b -> a -> b -> Map a b -> Map a b
  n B (N R (N R x a a' y) b b' z) c c' v = N R (N B x a a' y) b b' (N B z c c' v)
  n B (N R x a a' (N R y b b' z)) c c' v = N R (N B x a a' y) b b' (N B z c c' v)
  n B x a a' (N R (N R y b b' z) c c' v) = N R (N B x a a' y) b b' (N B z c c' v)
  n B x a a' (N R y b b' (N R z c c' v)) = N R (N B x a a' y) b b' (N B z c c' v)
  n c l a a' r                           = N c l a a' r


------------------------------------------------ IntMap

half :: Word -> Word
half i = shiftR i 1

data IntMap a b   -- a = key,  b = value
  = Empty
  | Zero a b               -- image of 0
  | Node (IntMap a b) (IntMap a b)  -- (*2), (+1).(*2)

instance Tag (IntMap a b) where
  tag Empty = 0
  tag Zero{} = 1
  tag Node{} = 2

instance Ord b => Ord (IntMap a b) where
  compare (Zero _ b) (Zero _  b') = compare b b'
  compare (Node a b) (Node a' b') = compare a a' &&& lazy (compare b b')
  compare a b = compareTag a b

emptyIM = Empty

instance Functor (IntMap a) where
  _ <$> Empty    = Empty
  f <$> Zero a b = Zero a (f b)
  f <$> Node a b = Node (f <$> a) (f <$> b)

getNode = \case
  n@Empty  -> T2 n n
  n@Zero{} -> T2 n Empty
  Node l r -> T2 l r

pattern ENode l r <- (getNode -> T2 l r)
  where ENode Empty    Empty = Empty
        ENode l@Zero{} Empty = l
        ENode l        r     = Node l r

{-# COMPLETE ENode #-}

lookupIM :: HasId k => k -> IntMap k a -> Maybe a
lookupIM a m = (<$>) snd (lookup (getId a) m)  where
  lookup 0 (Zero a b) = Just (T2 a b)
  lookup i (Node l r) | even i = lookup (half i) l
                      | True   = lookup (half i) r
  lookup _ _ = Nothing

insertIM :: HasId k => k -> a -> IntMap k a -> IntMap k a
insertIM a b m = insert (getId a) a b m  where
  insert 0 x y Empty  = Zero x y
  insert 0 x y Zero{} = Zero x y
  insert i x y (ENode l r) | even i = ENode (insert (half i) x y l) r
                           | True   = ENode l (insert (half i) x y r)

deleteIM :: HasId k => k -> IntMap k a -> IntMap k a
deleteIM a m = delete (getId a) m  where
  delete i (Node l r) | even i = ENode (delete (half i) l) r
                      | True   = ENode l (delete (half i) r)
  delete 0 _ = Empty
  delete _ l = l

fromListIM :: HasId a => List (Tup2 a b) -> IntMap a b
fromListIM = foldl (\m (T2 a b) -> insertIM a b m) Empty


-------------------------------------------------- IntSets

type IntSet a = IntMap a Tup0

emptyIS :: IntSet a
emptyIS = emptyIM

insertIS :: HasId k => k -> IntSet k -> IntSet k
insertIS a m = insertIM a T0 m

memberIS :: HasId a => a -> IntSet a -> Bool
memberIS a m = isJust (lookupIM a m)

deleteIS :: HasId k => k -> IntSet k -> IntSet k
deleteIS = deleteIM


----------------------------------------------- bitset

data BitSet = MkBS Word

instance Semigroup BitSet where
  MkBS a <> MkBS b = MkBS (orWord a b)

instance Monoid BitSet where
  mempty = MkBS 0

singletonBS :: Word -> BitSet
singletonBS i | i < 64 = MkBS $ shiftL 1 i
singletonBS _ = (undefined "src/B5_Map.hs" 142)

memberBS w (MkBS i) | w < 64 = andWord i (shiftL 1 w) /= 0
memberBS _ _ = (undefined "src/B5_Map.hs" 145)

toListBS :: BitSet -> List Word
toListBS (MkBS i) = f 0 i where
  f _ 0 = Nil
  f k i = condCons (not $ even i) k $ f (k+1) (shiftR i 1)

------------------------------------------------- graph algorithms

-- top-down & bottom-up  graph walking;  sharing and cycle friendly
walkIM
  :: HasId a
  => (a -> Mem (Tup2 b (List a)))              -- down
  -> (a -> b -> Mem b)                -- shared try
  -> (a -> b -> List (Tup2 a b) -> Mem b)
  -> List a
  -> Mem (IntMap a b)
walkIM children  down up xs = snd <$> runState emptyIM go where
  go st = walk (map Left xs)  where
    walk Nil = pure T0
    walk (Left v:. ts) = gets st (lookupIM v) >>= \case
      Nothing -> do
        T2 r ch <- children v
        modify st (insertIM v r)
        walk (map Left ch ++ Right (T2 v ch):. ts)
      Just r -> do
        r' <- down v r
        modify st (insertIM v r')
        walk ts
    walk (Right (T2 e ch):. ts) = do
      m <- gets st (fromMaybe (lazy (impossible "src/B5_Map.hs" 175)) . lookupIM e)
      ms <- forM ch \v -> gets st (fromMaybe (lazy (impossible "src/B5_Map.hs" 176)) . lookupIM v)
      r <- up e m (zipWith T2 ch ms)
      modify st (insertIM e r)
      walk ts

-- does not work with cycles in the graph
downUpIM
  :: HasId a
  => (a -> Mem (Tup2 b (List a)))              -- down
  -> (a -> b -> Mem b)                         -- pre-share
  -> (a -> c -> Mem c)                         -- post-share
  -> (a -> b -> List (Tup2 a c) -> Mem c)      -- up
  -> List a
  -> Mem (IntMap a c)
downUpIM down share1 share2 up as = (g <$>) <$> walkIM down' share up2 as
 where
  down' a = down a <&> first Left

  share v (Left b)  = Left  <$> share1 v b
  share v (Right c) = Right <$> share2 v c

  up2 a (Left b) cs = Right <$> up a b (map (second g) cs)
  up2 _ _ _ = (impossible "src/B5_Map.hs" 198)

  g (Right c) = c
  g _ = (impossible "src/B5_Map.hs" 201)


----------------------------------------------- StringMap

itemsMask = 127 :: Word

hashString' (ConsChar c _cs) = andWord (ord c) itemsMask
hashString' _ = 0

data HItem a
  = NilHM
  | YesHM a
  | ConsHM Char (HItem a) (HItem a)

consHM _ NilHM b = b
consHM c a b = ConsHM c a b

data StringMap a = MkSM (Array (HItem a))

newStringMap :: Mem (StringMap a)
newStringMap = MkSM <$> newArray itemsMask NilHM

topStringMap :: Reset -> (StringMap a -> Mem Tup0) -> StringMap a
topStringMap mr init = topMemReset mr do
  MkSM m <- newStringMap
  init (MkSM m)
  pure $ T2 (MkSM m) do
    forM_ (enumFromTo 0 $ itemsMask + 1) \i -> writeArray m i NilHM
    init (MkSM m)

lookupSM_ :: String -> StringMap a -> Mem (HItem a)
lookupSM_ s (MkSM hm) | h <- hashString' s = readArray hm h <&> f s  where

  f s@NilStr = \case
    ConsHM _ _ t -> f s t
    z -> z
  f s@(ConsChar c cs) = \case
    ConsHM c' a b
      | c' == c -> f cs a
      | True    -> f s b
    _ -> NilHM

lookupSM :: String -> StringMap a -> Mem (Maybe a)
lookupSM s sm = lookupSM_ s sm <&> \case
  YesHM a -> Just a
  NilHM   -> Nothing
  _       -> (impossible "src/B5_Map.hs" 248)

updateSM :: String -> HItem a -> StringMap a -> Mem Tup0
updateSM s x (MkSM hm) | h <- hashString' s = do
    t <- readArray hm h
    writeArray hm h $ ins s t
   where
    ins s@NilStr = \case
      ConsHM c a b -> ConsHM c a (ins s b)
      _ -> x
    ins s@(ConsChar c cs) = \case
      ConsHM c' a b
        | c' == c -> consHM c' (ins cs a) b
        | True    -> ConsHM c' a (ins s b)
      z -> ConsHM c (ins cs NilHM) z

insertSM :: String -> a -> StringMap a -> Mem Tup0
insertSM s a sm = updateSM s (YesHM a) sm

deleteSM :: String -> StringMap a -> Mem Tup0
deleteSM s sm = updateSM s NilHM sm
