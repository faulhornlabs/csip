module B6_IntMap
  ( IntMap, insertIM, lookupIM, fromListIM, toListIM, singletonIM, nullIM, deleteIM, assocsIM, unionWithIM
  , IntSet, insertIS, memberIS, fromListIS, toListIS, singletonIS, nullIS, deleteIS
  , walkIM, downUpIM, topDownIM, bottomUpIM
  ) where

import B0_Builtins
import B1_Basic
import B2_String
import B3_RefM
import B4_Partial

-------------------

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

instance Semigroup (IntMap a b) where
  (<>) = unionWithIM \a _ -> a

instance Monoid (IntMap a b) where
  mempty = Empty

instance Functor (IntMap a) where
  _ <$> Empty    = Empty
  f <$> Zero a b = Zero a (f b)
  f <$> Node a b = Node ((<$>) f a) ((<$>) f b)

nullIM m = case m of
  Empty -> True
  _     -> False

getNode = \case
  n@Empty  -> T2 n n
  n@Zero{} -> T2 n Empty
  Node l r -> T2 l r

pattern ENode l r <- (getNode -> T2 l r)
  where ENode l@Zero{} Empty = l
        ENode Empty    Empty = Empty
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
  delete _ _ = Empty

unionWithIM :: (b -> b -> b) -> IntMap a b -> IntMap a b -> IntMap a b
unionWithIM _ Empty x = x
unionWithIM _ x Empty = x
unionWithIM f (Zero a b)  (Zero _ b')   = Zero a (f b b')
unionWithIM f (ENode l r) (ENode l' r') = Node (unionWithIM f l l') (unionWithIM f r r')

-- TODO: make a variant with no ordering
assocsIM :: IntMap a b -> List (Tup2 a b)
assocsIM = map snd . go (1 :: Word) 0 where
  go _ _ Empty = Nil
  go _ o (Zero a b) = T2 o (T2 a b) :. Nil
  go i o (Node l r) | i' <- shiftL i 1 = merge (go i' o l) (go i' (o+i') r)

  merge Nil xs = xs
  merge xs Nil = xs
  merge (x@(T2 i _):. xs') ys@(T2 j _ :. _)
    | i < j  = x:. merge xs' ys
  merge xs (y:. ys')
    = y:. merge xs ys'

fromListIM :: HasId a => List (Tup2 a b) -> IntMap a b
fromListIM = foldl (\m (T2 a b) -> insertIM a b m) Empty

toListIM :: IntMap a b -> List b
toListIM m = map snd (assocsIM m)

singletonIM a b = insertIM a b Empty


-------------------------------------------------- IntSets

type IntSet a = IntMap a Tup0

insertIS :: HasId k => k -> IntSet k -> IntSet k
insertIS a m = insertIM a T0 m

singletonIS a = singletonIM a T0

nullIS :: IntSet a -> Bool
nullIS = nullIM

memberIS :: HasId a => a -> IntSet a -> Bool
memberIS a m = isJust (lookupIM a m)

deleteIS :: HasId k => k -> IntSet k -> IntSet k
deleteIS = deleteIM

fromListIS :: HasId k => List k -> IntSet k
fromListIS = foldl (\m a -> insertIM a T0 m) Empty

toListIS :: IntSet a -> List a
toListIS m = map fst (assocsIM m)


------------------------------------------------- graph algorithms

-- top-down & bottom-up  graph walking;  sharing and cycle friendly
walkIM
  :: HasId a
  => (a -> RefM (Tup2 b (List a)))              -- down
  -> (a -> b -> RefM b)                -- shared try
  -> (a -> b -> List (Tup2 a b) -> RefM b)
  -> List a
  -> RefM (IntMap a b)
walkIM children  down up xs = (<$>) snd (runState mempty go) where
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
      m <- gets st (fromMaybe (lazy impossible) . lookupIM e)
      ms <- forM ch \v -> gets st (fromMaybe (lazy impossible) . lookupIM v)
      r <- up e m (zip ch ms)
      modify st (insertIM e r)
      walk ts


downUpIM
  :: HasId a
  => (a -> RefM (Tup2 b (List a)))              -- down
  -> (a -> b -> List (Tup2 a c) -> RefM c)
  -> List a
  -> RefM (IntMap a c)
downUpIM down up as = walkIM down' (\_ -> pure) up' as <&> (<$>) g
 where
  down' a = down a <&> first Left
  up' a (Left b) cs = (<$>) Right (up a b (map (second g) cs))
  up' _ _ _ = impossible
  g (Right c) = c
  g _ = impossible

topDownIM
  :: HasId a
  => (a -> RefM (Tup2 b (List a)))
  -> List a
  -> RefM (IntMap a b)
topDownIM down
  = walkIM down (\_ -> pure) (\_ b _ -> pure b)

bottomUpIM
  :: HasId a
  => b
  -> (a -> RefM (List a))
  -> (a -> List (Tup2 a b) -> RefM b)
  -> a
  -> RefM (IntMap a b)
bottomUpIM init children up x
  = walkIM (\v -> T2 init <$> children v) (\_ -> pure) (\a _ b -> up a b) (x :. Nil)
