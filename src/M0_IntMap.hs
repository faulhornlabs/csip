module M0_IntMap
  ( HasId(getId)
  , IntMap, insertIM, lookupIM, fromListIM, toListIM, singletonIM, assocsIM, unionWithIM, nullIM
  , walkIM, downUpIM, topDownIM, bottomUpIM
  , IntSet, singletonIS, memberIS, insertIS, deleteIS, fromListIS, toListIS, nullIS
  , nubIS
  ) where

import B_Prelude hiding (null, toList, fromList)

-------------------

class HasId k where
  getId :: k -> Word

instance HasId Word where
  getId i = i

-------------------

half :: Word -> Word
half i = shiftR i 1

data IntMap a b
    = Empty
    | Zero a b               -- image of 0
    | Node (IntMap a b) (IntMap a b)  -- (*2), (+1).(*2)
    deriving (Eq, Ord)

instance Semigroup (IntMap a b) where
  (<>) = union
instance Monoid (IntMap a b) where
  mempty = Empty
instance Functor (IntMap a) where
  fmap _ Empty = Empty
  fmap f (Zero a b)   = Zero a (f b)
  fmap f (Node a b) = Node (fmap f a) (fmap f b)

singleton i a b = insert i a b Empty

null m = case m of
  Empty -> True
  _     -> False

getNode = \case
    n@Empty -> (n, n)
    n@Zero{} -> (n, Empty)
    Node l r -> (l, r)

pattern ENode l r <- (getNode -> (l, r))
  where ENode l@Zero{} Empty = l
        ENode Empty Empty = Empty
        ENode l r = Node l r

{-# COMPLETE ENode #-}

union :: IntMap a b -> IntMap a b -> IntMap a b
Empty     `union` x           = x
x         `union` Empty       = x
a@Zero{}  `union` Zero{}      = a
ENode l r `union` ENode l' r' = Node (l `union` l') (r `union` r')

unionWith :: (b -> b -> b) -> IntMap a b -> IntMap a b -> IntMap a b
unionWith _ Empty x = x
unionWith _ x Empty = x
unionWith f (Zero a b) (Zero _ b') = Zero a (f b b')
unionWith f (ENode l r) (ENode l' r') = Node (unionWith f l l') (unionWith f r r')

delete :: Word -> IntMap a b -> IntMap a b
delete i (Node l r) | even i = ENode (delete (half i) l) r
delete i (Node l r)          = ENode l (delete (half i) r)
delete _ _ = Empty

insert :: Word -> a -> b -> IntMap a b -> IntMap a b
insert 0 x y Empty = Zero x y
insert 0 x y Zero{} = Zero x y
insert i x y (ENode l r) | even i = ENode (insert (half i) x y l) r
insert i x y (ENode l r)          = ENode l (insert (half i) x y r)

lookup :: Word -> IntMap a b -> Maybe (a, b)
lookup 0 (Zero a b) = Just (a, b)
lookup i (Node l _) | even i = lookup (half i) l
lookup i (Node _ r)          = lookup (half i) r
lookup _ _ = Nothing

toList :: IntMap a b -> List (a, b)
toList = map snd . go (1 :: Word) 0 where
  go _ _ Empty = Nil
  go _ o (Zero a b) = (o, (a, b)) :. Nil
  go i o (Node l r) | i' <- shiftL i 1 = merge (go i' o l) (go i' (o+i') r)

  merge Nil xs = xs
  merge xs Nil = xs
  merge (x@(i, _):. xs') ys@((j, _):. _)
    | i < j  = x:. merge xs' ys
  merge xs (y:. ys')
    = y:. merge xs ys'

fromList :: HasId a => List (a, b) -> IntMap a b
fromList = foldl (\m (a, b) -> insert (getId a) a b m) Empty



-------------------------------------------------- IntMaps

insertIM :: HasId k => k -> a -> IntMap k a -> IntMap k a
insertIM a b m = insert (getId a) a b m

deleteIM :: HasId k => k -> IntMap k a -> IntMap k a
deleteIM a m = delete (getId a) m

lookupIM :: HasId k => k -> IntMap k a -> Maybe a
lookupIM a m = fmap snd (lookup (getId a) m)

memberIM :: HasId k => k -> IntMap k a -> Bool
memberIM a m = isJust (lookup (getId a) m)

fromListIM :: HasId k => List (k, a) -> IntMap k a
fromListIM xs = (fromList xs)

assocsIM :: IntMap a b -> List (a, b)
assocsIM m = toList m

toListIM :: IntMap a b -> List b
toListIM m = map snd (assocsIM m)

keysIM :: IntMap a b -> List a
keysIM m = map fst (assocsIM m)

singletonIM a b = singleton (getId a) a b

nullIM m = null m

unionWithIM :: HasId a => (b -> b -> b) -> IntMap a b -> IntMap a b -> IntMap a b
unionWithIM = unionWith

-----

type IntSet a = IntMap a ()

insertIS :: HasId k => k -> IntSet k -> IntSet k
insertIS a m = insertIM a () m

singletonIS a = singletonIM a ()

nullIS :: IntSet a -> Bool
nullIS = nullIM

memberIS :: HasId a => a -> IntSet a -> Bool
memberIS = memberIM

deleteIS :: HasId k => k -> IntSet k -> IntSet k
deleteIS = deleteIM

fromListIS :: HasId k => List k -> IntSet k
fromListIS = foldl (\m a -> insert (getId a) a () m) Empty

toListIS :: IntSet a -> List a
toListIS = keysIM

nubIS :: HasId a => List a -> List a
nubIS = f mempty  where
  f _ Nil = Nil
  f s (x:. xs)
    | memberIS x s = f s xs
  f s (x:. xs)
    = x:. f (insertIS x s) xs


------------------------------------------------- graph algorithms

-- top-down & bottom-up  graph walking;  sharing and cycle friendly
walkIM
  :: HasId a
  => (a -> RefM (b, List a))              -- down
  -> (a -> b -> RefM b)                -- shared try
  -> (a -> b -> List (a, b) -> RefM b)
  -> List a
  -> RefM (IntMap a b)
walkIM children  down up xs = fmap snd (runState mempty go) where
  go st = walk (map Left xs)  where
    walk Nil = pure ()
    walk (Left v:. ts) = gets st (lookupIM v) >>= \case
      Nothing -> do
        (r, ch) <- children v
        modify st (insertIM v r)
        walk (map Left ch ++ Right (v, ch):. ts)
      Just r -> do
        r' <- down v r
        modify st (insertIM v r')
        walk ts
    walk (Right (e, ch):. ts) = do
      m <- gets st (fromMaybe impossible . lookupIM e)
      ms <- forM ch \v -> gets st (fromMaybe impossible . lookupIM v)
      r <- up e m (zip ch ms)
      modify st (insertIM e r)
      walk ts


downUpIM
  :: HasId a
  => (a -> RefM (b, List a))              -- down
  -> (a -> b -> List (a, c) -> RefM c)
  -> List a
  -> RefM (IntMap a c)
downUpIM down up as = walkIM down' (\_ -> pure) up' as <&> fmap g
 where
  down' a = down a <&> first Left
  up' a (Left b) cs = fmap Right (up a b (map (second g) cs))
  up' _ _ _ = impossible
  g (Right c) = c
  g _ = impossible

topDownIM
  :: HasId a
  => (a -> RefM (b, List a))
  -> List a
  -> RefM (IntMap a b)
topDownIM down
  = walkIM down (\_ -> pure) (\_ b _ -> pure b)

bottomUpIM
  :: HasId a
  => b
  -> (a -> RefM (List a))
  -> (a -> List (a, b) -> RefM b)
  -> a
  -> RefM (IntMap a b)
bottomUpIM init children up x
  = walkIM (\v -> (,) init <$> children v) (\_ -> pure) (\a _ b -> up a b) (x :. Nil)


