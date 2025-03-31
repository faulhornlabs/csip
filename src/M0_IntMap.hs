module M0_IntMap
  ( IntMap
  , delete, insert, lookup
  , member
  , null
  , fromList
  , elems
  , toList
  , singleton
  , unionWith
  ) where

import A_Builtins hiding (lookup, null)

half :: Int -> Int
half i = wordToInt (shiftR (intToWord i) 1)

data IntMap a
    = Empty
    | Zero a                -- image of 0
    | Node (IntMap a) (IntMap a)  -- (*2), (+1).(*2)
    deriving (Eq, Ord)

instance Show a => Show (IntMap a) where
  show = ("fromList " <>) . show . toList

instance Semigroup (IntMap a) where
  (<>) = union
instance Monoid (IntMap a) where
  mempty = Empty
instance Functor IntMap where
  fmap _ Empty = Empty
  fmap f (Zero a)   = Zero (f a)
  fmap f (Node a b) = Node (fmap f a) (fmap f b)

singleton i a = insert i a Empty

member i m = isJust $ lookup i m

null m = case m of
  Empty -> True
  _     -> False

getNode = \case
    Empty -> (Empty, Empty)
    Zero a -> (Zero a, Empty)
    Node l r -> (l, r)

pattern ENode l r <- (getNode -> (l, r))
  where ENode l@Zero{} Empty = l
        ENode Empty Empty = Empty
        ENode l r = Node l r

{-# COMPLETE ENode #-}

union :: IntMap a -> IntMap a -> IntMap a
Empty     `union` x           = x
x         `union` Empty       = x
a@Zero{}  `union` Zero{}      = a
ENode l r `union` ENode l' r' = Node (l `union` l') (r `union` r')

unionWith :: (a -> a -> a) -> IntMap a -> IntMap a -> IntMap a
unionWith _ Empty x = x
unionWith _ x Empty = x
unionWith f (Zero a) (Zero b) = Zero (f a b)
unionWith f (ENode l r) (ENode l' r') = Node (unionWith f l l') (unionWith f r r')

delete :: Int -> IntMap a -> IntMap a
delete i (Node l r)
  | even i    = ENode (delete (half i) l) r
  | True      = ENode l (delete (half i) r)
delete _ _ = Empty

insert :: Int -> a -> IntMap a -> IntMap a
insert 0 x Empty = Zero x
insert 0 x Zero{} = Zero x
insert i x (ENode l r)
  | even i    = ENode (insert (half i) x l) r
  | True      = ENode l (insert (half i) x r)

lookup :: Int -> IntMap a -> Maybe a
lookup 0 (Zero a) = Just a
lookup i (Node l r)
  | even i    = lookup (half i) l
  | True      = lookup (half i) r
lookup _ _ = Nothing

toList :: IntMap a -> List (Int, a)
toList = go 1 0 where
  go :: Int -> Int -> IntMap a -> List (Int, a)
  go _ o (Zero a) = (o, a): Nil
  go _ _ Empty = Nil
  go i o (Node l r) | i' <- shiftL i 1
    = merge (go i' o l) (go i' (o + i) r)

  merge Nil xs = xs
  merge xs Nil = xs
  merge xs@(x@(i, _): xs') ys@(y@(j, _): ys')
    | i < j     = x: merge xs' ys
    | True      = y: merge xs ys'

elems = map snd . toList

fromList :: List (Int, a) -> IntMap a
fromList = foldl (\m (i, a) -> insert i a m) Empty
