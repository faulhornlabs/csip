module M0_Map
  ( Map, insert, empty, fromList, lookup, toList
  ) where

import A_Builtins hiding (lookup)

fromList l = foldr (uncurry insert) empty l

empty = E

----------

data Colour = R | B

data Map a b = E | N Colour (Map a b) a b (Map a b)

instance Functor (Map a) where
  fmap f = \case
    E -> E
    N c l a b r -> N c (fmap f l) a (f b) (fmap f r)

insert :: Ord a => a -> b -> Map a b -> Map a b
insert a a' t  =  blacken (f t) where
    f (N c l b b' r)
        | a <  b    =  n c (f l) b b' r
        | a >  b    =  n c l     b b' (f r)
        | True      =  n c l     a a' r
    f E             =  n R E     a a' E

lookup :: Ord a => a -> Map a b -> Maybe b
lookup a = \case
  E -> Nothing
  N _ l b c r
    | a <  b    -> lookup a l
    | a >  b    -> lookup a r
    | True      -> Just c

blacken (N _ l a b r) =  N B l a b r
blacken t = t

n :: Colour -> Map a b -> a -> b -> Map a b -> Map a b
n B (N R (N R x a a' y) b b' z) c c' v = N R (N B x a a' y) b b' (N B z c c' v)
n B (N R x a a' (N R y b b' z)) c c' v = N R (N B x a a' y) b b' (N B z c c' v)
n B x a a' (N R (N R y b b' z) c c' v) = N R (N B x a a' y) b b' (N B z c c' v)
n B x a a' (N R y b b' (N R z c c' v)) = N R (N B x a a' y) b b' (N B z c c' v)
n c l a a' r                           = N c l a a' r

toList :: Map a b -> [(a, b)]
toList t = f Nil t  where
    f acc E = acc
    f acc (N _ l a b r) = f ((a, b): f acc r) l
