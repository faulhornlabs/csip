module M2_OpSeq
  ( OpSeq
    ( Empty, Node
    , Node2, Node3, (:<), (:=), (:>)   -- derived
    )
  , singOpSeq

  -- derived
  , toOpSeq
  , fromOpSeq
  , mapOpSeq
  , topOp
  ) where

import M1_Base

----------------------------------------

newtype SeqPrec a = MkPrec [(a, Int)]
  deriving (Eq, Show)

instance Ord a => Ord (SeqPrec a) where
  _              <= MkPrec [] = True
  MkPrec []      <= _         = False
  MkPrec (a: as) <= MkPrec (b: bs)
    = a < b || a == b && MkPrec as <= MkPrec bs

singPrec :: a -> SeqPrec a
singPrec p = MkPrec [(p, -1)]

minPrec :: Ord a => a -> SeqPrec a -> SeqPrec a
minPrec a (MkPrec []) = singPrec a
minPrec a (MkPrec (b: bs)) = case compare a (fst b) of
  LT -> singPrec a
  EQ -> MkPrec [(a, snd b - 1)]
  GT | MkPrec bs' <- minPrec a (MkPrec bs) -> MkPrec (b: bs')

----------------------------------------

data OpSeq a b
  = Empty
  | Node_ ~(Cached (SeqPrec a))
          (OpSeq a b)
          a
          b
          (Enclosed a b)
          a
          (OpSeq a b)
          ~(Cached (SeqPrec a))
  deriving (Eq)

data Mid a b = MkMid !a !(OpSeq a b) !a !b
  deriving (Eq)

type Enclosed a b = [Mid a b]

----------------------------------------

leftPrecSeq Empty = MkPrec []
leftPrecSeq (Node_ a _ _ _ _ _ _ ~_) = getCached a

rightPrecSeq Empty = MkPrec []
rightPrecSeq (Node_ ~_ _ _ _ _ _ _ a) = getCached a

-- not a proper Ord instance!
instance (Ord a, Eq b) => Ord (OpSeq a b) where
  compare a b = compare (rightPrecSeq a) (leftPrecSeq b)

  a < b = compare a b == LT
  a > b = compare a b == GT
  a <= b = not $ a > b
  a >= b = not $ a < b
  max = undefined
  min = undefined

pattern Node :: OpSeq a b -> a -> b -> Enclosed a b -> a -> OpSeq a b -> OpSeq a b
pattern Node a b c d e f <- Node_ ~_ a b c d e f ~_

{-# COMPLETE Node, Empty #-}

mkNode :: Ord a => OpSeq a b -> a -> b -> Enclosed a b -> a -> OpSeq a b -> OpSeq a b
mkNode a b c d e f
  = Node_ (MkCached (b `minPrec` leftPrecSeq a)) a b c d e f (MkCached (e `minPrec` rightPrecSeq f))

singOpSeq :: Ord a => (a, b, a) -> OpSeq a b
singOpSeq (a, b, c) = mkNode Empty a b [] c Empty

instance (Ord a) => Semigroup (OpSeq a b) where
  Empty <> a = a
  a <> Empty = a
  x <> y = case compare (rightPrecSeq x) (leftPrecSeq y) of
    LT | Node a b c d e f <- x -> mkNode a b c d e (f <> y)
    GT | Node a b c d e f <- y -> mkNode (x <> a) b c d e f
    EQ | Node a b c d e f <- x
       , Node g h i j k l <- y
      -> mkNode a b c (d <> [MkMid e (f <> g) h i] <> j) k l

instance (Ord a) => Monoid (OpSeq a b) where
  mempty = Empty


---------------------------------------- derived

infixr 2 :<, :=, :>

getLeft (Node a b c d e f) = Just (a, mkNode Empty b c d e f)
getLeft _ = Nothing

pattern (:<) :: Ord a => OpSeq a b -> OpSeq a b -> OpSeq a b
pattern a :< b <- (getLeft -> Just (a, b))

getRight (Node Empty _ a [] _ b) = Just (a, b)
getRight _ = Nothing

pattern (:>) :: b -> OpSeq a b -> OpSeq a b
pattern a :> b <- (getRight -> Just (a, b))

getMid (Node Empty _ a (MkMid _ b c d: e) f g) = Just (a, mkNode b c d e f g)
getMid _ = Nothing

pattern (:=) :: Ord a => b -> OpSeq a b -> OpSeq a b
pattern a := b <- (getMid -> Just (a, b))

{-# COMPLETE Empty, (:<) #-}

pattern Node2 a b c <- Node a _ b [] _ c
pattern Node3 a b c d e <- Node a _ b [MkMid _ c _ d] _ e

toOpSeq :: (Ord a) => [(a, b, a)] -> OpSeq a b
toOpSeq = foldMap singOpSeq

fromOpSeq :: Ord a => OpSeq a b -> [b]
fromOpSeq t = f1 t []
 where
  f1 = \case
    Empty  -> id
    a := b -> (a:) . f1 b
    a :> b -> (a:) . f1 b
    a :< b -> f1 a . f1 b

mapOpSeq f = comm where
  comm = \case
      a := b -> f a <> comm b
      a :> b -> f a <> comm b
      a :< b -> comm a <> comm b
      Empty -> mempty

topOp :: Ord a => OpSeq a b -> ([b], OpSeq a b, [OpSeq a b], OpSeq a b)
topOp = \case
  Empty -> ([], Empty, [], Empty)
  Node a _ c d _ f -> (c : [x | MkMid _ _ _ x <- d], a, [x | MkMid _ x _ _ <- d], f)

