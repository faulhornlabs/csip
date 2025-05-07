module C_OpSeq
  ( Precedence
  , OpSeq
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

import B_Prelude

----------------------------------------

type Precedence = Word

data SeqPrec
  = ConsP {-# UNPACK #-} Precedence {-# UNPACK #-} Int SeqPrec
  | NilP
  deriving (Eq, Ord)

singPrec :: Precedence -> SeqPrec
singPrec p = ConsP p 0 NilP

minPrec :: Precedence -> SeqPrec -> SeqPrec
minPrec a NilP = singPrec a
minPrec a (ConsP b b' bs) = case compare a b of
  LT -> singPrec a
  EQ -> ConsP a (b' - 1) NilP
  GT -> ConsP b b' (minPrec a bs)

----------------------------------------

data OpSeq b
  = Empty
  | Node_ ~(Cached SeqPrec)
          (OpSeq b)
          Precedence
          b
          (Enclosed b)
          Precedence
          (OpSeq b)
          ~(Cached SeqPrec)
  deriving (Eq)

data Mid b = MkMid Precedence (OpSeq b) Precedence b
  deriving (Eq)

type Enclosed b = List (Mid b)

----------------------------------------

leftPrecSeq Empty = NilP
leftPrecSeq (Node_ a _ _ _ _ _ _ ~_) = getCached a

rightPrecSeq Empty = NilP
rightPrecSeq (Node_ ~_ _ _ _ _ _ _ a) = getCached a

-- not a proper Ord instance!
instance (Eq b) => Ord (OpSeq b) where
  compare a b = compare (rightPrecSeq a) (leftPrecSeq b)

pattern Node :: OpSeq b -> Precedence -> b -> Enclosed b -> Precedence -> OpSeq b -> OpSeq b
pattern Node a b c d e f <- Node_ ~_ a b c d e f ~_

{-# COMPLETE Node, Empty #-}

mkNode :: OpSeq b -> Precedence -> b -> Enclosed b -> Precedence -> OpSeq b -> OpSeq b
mkNode a b c d e f
  = Node_ (MkCached (b `minPrec` leftPrecSeq a)) a b c d e f (MkCached (e `minPrec` rightPrecSeq f))

singOpSeq :: Tup3 Precedence b Precedence -> OpSeq b
singOpSeq (T3 a b c) = mkNode Empty a b Nil c Empty

instance Semigroup (OpSeq b) where
  Empty <> a = a
  a <> Empty = a
  x <> y = case compare (rightPrecSeq x) (leftPrecSeq y) of
    LT | Node a b c d e f <- x -> mkNode a b c d e (f <> y)
    GT | Node a b c d e f <- y -> mkNode (x <> a) b c d e f
    EQ | Node a b c d e f <- x
       , Node g h i j k l <- y
      -> mkNode a b c (d ++ MkMid e (f <> g) h i :. j) k l

instance Monoid (OpSeq b) where
  mempty = Empty


---------------------------------------- derived

infixr 2 :<, :=, :>

getLeft (Node a b c d e f) = Just (T2 a (mkNode Empty b c d e f))
getLeft _ = Nothing

pattern (:<) :: OpSeq b -> OpSeq b -> OpSeq b
pattern a :< b <- (getLeft -> Just (T2 a b))

getRight (Node Empty _ a Nil _ b) = Just (T2 a b)
getRight _ = Nothing

pattern (:>) :: b -> OpSeq b -> OpSeq b
pattern a :> b <- (getRight -> Just (T2 a b))

getMid (Node Empty _ a (MkMid _ b c d:. e) f g) = Just (T2 a (mkNode b c d e f g))
getMid _ = Nothing

pattern (:=) :: b -> OpSeq b -> OpSeq b
pattern a := b <- (getMid -> Just (T2 a b))

{-# COMPLETE Empty, (:<) #-}

pattern Node2 a b c <- Node a _ b Nil _ c
pattern Node3 a b c d e <- Node a _ b (MkMid _ c _ d :. Nil) _ e

toOpSeq :: List (Tup3 Precedence b Precedence) -> OpSeq b
toOpSeq = foldMap singOpSeq

fromOpSeq :: OpSeq b -> List b
fromOpSeq t = f1 t Nil
 where
  f1 = \case
    Empty  -> id
    a := b -> (a:.) . f1 b
    a :> b -> (a:.) . f1 b
    a :< b -> f1 a . f1 b

mapOpSeq f = comm where
  comm = \case
      a := b -> f a <> comm b
      a :> b -> f a <> comm b
      a :< b -> comm a <> comm b
      Empty -> mempty

topOp :: OpSeq b -> Tup4 (List b) (OpSeq b) (List (OpSeq b)) (OpSeq b)
topOp = \case
  Empty -> T4 Nil Empty Nil Empty
  Node a _ c d _ f -> T4 (c :. (d <&> \(MkMid _ _ _ x) -> x)) a (d <&> \(MkMid _ x _ _) -> x) f

