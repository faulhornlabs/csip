module B8_OpSeq
  ( Precedence, Precedences (MkPrecedences), HasPrecedences (precedences), leftPrec, rightPrec
  , OpSeq (Empty, Node2, Node3), singOpSeq
  , foldMapOpSeq, foldMapTopOp, filterOpSeq
  ) where

import B0_Builtins
import B1_Basic
import B2_String
import B3_Mem

----------------------------------------

type Precedence = Word

data Precedences = MkPrecedences Precedence Precedence   -- left and right precedence

class HasPrecedences a where
  precedences :: a -> Precedences

instance HasPrecedences Precedences where precedences p = p

leftPrec  (precedences -> MkPrecedences p _) = p
rightPrec (precedences -> MkPrecedences _ p) = p

----------------------------------------

data SeqPrec = NilP | ConsP Precedence Word SeqPrec

instance Tag SeqPrec where
  tag ConsP{} = 0
  tag NilP    = 1

instance Ord SeqPrec where
  compare (ConsP a b c) (ConsP a' b' c') = compare a a' &&& lazy (compare b' b &&& lazy (compare c c'))
  compare a b = compareTag a b

singPrec :: Precedence -> SeqPrec
singPrec p = ConsP p 0 NilP

minPrec :: Precedence -> SeqPrec -> SeqPrec
minPrec a NilP = singPrec a
minPrec a (ConsP b b' bs) = case compare a b of
  LT -> singPrec a
  EQ -> ConsP a (b' + 1) NilP
  GT -> ConsP b b' (minPrec a bs)

----------------------------------------

data OpSeq b
  = Empty
  | Node2_ SeqPrec (OpSeq b) b (OpSeq b) SeqPrec
  | Node3_ SeqPrec (OpSeq b) b (OpSeq b) b (OpSeq b) SeqPrec

pattern Node2 a b c     <- Node2_ _ a b c _
pattern Node3 a b c d e <- Node3_ _ a b c d e _

{-# COMPLETE Empty, Node2, Node3 #-}

leftPrecSeq Empty = NilP
leftPrecSeq (Node2_ a _ _     _ _) = a
leftPrecSeq (Node3_ a _ _ _ _ _ _) = a

rightPrecSeq Empty = NilP
rightPrecSeq (Node2_ _ _ _     _ a) = a
rightPrecSeq (Node3_ _ _ _ _ _ _ a) = a

-- not a proper Ord instance!
instance Ord (OpSeq b) where
  compare a b = compare (rightPrecSeq a) (leftPrecSeq b)

singOpSeq :: HasPrecedences b => b -> OpSeq b
singOpSeq b@(precedences -> MkPrecedences l r) = Node2_ (singPrec l) Empty b Empty (singPrec r)

instance HasPrecedences b => Semigroup (OpSeq b) where
  Empty <> a = a
  a <> Empty = a
  x@(Node2_ ll l a     r _) <> y | x < y, z <- r <> y = Node2_ ll l a     z (rightPrec a `minPrec` rightPrecSeq z)
  x@(Node3_ ll l a m b r _) <> y | x < y, z <- r <> y = Node3_ ll l a m b z (rightPrec b `minPrec` rightPrecSeq z)
  x <> y@(Node2_ _ l a     r rr) | x > y, z <- x <> l = Node2_ (leftPrec a `minPrec` leftPrecSeq z) z a     r rr
  x <> y@(Node3_ _ l a m b r rr) | x > y, z <- x <> l = Node3_ (leftPrec a `minPrec` leftPrecSeq z) z a m b r rr
  x@(Node2_ ll l a ml _) <> y@(Node2_ _ mr b r rr) | x == y = Node3_ ll l a (ml <> mr) b r rr
  _ <> _ = $impossible

instance HasPrecedences b => Monoid (OpSeq b) where
  mempty = Empty


---------------------------------------- derived

foldMapTopOp :: Monoid m => (a -> m) -> (OpSeq a -> m) -> OpSeq a -> m
foldMapTopOp fx gx = \case
  Empty  -> mempty
  Node2 l a r     -> gx l <> fx a <> gx r
  Node3 l a m b r -> gx l <> fx a <> gx m <> fx b <> gx r

foldMapOpSeq :: Monoid m => (a -> m) -> OpSeq a -> m
foldMapOpSeq fx = foldMapTopOp fx (foldMapOpSeq fx)

filterOpSeq :: HasPrecedences a => (a -> Bool) -> OpSeq a -> OpSeq a
filterOpSeq p = foldMapOpSeq c where
  c s | p s = singOpSeq s
  c _ = mempty
