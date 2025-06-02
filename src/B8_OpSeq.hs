module B8_OpSeq
  ( Precedence, Precedences (MkPrecedences), leftPrec, rightPrec, HasPrecedences(..)
  , OpSeq
    ( Empty
    , Node2, Node3, (:<), (:=), (:>)
    )
  , singOpSeq
  , topOp
  , foldMapOpSeq, filterOpSeq
  ) where

import B0_Builtins
import B1_Basic

----------------------------------------

type Precedence = Word

data Precedences = MkPrecedences Precedence Precedence   -- left and right precedence

leftPrec  (MkPrecedences p _) = p
rightPrec (MkPrecedences _ p) = p

instance Ord Precedences where
  MkPrecedences a b `compare` MkPrecedences a' b' = compare a a' &&& lazy (compare b b')

class HasPrecedences a where
  precedences :: a -> Precedences



data SeqPrec
  = ConsP Precedence Word SeqPrec
  | NilP

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
  | Node SeqPrec
         (OpSeq b)
         Precedence
         b
         (Mid b)
         Precedence
         (OpSeq b)
         SeqPrec

data Mid b
  = MCons Precedence (OpSeq b) Precedence b (Mid b)
  | MNil

instance Semigroup (Mid b) where
  MNil            <> ms = ms
  MCons a b c d e <> ms = MCons a b c d (e <> ms)

----------------------------------------

leftPrecSeq Empty = NilP
leftPrecSeq (Node a _ _ _ _ _ _ _) = a

rightPrecSeq Empty = NilP
rightPrecSeq (Node _ _ _ _ _ _ _ a) = a

-- not a proper Ord instance!
instance Ord (OpSeq b) where
  compare a b = compare (rightPrecSeq a) (leftPrecSeq b)

mkNodeL l a b c d e f   = Node l a b c d e f (e `minPrec` rightPrecSeq f)
mkNodeR   a b c d e f r = Node (b `minPrec`  leftPrecSeq a) a b c d e f r

singOpSeq :: HasPrecedences b => b -> OpSeq b
singOpSeq b@(precedences -> MkPrecedences l r) = Node (singPrec l) Empty l b MNil r Empty (singPrec r)

instance Semigroup (OpSeq b) where
  Empty <> a = a
  a <> Empty = a
  x@(Node le a b c d e f _) <> y@(Node _ g h i j k l r) = case compare (rightPrecSeq x) (leftPrecSeq y) of
    LT -> mkNodeL le a b c d e (f <> y)
    EQ -> Node le a b c (d <> MCons e (f <> g) h i j) k l r
    GT -> mkNodeR (x <> g) h i j k l r

instance Monoid (OpSeq b) where
  mempty = Empty


---------------------------------------- derived

infixr 2 :<, :=, :>

getLeft (Node _ a b c d e f r) = Just (T2 a (mkNodeR Empty b c d e f r))
getLeft _ = Nothing

pattern (:<) :: OpSeq b -> OpSeq b -> OpSeq b
pattern a :< b <- (getLeft -> Just (T2 a b))

getRight (Node _ Empty _ a MNil _ b _) = Just (T2 a b)
getRight _ = Nothing

pattern (:>) :: b -> OpSeq b -> OpSeq b
pattern a :> b <- (getRight -> Just (T2 a b))

getMid (Node _ Empty _ a (MCons _ b c d e) f g r) = Just (T2 a (mkNodeR b c d e f g r))
getMid _ = Nothing

pattern (:=) :: b -> OpSeq b -> OpSeq b
pattern a := b <- (getMid -> Just (T2 a b))

{-# COMPLETE Empty, (:<) #-}

pattern Node2 a b c <- Node _ a _ b MNil _ c _
pattern Node3 a b c d e <- Node _ a _ b (MCons _ c _ d MNil) _ e _

foldMapOpSeq :: Monoid m => (a -> m) -> OpSeq a -> m
foldMapOpSeq fx s = f s
 where
  f = \case
    Empty  -> mempty
    Node _ l _ a os _ r _ -> f l <> fx a <> g os <> f r
  g = \case
    MNil -> mempty
    MCons _ os _ a ms -> f os <> fx a <> g ms

filterOpSeq :: HasPrecedences a => (a -> Bool) -> OpSeq a -> OpSeq a
filterOpSeq p = foldMapOpSeq c where
  c s | p s = singOpSeq s
  c _ = mempty

topOp :: OpSeq b -> Tup4 (List b) (OpSeq b) (List (OpSeq b)) (OpSeq b)
topOp = \case
  Empty -> T4 Nil Empty Nil Empty
  Node _ a _ c d _ f _ -> T4 (c :. h d) a (g d) f
 where
  h (MCons _ _ _ x ms) = x :. h ms
  h MNil = Nil

  g (MCons _ x _ _ ms) = x :. g ms
  g MNil = Nil

