module M7_Stage
  ( stage
  ) where

import M1_Base
import M3_Parse
import M4_Eval

stage t = quoteNF t <&> unquote

unquote :: Raw -> Raw
unquote = \case
  RVar (MkName "Prod" _) :@ _ :@ _ :@ a :@ b -> "Prod" .@ unquote a .@ unquote b
  RVar (MkName "Pair" _) :@ _ :@ _ :@ a :@ b -> "Pair" .@ unquote a .@ unquote b
  RVar (MkName "Fst" _) :@ _ :@ _ :@ a -> "Fst" .@ unquote a
  RVar (MkName "Snd" _) :@ _ :@ _ :@ a -> "Snd" .@ unquote a
  RVar (MkName "App" _) :@ _ :@ _ :@ a :@ b -> unquote a .@ unquote b
  RVar (MkName "Lam" _) :@ _ :@ _ :@ a -> unquote a
  RVar (MkName "Let" _) :@ _ :@ _ :@ a :@ Lam n b -> rLet n (unquote a) (unquote b)
  a :@ b -> unquote a :@ unquote b
  RVar n -> RVar n
 where
  rLet n (RLet m Hole a b) c = rLet m a (rLet n b c)
  rLet n a b = RLet n Hole a b

--  RLet m Hole b c .@ a = rLet m b (c .@ a)
--  a .@ RLet m Hole b c = rLet m b (a .@ c)
  a .@ b = a :@ b

