module M7_Stage
  ( stage
  ) where

import M1_Base
import M3_Parse
import M4_Eval

stage t = quoteNF t <&> unquote

unquote :: Raw -> Raw
unquote = f []
 where
  f e = \case
    RVar (MkName "Prod" _) :@ _ :@ _ :@ a :@ b -> "Prod" .@ f e a .@ f e b
    RVar (MkName "Pair" _) :@ _ :@ _ :@ a :@ b -> "Pair" .@ f e a .@ f e b
    RVar (MkName "Fst" _) :@ _ :@ _ :@ a -> "Fst" .@ f e a
    RVar (MkName "Snd" _) :@ _ :@ _ :@ a -> "Snd" .@ f e a
    RVar (MkName "App" _) :@ _ :@ _ :@ a :@ b -> f e a .@ f e b
    RVar (MkName "Lam" _) :@ _ :@ _ :@ a -> f e a
    RVar (MkName "Let" _) :@ _ :@ _ :@ RVar a :@ Lam n b | isVarName a -> f ((n, a): e) b
    RVar (MkName "Let" _) :@ _ :@ _ :@ a :@ Lam n b -> rLet n (f e a) (f e b)
    a :@ b -> f e a :@ f e b
    RVar n -> RVar $ fromMaybe n $ lookupList n e

  rLet n (RLet m Hole a b) c = rLet m a (rLet n b c)
  rLet n a b = RLet n Hole a b

  RLet m Hole b c .@ a = rLet m b (c .@ a)
  a .@ RLet m Hole b c = rLet m b (a .@ c)
  a .@ b = a :@ b

