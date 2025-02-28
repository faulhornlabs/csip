module M7_Stage
  ( stage
  , convert
  ) where

import M1_Base
import M3_Parse hiding (Lam)
import qualified M3_Parse as E
import M4_Eval hiding (Con)

stage t = quoteNF t <&> unquote

unquote :: Raw -> Raw
unquote = f mempty
 where
  f e = \case
    RVar "Prod" :@ _ :@ _ :@ a :@ b -> "Prod" .@ f e a .@ f e b
    RVar "Pair" :@ _ :@ _ :@ a :@ b -> "Pair" .@ f e a .@ f e b
    RVar "Fst"  :@ _ :@ _ :@ a -> "Fst" .@ f e a
    RVar "Snd"  :@ _ :@ _ :@ a -> "Snd" .@ f e a
    RVar "App" :@ _ :@ _ :@ a -> f e a
--    RVar "App" :@ _ :@ _ :@ a :@ b -> f e a .@ f e b
    RVar "Lam" :@ _ :@ _ :@ a -> f e a
    RVar "TopLet" :@ _ :@ _ :@ RVar n :@ RVar a :@ b | isVarName a -> f (insert n a e) b
    RVar "TopLet" :@ _ :@ _ :@ RVar n :@ a      :@ b -> rLet n (f e a) (f e b)
    RVar "Let"    :@ _ :@ _ :@ RVar a :@ E.Lam n b | isVarName a -> f (insert n a e) b
    RVar "Let"    :@ _ :@ _ :@      a :@ E.Lam n b -> rLet n (f e a) (f e b)
    E.Lam n a -> E.Lam n $ f e a
    a :@ b -> f e a .@ f e b
    RVar n -> RVar $ fromMaybe n $ lookup n e

  rLet n (RLet m Hole a b) c = rLet m a (rLet n b c)
  rLet n a b = RLet n Hole a b

--  RLet m Hole b c .@ a = rLet m b (c .@ a)
--  a .@ RLet m Hole b c = rLet m b (a .@ c)
  a .@ b = a :@ b

--------------------------------- priting for backends in Haskell

data HName
  = Builtin String        -- the String is globally unique
  | UserName String Int
  deriving Show

data Exp
  = Lam HName Exp
  | Let HName Exp Exp
  | App Exp Exp
  | Var HName
  | Con HName
  | String String
  | Nat Integer
  deriving Show

convert :: Raw -> Exp
convert = f  where
  f = \case
    E.Lam n e -> Lam (g n) $ f e
    RLet n Hole a b -> Let (g n) (f a) (f b)
    a :@ b -> App (f a) (f b)
    RVar (NNat n)    -> Nat n
    RVar (NString s) -> String s
    RVar n -> case n of
      m | isConName m -> Con $ g n
      _ -> Var $ g n

  g :: Name -> HName
  g n = case nameId n of
    i | i < 0     -> Builtin s
      | otherwise -> UserName s i
   where
    s = chars $ showMixfix $ nameStr n
