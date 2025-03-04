module M7_Stage
  ( stage
  , stageHaskell
  ) where

import M1_Base
import M3_Parse hiding (Lam)
import qualified M3_Parse as E
import M4_Eval hiding (name, TVar, TApp)

stage_ :: Val -> RefM (Raw, [(Name, Raw)])
stage_ t = do
  (r, m) <- quoteNF t
  pure (unquote r, [(n, t) | (n, r) <- assocs m, Just t <- [unquoteTy r]])

stage :: Val -> RefM Raw --, [(Name, Raw)
stage t = stage_ t <&> \(a, ds) -> foldr (\(n, t) -> RLetTy n t) a ds

stageHaskell v = do
  (r, ts) <- stage_ v
  pure $ (fromString :: String -> Source) $ show ({- map data2 $ -} groupData $ map (name *** convertTy) ts, convert r)

unquoteTy :: Raw -> Maybe Raw
unquoteTy = f where
  f :: Raw -> Maybe Raw
  f r = case r of
    RVar "Ty" -> Just r
    RVar "String" -> Just r
    RVar "Nat" -> Just r
    RVar "Code" :@ r -> Just r
    RVar "Pi"  :@ a :@ E.Lam _n e -> f a >>= \fa -> f e <&> \fe -> RVar "Pi" :@ fa :@ E.Lam "_" fe
    RVar "HPi" :@ a :@ E.Lam  n e -> f a >>= \fa -> f e <&> \fe -> RVar "HPi" :@ fa :@ E.Lam n fe
    a :@ b -> (:@) <$> f a <*> f b
    _ -> Nothing

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
    _ -> impossible

  rLet n (RLet m Hole a b) c = rLet m a (rLet n b c)
  rLet n a b = RLet n Hole a b

--  RLet m Hole b c .@ a = rLet m b (c .@ a)
--  a .@ RLet m Hole b c = rLet m b (a .@ c)
  a .@ b = a :@ b

--------------------------------- priting for backends in Haskell

data HName
  = Builtin String        -- the String is globally unique
  | UserName String Int
  deriving (Eq, Ord, Show)

data Exp
  = Lam HName Exp
  | Let HName Exp Exp
  | App Exp Exp
  | Var HName
  | Con HName
  | String String
  | Nat Integer
  deriving Show

data Ty
  = TCon HName
  | TVar HName
  | TApp Ty Ty
  | Pi        Ty Ty
  | HPi HName Ty Ty
  deriving (Eq, Show)

data Data
  = Data HName Ty [(HName, Ty)]
  deriving Show
{-
data Data2
  = Data2 HName [HName]
  deriving Show
-}
instance IsString HName where fromString = Builtin
instance IsString Exp   where fromString = Con . fromString
instance IsString Ty    where fromString = TCon . fromString

name :: Name -> HName
name n = case nameId n of
    i | i < 0     -> Builtin s
      | otherwise -> UserName s i
   where
    s = chars $ showMixfix $ nameStr n

convert :: Raw -> Exp
convert = f  where
  f = \case
    E.Lam n e -> Lam (name n) $ f e
    RLet n Hole a b -> Let (name n) (f a) (f b)
    a :@ b -> App (f a) (f b)
    RVar (NNat n)    -> Nat n
    RVar (NString s) -> String s
    RVar n -> case n of
      m | isConName m -> Con $ name n
      _ -> Var $ name n
    _ -> impossible

convertTy :: Raw -> Ty
convertTy = f  where
  f = \case
    RVar "Pi"  :@ a :@ E.Lam "_" b -> Pi (f a) (f b)
    RVar "HPi" :@ a :@ E.Lam n b -> HPi (name n) (f a) (f b)
    a :@ b -> TApp (f a) (f b)
    RVar n -> case n of
      m | isConName m -> TCon $ name n
      _ -> TVar $ name n
    _ -> impossible


groupData :: [(HName, Ty)] -> [Data]
groupData ts = [Data n t [(n', t) | (n', t) <- ts, con n t] | (n, t) <- ts, tcon t]
 where
  tcon = \case
    "Ty" -> True
    Pi _ a -> tcon a
    HPi _ _ a -> tcon a
    _ -> False

  con :: HName -> Ty -> Bool
  con n = f where
    f = \case
      TCon n' -> n' == n
      TApp a _ -> f a
      Pi _ a -> f a
      HPi _ _ a -> f a
      _ -> False
{-
data2 :: Data -> Data2
data2 (Data n _ cs) = Data2 n $ fst <$> cs
-}
