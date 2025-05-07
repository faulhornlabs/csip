module I_Stage
  ( stage
  , stageHaskell
  , stage_eval
  ) where

import qualified Prelude as P (String, Show, show)

import A_Builtins (toList)
import D_Base
import E_Parse hiding (Lam)
import qualified E_Parse as E
import F_Eval hiding (TVar, TApp, name)
import qualified F_Eval as E
import H_Elab

infoTable :: Scoped -> RefM (IntMap Name Scoped)
infoTable s = snd <$> runState mempty go
 where
  go st = f s
   where
    f = \case
      a :@ b -> f a >> f b
      RVar n | not $ elem (nameStr n) $ "App" :. "Arr" :. "Lam" :. "Let" :. "TopLet" :. Nil -> gets st (lookupIM n) >>= \case
        Just{} -> pure T0
        Nothing -> lookupDefs n >>= \case
          Just (MkDefData True (MkTmTy _ t) _) -> do
            s <- quoteNF t
            modify st (insertIM n s)
          _ -> pure T0
      _ -> pure T0

isCN n = lookupDefs n <&> \case
  Just (MkDefData True _ _) -> True
  _ -> False


stage_ :: Val -> RefM (Tup2 Scoped (List (Tup2 Name Scoped)))
stage_ t = do
  r <- quoteNF t
  m <- infoTable r
  r' <- unquote r
  pure (T2 r' (do T2 n r <- assocsIM m; t <- maybeToList (unquoteTy r); pure (T2 n t)))

stage :: Val -> RefM Scoped
stage t = stage_ t <&> \(T2 a ds) -> foldr (\(T2 n t) -> RLetTy n t) a ds


pShow = f 10 . fromString . P.show  where

  f :: Word -> String -> String
  f n = g n  where
    g 0 (ConsStr " " cs) = "\n" <> g n cs
    g i (ConsStr c@" " cs) = c <> g (i-.1) cs
    g i (ConsStr c@"\"" cs) = c <> skipString cs  where
      skipString (ConsStr c@"\"" cs) = c <> g i cs
      skipString (ConsStr "\\" cs) = error $ "TODO: " <<>> print cs
      skipString NilStr = impossible
      skipString (spanStr (\c -> c /= '\\' && c /= '\"') -> T2 as cs) = as <> skipString cs

    g _ NilStr = mempty
    g i (spanStr (\c -> c /= ' ' && c /= '\"') -> T2 as cs) = as <> g i cs


stageHaskell v = do
  T2 r ts <- stage_ v
  r' <- convert r
  ts' <- mapM (\(T2 a b) -> T2 (name a) <$> convertTy b) ts
  pure $ pShow ((,) (toList $ groupData ts') r')

unquoteTy :: Scoped -> Maybe Scoped
unquoteTy = f where
  f :: Scoped -> Maybe Scoped
  f r = case r of
    RVar "Ty" -> Just r
    RVar "String" -> Just r
    RVar "Nat" -> Just r
    RVar "Code" :@ r -> Just r
    RVar "Pi"  :@ a :@ E.Lam _n e -> f a >>= \fa -> f e <&> \fe -> RVar "Pi" :@ fa :@ E.Lam "_" fe
    RVar "HPi" :@ a :@ E.Lam  n e -> f a >>= \fa -> f e <&> \fe -> RVar "HPi" :@ fa :@ E.Lam n fe
    a :@ b -> (:@) <$> f a <*> f b
    _ -> Nothing


stage_eval :: Val -> RefM Scoped
stage_eval v = do
  t <- quoteTm_ True True False v
  v' <- evalClosed =<< unquoteTm t
  quoteNF v'

unquoteTm :: Tm -> RefM Tm
unquoteTm t = runReader mempty (g t) where
 g t st = f t  where
  f = \case
    TVal CTopLet :@. _ :@. _ :@. TVal (E.name -> n) :@. d :@. e -> TLet n <$> f d <*> local st (insertIS n) (f e)
    TVal CTopLet -> impossible
    E.TApp a b -> E.TApp <$> f a <*> f b
--    TVal 
    TVal v -> pure (TVal v)
    TSup c ts -> TSup c <$> mapM f ts
    TLet{} -> impossible
    TGen{} -> impossible
    E.TVar{} -> impossible
    TMatch{} -> impossible
    TRet{} -> impossible
    TNoRet{} -> impossible

unquote :: Scoped -> RefM Scoped
unquote = f mempty
 where
  f :: IntMap Name Name -> Scoped -> RefM Scoped
  f e = \case
    RVar "Prod" :@ _ :@ _ :@ a :@ b -> pure "Prod" .@ f e a .@ f e b
    RVar "Pair" :@ _ :@ _ :@ a :@ b -> pure "Pair" .@ f e a .@ f e b
    RVar "Fst"  :@ _ :@ _ :@ a -> pure "Fst" .@ f e a
    RVar "Snd"  :@ _ :@ _ :@ a -> pure "Snd" .@ f e a
    RVar "App" :@ _ :@ _ :@ (RVar "Lam" :@ _ :@ _ :@ b) :@ a -> getLam b >>= \(T2 n b) -> rLet' n a b
    RVar "App" :@ _ :@ _ :@ a :@ b -> f e a .@ f e b
    RVar "App" :@ _ :@ _ :@ a -> f e a
    RVar "Lam" :@ _ :@ _ :@ a -> getLam a >>= \(T2 n a) -> E.Lam n <$> f e a
    RVar "TopLet" :@ _ :@ _ :@ RVar n :@ a :@ b -> rLet'' n a b
    RVar "Let"    :@ _ :@ _           :@ a :@ b -> getLam b >>= \(T2 n b) -> rLet'' n a b
    RVar "noreturn" :@ _ -> pure $ RVar "Fail"
    E.Lam n a -> E.Lam n <$> f e a
    a :@ b -> f e a .@ f e b
    RVar n -> pure $ RVar $ fromMaybe n $ lookupIM n e
    r -> pure $ r
   where
    rLet' :: Name -> Scoped -> Scoped -> RefM Scoped
    rLet' n a b = f e a >>= \case
      RVar a -> f (insertIM n a e) b
      a -> rLet n (pure a) (f e b)

    rLet'' n a b = f e a >>= \a -> rLet n (pure a) (f e b)

  getLam (E.Lam n a) = pure (T2 n a)
  getLam a = do
    n <- mkName "v#"
    pure (T2 n (a `app` RVar n))

  rLet :: Name -> RefM Scoped -> RefM Scoped -> RefM Scoped
  rLet n a b = r n <$> a <*> b  where
    r n (RLet m Hole a b) c = r m a (r n b c)
    r n a b = RLet n Hole a b

--  RLet m Hole b c .@ a = rLet m b (c .@ a)
--  a .@ RLet m Hole b c = rLet m b (a .@ c)
  a .@ b = app <$> a <*> b

  app a@(RVar "Fail") _ = a
  app a b = a :@ b

--------------------------------- priting for backends in Haskell

data HName
  = Builtin P.String        -- the String is globally unique
  | UserName P.String Word
  deriving (Eq, P.Show)

data Exp
  = Lam HName Exp
  | Let HName Exp Exp
  | App Exp Exp
  | Var HName
  | Con HName
  | String P.String
  | Nat Integer
  deriving P.Show

data Ty
  = TCon HName
  | TVar HName
  | TApp Ty Ty
  | Pi        Ty Ty
  | HPi HName Ty Ty
  deriving (P.Show)

data Data
  = Data HName Ty [(HName, Ty)]
  deriving P.Show

toList' = toList . stringToList

instance IsString HName where fromString' = Builtin . toList'
instance IsString Exp   where fromString' = Con . fromString'
instance IsString Ty    where fromString' = TCon . fromString'

name :: Name -> HName
name n = case nameId n of
    i | i >= 9223372036854775808 -> Builtin s
    i -> UserName s i
   where
    s = toList' $ showMixfix $ nameStr n

convert :: Scoped -> RefM Exp
convert = f  where
  f = \case
    E.Lam n e -> Lam (name n) <$> f e
    RLet n Hole a b -> Let (name n) <$> f a <*> f b
    a :@ b -> App <$> f a <*> f b
    RNat n    -> pure $ Nat n
    RString s -> pure $ String (toList' s)
    RVar n -> isCN n <&> \case
      True  -> Con $ name n
      _ -> Var $ name n
    _ -> impossible

convertTy :: Scoped -> RefM Ty
convertTy = f  where
  f = \case
    RVar "Pi"  :@ a :@ E.Lam "_" b -> Pi <$> f a <*> f b
    RVar "HPi" :@ a :@ E.Lam n b -> HPi (name n) <$> f a <*> f b
    a :@ b -> TApp <$> f a <*> f b
    RVar n -> isCN n <&> \case
      True -> TCon $ name n
      _ -> TVar $ name n
    _ -> impossible


groupData :: List (Tup2 HName Ty) -> List Data
groupData ts = do
  T2 n t <- ts
  guard (tcon t)
  pure (Data n t $ toList $ map (\(T2 a b) -> (a, b)) (filter (con n . snd) ts))
 where
  tcon = \case
    TCon "Ty" -> True
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
