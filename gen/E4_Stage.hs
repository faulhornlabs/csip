
{-# LINE 1 "src/E4_Stage.hs" #-}
module E4_Stage
  ( stage, pstage
  , stageHaskell
  , stage_eval
  ) where

import D_Calculus
import E3_Elab

pShow :: Show a => a -> String
pShow = f 10 . (\e -> appEndo e NilStr) . show  where

  f :: Word -> String -> String
  f n = g n  where
    g 0 (ConsStr " " cs) = "\n" <> g n cs
    g i (ConsStr c@" " cs) = c <> g (i-1) cs
    g i (ConsStr c@"\"" cs) = c <> skipString cs  where
      skipString (ConsStr c@"\"" cs) = c <> g i cs
      skipString (ConsStr "\\" cs) = error $ "TODO: " <> print cs
      skipString NilStr = (impossible "src/E4_Stage.hs" 20)
      skipString (spanStr (\c -> c /= '\\' && c /= '\"') -> T2 as cs) = as <> skipString cs

    g _ NilStr = mempty
    g i (spanStr (\c -> c /= ' ' && c /= '\"') -> T2 as cs) = as <> g i cs

----------------

--infoTable' :: Mem (List (Tup2 SName Tm))
infoTable' = do
  is <- reverse <$> getInfos
  forM is \(T2 n t) -> do
    s <- (quoteNF >=> tmToRaw) t
    pure (T2 n s)

stage :: Val -> Mem Scoped
stage = quoteNF >=> unquoteTm >=> tmToRaw

pstage :: Val -> Mem Scoped
pstage = quoteNF >=> unquoteTm >=> tmToRaw

stageHaskell v = do
  r <- (quoteNF >=> unquoteTm >=> tmToRaw) v
  ts <- infoTable'
  pure $ pShow (T2 (groupData ts) r)

groupData :: List (Tup2 SName Ty) -> List Data
groupData ts = do
  T2 n t <- ts
  guard (con N135 t)
  pure (Data n t (filter (con n . snd) ts))
 where
  con :: SName -> Ty -> Bool
  con n = f
   where
    f = \case
      N58  :@ _ :@ Lam _ a -> f a
      N59 :@ _ :@ Lam _ a -> f a
      a -> g a

    g = \case
      N134 :@ a -> g a
      a       :@ _ -> g a
      RVar n' -> n' == n

stage_eval :: Val -> Mem Scoped
stage_eval v = do
  t <- quoteNF v
  v' <- evalClosed =<< unquoteTm t
  quoteNF v' >>= tmToRaw

unquoteTm :: Tm -> Mem Tm
unquoteTm t = runReader emptyIS (g t) where
 g t st = f t  where
  f = \case
    N146 :@. _ :@. _ :@. TVal (name -> n) :@. d :@. e -> tLet n <$> f d <*> local st (insertIS n) (f e)
    N146 -> (impossible "src/E4_Stage.hs" 76)
    N113 :@. _ :@. _ :@. a :@. b -> getLam b >>= \(T2 n b) -> tLet n <$> f a <*> f b
    N151 :@. _ :@. a :@. b -> getLam b >>= \(T2 n b) -> tLet n <$> f a <*> f b
    N112 :@. _ :@. _ :@. a -> getLam a >>= \(T2 n a) -> tLam n =<< f a
    N152 :@. _ :@. _ :@. _ :@. a -> getLam a >>= \(T2 n a) -> tLam n =<< f a
    N57 :@. _ :@. _ :@. a -> f a
    N153 :@. _ :@. _ :@. _ :@. a -> f a
    TVal v -> asks st (memberIS $ name v) <&> \case
      True  -> TVar $ name v
      False -> TVal v
    TVar n -> pure $ TVar n
    a :@. b -> f a .@ f b
    t@TSup{} -> getLam t >>= \(T2 n a) -> tLam n =<< f a         -- TODO?
    t -> error $ pprint' t -- (impossible "src/E4_Stage.hs" 89)

  getLam = \case
    TLam g -> g
    t -> do
      n <- nameOf N75
      pure $ T2 n $ t :@. TVar n

  a .@ b = (:@.) <$> a <*> b

  tLet n (TLet m a b) c = tLet m a (tLet n b c)
  tLet n a b = TLet n a b

{-
    N154 :@ _ :@ _ :@ a :@ b -> N154 .@ f e a .@ f e b
    N155 :@ _ :@ _ :@ a :@ b -> N155 .@ f e a .@ f e b
    N156  :@ _ :@ _ :@ a -> N156 .@ f e a
    N157  :@ _ :@ _ :@ a -> N157 .@ f e a
    N57 :@ _ :@ _ :@ (N112 :@ _ :@ _ :@ b) :@ a -> getLam b >>= \(T2 n b) -> rLet' n a b
    N57 :@ _ :@ _ :@ a :@ b -> f e a .@ f e b
    N158 :@ _ -> pure $ N91
    Lam n a -> Lam n <$> f e a
-}

--------------------------------- priting for backends in Haskell

type EString = Endo String

(<+>) :: EString -> EString -> EString
a <+> b = a <> " " <> b

parens True a = "(" <> a <> ")"
parens False a = a


class Show a where
  show_ :: Bool -> a -> EString

show = show_ True

instance Show String where
  show_ _ s = MkEndo (("\"" <> s <> "\"") <>)

instance Show Word where
  show_ _ w = MkEndo (showWord w <>)

instance Show a => Show (List a) where
  show_ _ xs = "[" <> f xs <> "]" where
    f Nil = ""
    f (a :. Nil) = show_ False a
    f (a :. as) = show_ False a <> "," <+> f as

instance (Show a, Show b) => Show (Tup2 a b) where
  show_ _ (T2 a b) = parens True (show_ False a <> "," <+> show_ False b)

instance Show SName where
  show_ p n = parens p ("UserName" <+> show (showName n) <+> show (getId n))


---------------------------------

{-
data Exp
  = Lam SName Exp
  | Let SName Exp Exp
  | App Exp Exp
  | Var SName
  | String String
  | Nat Word
-}
type Exp = Scoped
type Ty = Exp

pattern Let n a b = RLet (RVar n) N39 a b

instance Show Exp where
  show_ p = parens p . \case
    Lam a b           -> "Lam" <+> show a <+> show b
    Let a b c         -> "Let" <+> show a <+> show b <+> show c
    N134 :@ a      -> show_ False a
    a :@ b            -> "App" <+> show a <+> show b
    RVar (RString a)  -> "String" <+> show (force a)
    RVar (RNat a)     -> "Word" <+> show (force a)
    RVar a            -> "Var" <+> show a

data Data = Data SName Ty (List (Tup2 SName Ty))

instance Show Data where
  show_ p = parens p . \case
    Data a b c -> "Data" <+> show a <+> show b <+> show c
