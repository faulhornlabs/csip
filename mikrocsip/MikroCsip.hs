{-# language BlockArguments, LambdaCase, PatternSynonyms, PatternGuards, ViewPatterns, OverloadedStrings, MultilineStrings #-}
{-# OPTIONS_GHC -odir tmp -outputdir tmp -fdefer-type-errors -Wall -Wno-missing-signatures -Wno-missing-pattern-synonym-signatures -Wno-name-shadowing -Wno-unused-do-bind -Wno-incomplete-uni-patterns -Wno-incomplete-patterns -Wno-type-defaults #-}

---------------------------------------------- imports

import Data.Char
import Data.Function
import Data.Functor
import Data.List
import Data.Maybe
--import Data.Either
import Data.String
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Arrow
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Control.Exception
import System.Environment
import System.IO

---------------------------------------------- utils

newtype NoOrd a = MkNoOrd a

instance Eq  (NoOrd a) where (==)    = \_ _ -> True
instance Ord (NoOrd a) where compare = \_ _ -> EQ

--------------------------------------------- raw name

type Str = String

data Name
  = UserName (NoOrd Str) Int    -- the Int is globally unique
  | BuiltinName Str             -- the Str should be globally unique
  deriving (Eq, Ord)

instance IsString Name where fromString = BuiltinName

nameStr :: Name -> Str
nameStr (BuiltinName s) = s
nameStr (UserName (MkNoOrd s) _) = s

instance Show Name where
  show (BuiltinName s) = s
  show (UserName (MkNoOrd s) i) = s ++ "_" ++ show i    -- TODO: cleaner show

------------------------------------------------------- Raw terms

data Raw
  = RVar Str
  | RApp Raw Raw

pattern RLam  a b  = RVar "Lam"  `RApp` a `RApp` b
pattern RHLam a b  = RVar "HLam" `RApp` a `RApp` b
pattern RPi   a b  = RVar "Pi"   `RApp` a `RApp` b   -- type, lam
pattern RHPi  a b  = RVar "HPi"  `RApp` a `RApp` b
pattern REApp a b  = RVar "App"  `RApp` a `RApp` b
pattern RHApp a b  = RVar "HApp" `RApp` a `RApp` b
pattern RRule  a b = RVar "="    `RApp` a `RApp` b
pattern RSRule a b = RVar ":="   `RApp` a `RApp` b
pattern RGuard a b = RVar "|"    `RApp` a `RApp` b
pattern RMatch a b = RVar "<-"   `RApp` a `RApp` b
pattern RTy   a b  = RVar ":"    `RApp` a `RApp` b
pattern RFun  a b  = RVar "::"   `RApp` a `RApp` b
pattern RDef  a b  = RVar ";"    `RApp` a `RApp` b
pattern RMeta      = RVar "_"
pattern RWild      = RVar "_"
pattern RClose f   = RVar "Close" `REApp` f

-- for intermediate raw representation
pattern RBraces a  = RVar "{}"   `RApp` a


----------------------------------- Raw -> String

{-
precedence table
  14   SPACE       15
  13   ->          12
  11   : :: .      10
  8    <-          8
  6    |           7
  5    = :=        4
  3    ;           2
  1    \n          0
-}
instance Show Raw where
  showsPrec p = \case
    RVar n                    -> (n ++)
    RHApp a b                 -> showsPrec p $ RApp a $ RBraces b
    RBraces b                 -> braces (showsPrec 0 b)
    RVar "Fun" `RApp` t `RApp` RLam (RVar n) b
                              -> parens' (p > 0) $ ("\n" ++) . (n ++) . (" :: " ++) . showsPrec 10 t . ("\n" ++) . showsPrec 0 b
    RVar "Body" `RApp` a `RApp` b `RApp` c
                              -> parens' (p > 0) $ showsPrec 5 a . (" += " ++) . showsPrec 4 b . ("\n" ++) . showsPrec 0 c
    RDef a b                  -> parens' (p > 0) $ showsPrec 1 a . ("\n" ++) . showsPrec 0 b
    RApp  (RLam (RVar n) b) a -> parens' (p > 0) $ (n ++) . (" = " ++) . showsPrec 4 a . ("\n" ++) . showsPrec 0 b
    RRule a b                 -> parens (p > 4)  $ showsPrec 5 a . (" = "  ++) . showsPrec 4 b
    RSRule a b                -> parens (p > 4)  $ showsPrec 5 a . (" := " ++) . showsPrec 4 b
    RTy  n a                  -> parens (p > 10) $ showsPrec 11 n . (" : "  ++) . showsPrec 10 a
    RFun n a                  -> parens (p > 10) $ showsPrec 11 n . (" :: " ++) . showsPrec 10 a
    RLam n b                  -> parens (p > 10) $ showsPrec 11 n . (". "   ++) . showsPrec 10 b
    RPi a (RLam RWild b)      -> parens (p > 12) $ showsPrec 13 a                                     . (" -> " ++) . showsPrec 12 b
    RPi  a (RLam (RVar n) b)  -> parens (p > 12) $ parens True ((n ++) . (" : " ++) . showsPrec 10 a) . (" -> " ++) . showsPrec 12 b
    RHPi a (RLam (RVar n) b)  -> parens (p > 12) $ braces      ((n ++) . (" : " ++) . showsPrec 10 a) . (" -> " ++) . showsPrec 12 b
    REApp a b                 -> showsPrec p $ RApp a b
    RApp  a b                 -> parens (p > 14) $ showsPrec 14 a . (" " ++) . showsPrec 15 b
   where
    braces a = ("{" ++) . a . ("}" ++)

    parens True a = ("(" ++) . a . (")" ++)
    parens _    a = a

    parens' True a = ("(\n" ++) . a . ("\n)" ++)
    parens' _    a = a

-------------------------------- String -> Raw

isAlphaNumeric c = isAlphaNum c || c == '_' || c == '\'' || c == '#'
isGraphic c = c `elem` ("*+-^=@%$&~.!?:<>/\\|" :: String)

tokenize = filter (not . all isSpace) . groupBy g where
  g a b = isAlphaNumeric a && isAlphaNumeric b
       || isGraphic  a && isGraphic  b

parse :: String -> M Raw
parse s = fmap (foldr1 RDef) $ mapM (h0 end . tokenize) $ lines' s
 where
  lines' = go []  where
    go acc = \case
      '-': '-': cs -> go acc $ dropWhile (/= '\n') cs
      '\n': ' ': cs -> go (' ': acc) cs
      '\n': '\n': cs -> go acc ('\n': cs)
      '\n': cs -> add acc $ lines' cs
      c: cs -> go (c: acc) cs
      [] -> add acc []
    add s ls = case dropWhile (== ' ') s of
      "" -> ls
      s -> reverse s: ls

  end a [] = pure a
  end _ ts = throwError $ "end of file expected instead of\n" <> unwords ts

  expect t r (t': ts) | t' == t = r ts
  expect t _ ts = throwError $ "expected " <> show t <> " at\n" <> unwords ts

  h9 r _ ("(": ts) = h0 (\b -> expect ")" $ r b) ts
  h9 r _ ("{": ts) = h0 (\b -> expect "}" $ r (RBraces b)) ts
  h9 r _ (t: ts) | all isAlphaNumeric t = r (RVar t) ts
  h9 _ z ts = z ts

  h8 r = h9 (h8' r) (\ss -> throwError $ "unknown token at\n" <> unwords ss)
  h8' r a ts = h9 (\b -> h8' r (REApp a b)) (r a) ts

  hn os g r = g (hn' r) where
    hn' r a (n: ts) | Just f <- lookup n os = hn os g (\b -> r (f a b)) ts
    hn' r a        ts  = r a ts

  h0 = hn [(";", RDef)]
     $ hn [("=", RRule), (":=", RSRule)]
     $ hn [("|", RGuard)]
     $ hn [("<-", RMatch)]
     $ hn [(":", RTy), ("::", RFun), (".", lam)]
     $ hn [("->", pi)] h8

  pi (RBraces (RTy (REApp ns n) t)) b = pi (RBraces (RTy ns t)) $ pi (RBraces (RTy n t)) b
  pi (RBraces (RTy (RVar n) a)) b = RHPi a $ RLam (RVar n) b
  pi (RBraces (REApp as a)) b = pi (RBraces as) $ pi (RBraces a) b
  pi (RBraces (RVar n)) b = RHPi RMeta $ RLam (RVar n) b
  pi (RTy (REApp ns n) t) b = pi (RTy ns t) $ pi (RTy n t) b
  pi (RTy (RVar n) a) b = RPi a $ RLam (RVar n) b
  pi (REApp as a@RTy{}) b = pi as $ pi a b
  pi a b = RPi a $ RLam RWild b

  lam (REApp as a) b = lam as $ lam a b
  lam (RBraces (RVar a)) b = RHLam (RVar a) b
  lam (RVar a) b = RLam (RVar a) b


------------------------------------------ term names

data TName = MkTName_ (NoOrd StaticInfo) Name
  deriving (Eq, Ord)

-- this info does not change during typechecking
data StaticInfo
  = KCon              -- constructor
  | KMeta BoundVars   -- meta variable
  | KCMeta            -- context meta    -- TODO: remove
  | KFun              -- function          --   n :: ...; ...; n ... = ...; ...
  | KBVar             -- bound variable    --   n. ...
  | KDVar             -- defined variable  --   n :: ... = ...
  deriving Show

pattern MkTName a b = MkTName_ (MkNoOrd a) b

type BoundVars = [TName]

instance Show TName where show (MkTName _k n) = {- "(" <> show k <> ")-" <> -} show n
instance IsString TName where
  fromString s = MkTName KCon (BuiltinName s)

tnameStr :: TName -> Str
tnameStr (MkTName _ n) = nameStr n

pattern WildCard :: TName
pattern WildCard = "_"

pattern NCon     <- MkTName  KCon      _  -- TODO: rename to NameCon or IsCon
pattern NBVar    <- MkTName  KBVar     _
pattern NMeta bv <- MkTName (KMeta bv) _
pattern NCMeta   <- MkTName  KCMeta    _
pattern NFun     <- MkTName  KFun      _

------------------------------------------ terms

data Tm
  = TVar TName
  | TApp Tm Tm
  | TLam TName Tm

pattern TLet n a b      = TApp (TLam n b) a

{-
     n ... ... ...
     caseCons neut (\head tail -> ok) fail
-}
pattern TMatch n a b c  = a `TApp` (TVar "Match" `TApp` TVar n `TApp` b `TApp` c)

pattern TType           = TVar "Type"
pattern TRule  a b      = TVar "="  `TApp` a `TApp` b
pattern TSRule a b      = TVar ":=" `TApp` a `TApp` b
pattern TOLet n a b     = TVar "Let" `TApp` a `TApp` TLam n b     --   :=
pattern TRet a          = TVar "Ret" `TApp` a
pattern TGuard a b c d  = TVar "Guard"  `TApp` a `TApp` b `TApp` c `TApp` d
pattern TLGuard a b c   = TVar "LGuard" `TApp` a `TApp` b `TApp` c
pattern TFail           = TVar "FAIL"
pattern TFun n ty b     = TVar "Fun"  `TApp` ty `TApp` TLam n b
pattern TDef n a b      = TVar "Body" `TApp` TVar n  `TApp` a `TApp` b

---------- show

instance Show Tm where show = show . tmToRaw

tmToRaw :: Tm -> Raw
tmToRaw = \case
  TVar n   -> RVar $ show n
  TApp a b -> RApp (tmToRaw a) (tmToRaw b)
  TLam n a -> RLam (RVar (show n)) $ tmToRaw a

show' :: Tm -> String
show' = indent 2 . ("  " ++) . show  where
  indent _ [] = []
  indent i ('(': '\n': cs) | i <- i + 2 = '(': '\n': replicate i ' ' ++ indent i cs
  indent i ('\n': ')': cs) | i <- i - 2 = '\n': replicate i ' ' ++ ')': indent i cs
  indent i ('\n': cs) = '\n': replicate i ' ' ++ indent i cs
  indent i (c: cs) = c: indent i cs

getTApps (TApp (getTApps -> (a, as)) b) = (a, b: as)
getTApps v = (v, [])

pattern TApps :: Tm -> [Tm] -> Tm
pattern TApps a as <- (getTApps -> (a, reverse -> as))
  where TApps a as =  foldl TApp a as


------------------------------------------ values

data Val
  = VVar TName
  | VApp Val Val
  | VLam TName Env Tm             -- TODO: store defs only

type VTy = Val

pattern VType     =  VVar "Type"
pattern VMeta v   <- VVar v@NMeta{}
pattern VPi  a b  <- VVar "Pi"  `VApp` a `VApp` b
pattern VHPi a b  <- VVar "HPi" `VApp` a `VApp` b
pattern VRet a    <- VVar "Ret" `VApp` a
pattern VCode a b <- VVar "Code" `VApp` a `VApp` b

-----------

getVApps (VApp (getVApps -> (a, as)) b) = (a, b: as)
getVApps v = (v, [])

pattern VApps :: Val -> [Val] -> Val
pattern VApps a as <- (getVApps -> (a, reverse -> as))
  where VApps a as =  foldl VApp a as

----------

type MVal = M Val

mlift :: (Val -> Val -> M a) -> MVal -> MVal -> M a
mlift f a b = a >>= \a -> b >>= \b -> f a b

mApp :: MVal -> MVal -> MVal
mApp a b = VApp <$> a <*> b

mVar :: TName -> MVal
mVar n = pure (VVar n)

mMeta :: MVal
mMeta = VVar <$> newMeta

mPi  a b     = mVar "Pi"   `mApp` a `mApp` b
mHPi a b     = mVar "HPi"  `mApp` a `mApp` b
mValue       = mVar "Value"                            --  V    : Polarity
mComputation = mVar "Computation"                      --  C    : Polarity
                                                       --  Ty   : Polarity -> Type
mArr  a b c  = mVar "Arr"  `mApp` a `mApp` b `mApp` c  --  Arr  : {p} -> Ty V -> Ty p -> Ty C
mCode a b    = mVar "Code" `mApp` a `mApp` b           --  Code : {p} -> Ty p -> Type
                                                            -- object terms





-------------------------------------------- elaboration monad

type M = ExceptT Error (WriterT [Log] (StateT St (Reader Env)))

type Error = String

data St = MkSt
  { idCounter :: Int
  , dynInfo   :: Map.Map TName DynInfo
  }

data DynInfo
  = DMeta (Either PruneTm Tm)       -- meta solution
  | DCMeta Env Tm                   -- context meta solution  -- could be (DCMeta Val)?
  | DFun TName                      -- function body

data PruneTm = MkPruneTm [Bool] Tm

emptySt = MkSt 0 mempty


data Env = MkEnv
  { tnames    :: Map.Map Str TName
  , types     :: Map.Map TName VTy
  , defs      :: Map.Map TName Val
  , funCont   :: Map.Map TName TName
  , boundVars :: BoundVars
  }

emptyEnv = MkEnv mempty mempty mempty mempty mempty

-- TODO: remove
data Log
  = LBegin String
  | LEnd String
  | LSource Raw          -- parser test
  | LScope Raw
  | LElab Tm
  | LZonk Tm
  | LGeneralize Tm Tm
  | LCompile TName Tm
  | LInfer Raw
  | LInferRes Tm Tm
--  | LCheck Raw Tm
  | LMeta BoundVars TName
  | LCoerce Tm Tm
  | LCoerceRes Tm
  | LUnify Tm Tm
  | LSolve BoundVars TName (Either PruneTm Tm)
  | LDebug String
  | LEval Tm
  | LEvalRes Tm Tm

---------------------------

runM :: M a -> ((Either Error a, [Log]), St)
runM = flip runReader emptyEnv
     . flip runStateT emptySt
     . runWriterT
     . runExceptT

lazyM :: M a -> M a
lazyM m = do
  r <- ask
  s <- get
  pure $ either (error "lazyM") id . fst . flip runReader r . flip evalStateT s . runWriterT . runExceptT $ m

withoutDynInfo m = do
  di <- gets dynInfo
  modify \st -> st {dynInfo = mempty}
  a <- m
  modify \st -> st {dynInfo = di}
  pure a

---------------

addBoundVar :: TName -> M a -> M a
addBoundVar WildCard = id
addBoundVar n = local \st -> st {boundVars = n: boundVars st}

getBoundVars :: M BoundVars
getBoundVars = asks boundVars

newVar :: Str -> StaticInfo -> M TName
newVar "_" _ = pure WildCard
newVar s k = do
  i <- gets idCounter
  modify \s -> s {idCounter = i + 1}
  pure $ MkTName k $ UserName (MkNoOrd s) i

newVar' n_ k = case n_ of
    '#': s -> pure (s, MkTName k (BuiltinName s))
    s      -> (,) s <$> newVar s k

newBVar n c = do
  n' <- newVar n KBVar
  addBoundVar n' $ c n'

mkName :: StaticInfo -> VTy -> Str -> (TName -> M b) -> M b
mkName _ _ "_" f = f WildCard
mkName a ty n_ f = do
  (n_, n1) <- newVar' n_ a
  let
      ff = case a of
          KBVar -> addBoundVar n1
          _     -> id
  ff $ local (\s -> s {tnames = Map.insert n_ n1 $ tnames s, types = Map.insert n1 ty $ types s}) $ f n1

lookupName n = asks (Map.lookup n . tnames) >>= \case
  Nothing -> pure Nothing
  Just n  -> asks (Map.lookup n . types) <&> fmap ((,) (TVar n))

newCMeta = do
  i <- newVar "m" KCMeta
  tell [LMeta [] i]
  pure i

newMeta_ bv = do
  i <- newVar "m" (KMeta bv)
  tell [LMeta bv i]
  pure i

newMeta :: M TName
newMeta = getBoundVars >>= newMeta_

addDef :: TName -> Val -> M a -> M a
addDef n d m = local (\s -> s {defs = Map.insert n d $ defs s}) m

getDef n = asks (Map.lookup n . defs) >>= \case
  Just (VVar fn) -> pure fn
  _ -> asks defs >>= \ds -> throwError $ "getDef: " <> show n <> "\n" <> show (Map.keys ds)

getDef_ n = asks (Map.lookup n . defs) >>= \case
  Just fn -> pure fn
  _ -> asks defs >>= \ds -> throwError $ "getDef: " <> show n <> "\n" <> show (Map.keys ds)

lookupDyn n = gets (Map.lookup n . dynInfo)
setDyn n i = modify \s -> s {dynInfo = Map.insert n i $ dynInfo s}

lookupMeta n = lookupDyn n <&> \case
  Just (DMeta t) -> Just t
  _ -> Nothing

solveMeta_ i@(NMeta bv) t = do
  tell [LSolve bv i t]
  setDyn i $ DMeta t

lookupCMeta n = lookupDyn n >>= \case
  Just (DCMeta env t) -> local (const env) $ eval t <&> Just
  _ -> pure Nothing

solveCMeta_ i@NCMeta t = do
  env <- ask
  tell [LSolve (boundVars env) i $ Right t]
  setDyn i $ DCMeta env t


setFunCont n i m = local (\s -> s {funCont = Map.insert n i $ funCont s}) m

getFunCont n = asks (Map.lookup n . funCont) >>= \case
  Nothing -> throwError $ "not defined fun: " <> show n
  Just f -> pure f

indent str m = do
  tell [LBegin str]
  x <- m
  tell [LEnd str]
  pure x

-------------------------------------------------------------------------------------

-- do this before pattern matching and sharing of values
-- also do this before exiting context
force :: Val -> M Val
force v = do
  si <- gets dynInfo
  case v of
    VVar n@NFun | Just (DFun body) <- Map.lookup n si -> force (VVar body) >>= \case
      VRet v -> force v
      _      -> pure v
    VMeta i -> lookupMeta i >>= \case
      Just v -> eval =<< either evalPruneTm pure v
      _      -> pure v
    VVar i@NCMeta -> lookupCMeta i <&> \case
      Just v -> v
      _      -> v
    VVar n -> asks (Map.lookup n . defs) >>= \case
      Just v -> force v
      _      -> pure v
    VApp a b -> force a >>= \a -> case a of
      VLam WildCard env t -> local (const env) $ eval t
      VLam n        env t -> local (const env) $ addDef n b $ eval t
      VApps (VVar n@NFun) vs | Just (DFun body) <- Map.lookup n si -> force (VApp (VApps (VVar body) vs) b) >>= \case
        VRet v -> force v
        _      -> pure $ VApp a b
      VApps (VVar c@NCon{}) vs -> force b >>= \b -> case b of
        VVar "Match" `VApp` VVar n@NCon{} `VApp` ok `VApp` fail -> case () of
          _ | c == n    -> force $ VApps ok vs
            | otherwise -> pure fail
        _ -> pure $ VApp a b
      _ -> pure $ VApp a b
    v -> pure v

-- used for dependent pattern matching
generalize :: Tm -> (Tm -> M a) -> M a
generalize t c = case t of
  TApp a b -> generalize a \a -> generalize b \b -> c (TApp a b)
  TVar i@NMeta{} -> unsolvedMeta i >>= \case
    Nothing -> c t
    Just i -> newBVar "w" \n -> do
      solveMeta_ i $ Right (TVar n)
      c $ TVar n
  TVar{} -> c t
  t -> error $ show t
 where
  unsolvedMeta i = lookupMeta i >>= \case
    Just (Left (MkPruneTm [] _)) -> undefined --unsolvedMeta i
    Just (Right (TVar i@NMeta{})) -> unsolvedMeta i
    Just{} -> pure Nothing
    Nothing -> pure $ Just i

----------

-- gives back deeply forced value
eval :: Tm -> M Val
eval = go force
 where
  go force = \case
    TFun f _ty e -> do
      m <- newCMeta
      fn <- newVar (tnameStr f) KFun
      setDyn fn (DFun m)
      addDef f (VVar fn) $ setFunCont fn m $ eval e
    TDef f c e -> do
      fn <- getDef f
      m <- getFunCont fn
      m2 <- newCMeta
      solveCMeta_ m $ TApp c $ TVar m2
      setFunCont fn m2 $ eval e
    TLet n a b     -> eval a >>= \a -> addDef n a $ eval b
    TLam n b       -> ask <&> \env -> VLam n env b
    TApp a b       -> VApp <$> go pure a <*> eval b >>= force   -- a is already forced
    TVar i         -> force $ VVar i

----------

quote :: Val -> M Tm
quote v = force v >>= \case
  VVar kn        -> pure $ TVar kn
  VApp a b       -> TApp <$> quote a <*> quote b
  v@(VLam n _ _) -> newBVar (tnameStr n) \n -> TLam n <$> quote (VApp v (VVar n))

zonk :: Tm -> M Tm
zonk = go >=> either evalPruneTm pure where

  go :: Tm -> M (Either PruneTm Tm)
  go = \case
    TLam n a -> Right . TLam n <$> zonk a
--    TVar (NCon (Just k)) -> pure $ Right $ TVar k
    TVar i -> lookupMeta i >>= \case
      Nothing -> pure $ Right $ TVar i
--      Just{} -> pure $ Right $ TVar WildCard
      Just (Right t) -> go t
      Just (Left (MkPruneTm bs t)) -> comp bs <$> go t
    TApps a bs -> Right <$> (tApps <$> go a <*> mapM zonk bs)

  comp :: [Bool] -> Either PruneTm Tm -> Either PruneTm Tm
  comp bs (Right tm) = Left $ MkPruneTm bs tm
  comp bs (Left (MkPruneTm bs' tm)) = Left $ MkPruneTm (f bs bs') tm where
    f [] [] = []
    f (True: bs) (c: cs) = c: f bs cs
    f (False: bs) cs = False: f bs cs

  tApps :: Either PruneTm Tm -> [Tm] -> Tm
  tApps (Right t) ts = TApps t ts
  tApps (Left (MkPruneTm bs t)) ts = f bs t ts where
    f (False: bs) t (_: ts) = f bs t ts
    f (True: bs)  t (x: ts) = f bs (TApp t x) ts
    f [] t ts = TApps t ts

lazyQuote = lazyM . quote

vLam :: TName -> Val -> M Val
vLam n v = do
  t <- quote v
  eval (tLam n t)

--  eta reduction for better meta solving
--           \n -> e n     (n is not free in e)     ~~>    e
tLam n (TApp a (TVar n')) | n == n', not $ freeIn n a  =  a
 where
  freeIn n = \case
    TVar (NMeta bv) -> n `elem` bv
    TVar n' -> n == n'
    TApp a b -> freeIn n a || freeIn n b
    TLam _ t -> freeIn n t
tLam n t = TLam n t

vConst :: Val -> M Val
vConst = vLam WildCard

------------------

type Prunes = [(TName, [(TName, Either Int Int)])]    -- var, pruning solutions; Left: prune from meta boundvars

mkPruneTm [] t = Right t
mkPruneTm bs t = Left $ MkPruneTm bs t

evalPruneTm :: PruneTm -> M Tm
evalPruneTm (MkPruneTm bs t) = mk bs t where
  mk (False: bs) t = TLam WildCard <$> mk bs t
  mk (True:  bs) t = newBVar "v" \v -> TLam v <$> mk bs (TApp t $ TVar v)
  mk [] t = pure t

solveMeta i v = indent "solveMeta" do
  t <- quote v
  prune i t
  solveMeta_ i $ Right t
 where
  prune i@(NMeta bv) t = case computePrunes $ filter ((`notElem` bv) . fst) $ prunes t of
    Nothing -> throwError $ "prune: " <> show i <> " [" <> intercalate "," (map show bv) <> "] " <> show t
    Just ps -> forM_ ps $ uncurry pruneMeta

  pruneMeta (m@(NMeta bv2)) (Set.toList -> is) = do
    t <- mkBV 0 bv2 is []
    solveMeta_ m t
   where
    mkBV n ~(b: bv) is_@(Left i: is) acc
      | n == i    = mkBV (n+1) bv is  acc
      | otherwise = mkBV (n+1) bv is_ (b: acc)
    mkBV _ _ is acc = do
      m' <- newMeta_ $ reverse acc
      pure $ mkPruneTm (mk 0 is) $ TVar m'

    mk n is_@(Right i: is)
      | n == i    = False: mk (n+1) is
      | otherwise = True:  mk (n+1) is_
    mk _ [] = []

  prunes :: Tm -> Prunes
  prunes (TApps (TVar m@(NMeta bv)) ts)
    =  zipWith (\i v -> (v, [(m, Left i)])) [0..] bv
    <> concat (zipWith (\i -> map $ second ((m, Right i):)) [0..] $ map prunes ts)
  prunes (TApp a b) = prunes a <> prunes b
  prunes (TLam n a) = filter ((/= n) . fst) $ prunes a
  prunes (TVar n@NBVar{}) = [(n, [])]
  prunes TVar{} = []

  computePrunes :: Prunes -> Maybe [(TName, Set.Set (Either Int Int))]
  computePrunes ps = f [] mempty ps  where

    f acc m [] = Just $ map (\d -> (d, fromMaybe undefined $ Map.lookup d m)) acc
    f _   _ ((_, []): _) = Nothing
    f acc m ((_, is): ps) | or [ maybe False (Set.member i) (Map.lookup dep m) | (dep, i) <- is] = f acc m ps
    f acc m ((_, (sortBy (compare `on` snd) -> (dep, i): _)): ps)
      = f (dep: acc) (Map.alter (Just . Set.insert i . fromMaybe mempty) dep m) ps

----------

unify :: Val -> Val -> M ()
unify a b = indent "unify" do
  a <- force a
  b <- force b
  ta <- lazyQuote a
  tb <- lazyQuote b
  tell [LUnify ta tb]
  let diff = case (a, b) of
        (VApps (VMeta n) _, VApps (VMeta n') _) -> n /= n'
        _ -> True
  case (a, b) of
    (VMeta i, v) | diff -> solveMeta i v
    (v, VMeta i) | diff -> solveMeta i v
    (VVar n, VVar n') | n == n' -> pure ()
    _ -> do
      a2 <- ff a
      b2 <- ff b
      case (a, b) of
        (VApp a1@(VApps VMeta{} _) _, _) | diff, Just n <- a2 -> mlift unify (pure a1) (vLam n b)
        (_, VApp b1@(VApps VMeta{} _) _) | diff, Just n <- b2 -> mlift unify (vLam n a) (pure b1)
        (VApp a1@(VApps VMeta{} _) _, _) | diff               -> mlift unify (pure a1) (vConst b)
        (_, VApp b1@(VApps VMeta{} _) _) | diff               -> mlift unify (vConst a) (pure b1)
        (VLam{}, b) -> withNewVar \vn                         -> unify (VApp a vn) (VApp b vn)
        (a, VLam{}) -> withNewVar \vn                         -> unify (VApp a vn) (VApp b vn)
        (VApp a1 a2, VApp b1 b2) -> unify a1 b1 >> unify a2 b2
        _ -> throwError $ "unify: " <> show (ta, tb)
 where
  ff (VApp _ x) = force x >>= \case
    VVar n@NBVar{} -> pure $ Just n
    _ -> pure Nothing
  ff _ = pure Nothing

  withNewVar m = newBVar "x" \c -> m $ VVar c

----------

-- hlam is needed for emulating hidden arguments with coercive subtyping
coerce :: Bool -> Val -> Val -> M (Tm -> Tm)
coerce hlam a{-got-} b{-expected-} = indent "coerce" do
  ta <- lazyQuote a
  tb <- lazyQuote b
  tell [LCoerce ta tb]
  a <- force a
  b <- force b
  t <- case (a, b) of

    (VHPi t s, VHPi u w) -> do
      q <- coerce True u t
      newBVar "r" {-u-} \v -> do
        h <- mlift (coerce True) (mApp (pure s) $ eval $ q $ TVar v) (pure $ VApp w (VVar v))
        pure \x -> tLam v $ h $ TApp x $ q $ TVar v

    (VPi t s, VPi u w) -> do
      q <- coerce True u t
      newBVar "r" {- u -} \v -> do
        h <- mlift (coerce True) (mApp (pure s) $ eval $ q $ TVar v) (pure $ VApp w (VVar v))
        pure \x -> tLam v $ h $ TApp x $ q $ TVar v

    (VHPi _ d, a) | rigid a -> do
      m <- newMeta
      f <- coerce hlam (VApp d (VVar m)) a
      pure \x -> f $ TApp x $ TVar m

    (a, VHPi _ d) | hlam, rigid a -> do
      f <- mlift (coerce hlam) (pure a) (mApp (pure d) mMeta)
      pure \x -> TLam WildCard $ f x

    (VVar "Polarity", VType) -> pure \x -> TVar "Ty" `TApp` x

    (VVar "Ty" `VApp` p, VType) -> do
      mp <- newMeta
      unify p $ VVar mp
      pure \x -> TVar "Code" `TApp` TVar mp `TApp` x

    (VCode p c, VPi t s) -> do
      unify p =<< mComputation
      mp <- newMeta
      m1 <- newMeta
      m2 <- newMeta
      f <- mlift (coerce True) (mCode mComputation (pure c)) (mCode mComputation (mArr (mVar mp) (mVar m1) (mVar m2)))
      q <- coerce True t =<< mCode mValue (mVar m1)
      newBVar "r" {-t-} \v -> do
        h <- mlift (coerce True) (mCode (mVar mp) (mVar m2)) (mApp (pure s) (mVar v))
        pure \x -> tLam v $ h $ TApps (TVar "PApp") [TVar mp, TVar m1, TVar m2, f x, q $ TVar v]

    (VPi t s, VCode p c) -> do
      unify p =<< mComputation
      mp <- newMeta
      m1 <- newMeta
      m2 <- newMeta
      f <- mlift (coerce True) (mCode mComputation (mArr (mVar mp) (mVar m1) (mVar m2))) (mCode mComputation (pure c))
      q <- mlift (coerce True) (mCode mValue (mVar m1)) (pure t)
      newBVar "r" {- mCode mValue (mVar m1) -} \v -> do
        h <- mlift (coerce True) (mApp (pure s) (eval $ q $ TVar v)) (mCode (mVar mp) (mVar m2))
        pure \x -> f $ TApps (TVar "PLam") [TVar mp, TVar m1, TVar m2, tLam v $ h $ TApp x $ q $ TVar v]

    _ -> do
      unify a b
      pure id

  tell [LCoerceRes $ t $ TVar "tm"]
  pure t
 where
  rigid (VApps (VVar NMeta{}) _) = False
  rigid _ = True

-------------------------

rVars :: Raw -> M [Str]
rVars r = nub <$> fv r
 where
  fv = \case
    RGuard a (RMatch b _) -> (<>) <$> fv a <*> fv b
    RLam (RVar n) a -> filter (/= n) <$> fv a
    RApp a b -> (<>) <$> fv a <*> fv b
    RVar n | isLowerName n -> lookupName n <&> \case
      Just{} -> []
      _ -> [n]
    RVar{} -> pure mempty

  isLowerName (c: _) = isLower c
  isLowerName _ = False

ruleHead (TLGuard a _ _) = ruleHead a
ruleHead (TApp a _) = ruleHead a
ruleHead (TVar n) = n
ruleHead t = error $ "ruleHead: " <> show t

----------

addVar n m = do
  mt <- mMeta
  mkName KBVar mt n \_ -> m

infer :: Raw -> M (Tm, Val)
infer r = indent "infer" do
  tell [LInfer r]
  (t, v) <- infer_ r
  v' <- lazyQuote v
  tell [LInferRes t v']
  pure (t, v)

infer_ :: Raw -> M (Tm, Val)
infer_ = \case

  RDef s d -> do
    tell [LSource s]
    case s of

      RRule (RTy (RVar n_) t) b -> do
        (t', t'') <- checkType t
        b' <- check b t''
        b'' <- eval b'
        mkName KDVar t'' n_ \n -> addDef n b'' do
          tell [LElab $ TRule (TVar ":" `TApp` TVar n `TApp` t') b']
          infer_ d <&> first (TLet n b')

      RSRule (RTy (RVar n_) t) b -> do
        (t', t'') <- checkOType t
        b' <- check b t''
        mkName KDVar t'' n_ \n -> do              -- KDOVar
          tell [LElab $ TSRule (TVar ":" `TApp` TVar n `TApp` t') b']
          (iCheck d =<< mCode mMeta mMeta) <&> first (TOLet n b')

      RTy (RVar n_) t -> do
        (t', t'') <- checkType t
        (n_, cn) <- newVar' n_ KCon
        bv <- getBoundVars
        mkName KDVar t'' n_ \n -> do
          addDef n (VApps (VVar cn) $ map VVar bv) $ do
            tell [LElab $ TVar ":" `TApp` TVar n `TApp` t']
            t''' <- lazyQuote t''
            tell [LZonk $ TVar ":" `TApp` TVar n `TApp` t''']
            infer_ d <&> first (TLet n {- t' -} $ TApps (TVar cn) $ map TVar bv)

      RFun (RVar n_) t -> do
        (t', t'') <- checkType t
        i <- newCMeta
        mkName KDVar t'' n_ \n -> do
          fn <- newVar (tnameStr n) KFun
          addDef n (VVar fn) $ setFunCont fn i do
            setDyn fn (DFun i)
            tell [LElab $ TVar "::" `TApp` TVar n `TApp` t']
            t''' <- lazyQuote t''
            tell [LZonk $ TVar "::" `TApp` TVar n `TApp` t''']
            infer_ d <&> first (TFun n t')

      RRule a b -> do                  -- rule def
        ns <- rVars a
        (a', b') <- flip (foldr addVar) ns do
          (a'', t) <- infer a
          generalize a'' \a''' -> do
            b' <- check b t
            pure (a''', b')
        tell [LGeneralize a' b']
        let f = ruleHead a'
        body_ <- compile a' b'
        body <- newBVar "fail" \ff -> pure $ tLam ff $ body_ $ TVar ff
        fn <- getDef f
        tell [LCompile fn body]
        m <- getFunCont fn
        m2 <- newCMeta
        solveCMeta_ m $ TApp body (TVar m2)
        setFunCont fn m2 $ infer_ d <&> first (TDef f body)

      -- ignore now
      RClose (RVar _f) -> infer_ d

  RGuard a (RMatch p e) -> do
    (a'', t) <- infer a
    (e'', s) <- infer e
    p'' <- check p s
    pure ((TLGuard a'' p'' e''), t)

  RMeta -> do
    i <- newMeta <&> TVar
    j <- newMeta <&> VVar
    pure (i, j)

  RVar "Type" -> do
    pure (TType, VType)

  RVar n_ -> lookupName n_ >>= \case
    Just tms -> pure tms
    _ -> throwError $ "Not in scope: " <> n_

  RLam (RVar n_) a -> do
    t1 <- mMeta
    t2 <- mMeta
    t <- mPi (pure t1) (pure t2)
    mkName KBVar t1 n_ \n -> do
      tm <- TLam n <$> check a (VApp t2 (VVar n))
      pure (tm, t)

  RVar n `RApp` a `RApp` b | Just pi <- lookup n [("Pi", "Pi"), ("HPi", "HPi")] -> do
    a'' <- check a VType
    av <- eval a''
    b'' <- check b =<< mPi (pure av) (vConst VType)
    pure (TVar pi `TApp` a'' `TApp` b'', VType)

  RVar "App" `RApp` a `RApp` RBraces b -> infer_ $ RHApp a b
  RVar n `RApp` a `RApp` b | Just pi <- lookup n [("App", mPi), ("HApp", mHPi)] -> do
    (a'', t) <- infer a
    d <- mMeta
    c <- mMeta
    tr <- coerce False t =<< pi (pure d) (pure c)
    b'' <- check b d
    bv <- eval b''
    pure (TApp (tr a'') b'', VApp c bv)

  x -> throwError $ "infer: " <> show x

check :: Raw -> Val -> M Tm
check (RVar l `RApp` RVar n_ `RApp` a) t | Just pi <- lookup l [("Lam", mPi), ("HLam", mHPi)] = do
  t1 <- newMeta <&> VVar
  t2 <- newMeta <&> VVar
  p <- pi (pure t1) (pure t2)
  f <- coerce True p t
  mkName KBVar t1 n_ \n -> f . TLam n <$> check a (VApp t2 (VVar n))
check (RVar "Guard" `REApp` p `REApp` e `REApp` ok `REApp` fail) t = do
  ok'' <- check ok t
  fail'' <- check fail t
  (e'', s) <- infer e
  p'' <- check p s
  pure $ (TGuard p'' e'' ok'' fail'')
check (RVar "FAIL") _t = pure $ TFail
check a t = do
  (a'', t') <- infer a
  f <- coerce True t' t
  pure $ (f a'')

checkType :: Raw -> M (Tm, VTy)
checkType a = do
  ns <- rVars a
  let a' = foldr (\n a -> RHPi RMeta $ RLam (RVar n) a) a ns
  tell [LScope a']
  t <- check a' VType
  t' <- eval t
  pure (t, t')

checkOType a = do
  (a', a'') <- checkType a
  f <- coerce True a'' =<< mCode mMeta mMeta
  let b = f a'
  b' <- eval b
  pure (b, b')

iCheck a t = do
  a' <- check a t
  pure (a', t)

------------------------ pattern match compilation

compile :: Tm -> Tm -> M (Tm -> Tm)
compile lhs rhs = ($) <$> mgo lhs <*> guards rhs
 where
  app (TLam WildCard fail) _ = fail
  app a b = TApp a b

  lam :: TName -> (Tm -> Tm) -> Tm -> Tm
  lam n rhs = \fail -> TLam n $ rhs $ app fail (TVar n)

  guards :: Tm -> M (Tm -> Tm)
  guards (TGuard p e a b) = (.) <$> (($) <$> match p e <*> guards a) <*> guards b
  guards TFail = pure id
  guards rhs = pure \_ -> TRet rhs

  mgo :: Tm -> M ((Tm -> Tm) -> Tm -> Tm)
  mgo TVar{}          = pure id
  mgo (TLGuard a p e) = (.) <$> mgo a <*> match p e
  mgo (TApp a p)      = (.) <$> mgo a <*> mgo' p

  mgo' :: Tm -> M ((Tm -> Tm) -> Tm -> Tm)
  mgo' (TVar n@NBVar{}) = pure $ lam n
  mgo' p = newBVar "z" \n -> do
    k <- match p (TVar n)
    pure $ lam n . k

  match :: Tm -> Tm -> M ((Tm -> Tm) -> Tm -> Tm)
  match p e = case p of
    TVar NMeta{}   -> pure \ok fail -> ok fail
    TVar WildCard  -> pure \ok fail -> ok fail
    TVar n@NBVar{} -> pure \ok fail -> TLet n e $ ok fail
    TApps (TVar k) ps -> getDef_ k >>= \case
      VApps (VVar k@NCon{}) vs -> do
        rr <- mgo p
        pure \ok fail -> TMatch k e (rep (length vs) clam $ rr ok $ rep (length ps) clam fail) fail
    p -> throwError $ "match: " <> show p

  clam = TLam WildCard
  rep n f a = iterate f a !! n

-------------------------------- virtual nanopasses

data LogTag = QLog | QCheck | QInfer | QInferRes | QEval | QSource | QScope | QElab | QZonk | QPartial | QCoerce | QUnify | QSolve | QGeneralize | QCompile | QMeta | QDebug
  deriving (Eq, Show)

filterLog :: [LogTag] -> [Log] -> [Log]
filterLog tags = filter \case
  LBegin{} -> True
  LEnd{}   -> True
  l -> maybe False (`elem` tags) (tag l)
 where
  tag = \case
--    LCheck{}        -> Just QCheck
    LInfer{}        -> Just QInfer
    LInferRes{}     -> Just QInferRes
    LEval{}         -> Just QEval
    LEvalRes{}      -> Just QEval
    LSource{}       -> Just QSource
    LSolve{}        -> Just QSolve
    LCoerce{}         -> Just QCoerce
    LCoerceRes{}         -> Just QCoerce
    LGeneralize{}   -> Just QGeneralize
    LCompile{}      -> Just QCompile
    LElab{}         -> Just QElab
    LZonk{}         -> Just QZonk
    LMeta{}         -> Just QMeta
    LScope{}        -> Just QScope
    LUnify{}        -> Just QUnify
    LDebug{}        -> Just QDebug
    _               -> Nothing

compactIndentation :: [Log] -> [Log]
compactIndentation = go [[]] . go1 []  where

  go1 (LBegin{}: acc) (LEnd{}: ls) = go1 acc ls
  go1 (LEnd{}: acc) (LBegin{}: ls) = go1 acc ls
  go1 acc (l: ls) = go1 (l: acc) ls
  go1 acc [] = reverse acc

  go acc            (LBegin{}: ls)      = go ([]: acc) ls
  go (ac: []: acc)  (LEnd s: LEnd{}: ls)  = go (ac: acc) (LEnd s: ls)
  go (ac: ac': acc) (LEnd s: ls)        = go ((LEnd s: ac ++ LBegin s: ac'): acc) ls
  go (ac: acc)      (l: ls)           = go ((l: ac): acc) ls
  go acc            []                = reverse $ concat acc


indentLog :: [Log] -> [(Int, Log)]
indentLog = go 0  where

  go _ [] = []
  go i (LBegin{}: ls) = go (i+1) ls
  go i (LEnd{}: ls) = go (i-1) ls
  go i (l: ls) = (i, l): go i ls

showLog :: Int -> Log -> String
showLog i l = concat (replicate i "  ") <> show l

instance Show Log where
  show = \case
--    LCheck a b        -> sh' "check"    $ show a <> "  :?  " <> show b
    LMeta bv m        -> sh' "meta"     $ show m <> " [" <> intercalate ", " (map show bv) <> "]"
    LInfer a          -> sh' "infer"    $ show a
    LInferRes a b     -> sh' "inferres" $ show a <> "  :  " <> show b
    LEval a           -> sh' "eval"     $ show a
    LEvalRes a b      -> sh' "evalres"  $ show a <> "  ~>  " <> show b
    LSource s         -> sh' "source"   $ show s
    LCoerce a b         -> sh' "" $ "? :  " <> show a <> "  ~>  " <> show b
    LCoerceRes t        -> sh' "" $ "? tm =  " <> show t
    LUnify a b        -> sh' "unify"    $ show a <> "  ===  " <> show b
    LSolve bv a (Right b)     -> sh' "" $ show a <> " [" <> intercalate ", " (map show bv) <> "] := " <> show b
    LGeneralize a b   -> sh' "generalized" $ show a <> " = " <> show b
    LCompile a b    -> sh' "compiled" $ show a <> "  |  " <> show b
    LElab r           -> sh' "elab"    $ show $ tmToRaw r
    LZonk r           -> sh' "zonk"    $ show $ tmToRaw r
    LScope x          -> sh' "scoped"   $ show x
    LBegin s -> "begin " <> s
    LEnd s   -> "end " <> s
    LDebug s          -> sh' "debug" $ s
   where
    sh' "" s = s
    sh' tit s = tit <> "  " <> s

passes :: [LogTag] -> String -> String
passes tags t = unlines
     $ concat ["--------- log": map show log | QLog `elem` tags ]
    <> [ "-----------------" <> show tags ]
    <> map (uncurry showLog) (indentLog $ compactIndentation $ filterLog tags log)
    <> case res of
      Right (_a2, a2z, a2v, ty) ->
           [ "--------- type", show' ty ]
--        <> [ "--------- result inner tm", show' a2 ]
        <> [ "--------- tm", show' a2z ]
        <> [ "--------- val", show' a2v ]
      Left e ->
           [ "--------- error" ]
        <> [ e ]
 where
  ((res, log), _st) = runM do
    (a2, ta) <- infer_ =<< parse t
    t <- quote ta
    a2' <- zonk a2
    a2v <- withoutDynInfo $ eval a2' >>= quote
    pure (a2, a2', a2v, t)

-------------------------------- tests

hashString :: String -> String
hashString = map char . base 22 . hash (5381 :: Integer)  where

  -- djb2
  hash acc [] = acc
  hash acc (c: s) = hash (mod (fromIntegral (ord c) + 33 * acc) (2^128)) s 

  base 0 _ = []
  base n i = fromIntegral (mod i 64): base (n-1) (div i 64)

  char i = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_" !! i

getRes :: String -> IO (Maybe String, String -> IO ())
getRes s =
  (,) <$> (try (readFile name) <&> either (\(_ :: IOException) -> Nothing) Just)
      <*> (pure $ writeFile name)
 where
  name = "/tmp/" <> hashString s <> ".mcsipout"

askYN s = do
  putStr $ s <> "? "
  c <- getChar
  putChar '\n'
  case () of
    _ | c `elem` ['y','Y'] -> pure True
    _ | c `elem` ['n','N'] -> pure False
    _ -> askYN s

firstDiff a b = unlines $ take 1 $ concat $ zipWith' (\x y -> [x ++ "\n" ++ y | x /= y]) (lines a) (lines b)
 where
  zipWith' f as@(length -> i) bs@(length -> j) = zipWith f (as ++ replicate (j-i) "") (bs ++ replicate (i-j) "")

_test qs fn = do
  s <- readFile fn
  putStr $ passes qs s

diff fn = do
  s <- readFile fn
  (a, b) <- getRes s
  let r = passes [] s
  case a == Just r of
    True -> pure ()
    False -> do
      putStrLn $ "----------- old " <> fn
      putStrLn $ fromMaybe "" a
      putStrLn $ "----------- new " <> fn
      putStrLn r
      putStrLn $ "----------- first diff"
      putStrLn $ firstDiff (fromMaybe "<<<empty>>>" a) r
      askYN "accept change" >>= \case
        False -> pure ()
        True -> b r

testName n = "test/" <> n <> ".mcsip"

diffs = mapM_ (diff . testName) ["map", "power", "id1", "id2", "fun1", "nat", "natadt", "tree", "fin"]

main = do
  hSetBuffering stdin NoBuffering
  hSetBuffering stdout NoBuffering
  getArgs >>= \case
    ("diff": fs) -> mapM_ diff fs
    ["diffs"] -> diffs
    [fn] -> do
      s <- readFile fn
      putStr $ passes [] s

-------------------------------------------------

{- TODOs

- HPi az output tm-ben ok?

- escape kezelés
  - quote-nál Nat' helyett Nat-ot írni
  - escape észervétel solveMeta-nál
    - boundvars-ba betenni Nat'-t
    - lecsekkolni, hogy a konstruktorok is látszanak-e a meta solutionben
  - pruning support
  - ugyanezek függvényekre is
- ne készüljenek dinamikus id-k
  should be true:  eval (quote v) ~~ v

- staging
  - kiegészíteni szemantikával power.mcsip-et
  - staging transformation
    A) írni (generálni) egy HOAS evaluátort a main kifejezéshez ami kicseréli a konstruktorokat az interpretációjukra
    B) elab & eval & quote & transformált Tm-hez hozzáillesztés & eval
    C) rich elab & Tm transzformáció <<<ez a pont érdekes>>> & eval
    D) rich elab & standard környezethez illesztés & eval
    E) rich elab & <<<ez a pont érdekes>>> stage_eval
    - Mul leképezése
    - interpreter
    - rechecking
  - pattern match compilation
  - port arith.csip
  - (->) instead of Arr

- make Tm reparsable & retypeable
  - better printing of UserName

- type classes
- modules as records
- pattern synonyms
- closure-free -> stack-free transformation

- late scope checking of compiled rules (because of lhs guards)
- occurs check
- more/better error messages
- literals
- plug in syntactic frontend?

- better code generation
  - avoid explosion in pattern match compilation (with lets)
  - rule chain optimization
- erasure?
- performance
  - cache App info
  - Map -> IORef in St
  - meta chain opt.
  - sharing
    - observable sharing (add ids to App nodes)
    - name regions -- evaquate with deepforce
    - supercombinators instead of closures
    - gluing?

-}

