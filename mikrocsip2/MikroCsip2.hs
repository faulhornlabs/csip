{-
running the tests:

> ghc -O2 -outputdir build MikroCsip2.hs
> ./MikroCsip2 diffs

-}


{-# language LambdaCase, BlockArguments, PatternSynonyms, ViewPatterns, MultilineStrings, OverloadedStrings #-}
{-#  OPTIONS_GHC -fdefer-type-errors #-}
import Data.Char
import Data.List
import Data.Maybe
import Data.Foldable
import Data.Functor hiding (unzip)
import Data.IORef
import Data.String
import qualified Data.Map as Map
import Control.Arrow
import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Exception
import System.Environment
import System.IO
import Debug.Trace

import MikroCsipCore (tc)

---------------------------------------

guardErr :: MonadError e f => e -> Bool -> f ()
guardErr err True  = pure ()
guardErr err False = throwError err

fromJustError :: MonadError e m => e -> m (Maybe a) -> m a
fromJustError e m = m >>= maybe (throwError e) pure

insertMap k v m | Nothing <- Map.lookup k m = pure $ Map.insert k v m
insertMap k v m = throwError $ "already in map: " ++ show k

modifyM :: MonadState s m => (s -> m (a, s)) -> m a
modifyM f = get >>= \s -> f s >>= \(a, s) -> put s >> pure a

hashString :: String -> String
hashString = map char . base 22 . hash (5381 :: Integer)  where

  -- djb2
  hash acc [] = acc
  hash acc (c: s) = hash (mod (fromIntegral (ord c) + 33 * acc) (2^128)) s 

  base 0 _ = []
  base n i = fromIntegral (mod i 64): base (n-1) (div i 64)

  char i = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_" !! i

--

newtype NoOrd a = MkNoOrd a

instance Eq  (NoOrd a) where (==)    = \_ _ -> True
instance Ord (NoOrd a) where compare = \_ _ -> EQ

--

solver :: Monad m => (a -> m (Maybe [a])) -> [a] -> m [a]
solver step rs = do
  ms <- forM rs \r -> step r >>= mapM (solver step)

  if all isNothing ms
    then pure rs
    else solver step $ concat $ zipWith (\a -> fromMaybe [a]) rs ms

---------------------------------------

type SName = String

data Name
  = UserName (NoOrd SName) Int    -- the Int is globally unique
  | BuiltinName SName             -- the SName should be globally unique
  deriving (Eq, Ord)

instance IsString Name where fromString = BuiltinName

nameStr :: Name -> SName
nameStr (BuiltinName s) = s
nameStr (UserName (MkNoOrd s) _) = s

instance Show Name where
  show (BuiltinName s) = s
  show (UserName (MkNoOrd s) i) | s `elem` ["meta", "fun", "var", "x", "tr", "lam", "h", "t", "a", "tt", "hh", "_"] = s ++ "_" ++ show i
  show (UserName (MkNoOrd s) i) = s -- ++ "_" ++ show i    -- TODO: cleaner show

---------------------------------

data Raw
  = RVar SName
  | RApp Raw Raw

pattern RRule a b = RVar "="   `RApp` a `RApp` b
pattern RAlt  a b = RVar "=>"  `RApp` a `RApp` b
pattern RDef  a b = RVar ";"   `RApp` a `RApp` b
pattern RTy   a b = RVar ":"   `RApp` a `RApp` b
pattern RFun  a b = RVar "::"  `RApp` a `RApp` b
pattern RLam  a b = RVar "."   `RApp` a `RApp` b
pattern RHApp a b = RVar "App" `RApp` a `RApp` RBraces b
pattern REApp a b = RVar "App" `RApp` a `RApp` b
pattern RPi   a b = RVar "Pi"  `REApp` a `REApp` b
pattern RHPi  a b = RVar "HPi" `REApp` a `REApp` b
pattern RWild     = RVar "_"
pattern RMeta     = RVar "_"

pattern RBraces a = RVar "{}"  `RApp` a

---------------------------------

{-
precedence table
  14   SPACE       15
  13   ->          12
  11   ~           10
  9    : ::        8
  7    . = =>      6
  3    ;           2
  1    \n          0
-}
instance Show Raw where
  showsPrec p = \case
    RVar n     -> (n ++)
    RTy  n a   -> parens (p > 8) $ showsPrec 9 n . (" : "  ++) . showsPrec 8 a
    RFun n a   -> parens (p > 8) $ showsPrec 9 n . (" :: " ++) . showsPrec 8 a
    RLam n b   -> parens (p > 6) $ showsPrec 7 n . (". "   ++) . showsPrec 6 b
    RRule n b  -> parens (p > 6) $ showsPrec 7 n . ("  =  "   ++) . showsPrec 6 b
    RAlt n b   -> parens (p > 6) $ showsPrec 7 n . (" => "   ++) . showsPrec 6 b
    REApp a b  -> showsPrec p $ RApp a b
    RApp  a b  -> parens (p > 14) $ showsPrec 14 a . (" " ++) . showsPrec 15 b
   where
    braces a = ("{" ++) . a . ("}" ++)

    parens True a = ("(" ++) . a . (")" ++)
    parens _    a = a

    parens' True a = ("(\n" ++) . a . ("\n)" ++)
    parens' _    a = a

---------------------------------

isAlphaNumeric c = isAlphaNum c || c == '_' || c == '\'' || c == '#'
isGraphic c = c `elem` ("*+-^=@%$&~.!?:<>/\\|" :: String)

tokenize = filter (not . all isSpace) . groupBy g where
  g a b = isAlphaNumeric a && isAlphaNumeric b
       || isGraphic  a && isGraphic  b


type Error = String

parse :: MonadError Error m => String -> m Raw
parse = fmap (foldr1 RDef) . mapM (h0 end . tokenize) . lines'
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

  h0 = hn [(".",  RLam), ("=",  RRule), ("=>", RAlt)]
     $ hn [(":",  RTy), ("::",  RFun)]
     $ hn [("->", pi)]
     $ h8

  pi (RBraces (RTy (REApp ns n) t)) b = pi (RBraces (RTy ns t)) $ pi (RBraces (RTy n t)) b
  pi (RBraces (RTy (RVar n) a)) b = RHPi a $ RLam (RVar n) b
  pi (RBraces (REApp as a)) b = pi (RBraces as) $ pi (RBraces a) b
  pi (RBraces (RVar n)) b = RHPi RMeta $ RLam (RVar n) b
  pi (RTy (REApp ns n) t) b = pi (RTy ns t) $ pi (RTy n t) b
  pi (RTy (RVar n) a) b = RPi a $ RLam (RVar n) b
  pi (REApp as a@RTy{}) b = pi as $ pi a b
  pi a b = RPi a $ RLam RWild b


---------------------------------

rVars :: Raw -> EM [SName]
rVars r = nub <$> fv r
 where
  fv = \case
    RLam (RVar n) a -> filter (/= n) <$> fv a
    RLam (RTy (RVar n) t) a -> (<>) <$> fv t <*> (filter (/= n) <$> fv a)
    RLam _ _ -> error "rVars"
    a `RApp` b -> (<>) <$> fv a <*> fv b
    RVar n@(c: _) | isLower c -> lookupName n <&> maybe [n] (const [])
    RVar{} -> pure mempty


---------------------------------------

data TName = MkTName_ (NoOrd StaticInfo) Name
  deriving (Eq, Ord)

pattern MkTName a b = MkTName_ (MkNoOrd a) b

data StaticInfo
  = SCon            -- constructor
  | SFun            -- function
  | SVar            -- local variable
  | SMeta           -- meta (top level function)
  deriving (Eq, Ord)

pattern MetaName <- MkTName SMeta _
pattern FunName  <- MkTName SFun  _
pattern ConName  <- MkTName SCon  _
pattern VarName  <- MkTName SVar  _

pattern PiName   = MkTName SCon "Pi"
pattern HPiName  = MkTName SCon "HPi"
pattern TypeName = MkTName SCon "Type"


instance Show TName where show (MkTName _ n) = show n

name :: TName -> Name
name (MkTName _ n) = n


---------------------------------------

data Tm
  = Var TName
  | Tm :@ Tm

getApps ((getApps -> (a, as)) :@ b) = (a, b: as)
getApps (Var v) = (v, [])

pattern Apps a bs <- (getApps -> (a, reverse -> bs))
  where Apps a bs =  foldl (:@) (Var a) bs

------------

tmToRaw :: Tm -> Raw
tmToRaw (Var a) = RVar $ show a
tmToRaw (TLam a b) = RLam (tmToRaw a) (tmToRaw b)
tmToRaw (HApp a b) = RHApp (tmToRaw a) (tmToRaw b)
tmToRaw (a :@ b) = tmToRaw a `RApp` tmToRaw b

instance Show Tm where show = show . tmToRaw


------------------

-- annotated Tm
type ATm = Val

pattern AVarName = MkTName SCon "AVar"
pattern ATmName  = MkTName SCon "ATm"
pattern ALamName = MkTName SCon "ALam"
pattern AAppName = MkTName SCon "AApp"
pattern AHAppName = MkTName SCon "AHApp"

pattern TLam n m = Var ALamName :@ n :@ m
pattern HApp n m = Var AHAppName :@ n :@ m

aTm :: Tm -> EM ATm
aTm a = vVar ATmName `mApp` eval a

aVar :: TName -> EM ATm
aVar a = vVar AVarName `mApp` vVar_ a `mApp` vVar a

aLam :: Tm -> TName -> ATm -> EM ATm
aLam a b c = vVar ALamName `mApp` eval a `mApp` vVar_ b `mApp` pure c

aApp :: ATm -> ATm -> EM ATm
aApp a b = vVar AAppName `mApp` pure a `mApp` pure b
aHApp a b = vVar AHAppName `mApp` pure a `mApp` pure b

pattern AVar n m  <- SApps AVarName [n, m]
pattern ATm  n   <- SApps ATmName  [n]
pattern ALam n a b  <- SApps ALamName [n, a, b]
pattern AApp a b <- SApps AAppName [a, b]
pattern AHApp a b <- SApps AHAppName [a, b]

evalATm :: ATm -> EM Val
evalATm v = vVar EvalFunName `mApp` pure v


ruleTm :: Bool -> ATm -> EM Tm
ruleTm pat t = do
 sview' t >>= \case
  AApp a b   -> (:@) <$> ruleTm pat a <*> ruleTm pat b
  AHApp a b  -> (:@) <$> ruleTm pat a <*> ruleTm pat b
  ATm n | not pat      -> nquote n
  AVar n m | not pat       -> nquote m
  AVar n m    -> nquote n
  ALam n _ _ | not pat -> nquote n
  xx -> error $ "incomplete ATm: " ++ show xx

ruleTm' :: Bool -> ATm -> EM Tm
ruleTm' pat t = do
 sview' t >>= \case
  AApp a b   -> (:@) <$> ruleTm' pat a <*> ruleTm' pat b
  AHApp a b  -> HApp <$> ruleTm' pat a <*> ruleTm' pat b
  ATm n | not pat      -> nquote' n
  AVar n m | not pat       -> nquote' m
  AVar n m   -> nquote' n
  ALam _ a b | not pat -> TLam <$> nquote' a <*> ruleTm' pat b
  xx -> error $ "incomplete ATm: " ++ show xx


--------------------------------

{- TODO
data Pat
  = PVar TName
  | PCon TName [Pat]
-}
data Pat
  = PVar TName
  | PCon TName
  | PApp Pat Pat

mkPat (a :@ b) = PApp (mkPat a) (mkPat b)
mkPat (Var n@VarName) = PVar n
mkPat (Var n) = PCon n

patToRaw :: Pat -> Raw
patToRaw (PVar a) = RVar $ show a
patToRaw (PCon a) = RVar $ show a
patToRaw (a `PApp` b) = patToRaw a `RApp` patToRaw b

instance Show Pat where show = show . patToRaw

data Rule = MkRule Pat [(Tm, Pat)] Tm

ruleToRaw (MkRule l mid r) = RRule (patToRaw l) $ foldr (\(a, b) r -> RAlt (tmToRaw a) $ RRule (patToRaw b) r) (tmToRaw r) mid


instance Show Rule where show = show . ruleToRaw

type Rules = [Rule]

data Scope
  = S_LHS
  | S_RHS
  deriving (Eq, Show)

type Time = Int

data Task
  = Coerce Scope Bool Tm Val Val
  | Unify Scope Val Val
  deriving Show

showTask (Coerce s x t a b) = pure (show s ++ " " ++ show x ++ " |   " ++ show t ++ " :  ") +.+ showM (nquote a) +.+ "  ~~>  " +.+ showM (nquote b)
showTask (Unify s a b) = pure (show s ++ " |   ") +.+ showM (nquote a) +.+ "  ~~  " +.+ showM (nquote b)

type Log = [String]

--------------------------------------- elaboration monad

data St = MkSt
  { rules         :: !Rules
  , time          :: !Time     -- length of rules
  , counter       :: !Int      -- for unique identifier generation
  , globalCtx     :: !(Map.Map TName Ty)
  , nameMap       :: !(Map.Map SName TName)

  -- expression checking state
  , localCtx      :: ![(TName, Ty)]
  , tasks     :: ![Task]

  -- rule checking state
  , substs        :: ![(TName, Tm)]
  , scope         :: !Scope

  , log_  :: !Log
  }

scopeLens st = (scope st, \x -> st {scope = x})

-- TODO: better Alternative?
newtype EM a = MkEM (ExceptT Error (StateT St IO) a)
  deriving (Functor, Applicative, Monad, Alternative, MonadError Error, MonadIO)

-------------------------------

data Val = MkVal !Tm !(Maybe Ref)

type Ref = IORef (Time, View)

data View
  = VVar TName
  | VApp Val Val
  deriving Show

valToRaw (MkVal t _) = tmToRaw t

--------------------------------

view :: Val -> EM View
view (MkVal v Nothing) = pure $ case v of
  Var n  -> VVar n
  a :@ b -> VApp (MkVal a Nothing) (MkVal b Nothing)
view w@(MkVal v (Just r)) = do
  t <- currentTime
  (t', e) <- liftIO $ readIORef r
  if t' == t then pure e else do
    e' <- go e =<< getRules
    liftIO $ writeIORef r (t, e')
    pure e'
 where
  go e [] = pure e
  go e (r: rs) = ruleFun r w e >>= \case
    Just v -> view v
    Nothing -> go e rs

view' (MkVal (Var n@VarName) Nothing) = pure $ VVar n
view' v = view v >>= \case
  VVar n -> goV n =<< getSubsts
  w -> pure w
 where
  goV n [] = pure $ VVar n
  goV n ((n', v): rs)
    | n' == n = eval v >>= view'
    | otherwise = goV n rs


---------

mkVal t v = liftIO $ MkVal t . Just <$> newIORef (-1 :: Time, v)

($$) :: Val -> Val -> EM Val
va@(MkVal a _) $$ vb@(MkVal b _) = mkVal (a :@ b) (VApp va vb)

vVar :: TName -> EM Val
vVar n@ConName = pure $ MkVal (Var n) Nothing
vVar n = mkVal (Var n) (VVar n)

vVar_ :: TName -> EM Val
vVar_ n@ConName = pure $ MkVal (Var n) Nothing
vVar_ n@VarName = pure $ MkVal (Var n) Nothing
vVar_ n = mkVal (Var n) (VVar n)

mLift f a b = a >>= \a -> b >>= \b -> f a b

mApp = mLift ($$)

vPi  a b = vVar  PiName `mApp` pure a `mApp` pure b
vHPi a b = vVar HPiName `mApp` pure a `mApp` pure b

--------------------------------

type Ty = Val

vType = MkVal (Var TypeName) Nothing


--------------------------------

data Spine
  = SHead TName
  | SApp Spine Val

spineToRaw :: Spine -> Raw
spineToRaw (SHead n) = RVar $ show n
spineToRaw (SApp a b) = RApp (spineToRaw a) (valToRaw b)

instance Show Spine where show = show . spineToRaw

getSApps (SApp (getSApps -> (a, as)) b) = (a, b: as)
getSApps (SHead v) = (v, [])

pattern SApps a bs <- (getSApps -> (a, reverse -> bs))

pattern VHPi a b <- SHead HPiName `SApp` a `SApp` b

sview :: Val -> EM Spine
sview v = view v >>= \case
  VVar n -> pure $ SHead n
  VApp a b -> sview a <&> \s -> SApp s b

sview' :: Val -> EM Spine
sview' v = view' v >>= \case
  VVar n -> pure $ SHead n
  VApp a b -> sview' a <&> \s -> SApp s b

-----------

eval :: Tm -> EM Val
eval (a :@ b) = join $ ($$) <$> eval a <*> eval b
eval (Var n) = vVar n

quote :: Val -> EM Tm
quote (MkVal v _) = pure v

nquote :: Val -> EM Tm
nquote v = do
 view v >>= \case
  VVar n -> pure $ Var n
  VApp a b -> (:@) <$> nquote a <*> nquote b

nquote' :: Val -> EM Tm
nquote' v = do
 view' v >>= \case
  VVar HPiName -> pure $ Var PiName
  VVar n -> pure $ Var n
  VApp a b -> (:@) <$> nquote' a <*> nquote' b


---------------------------------

type EM' = StateT [(TName, Val)] (ExceptT () EM)

lift2 :: EM a -> EM' a
lift2 m = lift $ lift m

ruleFun :: Rule -> Val -> View -> EM (Maybe Val)
ruleFun (MkRule lhs mid rhs) v t = fmap (either (const Nothing) Just) $ runExceptT $ flip evalStateT [] do
  match lhs v t
  forM_ mid \(b, c) -> evalLoc b >>= match' c
  evalLoc rhs
 where
  match' :: Pat -> Val -> EM' ()
  match' p v = lift2 (view' v) >>= match p v

  match :: Pat -> Val -> View -> EM' ()
  match (PVar n) t _ = modify ((n, t):)
  match (PCon n) _ (VVar n') | n == n' = pure ()
  match (PApp a b) _ (VApp a' b') = match' a a' >> match' b b'
  match _ _ _ = throwError ()

  evalLoc :: Tm -> EM' Val
  evalLoc t@(Var n) = gets (lookup n) >>= maybe (lift $ lift $ vVar n) pure
  evalLoc (a :@ b) = do
    a <- evalLoc a
    b <- evalLoc b
    lift $ lift $ a $$ b


----------------------------

runEM :: EM a -> IO (Either Error a, St)
runEM (MkEM m)
  = flip runStateT st
  $ runExceptT m
 where
  st = MkSt
    { rules =
      [ MkRule (PCon constType `PApp` PVar a) [] (Var TypeName)
      , MkRule (PCon piFun `PApp` PVar a) [] (Var PiName :@ (Var PiName :@ Var a :@ Var constType) :@ Var constType)
      , MkRule (PCon IdFunName `PApp` PVar a) [] (Var a)
      , MkRule (eval' (PCon AAppName `PApp` PVar a `PApp` PVar b)) [] (eval (Var a) :@ eval (Var b))
      , MkRule (eval' (PCon AHAppName `PApp` PVar a `PApp` PVar b)) [] (eval (Var a) :@ eval (Var b))
      , MkRule (eval' (PCon ATmName `PApp` PVar a)) [] (Var a)
      , MkRule (eval' (PCon AVarName `PApp` PVar a `PApp` PVar b)) [] (Var b)
      , MkRule (eval' (PCon ALamName `PApp` PVar a `PApp` PVar b `PApp` PVar c)) [] (Var a)
      ]
    , time = 2
    , counter = 0
    , tasks = []
    , substs = []

    , globalCtx = Map.fromList
      [ (TypeName, vType)
      , (PiName,    MkVal (Var PiName :@ Var TypeName :@ Var piFun) Nothing)
      , (HPiName,   MkVal (Var PiName :@ Var TypeName :@ Var piFun) Nothing)
      ]
    , localCtx = []
    , nameMap = Map.fromList
      [ ("Type", TypeName)
      , ("Pi",   PiName)
      , ("HPi",  HPiName)
      ]
    , scope = S_RHS
    , log_ = []
    }

  a = MkTName SVar "a"
  b = MkTName SVar "b"
  c = MkTName SVar "c"
  piFun = MkTName SFun "piFun"
  constType = MkTName SFun "constType"
  eval a = Var EvalFunName :@ a
  eval' a = PCon EvalFunName `PApp` a

pattern IdFunName   = MkTName SFun "id"
pattern EvalFunName = MkTName SFun "eval"

----------------------------

type LogMsg = String

infixr 5 +.+

a +.+ b = (++) <$> a <*> b

log' :: LogMsg -> EM ()
log' a = pure ()
         --liftIO $ putStrLn a

logM a = a >>= log'

log'' :: String -> EM ()
log'' a = do
  liftIO $ putStrLn a
  MkEM $ modify \st -> st {log_ = a: log_ st}

instance IsString a => IsString (EM a) where
  fromString = pure . fromString

showM :: Show a => EM a -> EM String
showM = fmap show

newTName :: SName -> StaticInfo -> EM TName
newTName s k = do
  i <- newId
  pure $ MkTName k $ UserName (MkNoOrd s) i

newTName' n_ k = case n_ of
    '#': s -> pure (s, MkTName k (BuiltinName s))
    s      -> (,) s <$> newTName s k


nameMapLens st = (nameMap st, \x -> st { nameMap = x })

addName :: StaticInfo -> SName -> (TName -> EM a) -> EM a
addName si s cont = do
  (s, n) <- newTName' s si
  MkEM $ localSt nameMapLens (Map.insert s n) $ unEM $ cont n

addName_ :: StaticInfo -> SName -> EM TName
addName_ si s = do
  (s, n) <- newTName' s si
  MkEM $ modify \st -> st { nameMap = Map.insert s n $ nameMap st }
  pure n

unEM (MkEM m) = m

currentTime :: EM Time
currentTime = MkEM $ gets time

context :: StaticInfo -> SName -> Ty -> EM a -> EM a
context si a b (MkEM m) = addName si a \a -> MkEM $ modify (\st -> st { globalCtx = Map.insert a b $ globalCtx st}) >> m

withScope :: Scope -> EM a -> EM a
withScope s (MkEM m) = do
  log' $ "==== " ++ show s
  a <- MkEM $ localSt scopeLens (\_ -> s) m
  log' $ "==== scope end: " ++ show s
  pure a

checkPatternScope :: EM ()
checkPatternScope = MkEM do
  modify \st -> st { substs = [], localCtx = [], nameMap = Map.filterKeys (`notElem` map (nameStr . name . fst) (localCtx st)) $ nameMap st }

type Lens s r = s -> (r, r -> s)

localCtxLens :: Lens St [(TName, Ty)]
localCtxLens st = (localCtx st, \x -> st {localCtx = x})

localSt :: MonadState s m => Lens s r -> (r -> r) -> m a -> m a
localSt l f m = do
  st <- get
  let (r, g) = l st
  put $ g $ f r
  a <- m
  st <- get
  put $ snd (l st) r
  pure a


localContext :: SName -> Ty -> (TName -> EM a) -> EM a
--localContext "_" b m = m  -- TODO!!
localContext a b cont = do
  addName SVar a \a -> MkEM $ localSt localCtxLens ((a, b):) $ unEM $ cont a

addBoundVar a ty = MkEM $ modify \st -> st {localCtx = (a, ty): localCtx st}


boundVars :: EM [TName]
boundVars = MkEM $ gets $ reverse . map fst . localCtx

lookupName :: SName -> EM (Maybe TName)
lookupName n = MkEM $ gets $ Map.lookup n . nameMap

addRule :: Rule -> EM ()
addRule r = do
  log' $ show r
  MkEM $ modify \st -> st {rules = r: rules st, time = 1 + time st}

getRules :: EM Rules
getRules = MkEM $ gets \st -> {- [MkRule (PCon n) [] t | (n, t) <- reverse $ substs st] <> -} reverse (rules st)

getSubsts :: EM [(TName, Tm)]
getSubsts = MkEM $ gets substs

newId :: EM Int
newId = MkEM $ state \st -> (counter st, st {counter = 1 + counter st})

addSubst' :: TName -> Val -> EM ()
addSubst' n e = do
  e <- nquote e
  MkEM $ modify \st -> st {substs = (n, e): substs st, time = 1 + time st}

lookupEnv'' :: (St -> [(TName, a)]) -> TName -> EM a
lookupEnv'' part n = MkEM $ do
  env <- get
  maybe (throwError $ "not in scope: " <> show n) pure $ lookup n $ part env

getScope = MkEM $ gets scope

------------------

newMeta_ :: SName -> EM Tm
newMeta_ n = do
  m <- newTName n SMeta
  ns <- boundVars
  pure $ Apps m $ map Var ns

newAMeta ty = getScope >>= \s -> newAMeta_ s ty

newAMeta_ :: Scope -> Ty -> EM (Tm, ATm)
newAMeta_ s ty = do
  x <- case s of
    S_LHS -> do
      n <- newTName "var" SVar
      addBoundVar n ty
      (,) (Var n) <$> aVar n
    _ -> do
      m <- newMeta_ "a"
      (,) m <$> aTm m
  log' $ "## new ameta: " ++ show x
  pure x

solveMeta :: Tm -> Tm -> EM ()
solveMeta n t = addRule $ MkRule (mkPat n) [] t

solveMeta' n v = do
  t <- quote v
  solveMeta (Var n) t

-- TODO: pruning
solveMeta'' n vs v = do
  t <- quote v
  ts <- mapM nquote vs
  solveMeta (Apps n $ map arg ts) t
 where
  arg n@(Var VarName) = n
--  arg _ = Var Wildcard

distinctVars vs = maybe False distinct . sequence . map f <$> mapM view vs
 where
  f (VVar n@VarName) = Just n
  f _ = Nothing

distinct vs = length vs == length (nub vs)

----------------------

-- TODO: remove?
data Level = L1 | L2
  deriving (Eq, Show)

equal :: Val -> Val -> EM ()
equal a b = do
  va <- sview' a
  vb <- sview' b
  case (va, vb) of
    (SApps an as, SApps bn bs) | an == bn, length as == length bs -> zipWithM_ equal as bs
    _ -> throwError "..."

equal' a b = catchError (equal a b >> pure True) \_ -> pure False

unify_ :: Level -> Scope -> Val -> Val -> EM (Maybe [Task])
unify_ l s a b = do
 equal' a b >>= \case
  True -> pure $ Just []
  False -> do
   va <- sview' a
   vb <- sview' b
   let unificationError = throwError $ "unification error: " ++ show (l, s, a, b, va, vb)
   case (va, vb) of
    (SApps an@ConName as, SApps bn@ConName bs)
      | an /= bn               -> unificationError
      | length as /= length bs -> unificationError
      | otherwise              -> pure $ Just $ zipWith (Unify s) as bs

    (SApps n@MetaName es, _) -> distinctVars es >>= \case
       True -> solveMeta'' n es b >> pure (Just [])
       _ -> pure Nothing
    (_, SApps n@MetaName es) -> distinctVars es >>= \case
       True -> solveMeta'' n es a >> pure (Just [])
       _ -> pure Nothing

    (SHead n@VarName, SHead VarName)
      | s == S_LHS -> addSubst' n b >> pure (Just [])
      | otherwise  -> pure Nothing
    (SHead n@VarName, vb) | s == S_LHS -> rigid' vb >>= \case
      True -> addSubst' n b >> pure (Just [])
      _    -> pure Nothing
    (va, SHead n@VarName) | s == S_LHS -> rigid' va >>= \case
      True -> addSubst' n a >> pure (Just [])
      _    -> pure Nothing

    -- TODO: eta

    _ -> pure Nothing

type ATmTr = Tm  --  ATm -> ATm

coerce' :: Scope -> Bool -> Val -> Val -> EM ([Task], ATmTr)
coerce' s hlam got expected = do
  tr <- newMeta_ "tr"
  pure ([Coerce s hlam tr got expected], tr)

coerce_ :: Level -> Scope -> Bool -> Tm -> Val -> Val -> EM (Maybe [Task])
coerce_ l s hlam tr a{-got-} b{-expected-} = do
  sa <- sview' a
  sb <- sview' b
  log' $ "-  " ++ show tr ++ " :  " ++ show sa ++ "  ~?~>  " ++ show sb
  case (sa, sb) of

    (VHPi ty d, b')
      | VHPi u w <- b' -> error "TODO"
      | rigid s b' -> do
        (y, m) <- newAMeta_ s ty
        x <- pure d `mApp` eval y
        (cs, f) <- coerce' s hlam {-(VApp d (VVar m))-} x b
        m' <- quote m
        x <- newTName "x" SVar
        r <- createLam x (f :@ (Var AAppName {-AHAppName-} :@ Var x :@ m'))
        solveMeta tr r
        pure $ Just cs
      | otherwise -> pure Nothing

    (a', b') | rigid s a', rigid s b' -> do
      solveMeta tr $ Var IdFunName
      pure $ Just [Unify s a b]

    _ -> pure Nothing

{- TODO

    (VHPi t s, VHPi u w) -> do
      q <- coerce_ s True u t
      newBVar "r" {-u-} \v -> do
        h <- mlift (coerce_ s True) (mApp (pure s) $ eval $ q $ TVar v) (pure $ VApp w (VVar v))
        pure \x -> tLam v $ h $ TApp x $ q $ TVar v

    (VPi t s, VPi u w) -> do
      q <- coerce_ s True u t
      newBVar "r" {- u -} \v -> do
        h <- mlift (coerce_ s True) (mApp (pure s) $ eval $ q $ TVar v) (pure $ VApp w (VVar v))
        pure \x -> tLam v $ h $ TApp x $ q $ TVar v

    (a, VHPi _ d)
      | hlam, rigid a -> do
        f <- mlift (coerce_ s hlam) (pure a) (mApp (pure d) mMeta)
        pure \x -> TLam WildCard $ f x
-}

rigid _     (SApps ConName  _) = True
rigid _     (SApps FunName  _) = False    -- TODO
rigid _     (SApps VarName  _) = True
--rigid S_RHS (SApps VarName  _) = True
--rigid S_LHS (SApps VarName  _) = False
rigid _     (SApps MetaName _) = False

rigid' (SApps ConName  _) = pure True
rigid' (SApps VarName  _) = pure True
rigid' (SApps MetaName _) = pure False
rigid' (SApps FunName  vs) = catchError (mapM_ f vs >> pure True) \_ -> pure False
 where
  f x = view x >>= \case
    VVar MetaName -> throwError "..."
    VVar _ -> pure ()
    VApp a b -> f a >> f b


----------------------

solveTasks :: EM ()
solveTasks = do
  cs <- MkEM $ gets tasks <* modify \st -> st { tasks = [] }
  logM $ mapM showTask cs <&> \ts -> unlines $ "~~~~~~~~~~~~~~~ constraints": ts ++ ["~~~~~~~~~~~~~~~"]
  solve $ cs -- reverse cs
 where
  solve :: [Task] -> EM ()
  solve ts = solver (solveTask L1) ts >>= \case
      [] -> pure ()
      ts -> mapM showTask ts >>= \ts -> throwError $ unlines $ "unsolvable constraints:": ts

  solveTask :: Level -> Task -> EM (Maybe [Task])
  solveTask l = \case
    Unify s a b -> unify_ l s a b
    Coerce s hlam tr got expected -> coerce_ l s hlam tr got expected

------------------------

coerce :: Bool -> Val -> Val -> EM ATmTr
coerce hlam got expected = do
  tr <- newMeta_ "tr"
  s <- getScope
  MkEM $ modify \st -> st { tasks = Coerce s hlam tr got expected: tasks st }
  logM $ pure ("---- " ++ show tr ++ "  :  ") +.+ showM (nquote got) +.+ "  ~~>  " +.+ showM (nquote expected)
  pure tr

unify :: Scope -> Val -> Val -> EM ()
unify s a b = do
  MkEM $ modify \st -> st { tasks = Unify s a b: tasks st }


-----------------------------------------

checkType :: Raw -> EM Val
checkType a = do
  ns <- rVars a
  let a' = foldr (\n a -> RHPi RMeta $ RLam (RVar n) a) a ns
  checkType' a'

checkType_ a = do
  ns <- rVars a
  let a' = foldr (\n a -> RHPi RMeta $ RLam (RVar n) a) a ns
  x <- check a' vType
  x' <- evalATm x
  solveTasks
  y <- ruleTm' False x
  pure (x', y)

checkType_' a = do
  ns <- rVars a
  let a' = foldr (\n a -> RHPi RMeta $ RLam (RVar n) a) a ns
  x <- check a' vType
  x' <- evalATm x
  pure (x', x)

checkType' a = check a vType >>= evalATm

createLam a b' = do
  ns <- boundVars
  name <- newTName "lam" SFun
  let tm = foldl (:@) (Var name) (map Var ns)
  addRule $ MkRule (mkPat tm `PApp` PVar a) [] b'
  pure tm

check :: Raw -> Ty -> EM ATm
check r t = do
  logM $ pure ("-- check begin:  " ++ show r ++ "  :?  ") +.+ showM (nquote t)
  s <- getScope
  nm <- MkEM $ gets nameMap
  r <- case r of
    RLam (RVar a) b -> do
      getScope >>= guardErr "lam is not allowed in patterns" . (/= S_LHS)
      s <- newMeta_ "tt"  >>= eval
      f <- newMeta_ "hh"  >>= eval
      p <- vPi s f
      tr <- coerce True p t
      (a, b', z) <- localContext a s \a -> do
        a' <- vVar a
        t' <- f $$ a'
        z <- check b t'
        solveTasks
        b' <- ruleTm False z
        pure (a, b', z)
      tm <- createLam a b'
      eval tr `mApp` aLam tm a z
    RMeta -> do
      snd <$> newAMeta t
    RVar n | s == S_LHS, n `Map.notMember` nm -> do
      n <- addName_ SVar n
      addBoundVar n t
      aVar n
    r | s == S_RHS -> do
      (r', t') <- infer r
      f <- coerce True t' t
      eval f `mApp` pure r'
    r | s == S_LHS -> do
      (r', t') <- infer r
      unify s t t'  -- TODO: allow coerce, view-app transformation
      pure r'
  log' $ "-- check end:  " ++ show r
  pure r

infer :: Raw -> EM (ATm, Ty)
infer r = do
  log' $ "-- infer begin:  " ++ show r
  (r, ty) <- case r of
    RLam a b  -> error "can't infer lambda"
    RMeta     -> error "TODO"
    RVar n    -> do
      s <- getScope
      tn <- fromJustError ("not in scope: " <> show n) $ lookupName n
      ty <- lookupEnv'' (\st -> (if s /= S_LHS then localCtx st else []) ++ Map.assocs (globalCtx st)) tn
      av <- aVar tn
      pure (av, ty)
    REApp a b -> do
      (a', ts) <- infer a
      t <- newMeta_ "t" >>= eval
      f <- newMeta_ "h" >>= eval
      tr <- coerce False ts =<< vPi t f
      -- coercion may introduce vars on LHS, so
      getScope >>= \case S_LHS -> solveTasks; _ -> pure ()
      b' <- check b t
      b'' <- evalATm b'
      s' <- f $$ b''
      ta <- eval tr `mApp` pure a'
      z <- aApp ta b'
      pure (z, s')
    t -> error $ show t
  logM $ "-- infer end:  " +.+ showM (nquote r) +.+ "  :  " +.+ showM (nquote ty)
  pure (r, ty)

elabRule te lhs acc (RAlt b (RRule c d)) = do
  (b, t) <- infer b
  c <- withScope S_LHS do
    (c, t') <- infer c
    solveTasks
    unify S_LHS t' t           -- TODO: allow coerce here
    solveTasks
    pure c
  elabRule te lhs ((b, c): acc) d
elabRule te lhs acc rhs = do
  rhs <- check rhs te
  solveTasks
  lhs <- mkPat <$> ruleTm True lhs
  acc <- forM acc \(a, b) -> (,) <$> ruleTm False a <*> (mkPat <$> ruleTm True b)
  rhs <- ruleTm False rhs
  pure $ MkRule lhs acc rhs

elab :: Raw -> ((ATm, Ty) -> EM a) -> EM a
elab (RDef r@(RTy (RVar a) b) c) cont = do
  log' $ "======== " ++ show r
  (b, b') <- checkType_ b
  log'' $ show $ RTy (RVar a) $ tmToRaw b'
  context SCon a b $ elab c cont
elab (RDef r@(RFun (RVar a) b) c) cont = do
  log' $ "======== " ++ show r
  (b, b') <- checkType_ b
  log'' $ show $ RFun (RVar a) $ tmToRaw b'
  context SFun a b $ elab c cont
elab (RDef r@(RRule lhs b) bb) cont = do
  log' $ "======== " ++ show r
  (lhs, te) <- withScope S_LHS (infer lhs)
  solveTasks
  r <- elabRule te lhs [] b
  solveTasks
  checkPatternScope
  addRule r
  log'' $ show r
  elab bb cont
elab (RTy e t) cont = do
  (t, t') <- checkType_' t
  e <- check e t
  solveTasks
  e' <- ruleTm' False e
  t' <- ruleTm' False t'
  log'' $ show $ RTy (tmToRaw e') (tmToRaw t')
  cont (e, t)
elab a cont = do
  log' $ "======== " ++ show a
  a@(e, t) <- infer a
  solveTasks
  e' <- ruleTm' False e
  t' <- nquote' t  -- TODO
  log'' $ show $ RTy (tmToRaw e') (tmToRaw t')
  cont a

evalRaw :: Raw -> EM (Tm, Tm)
evalRaw r = do
  elab r \(r', t) -> do
    v <- evalATm r' >>= nquote
    t' <- nquote t
    pure (v, t')

------------

instance Show Val where show (MkVal v _) = show v


------------

test_ s = runEM $ parse s >>= evalRaw


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


diff = diff_ passes

diff_ passes fn = do
  liftIO $ putStrLn $ "========= " ++ fn
  s <- readFile fn
  (a, b) <- getRes s
  r <- passes fn s
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

diffs = mapM_ (diff . testName) ["imp", "half", "cmp", "power", "powerStaged"]

main = do
  hSetBuffering stdin NoBuffering
  hSetBuffering stdout NoBuffering
  getArgs >>= \case
    ("diff": fs) -> mapM_ diff fs
    ["diffs"] -> diffs
    [fn] -> do
      s <- readFile fn
      putStr =<< passes fn s


passes :: FilePath -> String -> IO String
passes fn t = do
  (res, st) <- test_ t
  r <- case res of
      Right (tm, ty) -> do
        let fnc = fn <> ".core"
        writeFile fnc $ unlines $ reverse $ log_ st
        diff_ (\_ x -> tc x) fnc
        pure $
            [ "--------- type", show ty ]
         <> [ "--------- tm", show tm ]
      Left e -> pure $
           [ "--------- error" ]
        <> [ e ]
  pure $ unlines r

{- TODO
- just one reduction
- better core generation
-}