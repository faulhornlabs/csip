{-# language LambdaCase, BlockArguments, PatternSynonyms, ViewPatterns, OverloadedStrings #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}

module MikroCsipCore
  ( tc
  ) where

import Data.Char
import Data.List
import Data.Maybe
import Data.Functor ((<&>))
import Data.IORef
import Data.String
import qualified Data.Map as Map
import Control.Arrow
import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Except
import System.IO.Unsafe

--------------------------------------- tools

guardErr err True  = pure ()
guardErr err False = error err

fromJustError e m = m >>= maybe (error e) pure


newtype NoOrd a = MkNoOrd a

instance Eq  (NoOrd a) where (==)    = \_ _ -> True
instance Ord (NoOrd a) where compare = \_ _ -> EQ

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
  show (UserName (MkNoOrd s) i) = s ++ "_" ++ show i

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
pattern REApp a b = RVar "App" `RApp` a `RApp` b
pattern RPi   a b = RVar "Pi"  `REApp` a `REApp` b

---------------------------------

instance Show Raw where
  showsPrec p = \case
    RVar n     -> (n ++)
    REApp a b  -> showsPrec p $ RApp a b
    RTy  n a   -> parens (p > 8) $ showsPrec 9 n . (" : "   ++) . showsPrec 8 a
    RFun n a   -> parens (p > 8) $ showsPrec 9 n . (" :: "  ++) . showsPrec 8 a
    RLam n b   -> parens (p > 6) $ showsPrec 7 n . (". "    ++) . showsPrec 6 b
    RRule n b  -> parens (p > 6) $ showsPrec 7 n . ("  =  " ++) . showsPrec 6 b
    RAlt n b   -> parens (p > 6) $ showsPrec 7 n . (" => "  ++) . showsPrec 6 b
    RApp a b   -> parens (p > 14) $ showsPrec 14 a . (" "   ++) . showsPrec 15 b
   where
    parens True a = ("(" ++) . a . (")" ++)
    parens _    a = a

---------------------------------

isAlphaNumeric c = isAlphaNum c || c == '_' || c == '\'' || c == '#'
isGraphic c = c `elem` ("*+-^=@%$&~.!?:<>/\\|" :: String)

tokenize = filter (not . all isSpace) . groupBy g where
  g a b = isAlphaNumeric a && isAlphaNumeric b
       || isGraphic  a && isGraphic  b


parse :: Monad m => String -> m Raw
parse = fmap (foldr1 RDef) . mapM (h0 end . tokenize) . lines
 where
  end a [] = pure a
  end _ ts = error $ "end of file expected instead of\n" <> unwords ts

  expect t r (t': ts) | t' == t = r ts
  expect t _ ts = error $ "expected " <> show t <> " at\n" <> unwords ts

  h9 r _ ("(": ts) = h0 (\b -> expect ")" $ r b) ts
  h9 r _ (t: ts) | all isAlphaNumeric t = r (RVar t) ts
  h9 _ z ts = z ts

  h8 r = h9 (h8' r) (\ss -> error $ "unknown token at\n" <> unwords ss)
  h8' r a ts = h9 (\b -> h8' r (REApp a b)) (r a) ts

  hn os g r = g (hn' r) where
    hn' r a (n: ts) | Just f <- lookup n os = hn os g (\b -> r (f a b)) ts
    hn' r a        ts  = r a ts

  h0 = hn [(".",  RLam), ("=",  RRule), ("=>", RAlt)]
     $ hn [(":",  RTy), ("::",  RFun)]
     $ h8


---------------------------------------

data TName = MkTName_ (NoOrd StaticInfo) Name
  deriving (Eq, Ord)

pattern MkTName a b = MkTName_ (MkNoOrd a) b

data StaticInfo
  = SCon            -- constructor
  | SFun            -- function
  | SVar            -- local variable
  deriving (Eq, Ord)

pattern FunName  <- MkTName SFun  _
pattern ConName  <- MkTName SCon  _
pattern VarName  <- MkTName SVar  _

pattern PiName   = MkTName SCon "Pi"
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

pattern Apps :: TName -> [Tm] -> Tm
pattern Apps a bs <- (getApps -> (a, reverse -> bs))
  where Apps a bs =  foldl (:@) (Var a) bs

------------

tmToRaw :: Tm -> Raw
tmToRaw (Var a) = RVar $ show a
tmToRaw (a :@ b) = tmToRaw a `RApp` tmToRaw b

instance Show Tm where show = show . tmToRaw


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

--------------------------------------- elaboration monad

data St = MkSt
  { rules         :: !Rules
  , time          :: !Time     -- length of rules
  , counter       :: !Int      -- for unique identifier generation
  , globalCtx     :: !(Map.Map TName Ty)
  , nameMap       :: !(Map.Map SName TName)

  -- expression checking state
  , localCtx      :: ![(TName, Ty)]

  -- rule checking state
  , localRules    :: !Rules
  , scope         :: !Scope
  }

type Lens s r = s -> (r, r -> s)

scopeLens :: Lens St Scope
scopeLens st = (scope st, \x -> st {scope = x})

-- TODO: better Alternative?
newtype EM a = MkEM (StateT St IO a)
  deriving (Functor, Applicative, Monad, MonadIO)

unEM (MkEM m) = m

-------------------------------

newtype Val = MkVal (IORef (Time, View))

data View
  = VVar TName
  | VApp Val Val
  deriving Show

valToRaw (MkVal _) = RVar "<<val>>"

instance Show Val where show (MkVal _) = "<<val>>"


--------------------------------

view :: Val -> EM View
view w@(MkVal r) = do
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


---------

mkVal v = liftIO $ MkVal <$> newIORef (-1 :: Time, v)

mkVal' :: Tm -> Val
mkVal' t = unsafePerformIO $ MkVal <$> newIORef (maxBound :: Time, tmToView t)

tmToView (Var n) = VVar n
tmToView (a :@ b) = VApp (mkVal' a) (mkVal' b)

($$) :: Val -> Val -> EM Val
va $$ vb = mkVal (VApp va vb)

vVar :: TName -> EM Val
vVar n@ConName = pure $ mkVal' (Var n)
vVar n = mkVal (VVar n)

mLift :: (t1 -> t2 -> EM b) -> EM t1 -> EM t2 -> EM b
mLift f a b = a >>= \a -> b >>= \b -> f a b

mApp :: EM Val -> EM Val -> EM Val
mApp = mLift ($$)

vPi  a b = vVar  PiName `mApp` pure a `mApp` pure b

--------------------------------

type Ty = Val

vType = mkVal' (Var TypeName)


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

pattern SApps :: TName -> [Val] -> Spine
pattern SApps a bs <- (getSApps -> (a, reverse -> bs))

pattern VPi a b <- SHead PiName `SApp` a `SApp` b

sview :: Val -> EM Spine
sview v = view v >>= \case
  VVar n -> pure $ SHead n
  VApp a b -> sview a <&> \s -> SApp s b

-----------

eval :: Tm -> EM Val
eval (a :@ b) = eval a `mApp` eval b
eval (Var n) = vVar n

nquote :: Val -> EM Tm
nquote v = do
 view v >>= \case
  VVar n -> pure $ Var n
  VApp a b -> (:@) <$> nquote a <*> nquote b


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
  match' p v = lift2 (view v) >>= match p v

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

runEM :: EM a -> IO a
runEM (MkEM m)
  = flip evalStateT st m
 where
  st = MkSt
    { rules =
      [ MkRule (PCon constType `PApp` PVar a) [] (Var TypeName)
      , MkRule (PCon piFun `PApp` PVar a) [] (Var PiName :@ (Var PiName :@ Var a :@ Var constType) :@ Var constType)
      ]
    , time = 2
    , counter = 0
    , localRules = []

    , globalCtx = Map.fromList
      [ (TypeName, vType)
      , (PiName,   mkVal' $ Var PiName :@ Var TypeName :@ Var piFun)
      ]
    , localCtx = []
    , nameMap = Map.fromList
      [ ("Type", TypeName)
      , ("Pi",   PiName)
      ]
    , scope = S_RHS
    }

  a = MkTName SVar "a"
  b = MkTName SVar "b"
  c = MkTName SVar "c"
  piFun = MkTName SFun "piFun"
  constType = MkTName SFun "constType"

----------------------------

type LogMsg = String

infixr 5 +.+

a +.+ b = (++) <$> a <*> b

log' :: LogMsg -> EM ()
log' a = pure ()
         --liftIO $ putStrLn a

logM a = a >>= log'

instance IsString a => IsString (EM a) where
  fromString = pure . fromString

showM :: Show a => EM a -> EM String
showM = fmap show

newTName :: SName -> StaticInfo -> EM TName
newTName s k = do
  i <- newId
  pure $ MkTName k $ UserName (MkNoOrd s) i

nameMapLens st = (nameMap st, \x -> st { nameMap = x })

addName :: StaticInfo -> SName -> (TName -> EM a) -> EM a
addName si s cont = do
  n <- newTName s si
  MkEM $ localSt nameMapLens (Map.insert s n) $ unEM $ cont n

addName_ :: StaticInfo -> SName -> EM TName
addName_ si s = do
  n <- newTName s si
  MkEM $ modify \st -> st { nameMap = Map.insert s n $ nameMap st }
  pure n

currentTime :: EM Time
currentTime = MkEM $ gets time

context :: StaticInfo -> SName -> Ty -> EM ()
context si a b = do
  a <- addName_ si a
  MkEM $ modify (\st -> st { globalCtx = Map.insert a b $ globalCtx st})

withScope :: Scope -> EM a -> EM a
withScope s (MkEM m) = do
  log' $ "==== " ++ show s
  a <- MkEM $ localSt scopeLens (\_ -> s) m
  log' $ "==== scope end: " ++ show s
  pure a

checkPatternScope :: EM ()
checkPatternScope = MkEM do
  modify \st -> st { localRules = [], localCtx = [], nameMap = Map.filterKeys (`notElem` map (nameStr . name . fst) (localCtx st)) $ nameMap st }

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
getRules = do
  ss <- MkEM $ gets $ reverse . localRules
  rs <- MkEM $ gets $ reverse . rules
  pure $ ss <> rs

newId :: EM Int
newId = MkEM $ state \st -> (counter st, st {counter = 1 + counter st})

addSubst' :: TName -> Val -> EM ()
addSubst' n e = do
  e <- nquote e
  MkEM $ modify \st -> st {localRules = MkRule (PCon n) [] e: localRules st, time = 1 + time st}

getScope = MkEM $ gets scope

----------------------

equal' :: Val -> Val -> EM Bool
equal' a b = runExceptT (equal a b) <&> either (const False) (const True)
 where
  equal a b = do
    va <- lift $ sview a
    vb <- lift $ sview b
    case (va, vb) of
      (SApps an as, SApps bn bs) | an == bn, length as == length bs -> zipWithM_ equal as bs
      _ -> throwError ()


unify :: Val -> Val -> EM ()
unify a b = equal' a b >>= \case
  True -> pure ()
  False -> do
    s <- getScope
    va <- sview a
    vb <- sview b
    case (va, vb) of
      (SApps an@ConName as, SApps bn@ConName bs)
        | an == bn, length as == length bs -> zipWithM_ unify as bs

      (SHead n@VarName, vb) | s == S_LHS -> addSubst' n b
      (va, SHead n@VarName) | s == S_LHS -> addSubst' n a

      -- TODO: eta

      _ -> error $ "unification error: " ++ show (s, a, b, va, vb)


matchPi v = sview v >>= \case
  VPi a b -> pure (a, b)
  z -> error $ "not a pi: " ++ show z

-----------------------------------------

checkType :: Raw -> EM Val
checkType a = check a vType >>= eval

check :: Raw -> Ty -> EM Tm
check r t = do
  logM $ pure ("-- check begin:  " ++ show r ++ "  :?  ") +.+ showM (nquote t)
  s <- getScope
  nm <- MkEM $ gets nameMap
  r <- case r of
    RLam (RVar a) b -> do
      guardErr "lam is not allowed in patterns" $ s /= S_LHS
      (s, f) <- matchPi t
      (a, b') <- localContext a s \a -> do
        t' <- pure f `mApp` vVar a
        z <- check b t'
        pure (a, z)
      ns <- boundVars
      name <- newTName "lam" SFun
      let tm = foldl (:@) (Var name) (map Var ns)
      addRule $ MkRule (mkPat tm `PApp` PVar a) [] b'
      pure tm
    RVar n | s == S_LHS, n `Map.notMember` nm -> do
      n <- addName_ SVar n
      addBoundVar n t
      pure (Var n)
    r -> do
      (r, t') <- infer r
      unify t' t
      pure r
  log' $ "-- check end:  " ++ show r
  pure r

infer :: Raw -> EM (Tm, Ty)
infer r = do
  log' $ "-- infer begin:  " ++ show r
  (r, ty) <- case r of
    RLam a b  -> error "can't infer lambda"
    RVar n    -> do
      s <- getScope
      tn <- fromJustError ("not in scope: " <> show n) $ lookupName n
      ty <- fromJustError ("not in scope: " <> show n) $ MkEM $ gets \st ->
              lookup tn $ (if s /= S_LHS then localCtx st else []) ++ Map.assocs (globalCtx st)

      pure (Var tn, ty)
    REApp a b -> do
      (a, ts) <- infer a
      (t, f) <- matchPi ts
      b <- check b t
      s <- pure f `mApp` eval b
      pure (a :@ b, s)
    t -> error $ show t
--  logM $ "-- infer end:  " +.+ showM (nquote r) +.+ "  :  " +.+ showM (nquote ty)
  pure (r, ty)

elabRule te lhs acc (RAlt b (RRule c d)) = do
  (b, t) <- infer b
  c <- withScope S_LHS do
    (c, t') <- infer c
    unify t' t
    pure c
  elabRule te lhs ((b, mkPat c): acc) d
elabRule te lhs acc rhs = do
  rhs <- check rhs te
  pure $ MkRule lhs acc rhs

elab :: Raw -> ((Tm, Ty) -> EM a) -> EM a
elab (RDef r@(RTy (RVar a) b) c) cont = do
  log' $ "======== " ++ show r
  b <- checkType b
  context SCon a b
  elab c cont
elab (RDef r@(RFun (RVar a) b) c) cont = do
  log' $ "======== " ++ show r
  b <- checkType b
  context SFun a b
  elab c cont
elab (RDef r@(RRule lhs b) bb) cont = do
  log' $ "======== " ++ show r
  (lhs, te) <- withScope S_LHS (infer lhs)
  r <- elabRule te (mkPat lhs) [] b
  checkPatternScope
  addRule r
  elab bb cont
elab (RTy e t) cont = do
  t <- checkType t
  e <- check e t
  cont (e, t)
elab a cont = do
  log' $ "======== " ++ show a
  a <- infer a
  cont a

evalRaw :: Raw -> EM (Tm, Tm)
evalRaw r = do
  elab r \(r', t) -> do
    v <- eval r' >>= nquote
    t' <- nquote t
    pure (v, t')

------------

test_ s = runEM $ parse s >>= evalRaw

tc :: String -> IO String
tc t = test_ t <&> \(tm, ty) -> unlines $
        [ "--------- type", show ty ]
     <> [ "--------- tm", show tm ]

{- TODO
- simpler name handling?
- no Raw, just Tm with separate scope checking?
- simpler logging/printing?
- remove newId?
-}