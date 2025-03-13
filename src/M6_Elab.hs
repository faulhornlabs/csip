module M6_Elab
  ( check, inferTop
  ) where

import M1_Base
import M3_Parse
import M4_Eval
import M5_Unify

-------------

pattern CType, CPi, CHPi, CCode, CTy, CArr, CNat, CString, CApp, CLam, CAp, CBool :: Val
pattern CType   = "Type"
pattern CPi     = "Pi"
pattern CHPi    = "HPi"
pattern CCPi    = "CPi"   --   t => s
pattern CIPi    = "IPi"   --   t :-> s      -- injective function
pattern CCode   = "Code"
pattern CTy     = "Ty"
pattern CArr    = "Arr"
pattern CNat    = "Nat"
pattern CString = "String"
pattern CAp     = "Ap"
pattern CApp    = "App"
pattern CLam    = "Lam"
pattern CBool   = "Bool"

data Icit = Impl | ImplClass | Expl
  deriving Eq

matchCode :: Env -> Val -> RefM (Tm -> RefM Tm, Tm)
matchCode env v = spine v >>= \case
  (CCode, [a]) -> quoteTm' a <&> \a -> (pure, a)
  _ -> do
    (tm, m) <- freshMeta' env
    cm <- vApp CCode m
    f <- conv env v cm
    pure (f, tm)

matchArr :: Env -> Val -> RefM (Tm -> RefM Tm, Tm, Val, Tm, Val)
matchArr env v = spine v >>= \case
  (CArr, [a, b]) -> (,,,,) pure <$> quoteTm' a <*> pure a <*> quoteTm' b <*> pure b
  _ -> do
    (m1, m1')  <- freshMeta' env
    (m2, m2')  <- freshMeta' env
    ar <- vApp CCode =<< vApps CArr [m1', m2']
    f <- conv env ar v
    pure (f, m1, m1', m2, m2')

-- True:   x: t      f x: Pi
-- False:  x: Pi     f x: t
matchPi :: Bool -> Env -> Icit -> Val -> RefM (Tm -> RefM Tm, Icit, Val, Val)
matchPi cov env icit v = spine v >>= \case
  (CPi,  [pa, pb]) -> pure (pure, Expl,      pa, pb)
  (CHPi, [pa, pb]) -> pure (pure, Impl,      pa, pb)
  (CCPi, [pa, pb]) -> pure (pure, ImplClass, pa, pb)
  _ -> do
    (_, m1) <- freshMeta' env
    (_, m2) <- freshMeta' env
    let pi = case icit of Impl -> CHPi; Expl -> CPi; _ -> impossible
    v2 <- vApps pi [m1, m2]
    f <- if cov then conv env v v2 else conv env v2 v
    pure (f, icit, m1, m2)

matchHPi v = spine v <&> \case
  (CHPi, [pa, pb]) -> Just (Impl,      pa, pb)
  (CCPi, [pa, pb]) -> Just (ImplClass, pa, pb)
  _ -> Nothing

--------------------

data Env = MkEnv
  { boundVars   :: [Name]
  , localVals   :: IntMap Name Val
  , localTypes  :: IntMap Name Val
  , globals     :: IntMap Name (Val, Val)
  , classes     :: IntMap Name ClassData
  , nameMap     :: Map NameStr Name
  , isLHS       :: Bool    -- True if lhs is checked
  }

memptyEnv :: RefM Env
memptyEnv = foldM def (MkEnv mempty mempty mempty mempty mempty mempty False)
  [("Nat", CNat), ("String", CString), ("Type", CType)]
 where
  def env (n, v) = do
        (_, _, _, env) <- defineGlob n (\_ -> pure v) CType env
        pure env

onTop :: Env -> Bool
onTop = null . boundVars

data ClassData = MkClassData
  { _classVal     :: Val
  , _dictVal      :: Val
  , _superClasses :: [Val]
  , _methods      :: [(Name, Val)]    -- names and full (closed) types
  }

addClass :: Name -> ClassData -> Env -> RefM Env
addClass n d env = pure $ env { classes = insertIM n d $ classes env }

lookupClass :: Name -> Env -> Maybe ClassData
lookupClass n env = lookupIM n (classes env)

defineGlob_ :: NameStr -> (Name -> RefM Val) -> Val -> Env -> (Env -> RefM a) -> RefM (Name, Val, Val, Env, a)
defineGlob_ n_ fv t_ env elab = do
  (n, v_, env) <- addName' n_ fv env
  ct <- elab env { globals = insertIM n (v_, t_) $ globals env }
  v <- deepForce v_
  t <- deepForce t_
  env <- case () of
    _ | not (onTop env) -> pure $ addLocal False n v t env
      | not (rigid t)   -> print t >>= \s -> errorM $ "meta in global definition:\n" <> showName n <> " : " <> s
      | not (rigid v), n_ /= "lookupDict"   -> print v >>= \s -> errorM $ "meta in global definition:\n" <> showName n <> " = " <> s
      | otherwise       -> pure env { globals = insertIM n (v, t) $ globals env }
  pure (n, v, t, env, ct)

addName' n_ fv env = do
  n <- nameOf n_
  v <- fv n
  pure (n, v, env {nameMap = insert n_ n $ nameMap env})

addName_ n env = env {nameMap = insert (nameStr n) n $ nameMap env}

addLocal bound n v t env
  = env { localTypes = insertIM n t $ localTypes env
        , localVals = insertIM n v $ localVals env
        , boundVars = (if bound then (n:) else id) $ boundVars env
        }

defineBound :: NameStr -> Val -> Env -> RefM (Name, Env)
defineBound n_ t env = do
  (n, v, env) <- addName' n_ (\n -> pure $ vVar n) env
  env <- pure $ addLocal True n v t env
  pure (n, env)

defineGlob n v t e = defineGlob_ n v t e (\_ -> pure ()) <&> \(a, b, c, d, _) -> (a, b, c, d)

defineGlob' :: NameStr -> Val -> Val -> Env -> RefM (Name, Env)
defineGlob' n v t env = defineGlob n (\_ -> pure v) t env <&> \(n, _, _, env) -> (n, env)

lookupName n env = lookup n $ nameMap env

lookupLocal :: NameStr -> Env -> Maybe (Name, Val)
lookupLocal v env = lookupName v env >>= \v -> lookupIM v (localTypes env) <&> (,) v

lookupGlobal :: NameStr -> Env -> Maybe (Val, Val)
lookupGlobal v env = lookupName v env >>= \v -> lookupIM v (globals env)

evalEnv :: Env -> Tm -> RefM Val
evalEnv env = eval $ localVals env

evalEnv' env n t = evalEnv env t >>= \v -> if closed v then vTm n t v else pure v

freshMeta_ :: Env -> RefM Tm
freshMeta_ env = do
  m <- tMeta
  pure $ TApps m $ reverse $ TVar <$> boundVars env

freshMeta :: Env -> RefM Tm
freshMeta env = TGen <$> freshMeta_ env

instanceMeta :: Env -> RefM (Tm, Val)
instanceMeta env = do
  m <- freshMeta_ env
  m' <- evalEnv env m
  pure (TGen $ TApp (TVal lookupDictFun) m, m')

freshMeta' :: Env -> RefM (Tm, Val)
freshMeta' env = do
  m <- freshMeta env
  (,) m <$> evalEnv env m

typeName n = addSuffix n "_t"

---------

evalId :: Maybe (a -> RefM a) -> a -> RefM a
evalId = fromMaybe pure

conv
  :: Env
  -> Val                  -- actual type
  -> Val                  -- expected type
  -> RefM (Tm -> RefM Tm) -- transformation from actual to expected
conv env a b = evalId <$> conv_ env a b

conv_ :: Env
  -> Val
  -> Val
  -> RefM (Maybe (Tm -> RefM Tm))
conv_ env a b = do
  (ha, va) <- spine a
  (hb, vb) <- spine b
  case () of

    () | ha == CTy, hb == CType, [] <- va, [] <- vb -> do
      pure $ Just \t -> pure $ TVal CCode `TApp` t

    () | ha == CIPi, hb == CPi, [m1, m2] <- va, [m3, m4] <- vb -> do

      q <- conv_ env m3 m1

      v <- lamName "v" m4
      (v, env') <- defineBound v m3 env
      let vv = vVar v

      c2 <- vApp m4 vv
      h_v <- conv_ env' m2 c2{- m4 v -}

      m1' <- quoteTm' m1
      m2' <- quoteTm' m2

      pure $ case (h_v, q) of
        (Nothing, Nothing) -> Just \t -> pure $ TApps (TVal CAp) [m1', m2', t]
        _ -> Just \t -> tLam v =<< evalId h_v =<< TApp (TApps (TVal CAp) [m1', m2', t]) <$> evalId q (TVar v)

    () | ha == CPi, hb == CPi, [m1, m2] <- va, [m3, m4] <- vb -> do

      q <- conv_ env m3 m1

      v <- lamName "v" m2
      (v, env') <- defineBound v m3 env
      let vv = vVar v

      q_v <- evalEnv env' =<< evalId q (TVar v)
      c1 <- vApp m2 q_v
      c2 <- vApp m4 vv
      h_v <- conv_ env' c1{- m2 (q v) -} c2{- m4 v -}

      pure $ case (h_v, q) of
        (Nothing, Nothing) -> Nothing
        _ -> Just \t -> tLam v =<< evalId h_v =<< TApp t <$> evalId q (TVar v)

    () | ha == CCode, hb == CPi, [m3, m4] <- vb -> do

      (f, m1, m1', m2, m2') <- matchArr env a

      c1 <- vApp CCode m1'
      q <- conv_ env m3{- m3 -} c1{- Code m1 -}

      v <- lamName "v" m4
      (v, env') <- defineBound v c1 env
      let vv = vVar v

      c2 <- vApp CCode m2'
      m4_v <- vApp m4 vv
      h_v <- conv_ env' c2{- Code m2 -} m4_v  --  (Code m1 -> Code m2)  ==>  (Code m1 -> m4)

      let lam t = case (h_v, q) of
            (Nothing, Nothing) -> pure t
            _ -> tLam v =<< evalId h_v =<< TApp t <$> evalId q (TVar v)

      pure $ Just \t -> f t >>= \t -> lam $ TApps (TVal CApp) [m1, m2, t]

    () | ha == CPi, hb == CCode, [m3, m4] <- va -> do

      (f, m1, m1', m2, m2') <- matchArr env b

      c1 <- vApp CCode m1'
      q <- conv_ env c1{- Code m1 -} m3

      v <- lamName "v" m4
      (v, env') <- defineBound v c1 env
      let vv = vVar v

      c2 <- vApp CCode m2'
      m4_v <- vApp m4 vv
      h_v <- conv_ env' m4_v{- m4 v -} c2{- Code m2 -}  --  (Code m1 -> m4 v)  ==>  (Code m1 -> Code m2)

      let lam t = case (h_v, q) of
            (Nothing, Nothing) -> pure t
            _ -> tLam v =<< evalId h_v =<< TApp t <$> evalId q (TVar v)

      pure $ Just \t -> lam t >>= \t -> f $ TApps (TVal CLam) [m1, m2, t]

    _ -> do
      () <- unify a b
      pure Nothing


---------

insertH :: Env -> RefM (Tm, Val) -> RefM (Tm, Val)
insertH env et = et >>= \(e, t) -> matchHPi t >>= \case
  Nothing -> pure (e, t)
  Just (ImplClass, a, b) -> do
    a' <- quoteTm' a
    let m = TGen $ TApp (TVal lookupDictFun) a'
    insertH env $ pure (TApp e m, b)
  Just (Impl, _, b) -> do
    (m, vm) <- freshMeta' env
    t' <- vApp b vm
    insertH env $ pure (TApp e m, t')
  _ -> undefined

unlam :: Name -> Val -> RefM (Val, Val)
unlam n' f = do
  let v = vVar n'
  t <- vApp f v
  pure (v, t)

getPi (RPi  n a b) = Just (TVal  CPi, n, a, b)
getPi (RHPi n a b) = Just (TVal CHPi, n, a, b)
getPi _ = Nothing

--------------------

check :: Env ->  Raw -> Val -> RefM Tm
check env r ty = do
  traceShow "4" $ "check " <<>> showM r <<>> "\n :? " <<>> showM ty
  tag r $ do
    t <- check_ env r ty
    traceShow "5" $ "check end " <<>> showM r <<>> "\n ==> " <> showM t
    pure t

check_ :: Env -> Raw -> Val -> RefM Tm
check_ env r ty = case r of
  Hole -> freshMeta env
  RPi "_" a b | ty == CTy -> do
    ta <- check env a CTy
    tb <- check env b CTy
    pure $ TVal CArr `TApp` ta `TApp` tb
  RHLam n Hole a -> do
    (f, icit, pa, pb) <- matchPi True env Impl ty
    case icit of
      Impl -> do
        (n, env') <- defineBound n pa env
        (_, t) <- unlam n pb
        ta <- check env' a t
        f =<< tLam n ta
      ImplClass -> do
        (n, env') <- defineBound n pa env   -- TODO: add superclasses to the env
        ta <- check env' a pb
        f =<< tLam n ta
      _ -> undefined
  RLam n Hole a -> do
    (f, icit, pa, pb) <- matchPi True env Expl ty
    case icit of
      Expl -> do
        (n, env') <- defineBound n pa env
        (_, t) <- unlam n pb
        ta <- check env' a t
        f =<< tLam n ta
      Impl -> do
        n' <- lamName "z" pb
        f =<< check env (RHLam n' Hole r) ty
      _ -> undefined
  _ -> matchHPi ty >>= \case
    Just (Impl, _, pb) | not (isLHS env) -> do
      n' <- lamName "z" pb
      check env (RHLam n' Hole r) ty
    Just (ImplClass, _, _) | not (isLHS env) -> do
      check env (RHLam "c" Hole r) ty
    _ -> case r of
      RLet n t a b -> do
        (ta, vta) <- case t of
          Hole -> infer env a
          t -> do
            vta <- check env (addForalls env t) CType >>= evalEnv' env (typeName n)
            ta <- check env a vta
            pure (ta, vta)
        va <- evalEnv' env n ta
        (n, env') <- defineGlob' n va vta env
        tb <- check env' b ty
        pure $ if onTop env then tb else TLet n ta tb
      ROLet n t a b | onTop env -> do
        vta <- check env (addForalls env t) CType >>= evalEnv' env (typeName n)
        ta <- check env a vta
        (_n, c, vta, env) <- defineGlob n (\n -> pure $ vCon n Nothing) vta env
        tb <- check env b ty
        (fa, pa) <- matchCode env vta
        (fb, pb) <- matchCode env ty
        fta <- fa ta
        ftb <- fb tb
        pure $ TApps "TopLet" [pa, pb, TVal c, fta, ftb]
      ROLet n t a b -> do
        vta <- check env (addForalls env t) CType >>= evalEnv' env (typeName n)
        ta <- check env a vta
        (n, env') <- defineBound n vta env
        tb <- check env' b ty
        (fa, pa) <- matchCode env vta
        (fb, pb) <- matchCode env ty
        fta <- fa ta
        l <- tLam n =<< fb tb
        pure $ TApps "Let" [pa, pb, fta, l]
      r -> do
        (a, t) <- insertH env $ infer env r
        f <- conv env t ty
        f a

infer :: Env -> Raw -> RefM (Tm, Val)
infer env r = do
  traceShow "6" $ "infer " <<>> showM r
  tag r $ do
    (t, v) <- infer_ env r
    traceShow "7" $ "infer end " <<>> showM r <<>> "\n ==> " <<>> showM t <<>> "\n :: " <<>> showM v 
    pure (t, v)

codomain = \case
  RPi _ _ e -> codomain e
  RHPi _ _ e -> codomain e
  RCPi _ e -> codomain e
  RIPi _ e -> codomain e
  t -> t

appHead = \case
  RApp a _ -> appHead a
  RHApp a _ -> appHead a
  a -> a

getVarName = \case
  RVar n -> n
  _t -> undefined --error' $ print t

getHPi__ v = spine v <&> \case
    (CHPi, [a, b]) -> Just (a, b)
    _ -> Nothing

getHPi_ :: Name -> Val -> RefM (Val, Val)
getHPi_ n v = getHPi__ v <&> fromJust >>= \(a, b) -> vApp b (vVar n) <&> \b -> (a, b)

getHPi :: Val -> RefM (Maybe ((Name, Val), Val))
getHPi v = getHPi__ v >>= \case
  Nothing -> pure Nothing
  Just (a, b) -> do
    n <- lamName "m" b >>= mkName
    b <- vApp b $ vVar n
    pure $ Just ((n, a), b)

getApp :: Val -> RefM (Maybe (Val, Val))
getApp v = force v <&> \case
  WApp a b -> Just (a, b)
  _ -> Nothing

getConName :: Val -> RefM (Maybe Name)
getConName v = force v <&> \case
  WCon n -> Just n
  _ -> Nothing

getMult f v = f v >>= \case
    Just (c, v) -> getMult f v <&> first (c:)
    Nothing -> pure ([], v)

getSuper :: Val -> RefM (Maybe (Val, Val))
getSuper v = spine v <&> \case
    (CCPi, [a, b]) -> Just (a, b)
    _ -> Nothing

mkHPi :: (Name, Val) -> RefM Val -> RefM Val
mkHPi (n, a) b = b >>= \b -> vLam n b >>= \b -> vApps CHPi [a, b]

mkCPi a b = b >>= \b -> vApps CCPi [a, b]

mkPi a b = b >>= \b -> vConst b >>= \b -> vApps CPi [a, b]

mkMult :: (a -> RefM b -> RefM b) -> [a] -> RefM b -> RefM b
mkMult f as m = foldr f m as

dictName :: NameStr -> NameStr
dictName n = addSuffix n "Dict"

dictType :: Val -> [Val] -> RefM ([Val], Val)
dictType classTy methodTys = do
  ((n, parTy), classTy') <- getHPi classTy <&> fromJust
  (supers, classTy'') <- getMult getSuper classTy'
  methodTys' <- forM methodTys \methodTy -> do
    (_, methodTy') <- getHPi_ n methodTy
    (_, methodTy'') <- getSuper methodTy' <&> fromJust
    pure methodTy''
  t <- mkHPi (n, parTy) $ mkMult mkPi supers $ mkMult mkPi methodTys' $ pure classTy''
  supers' <- forM supers \s -> vLam n s
  pure (supers', t)

addMethodType :: [(Name, Val)] -> [Val] -> Val -> Env -> (Name, Val) -> RefM (Env, Val)
addMethodType ns is arg env (n_, t) = do
  let n = addSuffix (nameStr n_) "'"
  ((vn, _), t) <- getHPi t <&> fromJust
  (_, t) <- getSuper t <&> fromJust
  f <- vLam vn t
  t <- mkMult mkHPi ns $ mkMult mkCPi is $ vApp f arg
  (_, mn, _, env) <- defineGlob n mkFun t env
  pure (env, mn)

decomposeHead :: Val -> RefM ([(Name, Val)], [Val], Val)
decomposeHead t = do
  (ns, t) <- getMult getHPi t
  (is, t) <- getMult getSuper t
  pure (ns, is, t)

-- variables, instances, class name, arg type
analyzeInstanceHead :: Val -> RefM ([(Name, Val)], [Val], Name, Val)
analyzeInstanceHead t = do
  (ns, t) <- getMult getHPi t
  (is, t) <- getMult getSuper t
  (cn, t) <- getApp t <&> fromJust
  cn <- getConName cn <&> fromJust
  pure (ns, is, cn, t)

defineSuperclasses :: NameStr -> Val -> Name -> Int -> [Val] -> RefM ()
defineSuperclasses nclass vclass dict num supers = do
  m <- mkName "m"
  let c = TVal vclass `TApp` TVar m
  ss <- forM (zip [0..] supers) \(i, s) -> do
    sn <- mkName $ addSuffix (addPrefix "sel" nclass) (show i)
    sf <- mkFun sn
    addDictSelector sf dict num $ i + 1
    pure (TVal s `TApp` TVar m, TVal sf `TApp` TVar m)
  let rhs = foldr (\(a, b) t -> TApps (TVal "SuperClassCons") [c, a, b, t]) (TVal "SuperClassNil" `TApp` c) ss
  f <- mkFun "superClasses"
  addRule "superClasses" [m] (TVal f `TApp` c) rhs

inferMethods :: ((Env -> RefM Val) -> Env -> RefM Val) -> Env -> Raw -> RefM ([(Name, Val)], Env)
inferMethods under env r = case r of
  RLetTy n t b -> do
    vta <- under (\env -> check env (addForalls env t) CType >>= evalEnv' env (typeName n)) env
    let ff n = if isConName n then undefined else mkFun n
    (n, _, _, env) <- defineGlob n ff vta env
    inferMethods under env b <&> first ((n, vta):)
  REnd -> pure ([], env)
  _ -> errorM "can't infer method"

inferMethodBodies :: Env -> Raw -> RefM ()
inferMethodBodies env r = case r of
  RRule a b c -> addRule' env a b >> inferMethodBodies env c
  RLet a Hole b c -> addRule' env (RVar a) b >> inferMethodBodies env c
  REnd -> pure ()
  r -> error' $ ("can't infer method body :\n" <>) <$> print r

addRule' env a b = do
  let ns = [n | n <- fvs a, Nothing <- [lookupName n env]]
  env' <- foldM addName env ns
  (ta, vta) <- insertH env $ infer (env' {isLHS = True}) a
  tb <- check env' b vta
  addRule (ruleHead a) (boundVars env') ta tb

addLookupDictRule :: ClassData -> [(Name, Val)] -> [Val] -> Val -> [Val] -> RefM ()
addLookupDictRule (MkClassData classVal dictVal supers _) (map fst -> ns) is_ arg_ mns = do
  lookup <- TApp . TVal <$> mkFun "lookupDict"
  arg <- quoteTm' arg_
  arg' <- quoteTm_ False False False arg_
  is <- mapM quoteTm' is_
  ds <- forM is \_ -> mkName "d"
  let rhs
        = tLets (zip ds $ map lookup is)
        $ TApps (TVal dictVal)
        ( arg
        :  [lookup (TVal c `TApp` arg) | c <- supers]
        ++ [ TApps (TVal mn) $ map TVar $ ns ++ ds
           | mn <- mns]
        )
  addRule "lookupDict" ns (lookup (TVal classVal `TApp` arg')) rhs
  pure ()

introClass :: Val -> (Env -> RefM Val) -> Env -> RefM Val
introClass c f env = do
  v <- f env
  vApps CCPi [c, v]

introType :: (Name, Val) -> (Env -> RefM Val) -> Env -> RefM Val
introType (n, t) f env = do
  v <- f $ addLocal True n (vVar n) t $ addName_ n env
  f <- vLam n v
  vApps CHPi [t, f]

multIntro :: (a -> (Env -> RefM Val) -> Env -> RefM Val) -> [a] -> (Env -> RefM Val) -> Env -> RefM Val
multIntro _ [] g = g
multIntro f (a: as) g = f a $ multIntro f as g

infer_ :: Env -> Raw -> RefM (Tm, Val)
infer_ env r = case r of
  RClass a b e | onTop env -> do
    let n_ = getVarName $ appHead $ codomain a
    vta <- check env Hole CType >>= evalEnv' env (typeName n_)
    (n, tc, _, env, ct) <- defineGlob_ n_ (\n -> pure $ mkCon n $ Just vta) vta env
       \env -> check env (addForalls env a) CType >>= evalEnv env
    (is, _ss, cc) <- decomposeHead ct
    let under m = multIntro introType is $ introClass cc m
    (mts, env) <- inferMethods under env b
    (supers, dt) <- dictType ct $ map snd mts
    (dn, dv, _dt, env) <- defineGlob (dictName n_) (\n -> pure $ mkCon n $ Just dt) dt env
    env <- addClass n (MkClassData tc dv supers mts) env
    forM_ (zip [0..] mts) \(i, (mname, _)) -> case lookupIM mname (globals env) of
      Just (vf, _) -> addDictSelector vf dn (1 + length supers + length mts) (1 + length supers + i)
      _ -> impossible
    () <- defineSuperclasses n_ tc dn (1 + length supers + length mts) supers
    infer env e
  RInstance a b c | onTop env -> do
    ct <- check env (addForalls env a) CType >>= evalEnv env
    (ns, is, n, arg) <- analyzeInstanceHead ct
    case lookupClass n env of
      Nothing -> undefined
      Just cd@(MkClassData _ _ _ mts) -> do
        (env, mns) <- mapAccumM (addMethodType ns is arg) env mts
        () <- addLookupDictRule cd ns is arg mns
        () <- inferMethodBodies env b
        infer env c
--  RData     _a _b c | onTop env -> infer env c
  REnd -> pure (TVal CType, CType)
  RLam n t a -> do
    vt <- check env t CType >>= evalEnv' env (typeName n)
    (n, env') <- defineBound n vt env
    (ta, va) <- insertH env $ infer env' a
    f <- vLam n va
    (,) <$> tLam n ta <*> vApps CPi [vt, f]
  RHLam n t a -> do
    vt <- check env t CType >>= evalEnv' env (typeName n)
    (n, env') <- defineBound n vt env
    (ta, va) <- infer env' a
    f <- vLam n va
    (,) <$> tLam n ta <*> vApps CHPi [vt, f]
  Hole -> do
    t <- freshMeta env
    (_, m) <- freshMeta' env
    pure (t, m)
  RNat n    -> vNat n    <&> \v -> (TVal v, CNat)
  RString n -> vString n <&> \v -> (TVal v, CString)
  RVar n | Just (v, ty) <- lookupGlobal n env -> pure (TVal v, ty)
  RVar n | Just (n, ty) <- lookupLocal  n env -> pure (TVar n, ty)
  RVar{} -> errorM "Not in scope"
  RLetTy n t b | onTop env -> do
    vta <- check env (addForalls env t) CType >>= evalEnv' env (typeName n)
    let ff n = if isConName n then pure $ mkCon n $ Just vta else mkFun n
    (_n, _, _, env) <- defineGlob n ff vta env
    infer env b
  ROLet{} -> do
    (_, m) <- freshMeta' env
    ty <- vApp CCode m
    t <- check env r ty
    pure (t, ty)
  RRule a b c | onTop env -> do
    addRule' env a b
    infer env c
  RLet n t a b | isRuleTy t -> do
    vta <- check env (addForalls env t) CType >>= evalEnv' env (typeName n)
    let ff n = if isConName n then undefined else mkFun n
    (_n, _, _, env) <- defineGlob n ff vta env
    addRule' env (RVar n) a
    infer env b
  RLet n t a b -> do
    (ta, vta) <- case t of
      Hole -> infer env a
      t -> do
        vta <- check env (addForalls env t) CType >>= evalEnv' env (typeName n)
        ta <- check env a vta
        pure (ta, vta)
    va <- evalEnv' env n ta
    (n, env') <- defineGlob' n va vta env
    (tb, vtb) <- infer env' b
    pure (if onTop env then tb else TLet n ta tb, vtb)
  (getPi -> Just (pi, n, a, b)) -> do
    ta <- check env a CType
    va <- evalEnv' env (typeName n) ta
    (n, env) <- defineBound n va env
    tb <- check env b CType
    l <- tLam n tb
    pure (pi `TApp` ta `TApp` l, CType)
  RCPi a b -> do
    ta <- check env a CType
    tb <- check env b CType
    pure (TVal CCPi `TApp` ta `TApp` tb, CType)
  RIPi a b -> do
    ta <- check env a CType
    tb <- check env b CType
    pure (TVal CIPi `TApp` ta `TApp` tb, CType)
  RGuard a b -> do
    tb <- check env b CBool
    (ta, ty) <- infer env a
    pure (TGuard ta tb, ty)
  RView a b -> do
    (ta, ty) <- infer env a
    (f, Expl, pa, pb) <- matchPi True env Expl ty
    n <- lamName "t" pb
    (n, env') <- defineBound n pa env
    (_, vb) <- unlam n pb
    tb <- check env' b vb
    fta <- f ta
    pure (TView fta tb, pa)
  RHApp a b -> do
    inferApp Impl env a b
  RApp a b -> do
    inferApp Expl env a b
  REmbed (MkEmbedded t v) -> pure (t, v)
  _ -> errorM "can't infer"
 where
  inferApp i env a b = infer env a >>= \(av, ty) -> do
    (f, icit, pa, pb) <- matchPi True env i ty
    fav <- f av
    case () of
     _ | icit == ImplClass, i == Impl -> do
        tb <- check env b pa
        pure (TApp fav tb, pb)
       | icit == i -> do
        tb <- check env b pa
        n <- lamName "t" pb
        v <- evalEnv' env n tb
        b <- vApp pb v
        pure (TApp fav tb, b)
       | icit == Impl -> do
        infer env $ RApp (RHApp (REmbed $ MkEmbedded av ty) Hole) b
       | icit == ImplClass -> do
        (m, m') <- instanceMeta env
        infer env $ RApp (RHApp (REmbed $ MkEmbedded av ty) $ REmbed $ MkEmbedded m m') b
       | otherwise -> error "baj"

addName :: Env -> NameStr -> RefM Env
addName env n = do
  (_, m) <- freshMeta' env
  defineBound n m env <&> snd

--------------------

isRuleTy :: Raw -> Bool
isRuleTy = \case
  RHPi _ _ t -> isRuleTy t
  RCPi{} -> True
  _ -> False

ruleHead :: Raw -> NameStr
ruleHead = f where
  f = \case
    RGuard a _ -> f a
    RApp a _ -> f a
    RVar n -> n
    _ -> undefined

reverseRules :: Raw -> Raw
reverseRules = g where
  g = \case
    RRule a c b   -> f (ruleHead a) [(a, c)] b
    RLet  n t a b -> RLet  n t a (g b)
    ROLet n t a b -> ROLet n t a (g b)
    RLetTy  n t b -> RLetTy  n t (g b)
    RClass    a b c -> RClass    a b $ g c
    RInstance a b c -> RInstance a (g b) $ g c
    RData     a b c -> RData     a b $ g c
    REnd -> REnd
    r -> r

  f h acc = \case
    RRule a c b | ruleHead a == h -> f h ((a, c): acc) b
    r -> foldr (\(a, c) b -> RRule a c b) (g r) acc

inferTop :: Raw -> RefM (Tm, Val)
inferTop r = do
  env <- memptyEnv
  infer env $ reverseRules r

instance Parse (Tm, Val) where
  parse = parse >=> inferTop

instance Parse Tm where
  parse s = parse s <&> (fst :: (Tm, Val) -> Tm)


fvs :: Raw -> [NameStr]
fvs = nub . go where
  go = \case
    Hole -> []
    RDot{} -> []
    RView _ b -> go b
    RGuard a _ -> go a
    RHApp a b -> go a <> go b
    RApp a b -> go a <> go b
    RVar a -> [a]
    RNat{} -> []
    RString{} -> []
    x -> error' $ ("fvs: " <>) <$> print x

addForalls :: Env -> Raw -> Raw
addForalls env r = foldr (\n r -> RHPi n Hole r) r [n | n <- fvs' r, Nothing <- [lookupName n env]]

fvs' :: Raw -> [NameStr]
fvs' = nub . go where
  go = \case
    Hole -> []
    RDot{} -> undefined
    RView{} -> undefined
    RGuard{} -> undefined
    RRule{} -> undefined
    RHPi n a b -> go a <> del n (go b)
    RPi n a b -> go a <> del n (go b)
    RLet n t a b -> go t <> go a <> del n (go b)
    RCPi a b -> go a <> go b
    RIPi a b -> go a <> go b
    RHApp a b -> go a <> go b
    RApp a b -> go a <> go b
    RVar a -> [a]
    RNat{} -> []
    RString{} -> []
    x -> error' $ ("fvs': " <>) <$> print x

  del n = filter (/= n)
