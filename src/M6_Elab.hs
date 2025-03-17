module M6_Elab
  ( check, inferTop
  ) where

import M1_Base
import M3_Parse
import M4_Eval
import M5_Unify

-------------

pattern CType   = WCon 0 "Type"
pattern CPi     = WCon 2 "Pi"
pattern CHPi    = WCon 2 "HPi"
pattern CCPi    = WCon 2 "CPi"   --   t => s
pattern CIPi    = WCon 2 "IPi"   --   t :-> s      -- injective function
pattern CCode   = WCon 1 "Code"
pattern CTy     = WCon 0 "Ty"
pattern CArr    = WCon 2 "Arr"
pattern CNat    = WCon 0 "Nat"
pattern CString = WCon 0 "String"
pattern CAp     = WCon 2 "Ap"
pattern CApp    = WCon 2 "App"
pattern CLam    = WCon 2 "Lam"
pattern CBool   = WCon 0 "Bool"
pattern CTopLet = WCon 5 "TopLet"
pattern CLet    = WCon 4 "Let"

data Icit = Impl | ImplClass | Expl
  deriving Eq

matchCode :: Val -> RefM (Tm -> RefM Tm, Tm)
matchCode v = matchCon' "Code" v >>= \case
  Just [a] -> quoteTm' a <&> \a -> (pure, a)
  _ -> do
    (tm, m) <- freshMeta'
    cm <- vApp CCode m
    f <- conv v cm
    pure (f, tm)

matchArr :: Val -> RefM (Tm -> RefM Tm, Tm, Val, Tm, Val)
matchArr v = matchCon' "Arr" v >>= \case
  Just [a, b] -> (,,,,) pure <$> quoteTm' a <*> pure a <*> quoteTm' b <*> pure b
  _ -> do
    (m1, m1') <- freshMeta'
    (m2, m2') <- freshMeta'
    ar <- vApp CCode =<< vApps CArr [m1', m2']
    f <- conv ar v
    pure (f, m1, m1', m2, m2')

-- True:   x: t      f x: Pi
-- False:  x: Pi     f x: t
matchPi :: Bool -> Icit -> Val -> RefM (Tm -> RefM Tm, Icit, Val, Val)
matchPi cov icit v = spine' v >>= \case
  Just ("Pi",  [pa, pb]) -> pure (pure, Expl,      pa, pb)
  Just ("HPi", [pa, pb]) -> pure (pure, Impl,      pa, pb)
  Just ("CPi", [pa, pb]) -> pure (pure, ImplClass, pa, pb)
  _ -> do
    (_, m1) <- freshMeta'
    (_, m2) <- freshMeta'
    let pi = case icit of Impl -> CHPi; Expl -> CPi; _ -> impossible
    v2 <- vApps pi [m1, m2]
    f <- if cov then conv v v2 else conv v2 v
    pure (f, icit, m1, m2)

conArity :: Val -> RefM Int
conArity v = spine' v >>= \case
  Just ("Pi",  [_, pb]) -> (+1) <$> f pb
  Just ("HPi", [_, pb]) -> (+1) <$> f pb
  Just ("CPi", [_, pb]) -> (+1) <$> conArity pb
  Just ("IPi", [_, pb]) -> (+1) <$> conArity pb
  _ -> pure 0
 where
  f g = do
    n <- mkName "r"
    conArity =<< vApp g (vVar n)

matchHPi v = spine' v <&> \case
  Just ("HPi", [pa, pb]) -> Just (Impl,      pa, pb)
  Just ("CPi", [pa, pb]) -> Just (ImplClass, pa, pb)
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

{-# noinline envR #-}
envR :: Reader Env
envR = topReader memptyEnv

localEnv = local envR
asksEnv = asks envR

memptyEnv :: RefM Env
memptyEnv = foldM def (MkEnv mempty mempty mempty mempty mempty mempty False)
  [("Nat", CNat), ("String", CString), ("Type", CType)]
 where
  def env (n_, v) = do
        n <- nameOf n_
        pure $ env { globals = insertIM n (v, CType) $ globals env, nameMap = insert n_ n $ nameMap env }

onTop :: Env -> Bool
onTop = null . boundVars

data ClassData = MkClassData
  { _classVal     :: Val
  , _dictVal      :: Val
  , _superClasses :: [Val]
  , _methods      :: [(Name, Val)]    -- names and full (closed) types
  }

addClass :: Name -> ClassData -> RefM a -> RefM a
addClass n d = localEnv \env -> env { classes = insertIM n d $ classes env }

lookupClass :: Name -> Env -> Maybe ClassData
lookupClass n env = lookupIM n (classes env)

addName_ s n = localEnv \env -> env {nameMap = insert s n $ nameMap env}

addGlobal n v t = localEnv \env -> env { globals = insertIM n (v, t) $ globals env }

addLocal bound n v t = localEnv \env ->
    env { localTypes = insertIM n t $ localTypes env
        , localVals  = insertIM n v $ localVals env
        , boundVars  = (if bound then (n:) else id) $ boundVars env
        }

defineGlob_ :: NameStr -> (Name -> RefM Val) -> Val -> RefM a -> (Name -> Val -> Val -> a -> RefM b) -> RefM b
defineGlob_ n_ fv t_ elab cont = nameOf n_ >>= \n -> addName_ n_ n do
  v_ <- fv n
  ct <- addGlobal n v_ t_ elab
  v <- deepForce v_
  t <- deepForce t_
  let co = cont n v t ct
  top <- asksEnv onTop
  case () of
    _ | not top -> addLocal False n v t co
      | not (rigid t)   -> print t >>= \s -> errorM $ "meta in global definition:\n" <> showName n <> " : " <> s
      | not (rigid v), n_ /= "lookupDict"   -> print v >>= \s -> errorM $ "meta in global definition:\n" <> showName n <> " = " <> s
      | otherwise       -> addGlobal n v t co

defineBound'_ :: NameStr -> Name -> Val -> RefM a -> RefM a
defineBound'_ n_ n t cont = addName_ n_ n $ addLocal True n (vVar n) t cont

defineBound' :: NameStr -> Val -> (Name -> RefM a) -> RefM a
defineBound' n_ t cont = nameOf n_ >>= \n -> defineBound'_ n_ n t $ cont n

defineGlob n v t cont = do
  defineGlob_ n v t (pure ()) \a b c _ -> cont a b c

defineGlob' :: NameStr -> Val -> Val -> (Name -> RefM a) -> RefM a
defineGlob' n v t cont = do
  defineGlob n (\_ -> pure v) t \n _ _ -> cont n

lookupName env = \n -> lookup n $ nameMap env

lookupLocal :: NameStr -> Env -> Maybe (Name, Val)
lookupLocal v env = lookupName env v >>= \v -> lookupIM v (localTypes env) <&> (,) v

lookupGlobal :: NameStr -> Env -> Maybe (Val, Val)
lookupGlobal v env = lookupName env v >>= \v -> lookupIM v (globals env)

evalEnv :: Tm -> RefM Val
evalEnv t = asksEnv localVals >>= \ls -> eval ls t

evalEnv' n t = evalEnv t >>= \v -> if closed v then vTm n t v else pure v

freshMeta_ :: RefM Tm
freshMeta_ = do
  m <- tMeta
  bv <- asksEnv boundVars
  pure $ TApps m $ reverse $ TVar <$> bv

freshMeta :: RefM Tm
freshMeta = TGen <$> freshMeta_

instanceMeta :: RefM (Tm, Val)
instanceMeta = do
  m <- freshMeta_
  m' <- evalEnv m
  pure (TGen $ TApp (TVal lookupDictFun) m, m')

freshMeta' :: RefM (Tm, Val)
freshMeta' = do
  m <- freshMeta
  (,) m <$> evalEnv m

typeName n = addSuffix n "_t"

---------

evalId :: Maybe (a -> RefM a) -> a -> RefM a
evalId = fromMaybe pure

conv
  :: Val                  -- actual type
  -> Val                  -- expected type
  -> RefM (Tm -> RefM Tm) -- transformation from actual to expected
conv a b = evalId <$> conv_ a b

conv_
  :: Val
  -> Val
  -> RefM (Maybe (Tm -> RefM Tm))
conv_ a b = do
  sa <- spine' a
  sb <- spine' b
  case (sa, sb) of

    (Just ("Ty", []), Just ("Type", [])) -> do
      pure $ Just \t -> pure $ TVal CCode `TApp` t

    (Just ("IPi", [m1, m2]), Just ("Pi", [m3, m4])) -> do

      q <- conv_ m3 m1

      v <- lamName "v" m4
      defineBound' v m3 \v -> do
        let vv = vVar v

        c2 <- vApp m4 vv
        h_v <- conv_ m2 c2{- m4 v -}

        m1' <- quoteTm' m1
        m2' <- quoteTm' m2

        pure $ case (h_v, q) of
          (Nothing, Nothing) -> Just \t -> pure $ TApps (TVal CAp) [m1', m2', t]
          _ -> Just \t -> tLam v =<< evalId h_v =<< TApp (TApps (TVal CAp) [m1', m2', t]) <$> evalId q (TVar v)

    (Just ("Pi", [m1, m2]), Just ("Pi", [m3, m4])) -> do

      q <- conv_ m3 m1

      v <- lamName "v" m2
      defineBound' v m3 \v -> do
        let vv = vVar v

        q_v <- evalEnv =<< evalId q (TVar v)
        c1 <- vApp m2 q_v
        c2 <- vApp m4 vv
        h_v <- conv_ c1{- m2 (q v) -} c2{- m4 v -}

        pure $ case (h_v, q) of
          (Nothing, Nothing) -> Nothing
          _ -> Just \t -> tLam v =<< evalId h_v =<< TApp t <$> evalId q (TVar v)

    (Just ("Code", _), Just ("Pi", [m3, m4])) -> do

      (f, m1, m1', m2, m2') <- matchArr a

      c1 <- vApp CCode m1'
      q <- conv_ m3{- m3 -} c1{- Code m1 -}

      v <- lamName "v" m4
      defineBound' v c1 \v -> do
        let vv = vVar v

        c2 <- vApp CCode m2'
        m4_v <- vApp m4 vv
        h_v <- conv_ c2{- Code m2 -} m4_v  --  (Code m1 -> Code m2)  ==>  (Code m1 -> m4)

        let lam t = case (h_v, q) of
              (Nothing, Nothing) -> pure t
              _ -> tLam v =<< evalId h_v =<< TApp t <$> evalId q (TVar v)

        pure $ Just \t -> f t >>= \t -> lam $ TApps (TVal CApp) [m1, m2, t]

    (Just ("Pi", [m3, m4]), Just ("Code", _)) -> do

      (f, m1, m1', m2, m2') <- matchArr b

      c1 <- vApp CCode m1'
      q <- conv_ c1{- Code m1 -} m3

      v <- lamName "v" m4
      defineBound' v c1 \v -> do
        let vv = vVar v

        c2 <- vApp CCode m2'
        m4_v <- vApp m4 vv
        h_v <- conv_ m4_v{- m4 v -} c2{- Code m2 -}  --  (Code m1 -> m4 v)  ==>  (Code m1 -> Code m2)

        let lam t = case (h_v, q) of
              (Nothing, Nothing) -> pure t
              _ -> tLam v =<< evalId h_v =<< TApp t <$> evalId q (TVar v)

        pure $ Just \t -> lam t >>= \t -> f $ TApps (TVal CLam) [m1, m2, t]

    _ -> do
      () <- unify a b
      pure Nothing


---------

insertH :: RefM (Tm, Val) -> RefM (Tm, Val)
insertH et = et >>= \(e, t) -> matchHPi t >>= \case
  Nothing -> pure (e, t)
  Just (ImplClass, a, b) -> do
    a' <- quoteTm' a
    let m = TGen $ TApp (TVal lookupDictFun) a'
    insertH $ pure (TApp e m, b)
  Just (Impl, _, b) -> do
    (m, vm) <- freshMeta'
    t' <- vApp b vm
    insertH $ pure (TApp e m, t')
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

check :: Raw -> Val -> RefM Tm
check r ty = do
  traceShow "4" $ "check " <<>> showM r <<>> "\n :? " <<>> showM ty
  tag r $ do
    (top, lhs) <- asksEnv \env -> (onTop env, isLHS env)
    t <- check_ top lhs r ty
    traceShow "5" $ "check end " <<>> showM r <<>> "\n ==> " <> showM t
    pure t

check_ :: Bool -> Bool -> Raw -> Val -> RefM Tm
check_ top lhs r ty = case r of
  Hole -> freshMeta
  RDot t | lhs -> do
    t' <- check t ty  -- TODO: use t'
    m <- freshMeta
    pure $ TDot m
  RDot{} -> undefined
  RPi "_" a b | ty == CTy -> do
    ta <- check a CTy
    tb <- check b CTy
    pure $ TVal CArr `TApp` ta `TApp` tb
  RHLam n Hole a -> do
    (f, icit, pa, pb) <- matchPi True Impl ty
    case icit of
      Impl -> do
        defineBound' n pa \n -> do
          (_, t) <- unlam n pb
          ta <- check a t
          f =<< tLam n ta
      ImplClass -> do
        defineBound' n pa \n -> do   -- TODO: add superclasses to the env
          ta <- check a pb
          f =<< tLam n ta
      _ -> undefined
  RLam n Hole a -> do
    (f, icit, pa, pb) <- matchPi True Expl ty
    case icit of
      Expl -> do
        defineBound' n pa \n -> do
          (_, t) <- unlam n pb
          ta <- check a t
          f =<< tLam n ta
      Impl -> do
        n' <- lamName "z" pb
        f =<< check (RHLam n' Hole r) ty
      _ -> undefined
  _ -> matchHPi ty >>= \case
    Just (Impl, _, pb) | not lhs -> do
      n' <- lamName "z" pb
      check (RHLam n' Hole r) ty
    Just (ImplClass, _, _) | not lhs -> do
      check (RHLam "c" Hole r) ty
    _ -> case r of
      RLet n t a b -> do
        (ta, vta) <- case t of
          Hole -> infer a
          t -> do
            vta <- addForalls t >>= \t -> check t CType >>= evalEnv' (typeName n)
            ta <- check a vta
            pure (ta, vta)
        va <- evalEnv' n ta
        (n, tb) <- defineGlob' n va vta \n -> (,) n <$> check b ty
        pure $ if top then tb else TLet n ta tb
      ROLet n t a b | top -> do
        vta <- addForalls t >>= \t -> check t CType >>= evalEnv' (typeName n)
        ta <- check a vta
        ar <- conArity vta
        defineGlob n (\n -> pure $ vCon ar n Nothing) vta \_n c vta -> do
          tb <- check b ty
          (fa, pa) <- matchCode vta
          (fb, pb) <- matchCode ty
          fta <- fa ta
          ftb <- fb tb
          pure $ TApps (TVal CTopLet) [pa, pb, TVal c, fta, ftb]
      ROLet n t a b -> do
        vta <- addForalls t >>= \t -> check t CType >>= evalEnv' (typeName n)
        ta <- check a vta
        (n, tb) <- defineBound' n vta \n -> do
          (,) n <$> check b ty
        (fa, pa) <- matchCode vta
        (fb, pb) <- matchCode ty
        fta <- fa ta
        l <- tLam n =<< fb tb
        pure $ TApps (TVal CLet) [pa, pb, fta, l]
      r -> do
        (a, t) <- insertH $ infer r
        f <- conv t ty
        f a

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

getHPi__ v = matchCon' "HPi" v <&> \case
    Just [a, b] -> Just (a, b)
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
  WCon _ n -> Just n
  _ -> Nothing

getMult f v = f v >>= \case
    Just (c, v) -> getMult f v <&> first (c:)
    Nothing -> pure ([], v)

getSuper :: Val -> RefM (Maybe (Val, Val))
getSuper v = matchCon' "CPi" v <&> \case
    Just [a, b] -> Just (a, b)
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

ff :: (a -> (b -> RefM c) -> RefM c) -> [a] -> ([b] -> RefM c) -> RefM c
ff _ [] cont = cont []
ff f (a: as) cont = f a \b -> ff f as \bs -> cont (b: bs)

addMethodType :: [(Name, Val)] -> [Val] -> Val -> (Name, Val) -> (Val -> RefM a) -> RefM a
addMethodType ns is arg (n_, t) cont = do
  let n = tickName (nameStr n_)
  ((vn, _), t) <- getHPi t <&> fromJust
  (_, t) <- getSuper t <&> fromJust
  f <- vLam vn t
  t <- mkMult mkHPi ns $ mkMult mkCPi is $ vApp f arg
  defineGlob n mkFun t \_ mn _ -> do
    cont mn

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
  let rhs = foldr (\(a, b) t -> TApps (TVal CSuperClassCons) [c, a, b, t]) (TVal CSuperClassNil `TApp` c) ss
  f <- mkFun "superClasses"
  addRule_ "superClasses" (TVal f `TApp` c) rhs

inferMethods :: (RefM Val -> RefM Val) -> Raw -> ([(Name, Val)] -> RefM a) -> RefM a
inferMethods under r cont = case r of
  RLetTy n t b -> do
    vta <- under $ addForalls t >>= \t -> check t CType >>= evalEnv' (typeName n)
    let ff n = if isConName n then undefined else mkFun n
    defineGlob n ff vta \n _ _ -> do
      inferMethods under b \mts -> cont $ (n, vta): mts
  REnd -> cont []
  _ -> errorM "can't infer method"

inferMethodBodies :: Raw -> RefM ()
inferMethodBodies r = case r of
  RRule a b c -> addRule' (mapHead tickName a) b >> inferMethodBodies c
  RLet a Hole b c -> addRule' (RVar $ tickName a) b >> inferMethodBodies c
  REnd -> pure ()
  r -> error' $ ("can't infer method body :\n" <>) <$> print r

addRule' a b = do
  lu <- asksEnv lookupName
  let ns = [n | n <- fvs a, Nothing <- [lu n]]
  flip (foldr addName) ns $ do
    (lhs, vta) <- insertH $ localEnv (\env -> env {isLHS = True}) $ infer a
    bv <- asksEnv boundVars <&> fromListIS
    (lhs', (st', vs)) <- runState mempty \st -> getGens (Left st) bv lhs
    flip (foldr addName') (reverse vs) $ do
      rhs <- check b vta
      bv <- asksEnv boundVars <&> fromListIS
      rhs' <- getGens (Right st') bv rhs
      addRule_ (ruleHead a) lhs' rhs'



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
  addRule_ "lookupDict" (lookup (TVal classVal `TApp` arg')) rhs
  pure ()

introClass :: Val -> RefM Val -> RefM Val
introClass c f = do
  v <- f
  vApps CCPi [c, v]

introType :: (Name, Val) -> RefM Val -> RefM Val
introType (n, t) f = do
  v <- defineBound'_ (nameStr n) n t f
  f <- vLam n v
  vApps CHPi [t, f]

multIntro :: (a -> RefM Val -> RefM Val) -> [a] -> RefM Val -> RefM Val
multIntro _ [] g = g
multIntro f (a: as) g = f a $ multIntro f as g

infer :: Raw -> RefM (Tm, Val)
infer r = do
  traceShow "6" $ "infer " <<>> showM r
  tag r $ do
    top <- asksEnv onTop
    (t, v) <- infer_ top r
    traceShow "7" $ "infer end " <<>> showM r <<>> "\n ==> " <<>> showM t <<>> "\n :: " <<>> showM v 
    pure (t, v)

infer_ :: Bool -> Raw -> RefM (Tm, Val)
infer_ top r = case r of
  RClass a b e | top -> do
    let n_ = getVarName $ appHead $ codomain a
    vta <- check Hole CType >>= evalEnv' (typeName n_)
    defineGlob_ n_ (\n -> pure $ mkCon 1{-TODO-} n $ Just vta{-TODO-}) vta
       (addForalls a >>= \a -> check a CType >>= evalEnv)
       \n tc _ ct -> do
     (is, _ss, cc) <- decomposeHead ct
     let under m = multIntro introType is $ introClass cc m
     inferMethods under b \mts -> do
      (supers, dt) <- dictType ct $ map snd mts
      ar <- conArity dt
      defineGlob (dictName n_) (\n -> pure $ mkCon ar n $ Just dt) dt \dn dv _dt -> do
       addClass n (MkClassData tc dv supers mts) do
        gl <- asksEnv globals
        forM_ (zip [0..] mts) \(i, (mname, _)) -> case lookupIM mname gl of
         Just (vf, _) -> addDictSelector vf dn (1 + length supers + length mts) (1 + length supers + i)
         _ -> impossible
        defineSuperclasses n_ tc dn (1 + length supers + length mts) supers
        infer e
  RInstance a b c | top -> do
    ct <- addForalls a >>= \a -> check a CType >>= evalEnv
    (ns, is, n, arg) <- analyzeInstanceHead ct
    asksEnv (lookupClass n) >>= \case
      Nothing -> undefined
      Just cd@(MkClassData _ _ _ mts) -> do
        ff (addMethodType ns is arg) mts \mns -> do
          addLookupDictRule cd ns is arg mns
          inferMethodBodies b
        infer c
--  RData     _a _b c | top -> infer c
  REnd -> pure (TVal CType, CType)
  RLam n t a -> do
    vt <- check t CType >>= evalEnv' (typeName n)
    defineBound' n vt \n -> do
      (ta, va) <- insertH $ infer a
      f <- vLam n va
      (,) <$> tLam n ta <*> vApps CPi [vt, f]
  RHLam n t a -> do
    vt <- check t CType >>= evalEnv' (typeName n)
    defineBound' n vt \n -> do
      (ta, va) <- infer a
      f <- vLam n va
      (,) <$> tLam n ta <*> vApps CHPi [vt, f]
  Hole -> do
    t <- freshMeta
    (_, m) <- freshMeta'
    pure (t, m)
  RNat n    -> vNat n    <&> \v -> (TVal v, CNat)
  RString n -> vString n <&> \v -> (TVal v, CString)
  RVar n -> asksEnv (lookupGlobal n) >>= \case
    Just (v, ty) -> pure (TVal v, ty)
    _ -> asksEnv (lookupLocal n) >>= \case
      Just (n, ty) -> pure (TVar n, ty)
      _ -> errorM "Not in scope"
  RLetTy n t b | top -> do
    vta <- addForalls t >>= \t -> check t CType >>= evalEnv' (typeName n)
    let ff n = if isConName n
         then do
          ar <- conArity vta
          pure $ mkCon ar n $ Just vta
         else mkFun n
    defineGlob n ff vta \_ _ _ -> infer b
  ROLet{} -> do
    (_, m) <- freshMeta'
    ty <- vApp CCode m
    t <- check r ty
    pure (t, ty)
  RRule a b c | top -> do
    addRule' a b
    infer c
  RLet n t a b | isRuleTy t -> do
    vta <- addForalls t >>= \t -> check t CType >>= evalEnv' (typeName n)
    let ff n = if isConName n then undefined else mkFun n
    defineGlob n ff vta \_ _ _ -> do
      addRule' (RVar n) a
      infer b
  RLet n t a b -> do
    (ta, vta) <- case t of
      Hole -> infer a
      t -> do
        vta <- addForalls t >>= \t -> check t CType >>= evalEnv' (typeName n)
        ta <- check a vta
        pure (ta, vta)
    va <- evalEnv' n ta
    (n, (tb, vtb)) <- defineGlob' n va vta \n -> (,) n <$> infer b
    pure (if top then tb else TLet n ta tb, vtb)
  (getPi -> Just (pi, n, a, b)) -> do
    ta <- check a CType
    va <- evalEnv' (typeName n) ta
    defineBound' n va \n -> do
      tb <- check b CType
      l <- tLam n tb
      pure (pi `TApp` ta `TApp` l, CType)
  RCPi a b -> do
    ta <- check a CType
    tb <- check b CType
    pure (TVal CCPi `TApp` ta `TApp` tb, CType)
  RIPi a b -> do
    ta <- check a CType
    tb <- check b CType
    pure (TVal CIPi `TApp` ta `TApp` tb, CType)
  RGuard a b -> do
    tb <- check b CBool
    (ta, ty) <- infer a
    pure (TGuard ta tb, ty)
  RView a b -> do
    (ta, ty) <- infer a
    (f, Expl, pa, pb) <- matchPi True Expl ty
    n <- lamName "t" pb
    defineBound' n pa \n -> do
      (_, vb) <- unlam n pb
      tb <- check b vb
      fta <- f ta
      pure (TView fta tb, pa)
  RAnn b a -> do
    va <- check a CType >>= evalEnv
    tb <- check b va
    pure (tb, va)
  RHApp a b -> do
    inferApp Impl a b
  RApp a b -> do
    inferApp Expl a b
  REmbed (MkEmbedded t v) -> pure (t, v)
  _ -> errorM "can't infer"
 where
  inferApp i a b = infer a >>= \(av, ty) -> do
    (f, icit, pa, pb) <- matchPi True i ty
    fav <- f av
    case () of
     _ | icit == ImplClass, i == Impl -> do
        tb <- check b pa
        pure (TApp fav tb, pb)
       | icit == i -> do
        tb <- check b pa
        n <- lamName "t" pb
        v <- evalEnv' n tb
        b <- vApp pb v
        pure (TApp fav tb, b)
       | icit == Impl -> do
        infer $ RApp (RHApp (REmbed $ MkEmbedded av ty) Hole) b
       | icit == ImplClass -> do
        (m, m') <- instanceMeta
        infer $ RApp (RHApp (REmbed $ MkEmbedded av ty) $ REmbed $ MkEmbedded m m') b
       | otherwise -> error "baj"

addName' :: Name -> RefM a -> RefM a
addName' n cont = do
  (_, m) <- freshMeta'
  defineBound'_ (nameStr n) n m cont

addName :: NameStr -> RefM a -> RefM a
addName n_ cont = nameOf n_ >>= \n -> addName' n cont

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

mapHead :: (NameStr -> NameStr) -> Raw -> Raw
mapHead g = f where
  f = \case
    RGuard a b -> RGuard (f a) b
    RApp a b -> RApp (f a) b
    RVar n -> RVar (g n)
    _ -> undefined

tickName n = addSuffix n (if isGraphicMixfix n then "#" else "'")

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
  infer $ reverseRules r

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

addForalls :: Raw -> RefM Raw
addForalls r = do
  lu <- asksEnv lookupName
  pure $ foldr (\n r -> RHPi n Hole r) r [n | n <- fvs' r, Nothing <- [lu n]]

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
