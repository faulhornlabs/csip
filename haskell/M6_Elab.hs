module M6_Elab
  ( check, inferTop
  ) where

import M1_Base
import M3_Parse
import M4_Eval
import M5_Unify

-------------

pattern CType, CPi, CHPi :: Val
pattern CType = "Type"
pattern CPi   = "Pi"
pattern CHPi  = "HPi"

data Icit = Impl | Expl
  deriving Eq

matchCode :: Env -> Val -> RefM (Tm -> Tm, Tm)
matchCode env v | Just code <- lookupGlobal' "Code" env = do
  (tm, m) <- freshMeta' env
  cm <- vApp code m
  f <- conv env v cm
  pure (f, tm)
matchCode _ _ = undefined


-- True:   x: t      f x: Pi
-- False:  x: Pi     f x: t
matchPi :: Bool -> Env -> Icit -> Val -> RefM (Tm -> Tm, Icit, Val, Val)
matchPi cov env icit v_ = force v_ >>= \v -> do
 let
   def = do
    (_, m1) <- freshMeta' env
    (_, m2) <- freshMeta' env
    let pi = case icit of Impl -> CHPi; Expl -> CPi
    v2 <- vApps pi [m1, m2]
    f <- if cov then conv env v v2 else conv env v2 v
    pure (f, icit, m1, m2)
 case view v of
  VApp f pb -> force f >>= \f -> case view f of
    VApp p pa -> force p >>= \case
      CPi  -> pure (id, Expl, pa, pb)
      CHPi -> pure (id, Impl, pa, pb)
      _ -> def
    _   -> def
  _     -> def

matchHPi v_ = force v_ >>= \v -> case view v of
  VApp f pb -> force f >>= \f -> case view f of
    VApp p pa -> force p <&> \case
      CHPi -> Just (pa, pb)
      _ ->    Nothing
    _ -> pure Nothing
  _   -> pure Nothing

--------------------

data Env = MkEnv
  { boundVars   :: [Name]
  , localVals   :: Map Name Val
  , localTypes  :: Map Name Val
  , globals     :: Map Name (Val, Val)
  , globalNames :: Map NameStr Name          -- TODO: remove
  }

memptyEnv :: Env
memptyEnv = foldr def (MkEnv mempty mempty mempty mempty mempty)
  [("Nat", "Nat"), ("String", "String"), ("Type", CType)]
 where
  def (n, v) = defineGlob n v CType

onTop :: Env -> Bool
onTop = null . boundVars

define :: Bool -> Name -> Val -> Val -> Env -> Env
define bound n v t env
  | bound || not (onTop env)
  = env { localTypes = insert n t $ localTypes env
        , localVals = insert n v $ localVals env
        , boundVars = (if bound then (n:) else id) $ boundVars env
        }
  | otherwise = defineGlob_ n v t env

defineGlob = define False

defineGlob_ :: Name -> Val -> Val -> Env -> Env
defineGlob_ n v t env
  = env { globals = insert n (v, t) $ globals env
        , globalNames = insert (nameStr n) n $ globalNames env
        }

lookupLocal      v env = lookup v (localTypes  env)
lookupGlobal     v env = lookup v (globals     env)
lookupGlobalName v env = lookup v (globalNames env)

lookupGlobal' v env = do
  n <- lookupGlobalName v env
  fst <$> lookupGlobal n env

evalEnv :: Env -> Tm -> RefM Val
evalEnv env = eval $ localVals env

evalEnv' env n t = evalEnv env t >>= \v -> if closed v then vTm n t v else pure v

freshMeta :: Env -> RefM Tm
freshMeta env = do
  m <- mkName' "m" <&> TVal . vMeta
  pure $ TGen $ TApps m $ reverse $ TVar <$> boundVars env

freshMeta' :: Env -> RefM (Tm, Val)
freshMeta' env = do
  m <- freshMeta env
  (,) m <$> evalEnv env m

typeName = mapName (`addSuffix` "_t")

---------

evalId :: Maybe (a -> a) -> a -> a
evalId = fromMaybe id

conv
  :: Env
  -> Val               -- actual type
  -> Val               -- expected type
  -> RefM (Tm -> Tm)   -- transformation from actual to expected
conv env a b = evalId <$> conv_ env a b

conv_ :: Env
  -> Val               -- actual type
  -> Val               -- expected type
  -> RefM (Maybe (Tm -> Tm))   -- transformation from actual to expected (Nothing: identity)
conv_ env a b = do
  (ha, va) <- spine a
  (hb, vb) <- spine b
  case () of

    () | "Pi" <- name ha, "Pi" <- name hb, [m1, m2] <- va, [m3, m4] <- vb
       -> do

      q <- conv_ env m3 m1

      v <- lamName "v" m2
      vv <- vVar_ v
      let env' = define True v vv m3 env

      q_v <- evalEnv env' $ evalId q $ TVar v
      c1 <- vApp m2 q_v
      c2 <- vApp m4 vv
      h_v <- conv_ env' c1{- m2 (q v) -} c2{- m4 v -}

      pure $ case (h_v, q) of
        (Nothing, Nothing) -> Nothing
        _ -> Just \t -> tLam v $ evalId h_v $ TApp t (evalId q $ TVar v)

    () | MkName "Code" _ <- name ha, "Pi" <- name hb, [m3, m4] <- vb
       , Just ap <- get "App", Just code <- get "Code", Just arr <- get "Arr" -> do

      (m1, m1')  <- freshMeta' env
      (m2, m2')  <- freshMeta' env

      v <- mkName "v"
      vv <- vVar_ v

      ar <- vApp code =<< vApps arr [m1', m2']
      f <- conv env a ar{- Code (Arr m1 m2) -}

      c1 <- vApp code m1'
      c2 <- vApp code m2'
      m4_v <- vApp m4 vv
      h_v <- conv_ (define True v vv c1 env) c2{- Code m2 -} m4_v  --  (Code m1 -> Code m2)  ==>  (Code m1 -> m4)

      q <- conv_ env m3{- m3 -} c1{- Code m1 -}

      let lam t = case (h_v, q) of
            (Nothing, Nothing) -> t
            _ -> tLam v $ evalId h_v $ TApp t (evalId q $ TVar v)

      pure $ Just \t -> lam $ TApps (TVal ap) [m1, m2, f t]

    () | "Pi" <- name ha, MkName "Code" _ <- name hb, [m3, m4] <- va
       , Just la <- get "Lam", Just code <- get "Code", Just arr <- get "Arr" -> do

      (m1, m1')  <- freshMeta' env
      (m2, m2')  <- freshMeta' env

      v <- lamName "v" m4
      vv <- vVar_ v

      ar <- vApp code =<< vApps arr [m1', m2']
      f <- conv env ar{- Code (Arr m1 m2) -} b

      c1 <- vApp code m1'
      c2 <- vApp code m2'
      m4_v <- vApp m4 vv
      h_v <- conv_ (define True v vv c1 env) m4_v{- m4 v -} c2{- Code m2 -}  --  (Code m1 -> m4 v)  ==>  (Code m1 -> Code m2)

      q <- conv_ env c1{- Code m1 -} m3

      let lam t = case (h_v, q) of
            (Nothing, Nothing) -> t
            _ -> tLam v $ evalId h_v $ TApp t (evalId q $ TVar v)

      pure $ Just \t -> f $ TApps (TVal la) [m1, m2, lam t]

    _ -> do
      () <- unify a b
      pure Nothing
 where
  get n = lookupGlobal' n env


---------

insertH :: Env -> RefM (Tm, Val) -> RefM (Tm, Val)
insertH env et = et >>= \(e, t) -> matchHPi t >>= \case
  Nothing -> pure (e, t)
  Just (_, b) -> do
    (m, vm) <- freshMeta' env
    t' <- vApp b vm
    insertH env $ pure (TApp e m, t')

vVar_ n = pure $ vVar n

lamName n x = force x >>= \v -> case view v of
  VLam n -> n
  _ -> pure n

unlam n f = do
  n' <- lamName n f
  v <- vVar_ n'
  t <- vApp f v
  pure (v, t)

getPi (RPi  n a b) = Just (TVal  CPi, n, a, b)
getPi (RHPi n a b) = Just (TVal CHPi, n, a, b)
getPi _ = Nothing

--------------------

check :: Env -> Raw -> Val -> RefM Tm
check env r ty = do
  traceShow $ "check " <<>> showM r <<>> "\n :? " <<>> showM ty
  tag r $ do
    t <- check_ env r ty
    traceShow $ "check end " <<>> showM r <<>> "\n ==> " <> showM t
    pure t

check_ env r ty = case r of
  Hole -> freshMeta env
  RPi  (MkName "_" _) a b | Just ty' <- lookupGlobal' "Ty" env, ty == ty', Just arr <- lookupGlobal' "Arr" env -> do
    ta <- check env a ty'
    tb <- check env b ty'
    pure $ TVal arr `TApp` ta `TApp` tb
  RHLam n Hole a -> do
    (f, icit, pa, pb) <- matchPi True env Impl ty
    case icit of
      Impl -> do
        (v, t) <- unlam n pb
        ta <- check (define True n v pa env) a t
        pure $ f $ tLam n ta
      Expl -> undefined
  RLam n Hole a -> do
    (f, icit, pa, pb) <- matchPi True env Expl ty
    case icit of
      Expl -> do
        (v, t) <- unlam n pb
        ta <- check (define True n v pa env) a t
        pure $ f $ tLam n ta
      Impl -> do
        n' <- lamName "z" pb
        f <$> check env (RHLam n' Hole r) ty
  _ -> matchHPi ty >>= \case
    Just (_, pb) -> do
      n' <- lamName "z" pb
      check env (RHLam n' Hole r) ty
    Nothing -> case r of
      RLet n t a b -> do
        (ta, vta) <- case t of
          Hole -> infer env a
          t -> do
            vta <- check env t CType >>= evalEnv' env (typeName n)
            ta <- check env a vta
            pure (ta, vta)
        va <- evalEnv' env n ta
        tb <- check (define False n va vta env) b ty
        pure $ if onTop env then tb else TLet n ta tb
      ROLet n a b | onTop env -> do
        (ta, vta) <- infer env a
        tb <- check (defineGlob n (Con n) vta env) b ty
        (fa, pa) <- matchCode env vta
        (fb, pb) <- matchCode env ty
        pure $ TApps "TopLet" [pa, pb, TVal (Con n), fa ta, fb tb]
      ROLet n a b -> do
        (ta, vta) <- infer env a
        tb <- check (define True n (vVar n) vta env) b ty
        (fa, pa) <- matchCode env vta
        (fb, pb) <- matchCode env ty
        pure $ TApps "Let" [pa, pb, fa ta, tLam n $ fb tb]
      r -> do
        (a, t) <- insertH env $ infer env r
        f <- conv env t ty
        pure $ f a

infer :: Env -> Raw -> RefM (Tm, Val)
infer env r = do
  traceShow $ "infer " <<>> showM r
  tag r $ do
    (t, v) <- infer_ env r
    traceShow $ "infer end " <<>> showM r <<>> "\n ==> " <<>> showM t <<>> "\n :: " <<>> showM v 
    pure (t, v)

infer_ env r = case r of
  RLam n_ t a -> do
    n <- pure n_
    vt <- check env t CType >>= evalEnv' env (typeName n)
    v <- vVar_ n
    (ta, va) <- insertH env $ infer (define True n_ v vt env) a
    f <- vLam v va
    (,) (tLam n ta) <$> vApps CPi [vt, f]
  RHLam n t a -> do
    vt <- check env t CType >>= evalEnv' env (typeName n)
    v <- vVar_ n
    (ta, va) <- infer (define True n v vt env) a
    f <- vLam v va
    (,) (tLam n ta) <$> vApps CHPi [vt, f]
  Hole -> do
    t <- freshMeta env
    (_, m) <- freshMeta' env
    pure (t, m)
  RVar n@NNat{}    -> pure (TVal $ Con n, "Nat")
  RVar n@NString{} -> pure (TVal $ Con n, "String")
  RVar n | Just (v, ty) <- lookupGlobal n env -> pure (TVal v, ty)
  RVar n | Just ty      <- lookupLocal  n env -> pure (TVar n, ty)
  RVar{} -> errorM "Not in scope"
  RLetOTy n "Type" b | onTop env, Just vta <- lookupGlobal' "Ty" env -> do
    let c = Con n
    infer (defineGlob n c vta env) b
  RLetOTy n t b | onTop env, Just ty <- lookupGlobal' "Ty" env, Just code <- lookupGlobal' "Code" env -> do
    vta_ <- check env t ty >>= evalEnv' env (typeName n)
    vta <- vApp code vta_
    let c = Con n
    infer (defineGlob n c vta env) b
  RLetTy n t b | onTop env -> do
    vta <- check env t CType >>= evalEnv' env (typeName n)
    c <- if isConName n then pure $ Con n else do
      updateRule n $ Con "Fail"
      pure $ Fun n
    infer (defineGlob n c vta env) b
  ROLet{} | Just code <- lookupGlobal' "Code" env -> do
    (_, m) <- freshMeta' env
    ty <- vApp code m
    t <- check env r ty
    pure (t, ty)
  RLet n t a b -> do
    (ta, vta) <- case t of
      Hole -> infer env a
      t -> do
        vta <- check env t CType >>= evalEnv' env (typeName n)
        ta <- check env a vta
        pure (ta, vta)
    va <- evalEnv' env n ta
    (tb, vtb) <- infer (define False n va vta env) b
    pure (if onTop env then tb else TLet n ta tb, vtb)
  RRule a b {- | onTop env -} -> do
    (ta, vta) <- infer env a
    tb <- check env b vta
    addRule ta tb
    pure (TVal CType, CType)  -- TODO?
  (getPi -> Just (pi, n, a, b)) -> do
    ta <- check env a CType
    va <- evalEnv' env (typeName n) ta
    v <- vVar_ n
    tb <- check (define True n v va env) b CType
    pure (pi `TApp` ta `TApp` tLam n tb, CType)
  RView a b -> do
    (ta, ty) <- infer env a
    (f, Expl, pa, pb) <- matchPi True env Expl ty
    n <- mkName "t"
    (v, vb) <- unlam n pb
    tb <- check (define True n v pa env) b vb
    pure (TView (f ta) tb, pa)
  RHApp a b -> do
    inferApp Impl env a b
  RApp a b -> do
    inferApp Expl env a b
  _ -> errorM "can't infer"
 where
  inferApp i env a b = infer env a >>= \(av, ty) -> do
    (f, icit, pa, pb) <- matchPi True env i ty
    if icit == i then do
        tb <- check env b pa
        n <- lamName "t" pb
        v <- evalEnv' env n tb
        b <- vApp pb v
        pure (TApp (f av) tb, b)
      else if icit == Impl then do
        infer env $ RApp (RHApp a Hole) b
      else error "baj"

--------------------

ruleHead :: Raw -> Maybe Name
ruleHead = \case
  RRule a _  -> f a
  RPi _ _ b -> ruleHead b
  _ -> Nothing
 where
  f = \case
    RApp a _ -> f a
    RVar n -> Just n
    _ -> Nothing

reverseRules :: Raw -> Raw
reverseRules = g where
  g = \case
    RLet n t a b | Just h <- ruleHead a -> f h [(n, t, a)] b
    RLet  n t a b -> RLet  n t a (g b)
    RLetTy  n t b -> RLetTy  n t (g b)
    ROLet   n a b -> ROLet   n a (g b)
    RLetOTy n t b -> RLetOTy n t (g b)
    r -> r  -- TODO

  f h acc = \case
    RLet n t a b | Just h' <- ruleHead a, h' == h -> f h ((n, t, a): acc) b
    r -> foldr (\(n, t, a) b -> RLet n t a b) (g r) acc

inferTop :: Raw -> RefM (Tm, Val)
inferTop r = infer memptyEnv $ reverseRules r

instance Parse (Tm, Val) where
  parse = parse >=> inferTop

instance Parse Tm where
  parse s = parse s <&> (fst :: (Tm, Val) -> Tm)

