module M6_Elab
  ( check, inferTop
  ) where

import M1_Base
import M3_Parse
import M4_Eval
import M5_Unify

-------------

pattern CType, CPi, CHPi, CCode, CTy, CArr :: Val
pattern CType = "Type"
pattern CPi   = "Pi"
pattern CHPi  = "HPi"
pattern CCPi  = "CPi"   --   t => s
pattern CCode = "Code"
pattern CTy   = "Ty"
pattern CArr  = "Arr"

data Icit = Impl | ImplClass | Expl
  deriving Eq

matchCode :: Env -> Val -> RefM (Tm -> Tm, Tm)
matchCode env v = do
  (tm, m) <- freshMeta' env
  cm <- vApp CCode m
  f <- conv env v cm
  pure (f, tm)


-- True:   x: t      f x: Pi
-- False:  x: Pi     f x: t
matchPi :: Bool -> Env -> Icit -> Val -> RefM (Tm -> Tm, Icit, Val, Val)
matchPi cov env icit v_ = force v_ >>= \v -> do
 let
   def = do
    (_, m1) <- freshMeta' env
    (_, m2) <- freshMeta' env
    let pi = case icit of Impl -> CHPi; Expl -> CPi; _ -> impossible
    v2 <- vApps pi [m1, m2]
    f <- if cov then conv env v v2 else conv env v2 v
    pure (f, icit, m1, m2)
 case view v of
  VApp f pb -> force f >>= \f -> case view f of
    VApp p pa -> force p >>= \case
      CPi  -> pure (id, Expl,      pa, pb)
      CHPi -> pure (id, Impl,      pa, pb)
      CCPi -> pure (id, ImplClass, pa, pb)
      _ -> def
    _   -> def
  _     -> def

matchHPi v_ = force v_ >>= \v -> case view v of
  VApp f pb -> force f >>= \f -> case view f of
    VApp p pa -> force p <&> \case
      CHPi -> Just (Impl,      pa, pb)
      CCPi -> Just (ImplClass, pa, pb)
      _ ->    Nothing
    _ -> pure Nothing
  _   -> pure Nothing

--------------------

data Env = MkEnv
  { boundVars   :: [Name]
  , localVals   :: Map Name Val
  , localTypes  :: Map Name Val
  , globals     :: Map Name (Val, Val)
  , isLHS       :: Bool    -- True if lhs is checked
  }

memptyEnv :: Env
memptyEnv = foldr def (MkEnv mempty mempty mempty mempty False)
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
  | otherwise
  = env { globals = insert n (v, t) $ globals env
        }

defineGlob = define False
defineBound n = define True n (vVar n)

lookupLocal      v env = lookup v (localTypes  env)
lookupGlobal     v env = lookup v (globals     env)

evalEnv :: Env -> Tm -> RefM Val
evalEnv env = eval $ localVals env

evalEnv' env n t = evalEnv env t >>= \v -> if closed v then vTm n t v else pure v

freshMeta :: Env -> RefM Tm
freshMeta env = do
  m <- tMeta
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

    () | ha == CPi, hb == CPi, [m1, m2] <- va, [m3, m4] <- vb
       -> do

      q <- conv_ env m3 m1

      v <- lamName "v" m2
      let vv = vVar v
      let env' = defineBound v m3 env

      q_v <- evalEnv env' $ evalId q $ TVar v
      c1 <- vApp m2 q_v
      c2 <- vApp m4 vv
      h_v <- conv_ env' c1{- m2 (q v) -} c2{- m4 v -}

      pure $ case (h_v, q) of
        (Nothing, Nothing) -> Nothing
        _ -> Just \t -> tLam v $ evalId h_v $ TApp t (evalId q $ TVar v)

    () | ha == CCode, hb == CPi, [m3, m4] <- vb -> do

      (m1, m1')  <- freshMeta' env
      (m2, m2')  <- freshMeta' env

      v <- lamName "v" m4
      let vv = vVar v

      ar <- vApp CCode =<< vApps CArr [m1', m2']
      f <- conv env a ar{- Code (Arr m1 m2) -}

      c1 <- vApp CCode m1'
      c2 <- vApp CCode m2'
      m4_v <- vApp m4 vv
      h_v <- conv_ (defineBound v c1 env) c2{- Code m2 -} m4_v  --  (Code m1 -> Code m2)  ==>  (Code m1 -> m4)

      q <- conv_ env m3{- m3 -} c1{- Code m1 -}

      let lam t = case (h_v, q) of
            (Nothing, Nothing) -> t
            _ -> tLam v $ evalId h_v $ TApp t (evalId q $ TVar v)

      pure $ Just \t -> lam $ TApps (TVal $ Con "App") [m1, m2, f t]

    () | ha == CPi, hb == CCode, [m3, m4] <- va -> do

      (m1, m1')  <- freshMeta' env
      (m2, m2')  <- freshMeta' env

      v <- lamName "v" m4
      let vv = vVar v

      ar <- vApp CCode =<< vApps CArr [m1', m2']
      f <- conv env ar{- Code (Arr m1 m2) -} b

      c1 <- vApp CCode m1'
      c2 <- vApp CCode m2'
      m4_v <- vApp m4 vv
      h_v <- conv_ (defineBound v c1 env) m4_v{- m4 v -} c2{- Code m2 -}  --  (Code m1 -> m4 v)  ==>  (Code m1 -> Code m2)

      q <- conv_ env c1{- Code m1 -} m3

      let lam t = case (h_v, q) of
            (Nothing, Nothing) -> t
            _ -> tLam v $ evalId h_v $ TApp t (evalId q $ TVar v)

      pure $ Just \t -> f $ TApps (TVal $ Con "Lam") [m1, m2, lam t]

    _ -> do
      () <- unify a b
      pure Nothing


---------

insertH :: Env -> RefM (Tm, Val) -> RefM (Tm, Val)
insertH env et = et >>= \(e, t) -> matchHPi t >>= \case
  Nothing -> pure (e, t)
  Just (ImplClass, _, b) -> do
    m <- freshMeta env
    insertH env $ pure (TApp e (TApp (TVal $ Fun "instanceOf") m), b)
  Just (Impl, _, b) -> do
    (m, vm) <- freshMeta' env
    t' <- vApp b vm
    insertH env $ pure (TApp e m, t')
  _ -> undefined

lamName n x = force x >>= \v -> case view v of
  VLam n -> n
  _ -> pure n

unlam n' f = do
  let v = vVar n'
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
  RPi "_" a b | ty == CTy -> do
    ta <- check env a CTy
    tb <- check env b CTy
    pure $ TVal CArr `TApp` ta `TApp` tb
  RHLam n Hole a -> do
    (f, icit, pa, pb) <- matchPi True env Impl ty
    case icit of
      Impl -> do
        (_, t) <- unlam n pb
        ta <- check (defineBound n pa env) a t
        pure $ f $ tLam n ta
      _ -> undefined
  RLam n Hole a -> do
    (f, icit, pa, pb) <- matchPi True env Expl ty
    case icit of
      Expl -> do
        (_, t) <- unlam n pb
        ta <- check (defineBound n pa env) a t
        pure $ f $ tLam n ta
      Impl -> do
        n' <- lamName "z" pb
        f <$> check env (RHLam n' Hole r) ty
      _ -> undefined
  _ -> matchHPi ty >>= \case
    Just (Impl, _, pb) | not (isLHS env) -> do
      n' <- lamName "z" pb
      check env (RHLam n' Hole r) ty
    _ -> case r of
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
        tb <- check (defineBound n vta env) b ty
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
  RLam n t a -> do
    vt <- check env t CType >>= evalEnv' env (typeName n)
    let v = vVar n
    (ta, va) <- insertH env $ infer (defineBound n vt env) a
    f <- vLam v va
    (,) (tLam n ta) <$> vApps CPi [vt, f]
  RHLam n t a -> do
    vt <- check env t CType >>= evalEnv' env (typeName n)
    let v = vVar n
    (ta, va) <- infer (defineBound n vt env) a
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
  RLetOTy n "Type" b | onTop env -> do
    infer (defineGlob n (Con n) CTy env) b
  RLetOTy n t b | onTop env -> do
    vta_ <- check env t CTy >>= evalEnv' env (typeName n)
    vta <- vApp CCode vta_
    infer (defineGlob n (Con n) vta env) b
  RLetTy n t b | onTop env -> do
    vta <- check env t CType >>= evalEnv' env (typeName n)
    c <- if isConName n then pure $ Con n else do
      updateRule n $ Con "Fail"
      pure $ Fun n
    infer (defineGlob n c vta env) b
  ROLet{} -> do
    (_, m) <- freshMeta' env
    ty <- vApp CCode m
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
    (ta, vta) <- infer (env {isLHS = True}) a
    tb <- check env b vta
    addRule (boundVars env) ta tb
    pure (TVal CType, CType)  -- TODO?
  (getPi -> Just (pi, n, a, b)) -> do
    ta <- check env a CType
    va <- evalEnv' env (typeName n) ta
    tb <- check (defineBound n va env) b CType
    pure (pi `TApp` ta `TApp` tLam n tb, CType)
  RCPi a b -> do
    ta <- check env a CType
    tb <- check env b CType
    pure (TVal CCPi `TApp` ta `TApp` tb, CType)
  RView a b -> do
    (ta, ty) <- infer env a
    (f, Expl, pa, pb) <- matchPi True env Expl ty
    n <- lamName "t" pb
    (_, vb) <- unlam n pb
    tb <- check (defineBound n pa env) b vb
    pure (TView (f ta) tb, pa)
  RHApp a b -> do
    inferApp Impl env a b
  RApp a b -> do
    inferApp Expl env a b
  _ -> errorM "can't infer"
 where
  inferApp i env a b = infer env a >>= \(av, ty) -> do
    (f, icit, pa, pb) <- matchPi True env i ty
    case () of
     _ | icit == ImplClass, i == Impl -> do
        tb <- check env b pa
        pure (TApp (f av) tb, pb)
       | icit == i -> do
        tb <- check env b pa
        n <- lamName "t" pb
        v <- evalEnv' env n tb
        b <- vApp pb v
        pure (TApp (f av) tb, b)
       | icit == Impl -> do
        infer env $ RApp (RHApp a Hole) b
       | icit == ImplClass -> do
        infer env $ RApp (RHApp a (RVar "instanceOf" `RApp` Hole)) b
       | otherwise -> error "baj"

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

