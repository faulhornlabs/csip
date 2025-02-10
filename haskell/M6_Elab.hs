module M6_Elab
  ( check, inferTop
  ) where

import M1_Base
import M3_Parse
import M4_Eval
import M5_Unify

-------------

pattern CType, CPi, CHPi :: Val
pattern CType = "Type" --Con (MkName "Type" (-2))
pattern CPi   = "Pi"   --Con (MkName "Pi"   (-3))
pattern CHPi  = "HPi"  --Con (MkName "HPi"  (-4))

data Icit = Impl | Expl
  deriving Eq

volatile = \case
  VMeta   -> True
  VMetaApp{} -> True
  _      -> False

matchCode :: Env -> Val -> RefM Bool
matchCode env v_ = force v_ >>= \v -> case view v of
  VApp c _ -> force c <&> \case
    code' | Just code <- lookupGlobal' "Code" env, code' == code -> True
    _ -> False
  _ -> pure False

matchPi :: Icit -> Val -> RefM (Icit, Val, Val)
matchPi _icit v_ = force v_ >>= \v -> case view v of
  x | volatile x -> undefined
  VApp f pb -> force f >>= \f -> case view f of
    VApp p pa -> force p >>= \case
      CPi  -> pure (Expl, pa, pb)
      CHPi -> pure (Impl, pa, pb)
      _ -> print v >>= \s -> errorM $ "Not a function(3): " <> s
    _   -> print v >>= \s -> errorM $ "Not a function(2): " <> s
  _     -> print v >>= \s -> errorM $ "Not a function(1): " <> s

matchHPi v_ = force v_ >>= \v -> case view v of
  VApp f pb -> force f >>= \f -> case view f of
    VApp p pa -> force p <&> \case
      CHPi -> Just (pa, pb)
      _ ->    Nothing
    _ -> pure Nothing
  _   -> pure Nothing

--------------------

data Env = MkEnv
  { locals :: [(Name, (Bool, Val, Val))]
  , globals :: Map Name (Val, Val)
  }

memptyEnv :: Env
memptyEnv = MkEnv mempty $ fromList
  [(n, (v, CType)) | (n, v) <- [("Nat", "Nat"), ("String", "String"), ("Type", CType)]]

evalEnv :: Env -> Tm -> RefM Val
evalEnv env = eval $ second (\(_, v, _) -> v) <$> locals env

evalEnv' env n t = evalEnv env t >>= \v -> if closed v then vTm n t v else pure v

onTop = null . locals

define :: Bool -> Name -> Val -> Val -> Env -> Env
define bound n v t env
  | bound || not (onTop env) = env {locals = (n, (bound, v, t)): locals env}
  | otherwise                = env {globals = insert n (v, t) $ globals env}

lookupLocal  v env = lookupList v (locals env)
lookupGlobal v env = lookup v (globals env)
lookupGlobal' v env = lookupList v [(a, b) | (MkName a _, (b, _)) <- assocs (globals env)]
lookupGlobal'' v env = lookupList v [(a, TVal b) | (MkName a _, (b, _)) <- assocs (globals env)]
lookupGlobal''' v env = lookupList v [(a, RVar n) | (n@(MkName a _), _) <- assocs (globals env)]

freshMeta :: Env -> RefM Tm
freshMeta env = do
  m <- mkName "m" <&> TVal . vMeta
  pure $ TGen $ TApps m $ reverse [TVar n | (n, (True, _, _)) <- locals env]

typeName = mapName (`addSuffix` "_t")

---------

insertH :: Env -> RefM (Tm, Val) -> RefM (Tm, Val)
insertH env et = et >>= \(e, t) -> matchHPi t >>= \case
  Nothing -> pure (e, t)
  Just (_, b) -> do
    m <- freshMeta env
    vm <- evalEnv env m
    t' <- vApp b vm
    insertH env $ pure (TApp e m, t')

vVar_ n = pure $ vVar n

lamName n x = force x <&> \v -> case view v of
  VSup c _ -> varName c
  _ -> n

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
check env r ty = tag r $ case r of
  RPi  (MkName "_" _) a b | Just ty' <- lookupGlobal' "Ty" env, ty == ty', Just arr <- lookupGlobal'' "Arr" env -> do
    ta <- check env a ty'
    tb <- check env b ty'
    pure $ arr `TApp` ta `TApp` tb
  RHLam n Hole a -> do
    (icit, pa, pb) <- matchPi Impl ty
    case icit of
      Impl -> do
        (v, t) <- unlam n pb
        ta <- check (define True n v pa env) a t
        pure $ tLam n ta
      Expl -> undefined
  RLam n Hole a -> matchCode env ty >>= \case
   True | Just lam <- lookupGlobal''' "Lam" env -> do
    check env (lam `RApp` r) ty
   _ -> do
    (icit, pa, pb) <- matchPi Expl ty
    case icit of
      Expl -> do
        (v, t) <- unlam n pb
        ta <- check (define True n v pa env) a t
        pure $ tLam n ta
      Impl -> do
        n' <- lamName "z" pb
        check env (RHLam n' Hole r) ty
  _ -> matchHPi ty >>= \case
    Just (_, pb) -> do
      n' <- lamName "z" pb
      check env (RHLam n' Hole r) ty
    Nothing -> case r of
      RLet{} -> undefined
      ROLet n a b | Just let_ <- lookupGlobal''' "Let" env ->
        check env (let_ `RApp` a `RApp` RLam n Hole b) ty
      r -> do
        (a, t) <- insertH env $ infer env r
        conv t ty
        pure a

infer :: Env -> Raw -> RefM (Tm, Val)
infer env r = tag r $ case r of
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
    m <- freshMeta env >>= evalEnv env
    pure (t, m)
  RVar n@NNat{}    -> pure (TVal $ Con n, "Nat")
  RVar n@NString{} -> pure (TVal $ Con n, "String")
  RVar n | Just (v_, ty) <- lookupGlobal n env -> pure (TVal v_, ty)
  RVar n | Just (_bound, _, ty) <- lookupLocal n env -> pure (TVar n, ty)
  RVar{} -> errorM "Not in scope"
  RLetOTy n "Type" b | onTop env, Just vta <- lookupGlobal' "Ty" env -> do
    let c = Con n
    infer (define False n c vta env) b
  RLetOTy n t b | onTop env, Just ty <- lookupGlobal' "Ty" env, Just code <- lookupGlobal' "Code" env -> do
    vta_ <- check env t ty >>= evalEnv' env (typeName n)
    vta <- vApp code vta_
    let c = Con n
    infer (define False n c vta env) b
  RLetTy n t b | onTop env -> do
    vta <- check env t CType >>= evalEnv' env (typeName n)
    c <- if isConName n then pure $ Con n else do
      updateRule n $ Con "Fail"
      pure $ Fun n
    infer (define False n c vta env) b
  ROLet n a b | Just let_ <- lookupGlobal''' "Let" env ->
    infer env $ let_ `RApp` a `RApp` RLam n Hole b
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
    (Expl, pa, pb) <- matchPi Expl ty
    n <- mkName "t"
    (v, vb) <- unlam n pb
    tb <- check (define True n v pa env) b vb
    pure (TView ta tb, pa)
  RHApp a b -> do
    inferApp Impl env a b
  RApp a b -> do
    inferApp Expl env a b
  _ -> errorM "can't infer"
 where
  inferApp i env a b = infer env a >>= \(av, ty) -> matchCode env ty >>= \case
   True | Expl <- i, Just app <- lookupGlobal''' "App" env ->
        infer env $ RApp (RApp app a) b
   _ -> do
    (icit, pa, pb) <- matchPi i ty
    if icit == i then do
        tb <- check env b pa
        n <- lamName "t" pb
        v <- evalEnv' env n tb
        b <- vApp pb v
        pure (TApp av tb, b)
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

