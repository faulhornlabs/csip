module M4_Eval
  ( Combinator, varName

  , Tm_ (TGen, TVar, TApp, TApps, TLet, TVal, TView)
  , Tm, tLam

  , Val (Con, Fun)
  , View (VSup, VLam, VApp, VApp_, VMeta, VMetaApp, VVar, VCon, VFun, VTm)
  , vVar, vApp, vApps, vSup, vMeta, vTm, vLam, vLams, vConst
  , name, rigid, closed, view
  , force_, force', force

  , eval, evalClosed      -- Tm  -> Val
  , quoteTm'   -- Val -> Tm
  , quoteNF   -- Val -> Raw
  , quoteNF'

  , showMetaEnv, lookupMeta, updateMeta
  , updateRule
  , addRule

  , spine, forcedSpine
  ) where

import M1_Base
import M3_Parse

-------------

-- De Bruijn index
data DB = MkDB
  { dbIndex :: !Int
  , dbName  :: !NameStr
  }

instance Print  DB where print  = print  . dbName
instance PPrint DB where pprint = pprint . dbName
instance Eq  DB where (==)    = (==)    `on` dbIndex
instance Ord DB where compare = compare `on` dbIndex

-------------

data Combinator         -- supercombinator (rigid, closed)
  = Lams [NameStr] (Tm_ DB)     -- \x1 ... xN -> t

evalCombinator :: Combinator -> [Val] -> RefM Val
evalCombinator (Lams ns t) vs = eval (fromList $ zip (zipWith MkDB [0..] ns) vs) t

evalCombinatorTm :: Combinator -> [Tm] -> RefM Tm
evalCombinatorTm (Lams ns t) vs = evalTm (fromList $ zip (zipWith MkDB [0..] ns) vs) t

mkCombinator :: Name -> Tm_ Name -> (Combinator, [Name])
mkCombinator n t = (Lams (map nameStr nsA) $ f (fromList $ zip nsA [0..]) t, ns_)   where

  ns' = fvs t
  isconst = not $ member n ns'
  ns_ = filter (/= n) $ toList ns'
  nsA = ns_ ++ [if isconst then rename "_" n else n]

  fvs = \case
    TGen e -> fvs e
    TVar n -> singletonSet n
    TVal _ -> mempty
    TApp a b -> fvs a <> fvs b
    TLet n a b -> fvs a <> delete n (fvs b)
    TSup _ ts -> mconcat (map fvs ts)
    TMatch _ a b c -> fvs a <> fvs b <> fvs c
    TSel _ _ e -> fvs e
    TRet e -> fvs e

  f env = \case
    TVar n -> TVar $ MkDB (fromJust $ lookup n env) (nameStr n)
    TGen e -> TGen $ f env e
    TVal v -> TVal v
    TApp a b -> TApp (f env a) (f env b)
    TLet n a b | i <- size env -> TLet (MkDB i $ nameStr n) (f env a) (f (insert n i env) b)
    TSup c ts -> TSup c $ map (f env) ts
    TMatch n a b c -> TMatch n (f env a) (f env b) (f env c)
    TSel i j e -> TSel i j $ f env e
    TRet e -> TRet $ f env e

instance PPrint Combinator where
  pprint (Lams ns t) = "|->" :@ foldl1 (:@) (map pprint ns) :@ pprint t

varName (Lams ns _) = mkName $ last ns

pattern VLam n <- VSup (varName -> n) _


-------------

data Tm_ a
  = TVar a                  -- x
  | TApp (Tm_ a) (Tm_ a)    -- t u
  | TSup Combinator [Tm_ a] -- c t1 ... t(N-1)
  | TLet a (Tm_ a) (Tm_ a)  -- x = t; u

  | TMatch Name (Tm_ a) (Tm_ a) (Tm_ a)
  | TSel Int Int (Tm_ a)
  | TRet (Tm_ a)

  | TGen (Tm_ a)            -- generated term
  | TVal Val                -- closed value

instance PPrint a => PPrint (Tm_ a) where
  pprint = \case
    TVar n -> pprint n
    TApp a b -> "@" :@ pprint a :@ pprint b
    TSup c ts -> foldl (:@) (pprint c) $ map pprint ts
    TLet n a b -> zVar ["=",";"] :@ pprint n :@ pprint a :@ pprint b
    TVal v -> pprint $ name v
    _ -> undefined

-------------

type Tm = Tm_ Name

pattern TView :: Tm -> Tm -> Tm
pattern TView a b = TApp (TApp (TVal (Con "View")) a) b

getTApps (TApp (getTApps -> (a, es)) e) = (a, e: es)
getTApps e = (e, [])

pattern TApps :: Tm_ a -> [Tm_ a] -> Tm_ a
pattern TApps e es <- (getTApps -> (e, reverse -> es))
  where TApps e es = foldl TApp e es

tLam :: Name -> Tm -> Tm
tLam n t = TSup c $ TVar <$> ns'
  where (c, ns') = mkCombinator n t

instance IsString Tm where
  fromString = TVal . fromString

---------

notDefined x = error' $ fmap ("not defined: " <>) $ print x

eval_
  :: (Print a, Ord a)
  => (Val -> RefM b)
  -> (b -> RefM b)
  -> (b -> b -> RefM b)
  -> (Combinator -> [b] -> RefM b)
  -> (a -> RefM b)
  -> (Name -> b -> b -> b -> RefM b)
  -> (Int -> Int -> b -> RefM b)
  -> (b -> RefM b)
  -> Map a b
  -> Tm_ a
  -> RefM b
eval_ val box vApp vSup var match sel ret = go
 where
  go env = \case
    TVal v     -> val v
    TGen x     -> box =<< go env x
    TVar x     -> maybe (var x) pure $ lookup x env
    TApp t u   -> join $ vApp <$> go env t <*> go env u
    TSup c ts  -> join $ vSup c <$> mapM (go env) ts
    TLet x t u -> go env t >>= \v -> go (insert x v env) u
    TMatch n a b c -> join $ match n <$> go env a <*> go env b <*> go env c
    TSel i j e -> join $ sel i j <$> go env e
    TRet e     -> join $ ret <$> go env e

evalTm :: Map DB Tm -> Tm_ DB -> RefM Tm
evalTm  = eval_
  (pure . TVal)
  (pure . TGen)
  (\a b -> pure $ TApp a b)
  (\a b -> pure $ TSup a b)
  notDefined
  (\n a b c -> pure $ TMatch n a b c)
  (\i j -> pure . TSel i j)
  (pure . TRet)

--------

data H a = MkH Name a
idH (MkH n _) = n
instance Eq (H a) where (==) = (==) `on` idH
instance Ord (H a) where compare = compare `on` idH
{-
ungenTm :: Tm -> Tm
ungenTm = go  where
  go = \case
    TGen e -> eval [] e >>= quoteTm >>= go
    TVal v -> pure $ TVal v
    TVar n -> pure $ TVar n
    TApp a b -> TApp <$> go a <*> go b
    TLet n a b -> TLet n <$> go a <*> go b
    TSup (Lams ns e) ts -> TSup
-}
tmToRaw :: Tm -> RefM Raw
tmToRaw t = do
  (r, ds) <- basic t
  ma <- topDown down (mkH ds)
  foldM (\r (n, v) -> pure $ RLet n Hole v r) r $ reverse $ assocs $ mconcat $ toList ma
 where
  mkH ds = [MkH n v | (n, v) <- assocs ds]

  down :: H Val -> RefM (Map Name Raw, [H Val])
  down (MkH n v) = do
    t <- quoteTm v
    (r, ds) <- basic t
    pure $ (singleton n r, mkH ds)

  basic :: Tm -> RefM (Raw, Map Name Val)
  basic t = runWriter ff <&> second snd where
    ff wst = f mempty t  where
      add n env = insert n (vVar n) env

      f env = \case
        TVal v | n@NNat{}    <- name v -> pure (RVar n)
        TVal v | n@NString{} <- name v -> pure (RVar n)
        TVal v | n@NConst{}  <- name v -> pure (RVar n)
        TVal v | VCon  <- view v -> pure (RVar $ name v)
        TVal v | n <- name v -> force_ v >>= \v -> tell wst (mempty, singleton n v) >> pure (RVar n)
        TGen e -> eval' env e >>= quoteTm >>= f env
        TVar n  -> pure $ RVar n
        TApp a b -> (:@) <$> f env a <*> f env b
        TLet n a b -> tell wst (singletonSet n, mempty) >> (RLet n Hole <$> f env a <*> f (add n env) b)
        TSup c ts -> do
          n <- varName c
          t <- evalCombinatorTm c $ ts <> [TVar n]
          Lam n <$> f (add n env) t
        TMatch n a b c -> rMatch n <$> f env a <*> f env b <*> f env c
        TSel i j a -> rSel i j <$> f env a
        TRet a -> rRet <$> f env a

instance Print Tm where
  print t = print =<< tmToRaw t

-------------------------------

data View a
  = VVar   -- bound variable
  | VCon   -- constructor
  | VFun   -- function
  | VMeta  -- meta
  | VApp_ a a (Maybe a){-accumulated result-} (Maybe a){-meta dependency-}
  | VSup Combinator [a]     -- lambda
  | VSel Int Int a       -- Sel appears only behind the "then" branch of Match       -- meta dependency needed?
  | VMatch Name a a a (Maybe a){-meta dependency-}
  | VRet a
  | VTm Tm a

pattern VApp a b <- VApp_ a b _ _

-- volatile App depending on a meta
pattern VMetaApp a <- VApp_ _ _ _ (Just a)

-----

data Val = MkVal
  { name   :: Name
  , rigid  :: Bool     -- no meta inside   -- forceAll may change it from False to True
  , closed :: Bool                         -- forceAll may change it from False to True if not rigid
  , view   :: View Val
  }
-- invariant:  name v == name w  ==>  view v == view w

-- TODO: assert that names are forced (with time)?
instance Eq Val where
  (==) = (==) `on` name
instance Ord Val where
  compare = compare `on` name

pattern Con :: Name -> Val
pattern Con i = MkVal i True True VCon

pattern Fun :: Name -> Val
pattern Fun i = MkVal i True True VFun

instance IsString Val where
  fromString = Con . fromString

vVar :: Name -> Val
vVar n = MkVal n True False VVar

vMeta :: Name -> Val
vMeta n = MkVal n False True VMeta

mkValue :: Name -> Bool -> Bool -> View Val -> RefM Val
mkValue n r c v = do
  n <- mkName $ nameStr n
  pure $ MkVal n r c v

vTm :: Name -> Tm -> Val -> RefM Val
vTm n t v = mkValue n (rigid v) (closed v) $ VTm t v

vApp :: Val -> Val -> RefM Val
vApp a_ u = do
  (aa, a) <- force' a_
  let def = mkApp aa u Nothing (metaDep a)
  case view a of
    VCon
      | MkName "Succ" _ <- name a -> force u >>= \fu -> case view fu of
        VCon | NNat t <- name fu -> pure $ Con $ NNat $ t + 1
        _          -> def
      | "dec" <- name a -> spine u >>= \(h, vs) -> case name h of
        NNat t -> pure $ Con $ NNat $ t - 1
        MkName "Succ" _ | [v] <- vs -> pure v
        _          -> def
      | "tail" <- name a -> spine u >>= \(h, vs) -> case name h of
        NString (_: t) -> pure $ Con $ NString t
        MkName "Cons" _ | [_, v] <- vs -> pure v
        _          -> def
      | "head" <- name a -> spine u >>= \(h, vs) -> case name h of
        NString (h: _) -> pure $ Con $ NString [h]
        MkName "Cons" _ | [v, _] <- vs -> pure v
        _          -> def
      | MkName "AppendStr" _ <- name a -> forcedSpine u >>= \case
        (h, [va, vb])
          | VCon <- view h, MkName "PairStr" _ <- name h
          , VCon <- view va, NString va <- name va
          , VCon <- view vb, NString vb <- name vb
                   -> pure $ Con $ NString $ va <> vb
        _          -> def
      | MkName "EqStr" _ <- name a -> forcedSpine u >>= \case
        (h, [va, vb])
          | VCon <- view h, MkName "PairStr" _ <- name h
          , VCon <- view va, NString va <- name va
          , VCon <- view vb, NString vb <- name vb
                   -> pure $ Con $ NNat $ if va == vb then 1 else 0
        _          -> def
    VSup c vs      -> evalCombinator c $ vs ++ [u]
    VFun           -> lookupRule (name a) >>= \f -> app_ aa f u
    VApp_ _ _ (Just f) _                         -> app_ aa f u
    _              -> def
 where
  app_ aa f u = vApp f u >>= \vv -> mkApp aa u (Just vv) Nothing

  mkApp aa u vv i = case vv of
    Just (view -> VRet x) -> pure x
    c -> mkValue "app" (rigid aa && rigid u) (closed aa && closed u) $ VApp_ aa u c i

tLazy :: Tm -> Tm
tLazy = tLam "_"

vEval :: Val -> RefM Val
vEval x = vApp x "()"


vApps :: Val -> [Val] -> RefM Val
vApps v [] = pure v
vApps v (a: as) = vApp v a >>= \x -> vApps x as

vSup :: Combinator -> [Val] -> RefM Val
vSup c vs = mkValue "lam" (all rigid vs) (all closed vs) $ VSup c vs

vLam_ :: Val -> Tm -> RefM Val
vLam_ n t = do
  let (c, ns) = mkCombinator (name n) t
  vSup c $ vVar <$> ns

vLam :: Val -> Val -> RefM Val
vLam n v = force v >>= \case
  fv | VApp a b <- view fv -> force b >>= \case
    b | VVar <- view b, b == n -> do
      ta <- quoteTm' a
      let (Lams vs _, _) = mkCombinator (name n) ta
      case last vs of
        "_" -> pure a
        _ -> def   -- TODO: optimize this
    _ -> def
  _ -> def
 where
  def = do
    t <- quoteTm' v
    vLam_ n t

vConst :: Val -> RefM Val
vConst v = do
  n <- mkName "_"
  vLam (vVar n) v


vLams [] x = pure x
vLams (v: vs) x = vLams vs x >>= vLam v

-----------

{-# noinline metaEnv #-}
metaEnv :: Ref (Map Name Val)
metaEnv = topRef mempty

lookupMeta :: Val -> RefM (Maybe Val)
lookupMeta x = readRef metaEnv <&> lookup (name x)

updateMeta :: Val -> Val -> RefM ()
updateMeta a b = modifyRef metaEnv $ insert (name a) b

showMetaEnv = readRef metaEnv >>= \m -> mapM (print . pprint) (assocs m) <&> mconcat

-----------

{-# noinline ruleEnv #-}
ruleEnv :: Ref (Map Name Val)
ruleEnv = topRef mempty

lookupRule :: Name -> RefM Val
lookupRule n = readRef ruleEnv <&> fromJust . lookup n

updateRule :: Name -> Val -> RefM ()
updateRule n b = modifyRef ruleEnv $ insert n b

addRule :: Tm -> Tm -> RefM ()
addRule lhs rhs = do
  (n, ns) <- ruleName [] lhs
  old <- lookupRule n
  new <- compileLHS (TVal old) ns lhs $ TRet rhs
  updateRule n =<< evalClosed new
  pure ()
 where
  ruleName ns = \case
    TVal v -> pure (name v, ns)
    TApp a b -> do
      n <- mkName $ case b of
        TVar m -> nameStr m
        _ -> "v"
      ruleName (n: ns) a
    _ -> undefined

  compileLHS :: Tm -> [Name] -> Tm -> Tm -> RefM Tm
  compileLHS old (n: ns) (TApp a b) rhs = do
    e <- compilePat (tLazy $ TApps old $ TVar <$> (reverse $ n: ns)) b (TVar n) $ pure rhs
    compileLHS old ns a (tLam n e)
  compileLHS _ _ (TVal Fun{}) rhs = pure rhs
  compileLHS _ _ _ _ = undefined

  compilePat f p e m = case p of
    TVar n -> TLet n e <$> m
    TView g p -> compilePat f p (TApp g e) m
    TApps (TVal c) ps | VCon <- view c -> do
      let len = length ps
      ns <- sequence $ replicate len $ mkName "w"   -- TODO: better naming
      x <- foldr (uncurry $ compilePat f) m $ zip ps $ map TVar ns
      pure $ case (name c, ns) of
        (MkName "Cons" _, [a, b])
          -> TMatch (name c) e (TLet a (TApp "head" e) $ TLet b (TApp "tail" e) $ tLazy x) f
        (MkName "Succ" _, [a])
          -> TMatch (name c) e (TLet a (TApp "dec" e) $ tLazy x) f
        _ -> TMatch (name c) e (foldr (\(i, n) y -> TLet n (TSel len i e) y) (tLazy x) $ zip [0..] ns) f
    TGen _ -> m   -- TODO?
    TVal v -> force v >>= \v -> case view v of
      _     -> undefined
    _ -> undefined

vRet v = mkValue "ret" (rigid v) (closed v) $ VRet v

vSel :: Int -> Int -> Val -> RefM Val
vSel i j v = spine v >>= \case
  (h, vs) | VCon <- view h, length vs == i -> pure $ vs !! j
  _ -> mkValue "sel" True True $ VSel i j v

vMatch :: Name -> Val -> Val -> Val -> RefM Val
vMatch n v ok fail = spine v >>= \case
  (h, _vs) | MkName "Succ" _ <- n, NNat i <- name h, i > 0 -> vEval ok
  (h, _vs) | MkName "Cons" _ <- n, NString (_:_) <- name h -> vEval ok
  (h, _vs) | VCon <- view h, name h == n          -> vEval ok
  (h, _vs) | VCon <- view h                       -> vEval fail
  (h, _) -> mkValue "match" True True $ VMatch n v ok fail $ metaDep h

metaDep v = case view v of
  VMeta -> Just v
  VApp_    _ _ _ m -> m
  VMatch _ _ _ _ m -> m
  _ -> Nothing

spine v_ = second reverse <$> f v_ where
  f v_ = force v_ >>= \v -> case view v of
    VApp_ a b Nothing Nothing -> f a <&> second (b:)
    _        -> pure (v, [])

forcedSpine v_ = second reverse <$> f v_ where
  f v_ = force v_ >>= \v -> case view v of
    VApp_ a b Nothing Nothing -> (\b t -> second (b:) t) <$> force b <*> f a
    _        -> pure (v, [])


-----------

force, force_ :: Val -> RefM Val

force_ v = case view v of
  VMeta -> look <&> fromMaybe v
  _ | Just i <- metaDep v -> lookupMeta i >>= \case
    Nothing -> pure v
    Just{} -> look >>= \case
      Just r -> pure r
      Nothing -> do
        r <- case view v of
          VApp a b -> vApp a b
          VMatch n a b c _ -> vMatch n a b c
          _ -> impossible
        updateMeta v r
        pure r
  _ -> pure v
 where
  look :: RefM (Maybe Val)
  look = lookupMeta v >>= \case
    Nothing -> pure Nothing
    Just w -> do
      w' <- force_ w
      updateMeta v w'
      pure $ Just w'

force' v = force_ v >>= \u -> case view u of
    VTm _ z -> f u z
    _ -> pure (u, u)
 where
  f w v = force_ v >>= \u -> case view u of
    VTm _ z -> f w z
    _ -> pure (w, u)

force v = force' v <&> snd


-------------

eval :: (Print a, Ord a) => Map a Val -> Tm_ a -> RefM Val
eval = eval_ pure pure vApp vSup notDefined vMatch vSel vRet

eval' :: Map Name Val -> Tm -> RefM Val
eval' = eval_ pure pure vApp vSup (pure . vVar) vMatch vSel vRet

evalClosed = eval mempty

quoteNF :: Val -> RefM Raw
quoteNF v_ = force v_ >>= \v ->
  case view v of
    VVar     -> pure $ RVar $ name v
    VCon     -> pure $ RVar $ name v
    VMeta    -> pure $ RVar $ name v
    VFun     -> lookupRule (name v) >>= quoteNF
    VApp_ t u _ _ -> (:@) <$> quoteNF t <*> quoteNF u
    VLam c -> do
      n <- fmap vVar c
      b <- vApp v n
      q <- quoteNF b
      pure $ Lam (name n) q
    VSel i j e -> rSel i j <$> quoteNF e
    VMatch n a b c _ -> rMatch n <$> quoteNF a <*> quoteNF b <*> quoteNF c
    VRet a -> rRet <$> quoteNF a
    _ -> impossible

rMatch n a b c = "match" :@ RVar n :@ a :@ b :@ c
rSel i j e = "sel" :@ RVar (NNat $ fromIntegral i) :@ RVar (NNat $ fromIntegral j) :@ e
rRet e = "return" :@ e

quoteNF' = quoteTm >=> tmToRaw

quoteTm, quoteTm' :: Val -> RefM Tm
quoteTm  = quoteTm_ True False
quoteTm' = quoteTm_ True True

quoteTm_ vtm opt v =
  quoteTm__ vtm opt v <&> \(vs, x) -> foldl (\t (n, v) -> TLet n v t) x vs

quoteTm__ vtm opt v_ = do
  v <- force__ v_
  (ma_, vs_) <- runWriter $ go v  -- writer is needed for the right order
  let
    ma v = fromJust $ lookup v ma_
    vs = filter ma vs_

    ff' = force__ >=> ff

    ff v | opt, closed v = pure $ TVal v
    ff v | ma v = pure $ TVar $ name v
    ff v = gg v

    gg v = case view v of
      VSup c vs -> TSup c <$> mapM ff' vs
      VApp a b -> TApp <$> ff' a <*> ff' b
      VTm t _ -> pure t
      VVar  -> pure $ TVar $ name v
      _ | opt -> impossible
      VCon  -> pure $ TVar $ name v
      VMeta -> pure $ TVal v -- $ TVar $ name v
      VFun  -> lookupRule (name v) >>= gg
      VSel i j e -> TSel i j <$> ff' e
      VMatch n a b c _ -> TMatch n <$> ff' a <*> ff' b <*> ff' c
      VRet a -> TRet <$> ff' a
      _ -> impossible

  x <- ff v
  vs' <- mapM gg vs
  pure (zip (name <$> vs) vs', x)
 where
  force__ = if vtm then force_ else force

  go v wst = walk ch share up [v]
   where
    share v _ = case view v of
       _ | opt, closed v -> pure False
       VMeta -> pure False
       VVar  -> pure False
       VCon  -> pure False
       _ -> pure True

    up v sh _ = tell wst [v] >> pure sh

    ch v = fmap ((,) False) $ mapM force__ $ case view v of
      _ | opt, closed v -> []
      VSup _ vs -> vs
      VApp a b -> [a, b]
      _ -> []


-----------------------

instance Print Val where
  print v = quoteNF' v >>= print

-- TODO
instance PPrint Val where
  pprint a = pprint $ name a

