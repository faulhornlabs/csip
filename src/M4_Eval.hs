module M4_Eval
  ( Combinator, varName

  , Tm_ (TGen, TVar, TApp, TApps, TLet, TVal, TView)
  , Tm, tLam, tMeta
  , Raw

  , Val (Con, Fun, Fun_, WSup, WLam, WApp, WMeta, WMetaApp_, WMetaApp, WVar, WCon, WFun, WTm, Delta), vNat, vString
  , vVar, vApp, vApps, vSup, vMeta, vTm, vLam, vLams, vConst, isConst
  , mkCon, RuleRef
  , name, rigid, closed
  , lamName
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
  { dbIndex :: Int
  , dbName  :: NameStr
  }

instance Print  DB where print  = print  . dbName
instance PPrint DB where pprint = pprint . dbName
instance Eq  DB where (==)    = (==)    `on` dbIndex
instance Ord DB where compare = compare `on` dbIndex

-------------

-- supercombinator (closed)       -- \x1 ... xN -> t
data Combinator = MkCombinator
  { combName   :: Name
  , rigidCombinator :: Bool
  , _combNames :: [NameStr]                  -- x1 ... xN
  , _combBody  :: (Tm_ DB)                   -- t
  }

instance Eq  Combinator where (==)    = (==)    `on` combName
instance Ord Combinator where compare = compare `on` combName

evalCombinator :: Combinator -> [Val] -> RefM Val
evalCombinator (MkCombinator _ _ ns t) vs = eval (fromList $ zip (zipWith MkDB [0..] ns) vs) t

evalCombinatorTm :: Combinator -> [Tm] -> RefM Tm
evalCombinatorTm (MkCombinator _ _ ns t) vs = evalTm (fromList $ zip (zipWith MkDB [0..] ns) vs) t

mkCombinator :: Name -> Tm_ Name -> RefM (Combinator, [Name])
mkCombinator n t = do
  n <- mkName "c"
  pure (MkCombinator n (rigidTm t') (map nameStr nsA) t', ns_)
 where

  t' = f (fromList $ zip nsA [0..]) t

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
  pprint (MkCombinator _ _ ns t) = "|->" :@ foldl1 (:@) (map pprint ns) :@ pprint t

varName (MkCombinator _ _ ns _) = mkName $ case last ns of
  "_" -> "v"{-TODO?-}
  n -> n

lamName n x = force x >>= \case
  WLam n -> n
  _ -> pure n

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
 deriving (Eq, Ord)

instance PPrint a => PPrint (Tm_ a) where
  pprint = \case
    TVar n -> pprint n
    TApp a b -> "@" :@ pprint a :@ pprint b
    TSup c ts -> foldl (:@) (pprint c) $ map pprint ts
    TLet n a b -> zVar ["=",";"] :@ pprint n :@ pprint a :@ pprint b
    TVal v -> zVar ["{","}"] :@ pprint v
    _ -> undefined

-------------

type Tm = Tm_ Name

type Raw = Raw_ (Tm, Val)

pattern TView :: Tm -> Tm -> Tm
pattern TView a b = TApp (TApp (TVal (Con "View")) a) b

getTApps (TApp (getTApps -> (a, es)) e) = (a, e: es)
getTApps e = (e, [])

pattern TApps :: Tm_ a -> [Tm_ a] -> Tm_ a
pattern TApps e es <- (getTApps -> (e, reverse -> es))
  where TApps e es = foldl TApp e es

tLam :: Name -> Tm -> RefM Tm
tLam n t = do
  (c, ns') <- mkCombinator n t
  pure $ TSup c $ TVar <$> ns'

tMeta :: RefM Tm
tMeta = mkName' "m" <&> TVal . vMeta

instance IsString Tm where
  fromString = TVal . fromString

rigidTm :: Tm_ a -> Bool
rigidTm = f where
  f = \case
    TGen e -> f e
    TVar{} -> True
    TVal v -> rigid v
    TApp a b -> f a && f b
    TLet _ a b -> f a && f b
    TSup c ts -> rigidCombinator c && all f ts
    TMatch _ a b c -> f a && f b && f c
    TSel _ _ e -> f e
    TRet e -> f e

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
        TVal v_ -> force_ v_ >>= \case
           WNat n-> pure (RVar $ NNat n)
           WString n -> pure (RVar $ NString n)
           v@WCon -> pure (RVar $ name v)
           Delta n -> pure (RVar n)
           v -> tell wst (mempty, singleton (name v) v) >> pure (RVar $ name v)
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

data View
  = VCon   -- constructor | bound variable | metavar
  | VFun RuleRef   -- function
  | VDelta (Val -> RefM Val -> RefM Val) -- builtin function
  | VApp_ Val Val AppKind
  | VSup Combinator [Val]     -- lambda
  | VSel Int Int Val       -- Sel appears only behind the "then" branch of Match       -- meta dependency needed?
  | VMatch Name Val Val Val (Maybe Val){-meta dependency-}
  | VRet Val
  | VNat Integer
  | VString String
  | VTm Tm Val

data AppKind
  = NeutralApp Val{-meta dependency-}    -- volatile App depending on a meta
  | FunApp Val{-accumulated result-}
  | ConApp
--  | DeltaApp Int{-missing arguments-}

pattern WNat n <- (view -> VNat n)
pattern WString n <- (view -> VString n)
pattern WCon <- Con _
pattern WVar <- WVar_ _
pattern WFun <- Fun _
pattern WMeta <- WMeta_ _
pattern WSup a b <- (view -> VSup a b)
pattern WTm a b <- (view -> VTm a b)
pattern WSel a b c <- (view -> VSel a b c)
pattern WMatch a b c d e <- (view -> VMatch a b c d e)
pattern WRet n <- (view -> VRet n)
pattern WApp a b <- (view -> VApp_ a b _)
pattern WFunApp a b c <- (view -> VApp_ a b (FunApp c))
pattern WConApp a b <- (view -> VApp_ a b ConApp)
pattern WMetaApp_ a b c <- (view -> VApp_ a b (NeutralApp c))
pattern WMetaApp a <- WMetaApp_ _ _ a
pattern WLam n <- WSup (varName -> n) _



-----

data Val = MkVal
  { name   :: Name
  , rigid  :: Bool     -- no meta inside   -- forceAll may change it from False to True
  , closed :: Bool                         -- forceAll may change it from False to True if not rigid
  , view   :: View
  }
-- invariant:  name v == name w  ==>  view v == view w

-- TODO: assert that names are forced (with time)?
instance Eq Val where
  (==) = (==) `on` name
instance Ord Val where
  compare = compare `on` name

pattern Con i = MkVal i True True VCon

pattern WDelta i f = MkVal i True True (VDelta f)
pattern Delta i <- WDelta i _

vNat :: Integer -> RefM Val
vNat i = mkName "i" <&> \n -> MkVal n True True $ VNat i

vString :: String -> RefM Val
vString i = mkName "i" <&> \n -> MkVal n True True $ VString i

pattern Fun_ i f = MkVal i True True (VFun f)
pattern Fun i <- Fun_ i _

instance IsString Val where
  fromString = Con . fromString

vVar :: Name -> Val
vVar = WVar_

pattern WVar_ n = MkVal n True False VCon

vMeta :: Name -> Val
vMeta = WMeta_

pattern WMeta_ n = MkVal n False True VCon

mkValue :: Name -> Bool -> Bool -> View -> RefM Val
mkValue n r c v = do
  n <- mkName $ nameStr n
  pure $ MkVal n r c v

vTm :: Name -> Tm -> Val -> RefM Val
vTm n t v = mkValue n (rigid v) (closed v) $ VTm t v

mkCon :: Name -> Val
mkCon n = case n of
  "AppendStr" -> f \u def -> forcedSpine u >>= \case
        ("PairStr", [WString va, WString vb])
                   -> vString $ va <> vb
        _          -> def
  "dec" -> f \u def -> forcedSpine u >>= \case
        (WNat t, []) -> vNat $ t - 1
        ("Succ", [v]) -> pure v
        _          -> def
  "tail" -> f \u def -> forcedSpine u >>= \case
        (WString (_: t), []) -> vString t
        ("Cons", [_, v]) -> pure v
        _          -> def
  "head" -> f \u def -> forcedSpine u >>= \case
        (WString (h: _), []) -> vString [h]
        ("Cons", [v, _]) -> pure v
        _          -> def
  "EqStr" -> f \u def -> forcedSpine u >>= \case
        ("PairStr", [WString va, WString vb])
                   -> vNat $ if va == vb then 1 else 0
        _          -> def
  "EqNat" -> f \u def -> forcedSpine u >>= \case
        ("PairNat", [WNat va, WNat vb])
                   -> vNat $ if va == vb then 1 else 0
        _          -> def
  n -> Con n
 where
  f g = WDelta n g

vApp :: Val -> Val -> RefM Val
vApp a_ u = do
  (aa, a) <- force' a_
  let def = mkApp aa u Nothing (metaDep a)
  case a of
    WCon  -- TODO: elim
      | "Succ" <- name a -> force u >>= \case
        WNat t -> vNat $ t + 1
        _          -> def
    WDelta _ g     -> g u def
    WSup c vs      -> evalCombinator c $ vs ++ [u]
    Fun_ n r       -> lookupRule n r >>= \f -> app_ aa f u
    WFunApp _ _ f  -> app_ aa f u
    _              -> def
 where
  app_ aa f u = vApp f u >>= \vv -> mkApp aa u (Just vv) Nothing

  mkApp aa u vv i = case vv of
    Just (WRet x) -> pure x
    c -> mkValue "app" (rigid aa && rigid u) (closed aa && closed u) $ VApp_ aa u $ case (c, i) of
      (Just x,  Nothing) -> FunApp     x
      (Nothing, Just x)  -> NeutralApp x
      (Nothing, Nothing) -> ConApp
      _ -> impossible

tLazy :: Tm -> RefM Tm
tLazy = tLam "_"

vEval :: Val -> RefM Val
vEval x = vApp x "X"


vApps :: Val -> [Val] -> RefM Val
vApps v [] = pure v
vApps v (a: as) = vApp v a >>= \x -> vApps x as

vSup :: Combinator -> [Val] -> RefM Val
vSup c vs = mkValue "lam" (rigidCombinator c && all rigid vs) (all closed vs) $ VSup c vs

vLam_ :: Val -> Tm -> RefM Val
vLam_ n t = do
  (c, ns) <- mkCombinator (name n) t
  vSup c $ vVar <$> ns

vLam :: Val -> Val -> RefM Val
vLam n v = force v >>= \case
  WApp a b -> force b >>= \case
    b@WVar | b == n -> do
      ta <- quoteTm' a
      (c, _) <- mkCombinator (name n) ta
      if isConstComb c
        then pure a
        else def   -- TODO: optimize this
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

isConstComb (MkCombinator _ _ vs _) = last vs == "_"

isConst :: Val -> Bool
isConst = \case
  WTm _ v -> isConst v
  WSup c _ -> isConstComb c
  _ -> False

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

type RuleRef = Ref Val

lookupRule :: Name -> RuleRef -> RefM Val
lookupRule _n r = readRef r

updateRule :: Name -> RuleRef -> Val -> RefM ()
updateRule _n r b = writeRef r b

addRule :: [Name] -> Tm -> Tm -> RefM ()
addRule (fromListSet -> boundvars) lhs_ rhs_ = do
  (lhs, rhs) <- trRule boundvars (lhs_, rhs_)
  (n, r, ns) <- ruleName [] lhs
  old <- lookupRule n r
  new <- compileLHS (TVal old) ns lhs . TRet =<< {-metaToVarTm-} pure rhs
  updateRule n r =<< evalClosed new
  pure ()
 where
  ruleName ns = \case
    TVal (Fun_ n r) -> pure (n, r, ns)
    TApp a b -> do
      n <- mkName $ case b of
        TVar m -> nameStr m
        _ -> "v"
      ruleName (n: ns) a
    _ -> undefined

  compileLHS :: Tm -> [Name] -> Tm -> Tm -> RefM Tm
  compileLHS old (n: ns) (TApp a b) rhs = do
    tx <- tLazy $ TApps old $ TVar <$> (reverse $ n: ns)
    e <- compilePat (boundvars <> fromListSet (n: ns)) tx b (TVar n) $ pure rhs
    compileLHS old ns a =<< tLam n e
  compileLHS _ [] (TVal Fun{}) rhs = pure rhs
  compileLHS _ _ _ _ = undefined

  compilePat bv f p e m = case p of
    TVar n -> TLet n e <$> m
    TView g p -> compilePat bv f p (TApp g e) m
    TApps (TVal (getCon -> Just c)) ps -> do
      let len = length ps
      ns <- sequence $ replicate len $ mkName "w"   -- TODO: better naming
      x <- foldr (uncurry $ compilePat bv f) m $ zip ps $ map TVar ns
      tx <- tLazy x
      pure $ case (c, ns) of
        ("Cons", [a, b])
          -> TMatch c e (TLet a (TApp (TVal $ mkCon "head") e) $ TLet b (TApp (TVal $ mkCon "tail") e) tx) f
        ("Succ", [a])
          -> TMatch c e (TLet a (TApp (TVal $ mkCon "dec") e) tx) f
        _ -> TMatch c e (foldr (\(i, n) y -> TLet n (TSel len i e) y) tx $ zip [0..] ns) f
    _ -> impossible

getCon (Con c) = Just c
getCon (WNat n) = Just $ NNat n
getCon (WString n) = Just $ NString n
getCon _ = Nothing

vRet v = mkValue "ret" (rigid v) (closed v) $ VRet v

vSel :: Int -> Int -> Val -> RefM Val
vSel i j v = spine v >>= \case
  (WCon, vs) | length vs == i -> pure $ vs !! j
  _ -> mkValue "sel" (rigid v) (closed v) $ VSel i j v

vMatch :: Name -> Val -> Val -> Val -> RefM Val
vMatch n v ok fail = spine v >>= \case
  (WNat i, _vs) | "Succ" <- n, i > 0 -> vEval ok
  (WNat i, _vs) | NNat i == n        -> vEval ok
  (WNat{}, _vs)                     -> vEval fail
  (WString i, _vs) | NString i == n  -> vEval ok
  (WString (_:_), _vs) | "Cons" <- n -> vEval ok
  (WString{}, _vs)                  -> vEval fail
  (h@WCon, _vs) | name h == n          -> vEval ok
  (WCon, _vs)                       -> vEval fail
  (h, _) -> mkValue "match" (rigid v && rigid ok && rigid fail) (closed v && closed ok && closed fail) $ VMatch n v ok fail $ metaDep h

metaDep = \case
  v@WMeta -> Just v
  WMetaApp m -> Just m
  WMatch _ _ _ _ m -> m
  _ -> Nothing

spine v_ = second reverse <$> f v_ where
  f v_ = force v_ >>= \case
    WConApp a b -> f a <&> second (b:)
    v        -> pure (v, [])

forcedSpine v_ = second reverse <$> f v_ where
  f v_ = force v_ >>= \case
    WConApp a b -> (\b t -> second (b:) t) <$> force b <*> f a
    v        -> pure (v, [])


-----------

force, force_ :: Val -> RefM Val

force_ v = case v of
  WMeta -> look <&> fromMaybe v
  _ | Just i <- metaDep v -> lookupMeta i >>= \case
    Nothing -> pure v
    Just{} -> look >>= \case
      Just r -> pure r
      Nothing -> do
        r <- case v of
          WApp a b -> vApp a b
          WMatch n a b c _ -> vMatch n a b c
          _ -> impossible
        updateMeta v r
        pure r
  _ -> pure v
 where
  look :: RefM (Maybe Val)
  look = lookupMeta v >>= \case
    Nothing -> pure Nothing
    Just w_ -> do
      w <- force_ w_
      updateMeta v w
      pure $ Just w

force' v_ = force_ v_ >>= \case
    v@(WTm _ z) -> f v z
    v -> pure (v, v)
 where
  f w v_ = force_ v_ >>= \case
    WTm _ z -> f w z
    v -> pure (w, v)

force v = force' v <&> snd


-------------

eval :: (Print a, Ord a) => Map a Val -> Tm_ a -> RefM Val
eval = eval_ pure pure vApp vSup notDefined vMatch vSel vRet

eval' :: Map Name Val -> Tm -> RefM Val
eval' = eval_ pure pure vApp vSup (pure . vVar) vMatch vSel vRet

evalClosed = eval mempty

quoteNF :: Val -> RefM Raw
quoteNF v_ = force v_ >>= \case
  WNat n   -> pure $ RVar $ NNat n
  WString n-> pure $ RVar $ NString n
  Delta n    -> pure $ RVar $ n
  v@WCon     -> pure $ RVar $ name v
  v@WVar     -> pure $ RVar $ name v
  v@WMeta    -> pure $ RVar $ name v
  Fun_ n r   -> lookupRule n r >>= quoteNF
  WSel i j e -> rSel i j <$> quoteNF e
  WMatch n a b c _ -> rMatch n <$> quoteNF a <*> quoteNF b <*> quoteNF c
  WRet a -> rRet <$> quoteNF a
  WApp t u -> (:@) <$> quoteNF t <*> quoteNF u
  v@(WLam c) -> do
      n <- fmap vVar c
      b <- vApp v n
      q <- quoteNF b
      pure $ Lam (name n) q
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

    gg v = case v of
      WSup c vs -> TSup c <$> mapM ff' vs
      WApp a b -> TApp <$> ff' a <*> ff' b
      WTm t _ -> pure t
      WVar  -> pure $ TVar $ name v
      _ | opt -> impossible
      Delta n  -> pure $ TVar n
      WCon  -> pure $ TVar $ name v
      WMeta -> pure $ TVal v -- $ TVar $ name v
      Fun_ n r  -> lookupRule n r >>= gg
      WSel i j e -> TSel i j <$> ff' e
      WMatch n a b c _ -> TMatch n <$> ff' a <*> ff' b <*> ff' c
      WRet a -> TRet <$> ff' a
      _ -> impossible

  x <- ff v
  vs' <- mapM gg vs
  pure (zip (name <$> vs) vs', x)
 where
  force__ = if vtm then force_ else force

  go v wst = walk ch share up [v]
   where
    share v _ = case v of
       _ | opt, closed v -> pure False
       WMeta -> pure False
       WVar  -> pure False
       Delta{}  -> pure False
       WCon  -> pure False
       _ -> pure True

    up v sh _ = tell wst [v] >> pure sh

    ch v = fmap ((,) False) $ mapM force__ $ case v of
      _ | opt, closed v -> []
      WSup _ vs -> vs
      WApp a b -> [a, b]
      _ -> []

-- replace generated terms
trRule :: Set Name -> (Tm, Tm) -> RefM (Tm, Tm)
trRule bv (lhs, rhs) = runReader bv \rst -> fst <$> runState mempty \st -> do
    lhs' <- getGens True rst st lhs
    rhs' <- getGens False rst st rhs
    pure (lhs', rhs')
 where
  getGens :: Bool -> Reader (Set Name) -> State (Map Tm Tm) -> Tm -> RefM Tm
  getGens get rst st t = f t
   where
    eval' t = asks rst id >>= \bv -> eval (fromList [(n, vVar n) | n <- toList bv]) t

    f t = case t of
      TVal{} -> pure t
      TVar{} -> pure t
      TApp a b -> TApp <$> f a <*> f b
      TGen t -> eval' t >>= metaToVar >>= \ns ->
        if get
          then mkName "w" >>= \n -> modify st (insert ns $ TVar n) >> pure (TVar n)
          else gets st \m -> fromMaybe (TGen t) $ lookup ns m
      TLet n a b -> TLet n <$> f a <*> local rst (insertSet n) (f b)
      TSup c ts | rigidCombinator c  -> TSup c <$> mapM f ts
      TSup c ts  -> do 
          n <- varName c
          t <- evalCombinatorTm c $ ts <> [TVar n]
          tLam n =<< local rst (insertSet n) (f t)
      t -> error' $ ("TODO(8): " <>) <$> print t

metaToVar :: Val -> RefM Tm
metaToVar v_ = force v_ >>= \w -> case w of
  _ | rigid w -> pure $ TVal w
  WMeta    -> pure $ TVar $ name w
  WApp a b -> TApp <$> metaToVar a <*> metaToVar b
  WSup c vs | rigidCombinator c -> TSup c <$> mapM metaToVar vs
  WSup c vs -> do
          n <- varName c
          t <- evalCombinator c $ vs <> [vVar n]
          tLam n =<< metaToVar t
  w -> error' $ ("TODO(1): " <>) <$> print w
{-
-- TODO: preserve sharing?
metaToVarTm :: Tm -> RefM Tm
metaToVarTm = f where
  f t = case t of
    TVal v     -> metaToVar v
    TGen x     -> TGen <$> f x
    TVar{}     -> pure t
    TApp t u   -> TApp <$> f t <*> f u
    TSup c ts | rigidCombinator c  -> TSup c <$> mapM f ts
    TSup c ts  -> do
          n <- varName c
          t <- evalCombinatorTm c $ ts <> [TVar n]
          tLam n =<< f t
    TLet x t u -> TLet x <$> f t <*> f u
    w -> error' $ ("TODO(2): " <>) <$> print w
-}

-----------------------

instance Print Val where
  print v = quoteNF' v >>= print

-- TODO
instance PPrint Val where
  pprint = \case
    WNat n -> pprint $ NNat n
    WString n -> pprint $ NString n
    a -> pprint $ name a

