module M4_Eval
  ( Combinator, varName

  , Tm_ (TGen, TVar, TApp, TApps, TLet, TVal, TView, TGuard)
  , Tm, tLam, tMeta
  , Raw

  , Val (WSup, WLam, WApp, WMeta, WMetaApp_, WMetaApp, WVar, WCon, WFun, WTm, WDelta)
  , vNat, vString, vFun, vCon, vVar, vApp, vApps, vSup, vTm, vLam, vLams, vConst, isConst
  , mkCon, RuleRef
  , name, rigid, closed
  , lamName
  , force_, force', force

  , eval, evalClosed      -- Tm  -> Val
  , quoteTm'   -- Val -> Tm
  , quoteNF   -- Val -> Raw
  , quoteNF'

  , updateRule
  , addRule

  , spine, forcedSpine
  , Embedded (MkEmbedded)
  , MetaRef, MetaDep(..)
  , updateMeta

  , pattern CFail, lookupDictFun, superClassesFun
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
    TGen n -> "Gen" :@ pprint n
    _ -> undefined

-------------

type Tm = Tm_ Name

pattern TView :: Tm -> Tm -> Tm
pattern TView a b = TApp (TApp (TVal (WCon "View")) a) b

pattern TGuard :: Tm -> Tm -> Tm
pattern TGuard a b = TApp (TApp (TVal (WCon "Guard")) a) b

getTApps (TApp (getTApps -> (a, es)) e) = (a, e: es)
getTApps e = (e, [])

pattern TApps :: Tm_ a -> [Tm_ a] -> Tm_ a
pattern TApps e es <- (getTApps -> (e, reverse -> es))
  where TApps e es = foldl TApp e es

tLam :: Name -> Tm -> RefM Tm
tLam n t = do
  (c, ns') <- mkCombinator n t
  pure $ TSup c $ TVar <$> ns'

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
           WCon n -> pure (RVar n)
           v@WDelta{} -> pure (RVar $ name v)
           WFun_ n r -> lookupRule r >>= \v -> tell wst (mempty, singleton n v) >> pure (RVar n)
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

data Embedded = MkEmbedded Tm Val

instance PPrint Embedded where
  pprint (MkEmbedded r _) = zVar ["[","]"] :@ pprint r

type Raw = Raw_ Embedded

-------------------------------

data View
  = VCon (Maybe Val){-type-}
  | VVar
  | VMeta MetaRef
  | VFun RuleRef   -- function
  | VDelta Int{-arity-} (RefM Val -> [Val] -> RefM Val) -- builtin function
  | VApp_ Val Val AppKind
  | VSup Combinator [Val]     -- lambda
  | VSel Int Int Val       -- Sel appears only behind the "then" branch of Match       -- meta dependency needed?
  | VMatch Name Val Val Val (Maybe (MetaRef, MetaDep))
  | VRet Val
  | VNat Integer
  | VString String
  | VTm Tm Val

data AppKind
  = NeutralApp MetaRef MetaDep    -- volatile App depending on a meta
  | FunApp Val{-accumulated result-}
  | ConApp
  | DeltaApp Int{-remaining arity-}

-----------

pattern WNat n <- (view -> VNat n)
pattern WString n <- (view -> VString n)
pattern WVar <- (view -> VVar)
pattern WMeta_ r <- (view -> VMeta r)
pattern WSup a b <- (view -> VSup a b)
pattern WTm a b <- (view -> VTm a b)
pattern WSel a b c <- (view -> VSel a b c)
pattern WMatch a b c d e <- (view -> VMatch a b c d e)
pattern WRet n <- (view -> VRet n)
pattern WApp a b <- (view -> VApp_ a b _)
pattern WFunApp a b c <- (view -> VApp_ a b (FunApp c))
pattern WConApp a b <- (view -> VApp_ a b ConApp)
pattern WDeltaApp a b ar <- (view -> VApp_ a b (DeltaApp ar))
pattern WMetaApp_ a b c d <- (view -> VApp_ a b (NeutralApp c d))
pattern WMetaApp a b <- WMetaApp_ a b _ _
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

vCon n t = MkVal n True True $ VCon t

pattern WCon n <- MkVal n _    _    (VCon _)
  where WCon n =  MkVal n True True (VCon Nothing)

pattern WDelta i ar f <- MkVal i _    _    (VDelta ar f)
  where WDelta i ar f =  MkVal i True True (VDelta ar f)

vNat :: Integer -> RefM Val
vNat i = mkName "i" <&> \n -> MkVal n True True $ VNat i

vString :: String -> RefM Val
vString i = mkName "i" <&> \n -> MkVal n True True $ VString i

pattern WFun_ i f <- MkVal i _    _    (VFun f)
  where WFun_ i f =  MkVal i True True (VFun f)
pattern WFun i <- WFun_ i _

vFun :: Name -> Val -> RefM Val
vFun i f = do
  r <- newRef f
  pure $ WFun_ i r

instance IsString Val where
  fromString s = vCon (fromString s) Nothing

vVar :: Name -> Val
vVar n = MkVal n True False VVar

-----------

newtype MetaRef = MkMetaRef (Ref (Maybe Val))

mkMetaRef = MkMetaRef <$> newRef Nothing

lookupMeta :: MetaRef -> RefM (Maybe Val)
lookupMeta (MkMetaRef r) = readRef r

updateMeta :: MetaRef -> Val -> RefM ()
updateMeta (MkMetaRef r) b = writeRef r $ Just b

data MetaDep = MkMetaDep {metaDepName :: Name, metaRef :: MetaRef}

instance Print MetaDep where print = print . metaDepName
instance Eq MetaDep where (==) = (==) `on` metaDepName
instance Ord MetaDep where compare = compare `on` metaDepName

tMeta :: RefM Tm
tMeta = do
  n <- mkName' "m"
  TVal . MkVal n False True . VMeta <$> mkMetaRef

pattern WMeta d <- (mkMetaDep -> Just d)

mkMetaDep v@(WMeta_ r) = Just (MkMetaDep (name v) r)
mkMetaDep _ = Nothing

-----------

mkValue :: Name -> Bool -> Bool -> View -> RefM Val
mkValue n r c v = do
  n <- mkName $ nameStr n
  pure $ MkVal n r c v

vTm :: Name -> Tm -> Val -> RefM Val
vTm n t v = mkValue n (rigid v) (closed v) $ VTm t v

mkCon :: Name -> Maybe Val -> Val
mkCon n ty = case n of
  "AppendStr" -> f 2 \_ -> \case [WString va, WString vb] -> vString $ va <> vb; _ -> impossible
  "EqStr"     -> f 2 \_ -> \case [WString va, WString vb] -> if va == vb then "True" else "False"; _ -> impossible
  "AddNat"    -> f 2 \_ -> \case [WNat    va, WNat    vb] -> vNat $ va + vb; _ -> impossible
  "MulNat"    -> f 2 \_ -> \case [WNat    va, WNat    vb] -> vNat $ va * vb; _ -> impossible
  "DivNat"    -> f 2 \_ -> \case [WNat    va, WNat    vb] -> vNat $ va `div` vb; _ -> impossible
  "ModNat"    -> f 2 \_ -> \case [WNat    va, WNat    vb] -> vNat $ va `mod` vb; _ -> impossible
  "EqNat"     -> f 2 \_ -> \case [WNat    va, WNat    vb] -> if va == vb then "True" else "False"; _ -> impossible
  "dec" -> f 1 \def -> \case
      [u] -> forcedSpine u >>= \case
        (WNat t, []) -> vNat $ t - 1
        ("Succ", [v]) -> pure v
        _          -> def
      _ -> impossible
  "tail" -> f 1 \def -> \case
      [u] -> forcedSpine u >>= \case
        (WString (_: t), []) -> vString t
        ("Cons", [_, v]) -> pure v
        _          -> def
      _ -> impossible
  "head" -> f 1 \def -> \case
      [u] -> forcedSpine u >>= \case
        (WString (h: _), []) -> vString [h]
        ("Cons", [v, _]) -> pure v
        _          -> def
      _ -> impossible
  n -> vCon n ty
 where
  f ar g = WDelta n ar g

evalDelta (WDeltaApp a v _) u def = evalDelta a (v: u) def
evalDelta (WDelta _ _ g) u def = g def u
evalDelta _ _ _ = impossible

vApp :: Val -> Val -> RefM Val
vApp a_ u = do
  (aa, a) <- force' a_
  let def = mkApp aa u $ snd <$> metaDep a
      def2 ar u
        | closed u, rigid u = mkValue "app" (rigid a && rigid u) (closed a && closed u) $ VApp_ a u $ DeltaApp (ar - 1)
        | otherwise         = def
      def3 = force u >>= \case
         u | True {- closed u, rigid u -} -> evalDelta a [u] def
--           | otherwise -> def
  case a of
    WCon{}  -- TODO: elim
      | "Succ" <- name a -> force u >>= \case
        WNat t -> vNat $ t + 1
        _          -> def
    WDelta _ ar _
      | ar < 1     -> impossible
      | ar > 1     -> force u >>= \u -> def2 ar u
      | closed a, rigid a -> def3
      | otherwise  -> def
    WDeltaApp _ _ ar
      | ar < 1     -> impossible
      | ar > 1     -> force u >>= \u -> def2 ar u
      | closed a, rigid a -> def3
      | otherwise  -> def
    WSup c vs      -> evalCombinator c $ vs ++ [u]
    WFun_ _ r      -> lookupRule r >>= \f -> app_ aa f u
    WFunApp _ _ f  -> app_ aa f u
    _              -> def
 where
  app_ aa f u = vApp f u >>= \case
    WRet x -> pure x
    x -> mkValue "app" (rigid aa && rigid u) (closed aa && closed u) $ VApp_ aa u $ FunApp x

  mkApp aa u i = do
    ad <- case i of
      Just x  -> NeutralApp <$> mkMetaRef <*> pure x
      Nothing -> pure $ ConApp
    mkValue "app" (rigid aa && rigid u) (closed aa && closed u) $ VApp_ aa u ad

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

type RuleRef = Ref Val

lookupRule :: RuleRef -> RefM Val
lookupRule r = readRef r

updateRule :: RuleRef -> Val -> RefM ()
updateRule r b = writeRef r b

addRule :: [Name] -> Tm -> Tm -> RefM ()
addRule (fromListSet -> boundvars) lhs_ rhs_ = do
  (lhs, rhs) <- trRule boundvars (lhs_, rhs_)
  (r, ns) <- ruleName [] lhs
  old <- lookupRule r
  new <- compileLHS (TVal old) ns lhs . TRet =<< {-metaToVarTm-} pure rhs
  updateRule r =<< evalClosed new
  pure ()
 where
  ruleName :: [Name] -> Tm -> RefM (RuleRef, [Name])
  ruleName ns = \case
    TVal (WFun_ _ r) -> pure (r, reverse ns)
    TGuard a _ -> ruleName ns a
    TApp a b -> do
      n <- mkName $ case b of
        TVar m -> nameStr m
        _ -> "v"
      ruleName (n: ns) a
    t -> error' $ ("TODO (11): " <>) <$> print t

  compileLHS :: Tm -> [Name] -> Tm -> Tm -> RefM Tm
  compileLHS old ns (TGuard a e) rhs = do
    tx <- tLazy $ TApps old $ TVar <$> reverse ns
    e <- compilePat (boundvars <> fromListSet ns) tx (TVal $ vCon "True" $ Just "Bool") e $ pure rhs
    compileLHS old ns a e
  compileLHS old (n: ns) (TApp a b) rhs = do
    tx <- tLazy $ TApps old $ TVar <$> reverse (n: ns)
    e <- compilePat (boundvars <> fromListSet (n: ns)) tx b (TVar n) $ pure rhs
    compileLHS old ns a =<< tLam n e
  compileLHS _ [] (TVal WFun{}) rhs = pure rhs
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
          -> TMatch c e (TLet a (TApp (TVal $ mkCon "head" Nothing) e) $ TLet b (TApp (TVal $ mkCon "tail" Nothing) e) tx) f
        ("Succ", [a])
          -> TMatch c e (TLet a (TApp (TVal $ mkCon "dec" Nothing) e) tx) f
        _ -> TMatch c e (foldr (\(i, n) y -> TLet n (TSel len i e) y) tx $ zip [0..] ns) f
    _ -> impossible

getCon (WCon n) = Just n
getCon (WNat n) = Just $ NNat n
getCon (WString n) = Just $ NString n
getCon _ = Nothing

vRet v = mkValue "ret" (rigid v) (closed v) $ VRet v

vSel :: Int -> Int -> Val -> RefM Val
vSel i j v = spine v >>= \case
  (WCon{}, vs) | length vs == i -> pure $ vs !! j
  _ -> mkValue "sel" (rigid v) (closed v) $ VSel i j v

vMatch :: Name -> Val -> Val -> Val -> RefM Val
vMatch n v ok fail = spine v >>= \case
  (WNat i, _vs) | "Succ" <- n, i > 0 -> vEval ok
  (WNat i, _vs) | NNat i == n        -> vEval ok
  (WNat{}, _vs)                     -> vEval fail
  (WString i, _vs) | NString i == n  -> vEval ok
  (WString (_:_), _vs) | "Cons" <- n -> vEval ok
  (WString{}, _vs)                  -> vEval fail
  (WCon c, _vs) | c == n           -> vEval ok
  (WCon{}, _vs)                    -> vEval fail
  (h, _) -> do
    dep <- case snd <$> metaDep h of
      Nothing -> pure Nothing
      Just d  -> do
        r <- mkMetaRef
        pure $ Just (r, d)
    mkValue "match" (rigid v && rigid ok && rigid fail) (closed v && closed ok && closed fail) $ VMatch n v ok fail dep

metaDep :: Val -> Maybe (MetaRef, MetaDep)
metaDep = \case
  WMeta m -> Just (metaRef m, m)
  WMetaApp_ _ _ r m -> Just (r, m)
  WMatch _ _ _ _ rm -> rm
  _ -> Nothing

-----------

spine v_ = force v_ >>= \v -> second reverse <$> f v where
  f = \case
    WConApp a b -> f a <&> second (b:)
    v        -> pure (v, [])

forcedSpine v_ = force v_ >>= \v -> second reverse <$> f v where
  f = \case
    WConApp a b -> (\b t -> second (b:) t) <$> force b <*> f a
    v        -> pure (v, [])

force, force_ :: Val -> RefM Val
force_ v = force__ v pure

force__ v changed = case v of
  WMeta_ ref -> lookupMeta ref >>= \case
    Nothing -> pure v
    Just w_ -> force__ w_ \w -> do
      updateMeta ref w
      changed w
  _ | Just (ref, i) <- metaDep v -> lookupMeta ref >>= \case
    Just w_ -> force__ w_ \w -> do
      updateMeta ref w
      changed w
    Nothing -> lookupMeta (metaRef i) >>= \case
      Nothing -> pure v
      Just{} -> do
          r <- case v of
            WApp a b -> vApp a b
            WMatch n a b c _ -> vMatch n a b c
            _ -> impossible
          updateMeta ref r
          changed r
  _ -> pure v

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

quoteNF :: Val -> RefM (Raw, Map Name Raw)
quoteNF v = runWriter g where
 g wst = f v where
  f v_ = force v_ >>= \case
    WNat n   -> pure $ RVar $ NNat n
    WString n-> pure $ RVar $ NString n
    WDelta n _ _ -> pure $ RVar $ n
    v | VCon ty <- view v -> do
      case ty of
        Nothing -> pure ()
        Just ty -> do
          t <- f ty
          tell wst $ singleton (name v) t
      pure (RVar $ name v)
    v@WVar     -> pure $ RVar $ name v
    v@WMeta{}    -> pure $ RVar $ name v
    v@WFun{}  -> pure $ RVar $ name v --lookupRule n r >>= f
    WSel i j e -> rSel i j <$> f e
    WMatch n a b c _ -> rMatch n <$> f a <*> f b <*> f c
    WRet a -> rRet <$> f a
    WApp t u -> (:@) <$> f t <*> f u
    v@(WLam c) -> do
      n <- fmap vVar c
      b <- vApp v n
      q <- f b
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
    ma v = fromMaybe False $ lookup v ma_
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
      WDelta n _ _ -> pure $ TVar n
      WCon n  -> pure $ TVar n
      WMeta{} -> pure $ TVar $ name v
--      WFun_ n r  -> lookupRule n r >>= gg
      WFun{}  -> pure $ TVar $ name v
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
       WMeta{} -> pure False
       WVar  -> pure False
       WDelta{}  -> pure False
       WCon{}  -> pure False
       WFun{}  -> pure False
       _ -> pure True

    sh v = case v of
      _ | opt, closed v -> False
--      WFun -> True
      _ -> False

    up v sh _ = tell wst [v] >> pure sh

    ch v = fmap ((,) (sh v)) $ mapM force__ $ case v of
      _ | opt, closed v -> []
      WSup _ vs -> vs
      WApp a b -> [a, b]
      _ -> []

-- replace generated terms
trRule :: Set Name -> (Tm, Tm) -> RefM (Tm, Tm)
trRule bv (lhs, rhs) = runReader bv \rst -> fst <$> runState mempty \st -> do
    lhs' <- getGens True  rst st lhs
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
      TGen t -> do
        vns <- eval' t
        ns <- metaToVar vns
        if get
          then do
            n <- mkName "w"
            case vns of
              f `WApp` d | f == lookupDictFun -> addSuperClasses (vVar n) d
              _ -> pure ()
            modify st $ insert ns $ TVar n
            pure (TVar n)
          else gets st \m -> fromMaybe (TGen t) $ lookup ns m
      TLet n a b -> TLet n <$> f a <*> local rst (insertSet n) (f b)
      TSup c ts | rigidCombinator c  -> TSup c <$> mapM f ts
      TSup c ts  -> do 
          n <- varName c
          t <- evalCombinatorTm c $ ts <> [TVar n]
          tLam n =<< local rst (insertSet n) (f t)
      t -> error' $ ("TODO(8): " <>) <$> print t

    addSuperClasses v d = do
                r <- getSelectors =<< vApp superClassesFun d
                forM_ r \(a, b) -> do
                  a' <- metaToVar =<< vApp lookupDictFun a
                  vv <- vApp b v
                  b' <- metaToVar vv
                  modify st $ insert a' b'
                  addSuperClasses vv a

  getSelectors :: Val -> RefM [(Val, Val)]
  getSelectors v = forcedSpine v >>= \case
    (WCon "SuperClassCons", [_, a, b, tl]) -> ((a, b):) <$> getSelectors tl
    (WCon "SuperClassNil", [_]) -> pure []
    _ -> undefined

metaToVar :: Val -> RefM Tm
metaToVar v_ = force v_ >>= \w -> case w of
  _ | closed w && rigid w -> pure $ TVal w
  WVar    -> pure $ TVar $ name w
  WMeta{} -> pure $ TVal w
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

-----------------------

pattern CFail :: Val
pattern CFail   = "Fail"

{-# noinline lookupDictFun #-}
lookupDictFun :: Val
lookupDictFun = topM $ vFun "lookupDict" CFail

{-# noinline superClassesFun #-}
superClassesFun :: Val
superClassesFun = topM $ vFun "superClasses" CFail


