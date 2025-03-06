module M4_Eval
  ( Combinator, varName

  , Tm_ (TGen, TVar, TApp, TApps, TLet, TVal, TView, TGuard)
  , Tm, tLam, tMeta, tLets
  , Raw, Scoped

  , Val (WLam, WApp, WMeta, WMetaApp_, WMetaApp, WVar, WCon, WFun, WTm, WDelta,  WSel, WMatch, WRet)
  , vNat, vString, mkFun, vCon, vVar, vApp, vApps, vSup, vTm, vLam, vLams, vConst, isConst
  , mkCon, RuleRef
  , name, rigid, closed
  , lamName
  , force_, force', force

  , eval, evalClosed, evalClosed'      -- Tm  -> Val
  , quoteTm_, quoteTm'   -- Val -> Tm
  , quoteNF   -- Val -> Raw
  , quoteNF'

  , addRule

  , spine, forcedSpine
  , Embedded (MkEmbedded)
  , MetaRef, MetaDep(..)
  , updateMeta

  , pattern CFail, lookupDictFun, superClassesFun
  , addDictSelector
  , deepForce, strictForce, metaArgNum
  , closedTm
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
instance HasId DB where getId = dbIndex

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
evalCombinator (MkCombinator _ _ ns t) vs = eval (fromListIM $ zip (zipWith MkDB [0..] ns) vs) t

evalCombinatorTm :: Combinator -> [Tm] -> RefM Tm
evalCombinatorTm (MkCombinator _ _ ns t) vs = evalTm (fromListIM $ zip (zipWith MkDB [0..] ns) vs) t

mkCombinator :: Name -> Tm_ Name -> RefM (Combinator, [Name])
mkCombinator n t = do
  n <- mkName "c"
  pure (MkCombinator n (rigidTm t') (map nameStr nsA) t', ns_)
 where

  t' = f (fromListIM $ zip nsA [0..]) t

  ns' = fvs t
  isconst = not $ memberIS n ns'
  ns_ = filter (/= n) $ toListIS ns'
  nsA = ns_ ++ [if isconst then rename "_" n else n]

  fvs = \case
    TGen e -> fvs e
    TVar n -> singletonIS n
    TVal _ -> mempty
    TApp a b -> fvs a <> fvs b
    TLet n a b -> fvs a <> deleteIS n (fvs b)
    TSup _ ts -> mconcat (map fvs ts)
    TMatch _ a b c -> fvs a <> fvs b <> fvs c
    TSel _ _ e -> fvs e
    TRet e -> fvs e

  f env = \case
    TVar n -> TVar $ MkDB (fromJust $ lookupIM n env) (nameStr n)
    TGen e -> TGen $ f env e
    TVal v -> TVal v
    TApp a b -> TApp (f env a) (f env b)
    TLet n a b | i <- sizeIM env -> TLet (MkDB i $ nameStr n) (f env a) (f (insertIM n i env) b)
    TSup c ts -> TSup c $ map (f env) ts
    TMatch n a b c -> TMatch n (f env a) (f env b) (f env c)
    TSel i j e -> TSel i j $ f env e
    TRet e -> TRet $ f env e

instance PPrint Combinator where
  pprint (MkCombinator _ _ ns t) = "|->" :@ foldl1 (:@) (map pprint ns) :@ pprint t

varName_ d (MkCombinator _ _ ns _) = case last ns of
  "_" -> d
  n -> n

varName c = mkName $ varName_ "v"{-TODO?-} c

lamName n x = force x <&> \case
  WSup c _ -> varName_ n c
  _ -> n

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
    TVar n -> "Var" :@ pprint n
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

closedTm :: Tm_ a -> Bool
closedTm = f where
  f = \case
    TGen e -> f e
    TVar{} -> False
    TVal v -> closed v
    TApp a b -> f a && f b
    TLet _ a b -> f a && f b
    TSup _ ts -> all f ts
    TMatch _ a b c -> f a && f b && f c
    TSel _ _ e -> f e
    TRet e -> f e

---------

notDefined x = error' $ fmap ("not defined: " <>) $ print x

eval_
  :: (Print a, Ord a, HasId a)
  => (Val -> RefM b)
  -> (b -> RefM b)
  -> (b -> b -> RefM b)
  -> (Combinator -> [b] -> RefM b)
  -> (a -> RefM b)
  -> (Name -> b -> b -> b -> RefM b)
  -> (Int -> Int -> b -> RefM b)
  -> (b -> RefM b)
  -> IntMap a b
  -> Tm_ a
  -> RefM b
eval_ val box vApp vSup var match sel ret = go
 where
  go env = \case
    TVal v     -> val v
    TGen x     -> box =<< go env x
    TVar x     -> maybe (var x) pure $ lookupIM x env
    TApp t u   -> join $ vApp <$> go env t <*> go env u
    TSup c ts  -> join $ vSup c <$> mapM (go env) ts
    TLet x t u -> go env t >>= \v -> go (insertIM x v env) u
    TMatch n a b c -> join $ match n <$> go env a <*> go env b <*> go env c
    TSel i j e -> join $ sel i j <$> go env e
    TRet e     -> join $ ret <$> go env e

evalTm :: IntMap DB Tm -> Tm_ DB -> RefM Tm
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
instance HasId (H a) where getId = getId . idH

type HH = H (Either Val Tm)

tmToRaw :: Tm -> RefM Scoped
tmToRaw t = do
  (r, ds) <- basic t
  ma <- topDownIM down (mkH ds)
  foldM (\r (n, v) -> pure $ RLet n Hole v r) r $ reverse $ assocsIM $ mconcat $ toListIM ma
 where
  mkH ds = [MkH n v | (n, v) <- assocsIM ds]

  down :: HH -> RefM (IntMap Name Scoped, [HH])
  down (MkH n v) = do
    t <- either quoteTm pure v
    (r, ds) <- basic t
    pure $ (singletonIM n r, mkH ds)

  basic :: Tm -> RefM (Scoped, IntMap Name (Either Val Tm))
  basic t = runWriter ff where
    ff wst = f mempty t  where
      add n env = insertIM n (vVar n) env

      f env = \case
        TVal v -> g env v
        TGen e -> eval' env e >>= g env
        TVar n  -> pure $ RVar n
        TApp a b -> (:@) <$> f env a <*> f env b
        TLet n a b -> RLet n Hole <$> f env a <*> f (add n env) b
        TSup c ts -> do
          n <- varName c
          t <- evalCombinatorTm c $ ts <> [TVar n]
          Lam n <$> f (add n env) t
        TMatch n a b c -> rMatch n <$> f env a <*> f env b <*> f env c
        TSel i j a -> rSel i j <$> f env a
        TRet a -> rRet <$> f env a

      g env v_ = force_ v_ >>= \case
        WNat n-> pure (RNat n)
        WString n -> pure (RString n)
        WCon n -> pure (RVar n)
        v@WDelta{} -> pure (RVar $ name v)
        WFun_ n r -> lookupRule r >>= \v -> tell wst (singletonIM n $ Left v) >> pure (RVar n)
        v@WVar    -> pure $ RVar (name v)
        v@WMeta{} -> pure $ RVar (name v)
        w@(WTm t _) | nullIM env -> tell wst (singletonIM (name w) $ Right t) >> pure (RVar $ name w)
        WTm t _ -> f env t
        v | nullIM env -> tell wst (singletonIM (name v) $ Left v) >> pure (RVar $ name v)
        v -> quoteTm v >>= f env

instance Print Tm where
  print t = print =<< tmToRaw t

-------------------------------

data Embedded = MkEmbedded Tm Val

instance PPrint Embedded where
  pprint (MkEmbedded r _) = zVar ["[","]"] :@ pprint r

type Raw = Raw_ Embedded
type Scoped = Scoped_ Embedded

-------------------------------

data View
  = VCon (Maybe Val){-type-}
  | VVar
  | VMeta MetaRef
  | VFun RuleRef   -- function
  | VDelta Int{-arity-} (RefM Val -> [Val] -> RefM Val) -- builtin function
  | VNat Integer
  | VString String

  | VApp_ Val Val AppKind
  | VSup Combinator [Val]     -- lambda

  | VSel Int Int Val       -- Sel appears only behind the "then" branch of Match       -- meta dependency needed?
  | VMatch Name Val Val Val (Maybe (MetaRef, MetaDep))
  | VRet Val

  | VTm Tm Val

data AppKind
  = NeutralApp MetaRef MetaDep    -- volatile App depending on a meta
  | FunApp Val{-accumulated result-}
  | ConApp
  | DeltaApp Int{-remaining arity-}

rigidAppKind = \case
  NeutralApp{} -> False
  FunApp v -> rigid v
  DeltaApp{} -> True
  ConApp -> True

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

instance HasId Val where getId = getId . name

-- TODO: assert that names are forced (with time)?
instance Eq Val where
  (==) = (==) `on` name
instance Ord Val where
  compare = compare `on` name

vCon n t
  | True {-maybe True rigid t-} = MkVal n True True $ VCon t
  | otherwise = undefined

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
instance HasId MetaDep where getId = getId . metaDepName

tMeta :: RefM Tm
tMeta = do
  n <- mkName' "m"
  TVal . MkVal n False True . VMeta <$> mkMetaRef

pattern WMeta d <- (mkMetaDep -> Just d)

mkMetaDep v@(WMeta_ r) = Just (MkMetaDep (name v) r)
mkMetaDep _ = Nothing

-----------

mkValue :: NameStr -> Bool -> Bool -> View -> RefM Val
mkValue n r c v = do
  n <- mkName n
  pure $ MkVal n r c v

vTm :: NameStr -> Tm -> Val -> RefM Val
vTm n t v
--  | not (rigidTm t) = pure v
  | otherwise = mkValue n (rigid v {- TODO: && rigidTm t -}) (closed v) $ VTm t v

mkCon :: Name -> Maybe Val -> Val
mkCon n ty = case n of
  "AppendStr" -> f 2 \d -> \case [WString va, WString vb] -> vString $ va <> vb; _ -> d
  "EqStr"     -> f 2 \d -> \case [WString va, WString vb] -> if va == vb then "True" else "False"; _ -> d
  "TakeStr"   -> f 2 \d -> \case [WNat va, WString vb] -> vString $ take (fromIntegral va) vb; _ -> d
  "DropStr"   -> f 2 \d -> \case [WNat va, WString vb] -> vString $ drop (fromIntegral va) vb; _ -> d
  "DecNat"    -> f 1 \d -> \case [WNat va] -> vNat $ max 0 $ va - 1; _ -> d
  "AddNat"    -> f 2 \d -> \case [WNat va, WNat vb] -> vNat $ va + vb; _ -> d
  "MulNat"    -> f 2 \d -> \case [WNat va, WNat vb] -> vNat $ va * vb; _ -> d
  "DivNat"    -> f 2 \d -> \case [WNat va, WNat vb] -> vNat $ va `div` vb; _ -> d
  "ModNat"    -> f 2 \d -> \case [WNat va, WNat vb] -> vNat $ va `mod` vb; _ -> d
  "EqNat"     -> f 2 \d -> \case [WNat va, WNat vb] -> if va == vb then "True" else "False"; _ -> d
  n -> vCon n ty
 where
  f ar g = WDelta n ar g

vApp :: Val -> Val -> RefM Val
vApp a_ u = do
  (aa, a) <- force' a_
  let mkApp_ aa u l = mkValue "app" (rigid aa && rigid u && rigidAppKind l) (closed aa && closed u) $ VApp_ aa u l
      mkApp u d = do
        ad <- case snd <$> metaDep d of
          Just x  -> NeutralApp <$> mkMetaRef <*> pure x
          Nothing -> pure $ ConApp
        mkApp_ aa u ad

      evalDelta d (WDeltaApp a v _) us = evalDelta d a (v: us)
      evalDelta d (WDelta _ _ g) us = g d us
      evalDelta _ _ _ = impossible

      funApp f = vApp f u >>= \case
        WRet x -> pure x
        x -> mkApp_ aa u $ FunApp x

  case a of
    (deltaArity -> Just ar) -> force u >>= \u -> case ar of
      _ | ar < 1     -> impossible
        | not (closed u && rigid u) -> mkApp u u
        | ar > 1     -> mkApp_ a u $ DeltaApp (ar - 1)
        | otherwise  -> evalDelta (mkApp u u) a [u]
    WSup c vs      -> evalCombinator c $ vs ++ [u]
    WFun_ _ r      -> lookupRule r >>= funApp
    WFunApp _ _ f  -> funApp f
    _              -> mkApp u a
 where
  deltaArity = \case
    WDelta _ ar _    -> Just ar
    WDeltaApp _ _ ar -> Just ar
    _ -> Nothing

tLazy :: Tm -> RefM Tm
tLazy = tLam "_"

vEval :: Val -> RefM Val
vEval x = vApp x "X"


vApps :: Val -> [Val] -> RefM Val
vApps v [] = pure v
vApps v (a: as) = vApp v a >>= \x -> vApps x as

vSup :: Combinator -> [Val] -> RefM Val
vSup c vs = mkValue "lam" (rigidCombinator c && all rigid vs) (all closed vs) $ VSup c vs

vLam_ :: Name -> Tm -> RefM Val
vLam_ n t = do
  (c, ns) <- mkCombinator n t
  vSup c $ vVar <$> ns

vLam :: Name -> Val -> RefM Val
vLam n v = force v >>= \case
  WApp a b -> force b >>= \case
    b@WVar | name b == n -> do
      ta <- quoteTm' a
      (c, _) <- mkCombinator n ta
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
  vLam n v

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

updateRule :: NameStr -> RuleRef -> Val -> RefM ()
updateRule fn r b
  | not (rigid b), fn /= "lookupDict" = error' $ (("rule body is not rigid:\n" <> showMixfix fn <> " = ") <>) <$> print b
  | otherwise = writeRef r b

addRule :: NameStr -> [Name] -> Tm -> Tm -> RefM ()
addRule fn (fromListIS -> boundvars) lhs_ rhs_ = do
  (lhs, rhs) <- trRule boundvars (lhs_, rhs_)
  (r, ns) <- ruleName [] lhs
  old <- lookupRule r
  new <- compileLHS (TVal old) ns lhs . TRet =<< pure rhs
  updateRule fn r =<< evalClosed new
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
    e <- compilePat (boundvars <> fromListIS ns) tx (TVal $ vCon "True" $ Just "Bool") e $ pure rhs
    compileLHS old ns a e
  compileLHS old (n: ns) (TApp a b) rhs = do
    tx <- tLazy $ TApps old $ TVar <$> reverse (n: ns)
    e <- compilePat (boundvars <> fromListIS (n: ns)) tx b (TVar n) $ pure rhs
    compileLHS old ns a =<< tLam n e
  compileLHS _ [] (TVal WFun{}) rhs = pure rhs
  compileLHS _ _ _ _ = undefined

  compilePat bv f p e m = case p of
    TVar n -> TLet n e <$> m
    TView g p -> compilePat bv f p (TApp g e) m
    TApps (TVal (WCon c)) ps -> do
      let len = length ps
      ns <- sequence $ replicate len $ mkName "w"   -- TODO: better naming
      x <- foldr (uncurry $ compilePat bv f) m $ zip ps $ map TVar ns
      tx <- tLazy x
      ne <- mkName "w"   -- TODO: better naming
      pure $ TLet ne e $ TMatch c (TVar ne) (tLets (zip ns [TSel len i $ TVar ne | (i, _) <- zip [0..] ns]) tx) f
    TApps (TVal _) (_:_) -> undefined
    TApps v (_:_) -> error' $ print $ pprint v
    TGen{} -> undefined
    TVal{} -> undefined
    TSup{} -> undefined
    TLet{} -> undefined
    p -> error' $ (\a b -> "TODO (13):\n  " <> a <> "\n... =\n  " <> b) <$> print p <*> print rhs_

tLets ds e = foldr (uncurry TLet) e ds

addDictSelector :: Val -> Name -> Int -> Int -> RefM ()
addDictSelector (WFun_ _ r) dict args i = do
  old <- lookupRule r
  w <- mkName "_"
  d <- mkName "d"
  lold <- tLazy $ TApps (TVal old) [TVar w, TVar d]
  body <- tLazy $ TRet $ TSel args i $ TVar d
  f <- tLam d $ TMatch dict (TVar d) body lold
  new <- tLam w f
  updateRule (nameStr dict) r =<< evalClosed new
addDictSelector _ _ _ _ = impossible

vRet v = mkValue "ret" (rigid v) (closed v) $ VRet v

vSel :: Int -> Int -> Val -> RefM Val
vSel i j v = spine v >>= \case
  (WCon{}, vs) | length vs == i -> pure $ vs !! j
  _ -> mkValue "sel" (rigid v) (closed v) $ VSel i j v

vMatch :: Name -> Val -> Val -> Val -> RefM Val
vMatch n v ok fail = spine v >>= \case
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

eval :: (Print a, Ord a, HasId a) => IntMap a Val -> Tm_ a -> RefM Val
eval = eval_ pure pure vApp vSup notDefined vMatch vSel vRet

eval' :: IntMap Name Val -> Tm -> RefM Val
eval' = eval_ pure pure vApp vSup (pure . vVar) vMatch vSel vRet

evalClosed = eval mempty
evalClosed' v = evalClosed v >>= strictForce

quoteNF :: Val -> RefM (Scoped, IntMap Name Scoped)
quoteNF v = runWriter g where
 g wst = f v where
  f v_ = force v_ >>= \case
    WNat n   -> pure $ RNat n
    WString n-> pure $ RString n
    WDelta n _ _ -> pure $ RVar $ n
    v | VCon ty <- view v -> do
      case ty of
        Nothing -> pure ()
        Just ty -> do
          t <- f ty
          tell wst $ singletonIM (name v) t
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
rSel i j e = "sel" :@ RNat (fromIntegral i) :@ RNat (fromIntegral j) :@ e
rRet e = "return" :@ e

--------------------------------

quoteNF' = quoteTm >=> tmToRaw

quoteTm, quoteTm' :: Val -> RefM Tm
quoteTm  = quoteTm_ True True False
quoteTm' = quoteTm_ True True True

quoteTm_ lets vtm opt v =
  quoteTm__ lets vtm opt v <&> \(vs, x) -> tLets (reverse vs) x

quoteTm__ lets vtm opt v_ = do
  v <- force__ v_
  (ma_, vs_) <- runWriter $ go v  -- writer is needed for the right order
  let
    ma v = fromMaybe False $ lookupIM v ma_
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
      WDelta{} -> pure $ TVal v
      WCon{}  -> pure $ TVal v
      WMeta{} -> pure $ TVar $ name v
--      WFun_ n r  -> lookupRule n r >>= gg
      WFun{}  -> pure $ TVar $ name v
      WSel i j e -> TSel i j <$> ff' e
      WMatch n a b c _ -> TMatch n <$> ff' a <*> ff' b <*> ff' c
      WRet a -> TRet <$> ff' a
      WNat{} -> pure $ TVal v
      WString{} -> pure $ TVal v
      _ -> impossible

  x <- ff v
  vs' <- mapM gg vs
  pure (zip (name <$> vs) vs', x)
 where
  force__ = if vtm then force_ else force

  go v wst = walkIM ch share up [v]
   where
    share v _ = case v of
       _ | not lets -> pure False
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
trRule :: IntSet Name -> (Tm, Tm) -> RefM (Tm, Tm)
trRule bv (lhs, rhs) = runReader bv \rst -> fst <$> runState mempty \st -> do
    lhs' <- getGens True  rst st lhs
    assertM $ rigidTm lhs'
    rhs' <- getGens False rst st rhs
    assertM $ rigidTm rhs'
    pure (lhs', rhs')
 where
  getGens :: Bool -> Reader (IntSet Name) -> State (Map Tm Tm) -> Tm -> RefM Tm
  getGens get rst st tt = f get tt
   where
    eval' t = asks rst id >>= \bv -> eval (fromListIM [(n, vVar n) | n <- toListIS bv]) t

    f get t = case t of
      TView a b
        | get -> TView <$> f False a <*> f True b
        | otherwise -> undefined
      TApps (TVal "Succ") [n]
        | get       -> f get n <&> \r -> TView (TVal succView) (TVal "SuccOk" `TApp` r)
        | otherwise -> f get n >>= \r -> vNat 1 <&> \one -> TApps (TVal $ mkCon "AddNat" Nothing) [TVal one, r]
      TApps (TVal "Cons") [a, b] | get -> f get a >>= \a -> f get b <&> \b -> TView (TVal consView) (TApps (TVal "ConsOk") [a, b])
      TVal WNat{}    | get -> pure $ TView (TVal (mkCon "EqNat" Nothing) `TApp` t) $ TVal "True"
      TVal WString{} | get -> pure $ TView (TVal (mkCon "EqStr" Nothing) `TApp` t) $ TVal "True"

      TVal v_ -> deepForce v_ >>= \case
        v {- | rigid v -} -> pure $ TVal v
--        _ -> undefined
      TVar{} -> pure t
      TApp a b -> TApp <$> f get a <*> f get b
      TLet n a b -> TLet n <$> f get a <*> local rst (insertIS n) (f get b)
      TSup c ts | rigidCombinator c  -> TSup c <$> mapM (f get) ts
      TSup c ts  -> do 
          n <- varName c
          t <- evalCombinatorTm c $ ts <> [TVar n]
          tLam n =<< local rst (insertIS n) (f get t)
      TGen t -> eval' t >>= force >>= \vns -> do
        if get
          then do
            n <- mkName "w"
            m <- gets st id
            case vns of
                WMeta d -> do
                  updateMeta (metaRef d) (vVar n)
                WMetaApp_ _ _ _ d -> do
                  num <- metaArgNum vns
                  ns <- mapM mkName $ replicate num "wD"
                  updateMeta (metaRef d) =<< vLams ns (vVar n)
                _ -> do
                  t <- metaToVar (("TODO (22):\n" <>) <$> print vns) m vns
                  modify st $ insert t $ TVar n
            case vns of
              WApp f d | f == lookupDictFun -> addSuperClasses map (vVar n) d
              _ -> pure ()
            pure (TVar n)
          else do
            m <- gets st id
            ns <- metaToVar (pure "TODO (20)") m vns
            pure $ TGen $ fromMaybe ns $ lookup ns m
      t -> error' $ ("TODO(8): " <>) <$> print t

    addSuperClasses m v d = do
                r <- getSelectors =<< vApp superClassesFun d
                forM_ r \(a, b) -> do
                  a' <- quote =<< vApp lookupDictFun a
                  vv <- vApp b v
                  b' <- quote vv
                  modify st $ insert a' b'
                  addSuperClasses m vv a

    quote = metaToVar (pure "TODO (21)") mempty

  getSelectors :: Val -> RefM [(Val, Val)]
  getSelectors v = forcedSpine v >>= \case
    (WCon "SuperClassCons", [_, a, b, tl]) -> ((a, b):) <$> getSelectors tl
    (WCon "SuperClassNil", [_]) -> pure []
    _ -> undefined

metaArgNum v_ = force v_ >>= \case
  WMeta _     -> pure 0
  WMetaApp a _ -> (+1) <$> metaArgNum a
  _ -> undefined

metaToVar :: RefM Source -> Map Tm Tm -> Val -> RefM Tm
metaToVar err m = f where
 f v_ = force v_ >>= \w -> case w of
  _ | closed w && rigid w -> pure $ TVal w
  WFun{}  -> pure $ TVal w
  WVar    -> pure $ TVar $ name w
  WApp a b -> TApp <$> f a <*> f b
  WSup c vs | rigidCombinator c -> TSup c <$> mapM f vs
  WSup c vs -> do
          n <- varName c
          t <- evalCombinator c $ vs <> [vVar n]
          tLam n =<< f t
  WMeta{} -> err >>= errorM
  w -> error' $ ("TODO(1): " <>) <$> print w

-----------------------

instance Print Val where
  print v = quoteNF' v >>= print

-- TODO
instance PPrint Val where
  pprint = \case
    WNat n -> pprint (RNat n :: Raw)
    WString n -> pprint (RString n :: Raw)
    v@WVar -> "Var" :@ pprint (name v)
    WSup c vs -> "WSup" :@ pprint c :@ pprint vs
    v@WCon{} -> "Con" :@ pprint (name v)
    v@WMeta{} -> "Meta" :@ pprint (name v)
    WApp{} -> "App"
    WTm{} -> "Tm"
    v@WDelta{} -> "Delta" :@ pprint (name v)
    WFun n -> "Fun" :@ pprint n
    _ -> "???"

-----------------------

pattern CFail :: Val
pattern CFail = "Fail"

{-# noinline lookupDictFun #-}
lookupDictFun = metaFun "lookupDict" $ topRef CFail

metaFun i f = MkVal i False{-hack-} True (VFun f)

{-# noinline superClassesFun #-}
superClassesFun = WFun_ "superClasses" $ topRef CFail

{-# noinline succView #-}
succView = WFun_ "succView" $ topRef CFail

{-# noinline consView #-}
consView = WFun_ "consView" $ topRef CFail

mkFun = \case
  "succView"     -> pure succView
  "consView"     -> pure consView
  "lookupDict"   -> pure lookupDictFun
  "superClasses" -> pure superClassesFun
  n -> vFun n CFail


-------------------

strictForce :: Val -> RefM Val
strictForce v = deepForce v >>= \case
  v | rigid v -> pure v
    | otherwise -> print v >>= \s -> errorM $ "meta in value:\n" <> s

deepForce :: Val -> RefM Val
deepForce v_ = do
  v <- force_ v_
  m <- go [v]
  pure $ fromJust $ lookup v m
 where
  go sv = downUp down up sv
   where
    down :: Val -> RefM (Maybe Name, [Val])
    down v = case v of
      _ | rigid v  -> ret Nothing []
      WMeta{}      -> ret Nothing []
      WMetaApp{}   -> ret Nothing []
      WFun{}       -> ret Nothing []   -- meta funs
      WLam c -> do
        u <- c
        b <- vApp v $ vVar u
        ret (Just u) [b]
      WApp a b     -> ret Nothing [a, b]
      WTm _ b      -> ret Nothing [b]
      WSel{}       -> undefined
      WMatch{}     -> undefined
      WRet{}       -> undefined
      _ -> impossible
     where
      ret mn es = (,) mn <$> mapM force_ es

    up :: Val -> Maybe Name -> [(Val, Val)] -> RefM Val
    up v mn (map snd -> ts) = case v of
      _ | rigid v -> pure v
      WMetaApp{}  -> pure v
      WMeta{}     -> pure v
      WFun{}      -> pure v
      WLam{}  | Just n <- mn, [body] <- ts -> vLam n body
      WApp{}  | [a, b] <- ts -> vApp a b
--      WTm a _ | [b] <- ts -> if rigidTm a then vTm (nameStr $ name v) a b else pure b
      WTm a _ | [b] <- ts -> vTm (nameStr $ name v) a b
      _ -> undefined


