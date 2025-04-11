module M4_Eval
  ( Combinator, varName

  , Tm_ (TGen, TVar, TApp, TApps, TLet, TVal, TView, TGuard, TDot,  TRet, TSel, TMatch, TSup, TNoRet)
  , Tm, tLam, tMeta, tLets
  , Raw, Scoped

  , Val ( WLam, WApp, WMeta, WMetaApp_, WMetaApp, WVar, WCon, WFun, WTm, WDelta,  WSel, WMatch, WRet, WNoRet
        , CFail, CSuperClassCons, CSuperClassNil, CMkStr, CMkNat, CTopLet
        )
  , name
  , vNat, vString, mkFun, vCon, vVar, vApp, vApps, vSup, vTm, vLam, vLams, vConst, isConst
  , mkCon, mkBuiltin, RuleRef
  , rigid, closed
  , lamName
  , force_, force', force

  , eval, evalClosed, evalClosed'      -- Tm  -> Val
  , quoteTm_, quoteTm'   -- Val -> Tm
  , quoteNF   -- Val -> Raw
  , quoteNF'

  , addRule_, getGens

  , spine', matchCon, matchCon'
  , Embedded (MkEmbedded)
  , MetaRef, MetaDep(..)
  , updateMeta

  , addDictSelector
  , deepForce, strictForce, metaArgNum
  , closedTm
  , update
  ) where

import M1_Base
import M3_Parse

-------------

-- De Bruijn index
data DB = MkDB
  { dbIndex :: Word
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
  , _combNames :: List NameStr                  -- x1 ... xN
  , _combBody  :: (Tm_ DB)                   -- t
  }

instance Eq  Combinator where (==)    = (==)    `on` combName
instance Ord Combinator where compare = compare `on` combName

evalCombinator :: Combinator -> List Val -> RefM Val
evalCombinator (MkCombinator _ _ ns t) vs = eval (fromListIM $ zip (numberWith MkDB 0 ns) vs) t

evalCombinatorTm :: Combinator -> List Tm -> RefM Tm
evalCombinatorTm (MkCombinator _ _ ns t) vs = evalTm (fromListIM $ zip (numberWith MkDB 0 ns) vs) t

mkCombinator :: Name -> Tm_ Name -> RefM (Combinator, List Name)
mkCombinator n t = do
  n <- mkName "c#"
  pure (MkCombinator n (rigidTm t') (map nameStr nsA) t', ns_)
 where

  t' = f (length nsA, fromListIM $ numberWith (flip (,)) 0 nsA) t

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
    TNoRet e -> fvs e

  ins a b (n, e) = (maybe (n+1) (const n) (lookupIM a e), insertIM a b e)

  f env = \case
    TVar n -> TVar $ MkDB (fromJust $ lookupIM n $ snd env) (nameStr n)
    TGen e -> TGen $ f env e
    TVal v -> TVal v
    TApp a b -> TApp (f env a) (f env b)
    TLet n a b | i <- fst env -> TLet (MkDB i $ nameStr n) (f env a) (f (ins n i env) b)
    TSup c ts -> TSup c $ map (f env) ts
    TMatch n a b c -> TMatch n (f env a) (f env b) (f env c)
    TSel i j e -> TSel i j $ f env e
    TRet e -> TRet $ f env e
    TNoRet e -> tNoRet $ f env e

tNoRet (TRet e) = e
tNoRet e = TNoRet e

instance PPrint Combinator where
  pprint (MkCombinator _ _ ns t) = "|->" :@ foldl1 (:@) (map pprint ns) :@ pprint t

varName_ d (MkCombinator _ _ ns _) = case last ns of
  ((== "_") -> True) -> d
  n -> n

varName c = mkName $ varName_ "v#"{-TODO?-} c

lamName n x = force x <&> \case
  WSup _ c _ -> varName_ n c
  _ -> n

-------------

data Tm_ a
  = TVar a                  -- x
  | TApp (Tm_ a) (Tm_ a)    -- t u
  | TSup Combinator (List (Tm_ a)) -- c t1 ... t(N-1)
  | TLet a (Tm_ a) (Tm_ a)  -- x = t; u

  | TMatch Name (Tm_ a) (Tm_ a) (Tm_ a)
  | TSel Word Word (Tm_ a)  -- unused
  | TRet (Tm_ a)
  | TNoRet (Tm_ a)

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
pattern TView a b = TApp (TApp (TVal (WCon 2 "View")) a) b

pattern TGuard :: Tm -> Tm -> Tm
pattern TGuard a b = TApp (TApp (TVal (WCon 2 "Guard")) a) b

pattern TDot :: Tm_ a -> Tm_ a
pattern TDot a = TApp (TVal (WCon 1 "Dot")) a

getTApps (TApp (getTApps -> (a, es)) e) = (a, e:. es)
getTApps e = (e, Nil)

pattern TApps :: Tm_ a -> List (Tm_ a) -> Tm_ a
pattern TApps e es <- (getTApps -> (e, reverse -> es))
  where TApps e es = foldl TApp e es

tLam :: Name -> Tm -> RefM Tm
tLam n t = do
  (c, ns') <- mkCombinator n t
  pure $ TSup c $ map TVar ns'

tLams :: List Name -> Tm -> RefM Tm
tLams Nil t = pure t
tLams (n:. ns) t = tLam n =<< tLams ns t

tOLam :: Name -> Tm -> RefM Tm
tOLam n t = tLam n t <&> \t -> TApps (TVal COLam) [tErased, tErased, t]

tOLams :: List Name -> Tm -> RefM Tm
tOLams Nil t = pure t
tOLams (n:. ns) t = tLams ns t >>= tOLam n

tOLet :: Name -> Tm -> Tm -> RefM Tm
tOLet n a b = do
  f <- tLam n b
  pure $ TApps (TVal COLet) [tErased, tErased, a, f]

tOApp a b = TApps (TVal COApp) [tErased, tErased, a, b]

tErased = TVal CErased



{-
instance IsString Tm where
  fromString = TVal . fromString
-}
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
    TNoRet e -> f e

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
    TNoRet e -> f e

---------

notDefined x = errorM $ "not defined: " <<>> print x

eval_
  :: (Print a, Ord a, HasId a)
  => (Val -> RefM b)
  -> (b -> RefM b)
  -> (b -> RefM b)
  -> (b -> b -> RefM b)
  -> (Combinator -> List b -> RefM b)
  -> (a -> RefM b)
  -> (Name -> b -> b -> b -> RefM b)
  -> (Word -> Word -> b -> RefM b)
  -> (b -> RefM b)
  -> (b -> RefM b)
  -> IntMap a b
  -> Tm_ a
  -> RefM b
eval_ val box vDot vApp vSup var match sel ret noret = go
 where
  go env = \case
    TVal v     -> val v
    TGen x     -> box =<< go env x
    TVar x     -> maybe (var x) pure $ lookupIM x env
    TDot x     -> vDot =<< go env x
    TApp t u   -> join $ vApp <$> go env t <*> go env u
    TSup c ts  -> join $ vSup c <$> mapM (go env) ts
    TLet x t u -> go env t >>= \v -> go (insertIM x v env) u
    TMatch n a b c -> join $ match n <$> go env a <*> go env b <*> go env c
    TSel i j e -> join $ sel i j <$> go env e
    TRet e     -> join $ ret <$> go env e
    TNoRet e   -> join $ noret <$> go env e

evalTm :: IntMap DB Tm -> Tm_ DB -> RefM Tm
evalTm  = eval_
  (pure . TVal)
  (pure . TGen)
  (pure . TDot)
  (\a b -> pure $ TApp a b)
  (\a b -> pure $ TSup a b)
  notDefined
  (\n a b c -> pure $ TMatch n a b c)
  (\i j -> pure . TSel i j)
  (pure . TRet)
  (pure . tNoRet)

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
  mkH ds = assocsIM ds <&> \(n, v) -> MkH n v

  down :: HH -> RefM (IntMap Name Scoped, List HH)
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
        TNoRet a -> rNoRet <$> f env a

      g env v_ = force_ v_ >>= \case
        WNat n-> pure (RNat n)
        WString n -> pure (RString n)
        WCon _ n -> pure (RVar n)
        WDelta n _ _ -> pure (RVar n)
        WFun n r -> lookupRule r >>= \v -> tell wst (singletonIM n $ Left v) >> pure (RVar n)
        WVar n    -> pure $ RVar n
        WMeta_ n _ -> pure $ RVar n
        WTm n t _ | nullIM env -> tell wst (singletonIM n $ Right t) >> pure (RVar n)
        WTm _ t _ -> f env t
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
  = VCon Arity (Maybe Val){-type-}
  | VVar
  | VMeta MetaRef
  | VFun RuleRef   -- function
  | VDelta Arity (RefM Val -> List Val -> RefM Val) -- builtin function
  | VNat Integer
  | VString String

  | VApp_ Val Val {-# UNPACK #-} AppKind
  | VSup Combinator (List Val)     -- lambda

  | VSel Word Word Val       -- Sel appears only behind the "then" branch of Match       -- meta dependency needed?
                           -- unused
  | VMatch Name Val Val Val (Maybe (MetaRef, MetaDep))
  | VRet Val
  | VNoRet Val

  | VTm Tm Val

data AppKind
  = NeutralApp MetaRef MetaDep    -- volatile App depending on a meta
  | FunApp Val{-accumulated result-}
  | ConApp Arity Name
  | NeutralApp'
  | DeltaApp Arity{-remaining arity-}

rigidAppKind = \case
  NeutralApp{} -> False
  NeutralApp' -> True
  FunApp v -> rigid v
  DeltaApp{} -> True
  ConApp{} -> True

-----------

pattern WNat n <- (view -> VNat n)
pattern WString n <- (view -> VString n)
pattern WVar n <- MkVal n _ _ VVar
pattern WMeta_ n r <- MkVal n _ _ (VMeta r)
pattern WSup n a b <- MkVal n _ _ (VSup a b)
pattern WTm n a b <- MkVal n _ _ (VTm a b)
pattern WSel a b c <- (view -> VSel a b c)
pattern WMatch a b c d e <- (view -> VMatch a b c d e)
pattern WRet n <- (view -> VRet n)
pattern WNoRet n <- (view -> VNoRet n)
pattern WApp a b <- (view -> VApp_ a b _)
pattern WFunApp a b c <- (view -> VApp_ a b (FunApp c))
pattern WConApp a b c d <- (view -> VApp_ a b (ConApp c d))
pattern WDeltaApp a b ar <- (view -> VApp_ a b (DeltaApp ar))
pattern WMetaApp_ a b c d <- (view -> VApp_ a b (NeutralApp c d))
pattern WMetaApp a b <- WMetaApp_ a b _ _
pattern WNeutralApp a b <- (view -> VApp_ a b NeutralApp')
pattern WLam n f <- WSup n (varName -> f) _

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

vCon a n t
  {- | maybe True rigid t-} = MkVal n True True $ VCon a t
--  | True      = undefined

pattern WCon_ n a ty <- MkVal n _ _ (VCon a ty)

pattern WCon a n <- WCon_ n a _
  where WCon a n =  MkVal n True True (VCon a Nothing)

pattern WDelta i ar f <- MkVal i _    _    (VDelta ar f)
  where WDelta i ar f =  MkVal i True True (VDelta ar f)

vNat :: Integer -> RefM Val
vNat i = mkName "i#" <&> \n -> MkVal n True True $ VNat i

vString :: String -> RefM Val
vString i = mkName "i#" <&> \n -> MkVal n True True $ VString i

pattern WFun i f <- MkVal i _    _    (VFun f)
  where WFun i f =  MkVal i True True (VFun f)

vFun :: Name -> Val -> RefM Val
vFun i f = do
  r <- newRef f
  pure $ WFun i r
{-
instance IsString Val where
  fromString s = vCon (fromString s) Nothing
-}
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

vMeta :: RefM Val
vMeta = do
  n <- mkName' "m#"
  MkVal n False True . VMeta <$> mkMetaRef

tMeta :: RefM Tm
tMeta = TVal <$> vMeta

pattern WMeta d <- (mkMetaDep -> Just d)

mkMetaDep (WMeta_ n r) = Just (MkMetaDep n r)
mkMetaDep _ = Nothing

-----------

mkValue :: NameStr -> Bool -> Bool -> View -> RefM Val
mkValue n r c v = do
  n <- mkName n
  pure $ MkVal n r c v

vTm :: NameStr -> Tm -> Val -> RefM Val
vTm n t v
--  | not (rigidTm t) = pure v
  = mkValue n (rigid v {- TODO: && rigidTm t -}) (closed v) $ VTm t v

mkBuiltin :: Arity -> Name -> Maybe Val -> Val
mkBuiltin ar n ty = case n of
  "AppendStr" -> f 2 \d -> \case [WString va, WString vb] -> vString $ va <> vb; _ -> d
  "EqStr"     -> f 2 \d -> \case [WString va, WString vb] -> if va == vb then pure CTrue else pure CFalse; _ -> d
  "TakeStr"   -> f 2 \d -> \case [WNat va, WString vb] -> vString $ take (integerToWord va) vb; _ -> d
  "DropStr"   -> f 2 \d -> \case [WNat va, WString vb] -> vString $ drop (integerToWord va) vb; _ -> d
  "DecNat"    -> f 1 \d -> \case [WNat va] -> vNat $ max 0 $ va -. 1; _ -> d
  "AddNat"    -> f 2 \d -> \case [WNat va, WNat vb] -> vNat $ va + vb; _ -> d
  "MulNat"    -> f 2 \d -> \case [WNat va, WNat vb] -> vNat $ va * vb; _ -> d
  "DivNat"    -> f 2 \d -> \case [WNat va, WNat vb] -> vNat $ va `div` vb; _ -> d
  "ModNat"    -> f 2 \d -> \case [WNat va, WNat vb] -> vNat $ va `mod` vb; _ -> d
  "EqNat"     -> f 2 \d -> \case [WNat va, WNat vb] -> if va == vb then pure CTrue else pure CFalse; _ -> d
  n -> vCon ar n ty
-- TODO:  n -> error $ "Unknown builtin: " <> showName n
 where
  f ar g = WDelta n ar g

mkCon :: Arity -> Name -> Maybe Val -> Val
mkCon ar n ty = vCon ar n ty

vApp :: Val -> Val -> RefM Val
vApp a_ u = do
  (aa, a) <- force' a_
  let mkApp_ aa u l = mkValue "app#" (rigid aa && rigid u && rigidAppKind l) (closed aa && closed u) $ VApp_ aa u l
      mkApp d u = do
        ad <- case snd <$> metaDep d of
          Just x  -> NeutralApp <$> mkMetaRef <*> pure x
          Nothing -> pure NeutralApp'
        mkApp_ aa u ad

      evalDelta d (WDeltaApp a v _) us = evalDelta d a (v:. us)
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
      _              -> evalDelta (mkApp u u) a [u]
    WSup _ c vs      -> evalCombinator c $ vs ++ [u]
    WFun _ r      -> lookupRule r >>= funApp
    WFunApp _ _ f  -> funApp f
    WMeta{}        -> mkApp a u
    WMetaApp{}     -> mkApp a u
    WMatch{}       -> mkApp a u
    WRet{}         -> mkApp a u

    WCon ar n      -> mkApp_ aa u $ ConApp (ar-1) n
    WConApp _ _ a c-> mkApp_ aa u $ ConApp (a-1) c
    WNeutralApp{}  -> mkApp_ aa u NeutralApp'
    WVar{}         -> mkApp_ aa u NeutralApp'

    _z             -> errorM $ print _z
 where
  deltaArity = \case
    WDelta _ ar _    -> Just ar
    WDeltaApp _ _ ar -> Just ar
    _ -> Nothing

tLazy :: Tm -> RefM Tm
tLazy = tLam "_"

tOLazy :: Tm -> RefM Tm
tOLazy = tOLam "_"

tForce :: Tm -> Tm
tForce x = TApp x $ TVal $ WCon 0 "X"

tOForce :: Tm -> Tm
tOForce x = tOApp x $ TVal $ WCon 0 "X"

vForce :: Val -> RefM Val
vForce x = vApp x $ WCon 0 "X"


vApps :: Val -> List Val -> RefM Val
vApps v Nil = pure v
vApps v (a:. as) = vApp v a >>= \x -> vApps x as

vSup :: Combinator -> List Val -> RefM Val
vSup c vs = mkValue "lam#" (rigidCombinator c && all rigid vs) (all closed vs) $ VSup c vs

vLam_ :: Name -> Tm -> RefM Val
vLam_ n t = do
  (c, ns) <- mkCombinator n t
  vSup c (map vVar ns)

vLam :: Name -> Val -> RefM Val
vLam n v = force v >>= \case
  WApp a b -> force b >>= \case
    WVar vn | vn == n -> do
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
  WTm _ _ v -> isConst v
  WSup _ c _ -> isConstComb c
  _ -> False

vLams Nil x = pure x
vLams (v:. vs) x = vLams vs x >>= vLam v

-----------

type RuleRef = Ref Val

lookupRule :: RuleRef -> RefM Val
lookupRule r = readRef r

updateRule :: NameStr -> RuleRef -> Val -> RefM ()
updateRule fn _ b
  | not (rigid b), fn /= "lookupDict", fn /= "superClasses" = errorM $ (("rule body is not rigid:\n" <> showMixfix fn <> " = ") <>) <$> print b
updateRule _ r b
  = writeRef r b

type NameSet = IntSet Name

addRule_ :: NameStr -> Tm -> Tm -> RefM ()
addRule_ fn lhs rhs = do
  () <- runState mempty (linear lhs) >>= \case
    (Just a, _) -> error $ "non-linear lhs: " <> showName a
    _ -> pure ()
  let r = ruleName lhs
  old <- lookupRule r
  new <- compileLHS lhs old \_ -> pure $ TRet rhs
  updateRule fn r =<< evalClosed new
  pure ()
 where
  linear t st = f t  where
    f :: Tm -> RefM (Maybe Name)
    f = \case
      TVal{} -> pure Nothing
      TDot{} -> pure Nothing
      TView _ b -> f b
      TGuard a _ -> f a
      TVar n -> gets st (memberIS n) >>= \case
        True -> pure $ Just n
        _ -> modify st (insertIS n) >> pure Nothing
      TApp a b -> firstJust <$> f a <*> f b
      _ -> undefined

  ruleName :: Tm -> RuleRef
  ruleName = \case
    TVal (WFun _ r) -> r
    TGuard a _ -> ruleName a
    TApps (TVal (WCon _ "App")) [_, _, a, _] -> ruleName a
    TApp a _ -> ruleName a
    t -> error' $ "TODO (11): " <<>> print t

  compileLHS e old rhs = go e rhs where
   go :: Tm -> (Tm -> RefM Tm) -> RefM Tm
   go e rhs = case e of
    TGuard a e -> go a \fail -> do
      tx <- tLazy fail
      compilePat tx (TVal CTrue) e =<< rhs fail
    TApps (TVal (WCon _ "App")) [_, _, a, b] -> go a \fail -> do
      n <- mkName $ case b of
        TVar m -> nameStr m
        _ -> "v#"
      fn <- mkName "fail"
      r <- rhs $ tOForce $ TVar fn
      e <- compilePat' (TVar fn) b (TVar n) (tNoRet r)
      tx <- tOLazy $ tOApp (tNoRet fail) (TVar n)
      ee <- tOLet fn tx e
      TRet <$> tOLam n ee
    TApp a b -> go a \fail -> do
      n <- mkName $ case b of
        TVar m -> nameStr m
        _ -> "v#"
      fn <- mkName "fail"
      r <- rhs $ tForce $ TVar fn
      e <- compilePat (TVar fn) b (TVar n) r
      tx <- tLazy $ TApp fail $ TVar n
      ee <- pure $ TLet fn tx e
      tLam n ee
    TVal WFun{} -> rhs $ TVal old
    _ -> impossible

  compilePat :: Tm -> Tm -> Tm -> Tm -> RefM Tm
  compilePat f p e m = case p of
    TDot{} -> pure m
    TVar n -> pure $ TLet n e m
    TView g p -> compilePat f p (TApp g e) m
    TApps (TVal (WCon _ c)) ps -> do
      let len = length ps
      ns <- sequence $ replicate len $ mkName "wF#"   -- TODO: better naming
      x <- foldr (\(a, b) m -> m >>= \x -> compilePat f a b x) (pure m) $ zip ps $ map TVar ns
      tx <- tLazy x
      ne <- mkName "wG#"   -- TODO: better naming
      mok <- tLams ns tx
      pure $ TLet ne e $ TMatch c (TVar ne) mok f
    TApps (TVal _) (_:._) -> undefined
    TApps v (_:._) -> errorM (print (pprint v))
--    TVal WString{} -> compilePat f (TView (TVal (mkBuiltin 2 "EqStr" Nothing) `TApp` p) (TVal CTrue)) e m
    TGen{} -> undefined
    TVal{} -> undefined
    TSup{} -> undefined
    TLet{} -> undefined
    p -> errorM $ "TODO (13):\n  " <<>> print p <<>> "\n... =\n  " <<>> print rhs

  compilePat' :: Tm -> Tm -> Tm -> Tm -> RefM Tm
  compilePat' f p e m = case p of
    TDot{} -> pure m
    TVar n -> tOLet n e m
    TView g p -> compilePat' f p (TApp g e) m
    TApps (TVal (WCon _ c)) ps -> do
      let len = length ps
      ns <- sequence $ replicate len $ mkName "w#"   -- TODO: better naming
      x <- foldr (\(a, b) m -> m >>= \x -> compilePat' f a b x) (pure m) $ zip ps $ map TVar ns
      tx <- tOLazy x
      ne <- mkName "w#"   -- TODO: better naming
      mok <- tOLams ns tx
      cs <- vString $ chars $ showName c
      tOLet ne e $ TApps (TVal COMatch) [TVal cs, TVar ne, mok, f]
    TApps (TVal _) (_:._) -> undefined
    TApps v (_:._) -> errorM (print (pprint v))
--    TVal WString{} -> compilePat f (TView (TVal COEqStr `TApp` p) (TVal COTrue)) e m
    TGen{} -> undefined
    TVal{} -> undefined
    TSup{} -> undefined
    TLet{} -> undefined
    p -> errorM $ "TODO (23):\n  " <<>> print p <<>> "\n... =\n  " <<>> print rhs

tLets ds e = foldr (uncurry TLet) e ds

addDictSelector :: Val -> Name -> Word -> Word -> RefM ()
addDictSelector (WFun _ r) dict args i = do
  old <- lookupRule r
  w <- mkName "_"
  d <- mkName "d#"
  lold <- tLazy $ TApps (TVal old) [TVar w, TVar d]
  ns <- mapM mkName $ replicate args "ww#" -- TODO: better naming
  body <- tLams ns =<< tLazy (TRet $ TVar $ ns !! i)
  f <- tLam d $ TMatch dict (TVar d) body lold
  new <- tLam w f
  updateRule (nameStr dict) r =<< evalClosed new
addDictSelector _ _ _ _ = impossible

vRet v = mkValue "ret" (rigid v) (closed v) $ VRet v
vNoRet v_ = force v_ >>= \case
  WRet v -> pure v
  v -> mkValue "noret" (rigid v) (closed v) $ VNoRet v

vSel :: Word -> Word -> Val -> RefM Val
vSel i j v_ = force v_ >>= \v -> case headCon v of
  Just (_{-TODO: 0-}, _) -> case spineCon v of
    vs | length vs == i -> pure $ vs !! j
    _ -> mkValue "sel" (rigid v) (closed v) $ VSel i j v
  _ -> mkValue "sel" (rigid v) (closed v) $ VSel i j v

vMatch :: Name -> Val -> Val -> Val -> RefM Val
vMatch n v_ ok fail = force v_ >>= \v -> case headCon v of
  Just (_{-TODO: 0-}, c)
    | c == n      -> vForce =<< vApps ok (spineCon v)
  Just (_{-TODO: 0-}, _)
                  -> vForce fail
  _ -> do
    dep <- case snd <$> metaDep v of
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

headCon = \case
  WCon a n -> Just (a, n)
  WConApp _ _ a n -> Just (a, n)
  _ -> Nothing

matchCon' n v = force v <&> matchCon n
matchCon n v | headCon v == Just (0, n) = Just $ spineCon v
matchCon _ _ = Nothing

spineCon = f Nil
 where
  f acc WCon{} = acc
  f acc (WConApp a b _ _) = f (b:. acc) a
  f _ _ = impossible

spine' v = force v <&> spine
spine v = case headCon v of
  Just (0, n) -> Just (n, spineCon v)
  _ -> Nothing

force, force_ :: Val -> RefM Val
force_ v = force__ v pure

force__ v changed = case v of
  WMeta_ _ ref -> lookupMeta ref >>= \case
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
    v@(WTm _ _ z) -> f v z
    v -> pure (v, v)
 where
  f w v_ = force_ v_ >>= \case
    WTm _ _ z -> f w z
    v -> pure (w, v)

force v = force' v <&> snd

vVal v = force' v >>= \(a, b) -> case b of
  -- hack?
  WFun _ ref -> lookupRule ref >>= \case
    WRet x -> vVal x
    _ -> pure a
  _ -> pure a



-------------

eval :: (Print a, Ord a, HasId a) => IntMap a Val -> Tm_ a -> RefM Val
eval = eval_ vVal pure pure vApp vSup notDefined vMatch vSel vRet vNoRet

eval' :: IntMap Name Val -> Tm -> RefM Val
eval' = eval_ vVal pure pure vApp vSup (pure . vVar) vMatch vSel vRet vNoRet

evalClosed = eval mempty
evalClosed' v = evalClosed v >>= strictForce

quoteNF :: Val -> RefM (Scoped, IntMap Name Scoped)
quoteNF v = runWriter g where
 g wst = f v where
  f v_ = force v_ >>= \case
    WNat n   -> pure $ RNat n
    WString n-> pure $ RString n
    WDelta n _ _ -> pure $ RVar $ n
    WCon_ n _ ty -> do
      case ty of
        Nothing -> pure ()
        Just ty -> do
          t <- f ty
          tell wst $ singletonIM n t
      pure (RVar n)
    WVar n    -> pure $ RVar n
    WMeta_ n _    -> pure $ RVar n
    WFun n _  -> pure $ RVar n --lookupRule n r >>= f
    WSel i j e -> rSel i j <$> f e
    WMatch n a b c _ -> rMatch n <$> f a <*> f b <*> f c
    WRet a -> rRet <$> f a
    WNoRet a -> rNoRet <$> f a
    WApp t u -> (:@) <$> f t <*> f u
    v@(WLam _ c) -> do
      n <- fmap vVar c
      b <- vApp v n
      q <- f b
      pure $ Lam (name n) q
    _ -> impossible

rMatch n a b c = "match" :@ RVar n :@ a :@ b :@ c
rSel i j e = "sel" :@ RNat (wordToInteger i) :@ RNat (wordToInteger j) :@ e
rRet e = "return" :@ e
rNoRet e = "noreturn" :@ e

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
      WSup _ c vs -> TSup c <$> mapM ff' vs
      WApp a b -> TApp <$> ff' a <*> ff' b
      WTm _ t _ -> pure t
      WVar n  -> pure $ TVar n
      WNoRet a -> tNoRet <$> ff' a
      _ | opt -> impossible
      WDelta{} -> pure $ TVal v
      WCon{}  -> pure $ TVal v
      WMeta_ n _ -> pure $ TVar n
--      WFun n r  -> lookupRule n r >>= gg
      WFun n _  -> pure $ TVar n
      WSel i j e -> TSel i j <$> ff' e
      WMatch n a b c _ -> TMatch n <$> ff' a <*> ff' b <*> ff' c
      WRet a -> TRet <$> ff' a
      WNat{} -> pure $ TVal v
      WString{} -> pure $ TVal v
      _ -> impossible

  x <- ff v
  vs' <- mapM gg vs
  pure (zip (map name vs) vs', x)
 where
  force__ = if vtm then force_ else force

  go v wst = walkIM ch share up [v]
   where
    share v _ = case v of
       _ | not lets -> pure False
       _ | opt, closed v -> pure False
       WMeta{} -> pure False
       WVar{}  -> pure False
       WDelta{}  -> pure False
       WCon{}  -> pure False
       WFun{} -> pure False
       _ -> pure True

    sh v = case v of
      _ | opt, closed v -> False
--      WFun{} -> True
      _ -> False

    up v sh _ = tell wst [v] >> pure sh

    ch v = fmap ((,) (sh v)) $ mapM force__ $ case v of
      _ | opt, closed v -> Nil
      WSup _ _ vs -> vs
      WApp a b -> [a, b]
      _ -> Nil

pattern CFail = WCon 0{-?-} "Fail"
pattern CSucc = WCon 1 "Succ"
pattern CCons = WCon 2 "Cons"
pattern CSuccOk = WCon 1 "SuccOk"
pattern CConsOk = WCon 2 "ConsOk"
pattern CTrue  = WCon 0 "True"
pattern CFalse = WCon 0 "False"
pattern CSuperClassCons = WCon 4 "SuperClassCons"
pattern CSuperClassNil = WCon 1 "SuperClassNil"
pattern COApp = WCon 4 "App"
pattern COLam = WCon 3 "Lam"
pattern COLet = WCon 4 "Let"
pattern COMatch = WCon 4 "Match"
pattern CMkStr  = WCon 1 "MkOString"
pattern CMkNat  = WCon 1 "MkONat"
pattern COEqStr = WCon 2 "OEqStr"
pattern COEqNat = WCon 2 "OEqNat"
pattern COTrue = WCon 0 "OTrue"
pattern CErased = WCon 0 "Erased"
pattern CTopLet = WCon 5 "TopLet"

type MTT = Map Tm Tm

newCon n = mkName n <&> \n -> vCon 0 n Nothing

getGens :: Either (State (MTT, List Name)) MTT -> NameSet -> Tm -> RefM Tm
getGens get_ bv tt = do
  traceShow Nil $ "getGens " <<>> showM tt
  runReader bv ff
 where
  ff rst = f get_ tt
   where
    eval' t = asks rst id >>= \bv -> eval (fromListIM (toListIS bv <&> \n -> (n, vVar n))) t

    f get t = case t of
      TView a b
        | Left st <- get -> gets st fst >>= \m -> TView <$> f (Right m) a <*> f get b
      TView _ _ -> undefined
      TApps (TVal CSucc) [n]
        | Left{} <- get       -> f get n <&> \r -> TView (TVal succView) (TVal CSuccOk `TApp` r)
      TApps (TVal CSucc) [n]
        -> f get n >>= \r -> vNat 1 <&> \one -> TApps (TVal $ mkBuiltin 2 "AddNat" Nothing) [TVal one, r]
      TApps (TVal CCons) [a, b] | Left{} <- get -> f get a >>= \a -> f get b <&> \b -> TView (TVal consView) (TApps (TVal CConsOk) [a, b])
      TVal WNat{}    | Left{} <- get -> pure $ TView (TVal (mkBuiltin 2 "EqNat" Nothing) `TApp` t) $ TVal CTrue
      TVal WString{} | Left{} <- get -> pure $ TView (TVal (mkBuiltin 2 "EqStr" Nothing) `TApp` t) $ TVal CTrue
      TApps (TVal CMkStr) [_] | Left{} <- get -> pure $ TView (TVal COEqStr `TApp` t) $ TVal COTrue
      TApps (TVal CMkNat) [_] | Left{} <- get -> pure $ TView (TVal COEqNat `TApp` t) $ TVal COTrue

      TVal v_ -> deepForce v_ >>= \case
        v {- | rigid v -} -> pure $ TVal v
      TVar{} -> pure t
      TDot t | Left{} <- get -> do
        eval' t >>= metaToVar False (("TODO (34):\n" <>) <$> print t) <&> TDot
      TDot{} -> impossible
      TApp a b -> TApp <$> f get a <*> f get b
      TLet n a b -> TLet n <$> f get a <*> local rst (insertIS n) (f get b)
      TSup c ts | rigidCombinator c  -> TSup c <$> mapM (f get) ts
      TSup c ts  -> do 
          n <- varName c
          t <- evalCombinatorTm c $ ts <> [TVar n]
          tLam n =<< local rst (insertIS n) (f get t)
      TGen t -> eval' t >>= force >>= \vns -> case get of
        Left st -> case vns of
           WMeta d -> do
             n <- mkName "wS#"
             c <- newCon "cS#"
             traceShow Nil $ "meta->var " <<>> showM c <<>> "\n := " <<>> showM n
             update d c
             modify st $ first $ insert (TVal c) $ TVar n
             modify st $ second (n:.)
             pure $ TVar n
           WMetaApp_ _ _ _ d -> do
             n <- mkName "wR#"
             c <- newCon "cR#"
             traceShow Nil $ "meta->var2 " <<>> showM c <<>> "\n := " <<>> showM n
             num <- metaArgNum vns
             ns <- mapM mkName $ replicate num "wD#"
             update d =<< vLams ns c
             modify st $ first $ insert (TVal c) $ TVar n
             modify st $ second (n:.)
             pure $ TVar n
           WApp ff d | ff == lookupDictFun -> do
             t <- metaToVar True (("TODO (22):\n" <>) <$> print vns) vns
             n <- mkName "wH#"
             modify st $ first $ insert t $ TVar n
             traceShow Nil $ "addSuperClasses " <<>> showM d
             addSuperClasses st (vVar n) d
             pure $ TVar n
           _ -> do
             t <- metaToVar True (("TODO (22):\n" <>) <$> print vns) vns
             pure $ TDot t

        Right m -> do
            ns <- metaToVar False (pure "TODO (20)") vns
            let lo = lookupMap ns m
            case lo of
              Nothing -> traceShow Nil ("missed lookup: " <<>> showM' ns)
              _ -> pure ()
            pure $ TGen $ fromMaybe ns lo
      t -> errorM $ "TODO(8): " <<>> print t
     where
      addSuperClasses st v d = do
                r <- getProjections =<< vApp superClassesFun d
                forM_ r \(a, b) -> do
                  a' <- quote =<< vApp lookupDictFun a
                  vv <- vApp b v
                  b' <- quote vv
                  traceShow Nil ("superClass " <<>> showM' a' <<>> "\n  --> " <<>> showM b')
                  modify st $ first $ insert a' b'
                  addSuperClasses st vv a

      quote = metaToVar False (pure "TODO (21)")

      metaToVar :: Bool -> RefM Source -> Val -> RefM Tm
      metaToVar pat err = f where
       f v_ = force v_ >>= \w -> case w of
        WMeta _d | pat -> do
          pure $ TVal w
        WMetaApp_ _ _ _ _d | pat -> do
          pure $ TVal w
        WMeta{} -> errorM err
        WMetaApp{} -> errorM err
        WApp a b -> TApp <$> f a <*> f b
        WFun{}  -> pure $ TVal w
        WVar n  -> pure $ TVar n
        WSup _ c vs | rigidCombinator c -> TSup c <$> mapM f vs
        WSup _ c vs -> do
                n <- varName c
                t <- evalCombinator c $ vs <> [vVar n]
                tLam n =<< f t
        _ | closed w && rigid w -> pure $ TVal w
        w -> errorM $ "TODO(1): " <<>> print w

getProjections :: Val -> RefM (List (Val, Val))
getProjections v = spine' v >>= \case
    Just ("SuperClassCons", [_, a, b, tl]) -> ((a, b):.) <$> getProjections tl
    Just ("SuperClassNil", [_]) -> pure Nil
    _ -> undefined

metaArgNum v_ = force v_ >>= \case
  WMeta _     -> pure 0
  WMetaApp a _ -> (+1) <$> metaArgNum a
  _ -> undefined


-----------------------

instance Print Val where
  print v = quoteNF' v >>= print

-- TODO
instance PPrint Val where
  pprint = \case
    WNat n -> pprint (RNat n :: Raw)
    WString n -> pprint (RString n :: Raw)
    WVar n -> "Variable" :@ pprint n
    WSup _ c vs -> "WSup" :@ pprint c :@ pprint vs
    WCon _ n -> "Constr" :@ pprint n
    WMeta_ n _ -> "Meta" :@ pprint n
    WApp a b -> "App" :@ pprint a :@ pprint b
    WTm{} -> "Term"
    WDelta n _ _ -> "Delta" :@ pprint n
    WFun n _ -> "Funct" :@ pprint n
    _ -> "???"

-----------------------

metaFun i f = MkVal i False{-hack-} True (VFun f)

{-# noinline lookupDictFun #-}
lookupDictFun = metaFun "lookupDict" $ topRef CFail

{-# noinline superClassesFun #-}
superClassesFun = metaFun "superClasses" $ topRef CFail

{-# noinline succView #-}
succView = WFun "succView" $ topRef CFail

{-# noinline consView #-}
consView = WFun "consView" $ topRef CFail

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
  v -> errorM $ "meta in value:\n" <<>> print v

deepForce :: Val -> RefM Val
deepForce v_ = do
  v <- force_ v_
  m <- go [v]
  pure $ fromJust $ lookupIM v m
 where
  go sv = downUpIM down up sv
   where
    down :: Val -> RefM (Maybe Name, List Val)
    down v = case v of
      _ | rigid v  -> ret Nothing Nil
      WMeta{}      -> ret Nothing Nil
      WMetaApp{}   -> ret Nothing Nil
      WFun{}      -> ret Nothing Nil   -- meta funs
      WLam _ c -> do
        u <- c
        b <- vApp v $ vVar u
        ret (Just u) [b]
      WApp a b     -> ret Nothing [a, b]
      WTm _ _ b    -> ret Nothing [b]
      WNoRet a     -> ret Nothing [a]
      WSel{}       -> undefined
      WMatch{}     -> undefined
      WRet{}       -> undefined
      _ -> impossible
     where
      ret mn es = (,) mn <$> mapM force_ es

    up :: Val -> Maybe Name -> List (Val, Val) -> RefM Val
    up v mn (map snd -> ts) = case v of
      _ | rigid v -> pure v
      WMetaApp{}  -> pure v
      WMeta{}     -> pure v
      WFun{}     -> pure v
      WLam{}  | Just n <- mn, [body] <- ts -> vLam n body
      WApp{}  | [a, b] <- ts -> vApp a b
      WNoRet{}| [a] <- ts -> vNoRet a
--      WTm n a _ | [b] <- ts -> if rigidTm a then vTm (nameStr n) a b else pure b
      WTm n a _ | [b] <- ts -> vTm (nameStr n) a b
      _ -> undefined


-------------------------


{-
updatable v _e = lookupMeta (metaRef v) >>= \case
  Just{}  -> impossible
  Nothing -> pure ()
-}
update :: MetaDep -> Val -> RefM ()
update v e = do
--  () <- updatable v e
  traceShow "1" $ "update " <<>> showM v <<>> "\n ::= " <<>> showM e
  updateMeta (metaRef v) e

showM' a = showM (pprint a)
