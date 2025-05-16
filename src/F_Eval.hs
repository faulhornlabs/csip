module F_Eval
  ( Combinator, varName

  , Tm_ (TGen, TVar, TApp, (:@.), TApps, TLet, TVal, TView, TGuard, TDot,  TRet, TMatch, TSup, TNoRet)
  , Tm, tLam, tMeta, tLets
  , Raw, Scoped, ConInfo, name

  , Val ( WLam, WApp, WMeta, WMetaApp_, WMetaApp, WVar, WCon, WFun, WTm, WDelta, WMatch, WRet, WNoRet
        , CFail, CSuperClassCons, CSuperClassNil, CMkStr, CMkNat, CTopLet
        )
  , vNat, vString, mkFun, vCon, vVar, vApp, vApps, vSup, vTm, vLam, vLams, vConst, isConst
  , mkBuiltin, RuleRef, rigid, closed, lamName
  , force_, force', force

  , eval, evalClosed, evalClosed'
  , quoteTm_, quoteTm', quoteNF, quoteNF'

  , compileRule, replaceMetas

  , spine', matchCon, matchCon', Embedded (..), MetaRef, MetaDep(..), updateMeta

  , addDictSelector, deepForce, strictForce, metaArgNum, closedTm, update, unWTm, wordToNatFun
  ) where

import B_Base
import E_Parse

-------------

-- De Bruijn index
data DB = MkDB
  { dbIndex :: Word
  , dbName  :: NameStr
  }

instance Print  DB where print  = print  . dbName
instance PPrint DB where pprint = pprint . dbName
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

instance Ord Combinator where compare = compare `on` combName

evalCombinator :: Combinator -> List Val -> RefM Val
evalCombinator (MkCombinator _ _ ns t) vs = eval "combinator" (fromListIM $ zip (numberWith MkDB 0 ns) vs) t

evalCombinatorTm :: Combinator -> List Tm -> RefM Tm
evalCombinatorTm (MkCombinator _ _ ns t) vs = evalTm (fromListIM $ zip (numberWith MkDB 0 ns) vs) t

mkCombinator :: Name -> Tm_ Name -> RefM (Tup2 Combinator (List Name))
mkCombinator n t = do
  n <- mkName "c"
  pure (T2 (MkCombinator n (rigidTm t') (map nameStr nsA) t') ns_)
 where

  t' = f (T2 (length nsA) (fromListIM $ numberWith (flip T2) 0 nsA)) t

  ns' = fvs t
  isconst = not $ memberIS n ns'
  ns_ = filter (/= n) $ toListIS ns'
  nsA = ns_ ++ (if isconst then rename "_" n else n) :. Nil

  fvs = \case
    TGen e -> fvs e
    TVar n -> singletonIS n
    TVal _ -> mempty
    TApp a b -> fvs a <> fvs b
    TLet n a b -> fvs a <> deleteIS n (fvs b)
    TSup _ ts -> mconcat (map fvs ts)
    TMatch _ a b c -> fvs a <> fvs b <> fvs c
    TRet e -> fvs e
    TNoRet e -> fvs e

  ins a b (T2 n e) = T2 (maybe (n+1) (const n) (lookupIM a e)) (insertIM a b e)

  f env = \case
    TVar n -> TVar $ MkDB (fromJust $ lookupIM n $ snd env) (nameStr n)
    TGen e -> TGen $ f env e
    TVal v -> TVal v
    TApp a b -> TApp (f env a) (f env b)
    TLet n a b | i <- fst env -> TLet (MkDB i $ nameStr n) (f env a) (f (ins n i env) b)
    TSup c ts -> TSup c $ map (f env) ts
    TMatch n a b c -> TMatch n (f env a) (f env b) (f env c)
    TRet e -> TRet $ f env e
    TNoRet e -> tNoRet $ f env e

tNoRet (TRet e) = e
tNoRet e = TNoRet e

instance PPrint Combinator where
  pprint (MkCombinator _ _ ns t) = "|->" :@ foldl1 (:@) (map pprint ns) :@ pprint t

varName_ d (MkCombinator _ _ ns _) = case last ns of
  ((== "_") -> True) -> d
  n -> n

varName c = mkName $ varName_ "v"{-TODO?-} c

lamName n x = force x <&> \case
  WSup _ c _ -> varName_ n c
  _ -> n

-------------

data Tm_ a
  = TVar a                  -- x
  | TApp (Tm_ a) (Tm_ a)    -- t u
  | TSup Combinator (List (Tm_ a)) -- c t1 ... t(N-1)
  | TLet a (Tm_ a) (Tm_ a)  -- x = t; u

  | TMatch ConInfo (Tm_ a) (Tm_ a) (Tm_ a)
  | TRet (Tm_ a)
  | TNoRet (Tm_ a)

  | TGen (Tm_ a)            -- generated term
  | TVal Val                -- closed value

instance Tag (Tm_ a) where
  tag TVar{} = 0
  tag TApp{} = 1
  tag TSup{} = 2
  tag TLet{} = 3
  tag TMatch{} = 4
  tag TRet{} = 5
  tag TNoRet{} = 6
  tag TGen{} = 7
  tag TVal{} = 8

instance Ord a => Ord (Tm_ a) where
  compare (TVar a)  (TVar a') = compare a a'
  compare (TApp a b)  (TApp a' b') = compare a a' &&& compare b b'
  compare (TSup a b)  (TSup a' b') = compare a a' &&& compare b b'
  compare (TLet a b c)  (TLet a' b' c') = compare a a' &&& compare b b' &&& compare c c'
  compare (TMatch a b c d)  (TMatch a' b' c' d') = compare a a' &&& compare b b' &&& compare c c' &&& compare d d'
  compare (TRet a)  (TRet a') = compare a a'
  compare (TNoRet a)  (TNoRet a') = compare a a'
  compare (TGen a)  (TGen a') = compare a a'
  compare (TVal a)  (TVal a') = compare a a'
  compare a b = compareTag a b

infixl 9 :@.
pattern a :@. b = TApp a b

instance PPrint a => PPrint (Tm_ a) where
  pprint = \case
    TVar n -> "Var" :@ pprint n
    TApp a b -> "@" :@ pprint a :@ pprint b
    TSup c ts -> foldl (:@) (pprint c) $ map pprint ts
    TLet n a b -> zVar ("=":!";":!NilT) :@ pprint n :@ pprint a :@ pprint b
    TVal v -> zVar ("{":!"}":!NilT) :@ pprint v
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

getTApps (TApp (getTApps -> T2 a es) e) = T2 a (e:. es)
getTApps e = T2 e Nil

pattern TApps :: Tm_ a -> List (Tm_ a) -> Tm_ a
pattern TApps e es <- (getTApps -> T2 e (reverse -> es))
  where TApps e es = foldl TApp e es

tLam :: Name -> Tm -> RefM Tm
tLam n t = do
  traceShow "57" $ "tLam begin " <<>> print n <<>> "  -->  " <<>> print t
  T2 c ns' <- mkCombinator n t
  let r = TSup c $ map TVar ns'
  traceShow "57" $ "tLam end " <<>> print r
  pure r

tLams :: List Name -> Tm -> RefM Tm
tLams Nil t = pure t
tLams (n:. ns) t = tLam n =<< tLams ns t

tOLam :: Name -> Tm -> RefM Tm
tOLam n t = tLam n t <&> \t -> TVal COLam :@. tErased :@. tErased :@. t

tOLams :: List Name -> Tm -> RefM Tm
tOLams Nil t = pure t
tOLams (n:. ns) t = tLams ns t >>= tOLam n

tOLet :: Name -> Tm -> Tm -> RefM Tm
tOLet n a b = do
  f <- tLam n b
  pure $ TVal COLet :@. tErased :@. tErased :@. a :@. f

tOApp a b = TVal COApp :@. tErased :@. tErased :@. a :@. b

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
    TRet e -> f e
    TNoRet e -> f e

---------

eval_
  :: (Print a, Ord a, HasId a)
  => (Val -> RefM b)
  -> (b -> RefM b)
  -> (b -> RefM b)
  -> (b -> b -> RefM b)
  -> (Combinator -> List b -> RefM b)
  -> (a -> RefM b)
  -> (ConInfo -> b -> b -> b -> RefM b)
  -> (b -> RefM b)
  -> (b -> RefM b)
  -> IntMap a b
  -> Tm_ a
  -> RefM b
eval_ val box vDot vApp vSup var match ret noret = go where

  go env = \case
    TVal v     -> val v
    TGen x     -> box =<< go env x
    TVar x     -> maybe (var x) pure $ lookupIM x env
    TDot x     -> vDot =<< go env x
    TApp t u   -> join $ vApp <$> go env t <*> go env u
    TSup c ts  -> join $ vSup c <$> mapM (go env) ts
    TLet x t u -> go env t >>= \v -> go (insertIM x v env) u
    TMatch n a b c -> join $ match n <$> go env a <*> go env b <*> go env c
    TRet e     -> join $ ret <$> go env e
    TNoRet e   -> join $ noret <$> go env e

evalTm :: IntMap DB Tm -> Tm_ DB -> RefM Tm
evalTm  = eval_
  (pure . TVal)
  (pure . TGen)
  (pure . TDot)
  (\a b -> pure $ TApp a b)
  (\a b -> pure $ TSup a b)
  (\x -> fail $ "not defined(1): " <<>> print x)
  (\n a b c -> pure $ TMatch n a b c)
  (pure . TRet)
  (pure . tNoRet)

--------

data H a = MkH Name a
idH (MkH n _) = n

instance Ord (H a) where compare = compare `on` idH
instance HasId (H a) where getId = getId . idH

type HH = H (Either Val Tm)

tmToRaw :: Tm -> RefM Scoped
tmToRaw t = do
  T2 r ds <- basic t
  ma <- topDownIM down (mkH ds)
  foldM (\r (T2 n v) -> pure $ RLet n Hole v r) r $ reverse $ assocsIM $ mconcat $ toListIM ma
 where
  mkH ds = assocsIM ds <&> \(T2 n v) -> MkH n v

  down :: HH -> RefM (Tup2 (IntMap Name Scoped) (List HH))
  down (MkH n v) = do
    t <- either quoteTm pure v
    T2 r ds <- basic t
    pure (T2 (singletonIM n r) (mkH ds))

  basic :: Tm -> RefM (Tup2 Scoped (IntMap Name (Either Val Tm)))
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
          t <- evalCombinatorTm c $ ts ++ TVar n :. Nil
          Lam n <$> f (add n env) t
        TMatch n a b c -> rMatch n <$> f env a <*> f env b <*> f env c
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

data Embedded
  = MkEmbedded Tm Val
  | EVarStr NameStr
  | EVar    Name

instance Ord Embedded where
  EVarStr a `compare` EVarStr b = a `compare` b
  EVar    a `compare` EVar    b = a `compare` b
  -- TODO:  MkEmbedded a == MkEmbedded b = ...
  a `compare` b = compareTag a b

instance Tag Embedded where
  tag = \case
    MkEmbedded{} -> 0
    EVarStr{}    -> 1
    EVar{}       -> 2

instance IsString Embedded where
  fromString' s = EVarStr <$> fromString' s

instance HasArity Embedded where
  arity (EVarStr n) = arity n
  arity (EVar n) = arity n
  arity _ = 0

instance IsMixfix Embedded where
  fromMixfix m = EVarStr $ fromMixfix m

instance Print Embedded where
  print (MkEmbedded _ _) = "EMBEDDED" -- TODO
  print (EVarStr n) = print n
  print (EVar n) = print n

instance PPrint Embedded where
  pprint (MkEmbedded r _) = zVar ("[":!"]":!NilT) :@ pprint r
  pprint (EVarStr n) = pprint n
  pprint (EVar n) = pprint n

type Raw = ExpTree Embedded

instance Print Raw where
  print = print . (<$>) f where
    f (EVarStr s) = s
    f (EVar s) = nameStr s
    f MkEmbedded{} = "EMBEDDED"

instance Parse Raw where
  parse = (<$>) ((<$>) EVarStr) . parse

type Scoped = ExpTree Name

-------------------------------

type ConInfo = Name

data View
  = VCon Arity
  | VVar
  | VMeta MetaRef
  | VFun RuleRef   -- function
  | VDelta Arity (RefM Val -> List Val -> RefM Val) -- builtin function
  | VNat Word
  | VString String

  | VApp_ Val Val {-# UNPACK #-} AppKind
  | VSup Combinator (List Val)     -- lambda

  | VMatch ConInfo Val Val Val (Maybe (Tup2 MetaRef MetaDep))
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
instance Ord Val where
  compare = compare `on` name

vCon a n
  {- | maybe True rigid t-} = MkVal n True True $ VCon a
--  | True      = undefined

pattern WCon a n <- MkVal n _    _    (VCon a)
  where WCon a n =  MkVal n True True (VCon a)

pattern WDelta i ar f <- MkVal i _    _    (VDelta ar f)
  where WDelta i ar f =  MkVal i True True (VDelta ar f)

vNat :: Word -> RefM Val
vNat i = mkName "i" <&> \n -> MkVal n True True $ VNat i

vString :: String -> RefM Val
vString i = mkName "s" <&> \n -> MkVal n True True $ VString i

pattern WFun i f <- MkVal i _    _    (VFun f)
  where WFun i f =  MkVal i True True (VFun f)

{-
instance IsString Val where
  fromString s = vCon (fromString s)
-}
vVar :: Name -> Val
vVar n = MkVal n True False VVar

-----------

data MetaRef = MkMetaRef (Ref (Maybe Val))

mkMetaRef = MkMetaRef <$> newRef Nothing

lookupMeta :: MetaRef -> RefM (Maybe Val)
lookupMeta (MkMetaRef r) = readRef r

updateMeta :: MetaRef -> Val -> RefM Tup0
updateMeta (MkMetaRef r) b = writeRef r $ Just b

data MetaDep = MkMetaDep {metaDepName :: Name, metaRef :: MetaRef}

instance Print MetaDep where print = print . metaDepName
instance Ord MetaDep where compare = compare `on` metaDepName
instance HasId MetaDep where getId = getId . metaDepName

vMeta :: RefM Val
vMeta = do
  n <- mkName' "m"
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

mkBuiltin :: Arity -> Name -> Val
mkBuiltin ar n = case n of
  "AppendStr" -> f 2 \d -> \case WString va :. WString vb :. Nil -> vString $ va <> vb; _ -> d
  "EqStr"     -> f 2 \d -> \case WString va :. WString vb :. Nil -> if va == vb then pure CTrue else pure CFalse; _ -> d
  "TakeStr"   -> f 2 \d -> \case WNat va :. WString vb :. Nil -> vString $ takeStr va vb; _ -> d
  "DropStr"   -> f 2 \d -> \case WNat va :. WString vb :. Nil -> vString $ dropStr va vb; _ -> d
  "DecWord"    -> f 1 \d -> \case WNat va :. Nil -> vNat $ max 0 $ va -. 1; _ -> d
  "AddWord"    -> f 2 \d -> \case WNat va :. WNat vb :. Nil -> vNat $ va + vb; _ -> d
  "MulWord"    -> f 2 \d -> \case WNat va :. WNat vb :. Nil -> vNat $ va * vb; _ -> d
  "DivWord"    -> f 2 \d -> \case WNat va :. WNat vb :. Nil -> vNat $ va `div` vb; _ -> d
  "ModWord"    -> f 2 \d -> \case WNat va :. WNat vb :. Nil -> vNat $ va `mod` vb; _ -> d
  "EqWord"     -> f 2 \d -> \case WNat va :. WNat vb :. Nil -> if va == vb then pure CTrue else pure CFalse; _ -> d
  n -> vCon ar n
-- TODO:  n -> error $ "Unknown builtin: " <<>> print n
 where
  f ar g = WDelta n ar g

vApp :: Val -> Val -> RefM Val
vApp a_ u = do
  T2 aa a <- force' a_
  let mkApp_ aa u l = mkValue "a" (rigid aa && rigid u && rigidAppKind l) (closed aa && closed u) $ VApp_ aa u l
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
      _              -> evalDelta (mkApp u u) a (u :. Nil)
    WSup _ c vs      -> evalCombinator c $ vs ++ u :. Nil
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

    _z             -> fail $ print _z
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
vSup c vs = mkValue "l" (rigidCombinator c && all rigid vs) (all closed vs) $ VSup c vs

vLam_ :: Name -> Tm -> RefM Val
vLam_ n t = do
  T2 c ns <- mkCombinator n t
  vSup c (map vVar ns)

vLam :: Name -> Val -> RefM Val
vLam n v = force v >>= \case
  WApp a b -> force b >>= \case
    WVar vn | vn == n -> do
      ta <- quoteTm' a
      T2 c _ <- mkCombinator n ta
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

updateRule :: Name -> RuleRef -> Val -> RefM Tup0
updateRule fn _ b
  | not (rigid b), fn /= "lookupDict", fn /= "superClasses" = fail $ (("rule body is not rigid:\n" <> showName fn <> " = ") <>) <$> print b
updateRule _ r b
  = writeRef r b

type NameSet = IntSet Name

unWTm (WTm _ _ v) = unWTm v
unWTm v = v

compileRule :: Tm -> Tm -> RefM Tup0
compileRule lhs rhs = do
  T0 <- runState mempty (linear lhs) >>= \case
    T2 (Just a) _ -> fail $ "non-linear lhs: " <<>> print a
    _ -> pure T0
  old <- lookupRule r
  new <- compileLHS lhs (TVal old) \_ -> pure $ TRet rhs
  updateRule fn r =<< evalClosed new
  pure T0
 where
  T2 fn r = getFun lhs

  getFun = \case
    TVal (unWTm -> WFun fn r) -> T2 fn r
    TGuard a _ -> getFun a
    TVal (unWTm -> WCon _ "App") :@. _ :@. _ :@. a :@. _ -> getFun a
    TApp a _ -> getFun a
    _ -> impossible

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

  compileLHS :: Tm -> Tm -> (Tm -> RefM Tm) -> RefM Tm
  compileLHS e old rhs = go e rhs where
   go :: Tm -> (Tm -> RefM Tm) -> RefM Tm
   go e rhs = case e of
    TGuard a e -> go a \fail -> do
      tx <- tLazy fail
      compilePat tx (TVal CTrue) e =<< rhs fail
    TVal (unWTm -> WCon _ "App") :@. _ :@. _ :@. a :@. b -> go a \fail -> do
      n <- mkName $ case b of
        TVar m -> nameStr m
        _ -> "v"
      fn <- mkName "fail"
      r <- rhs $ tOForce $ TVar fn
      e <- compilePat' (TVar fn) b (TVar n) (tNoRet r)
      tx <- tOLazy $ tOApp (tNoRet fail) (TVar n)
      ee <- tOLet fn tx e
      TRet <$> tOLam n ee
    TApp a b -> go a \fail -> do
      n <- mkName $ case b of
        TVar m -> nameStr m
        _ -> "v"
      fn <- mkName "fail"
      r <- rhs $ tForce $ TVar fn
      e <- compilePat (TVar fn) b (TVar n) r
      tx <- tLazy $ TApp fail $ TVar n
      ee <- pure $ TLet fn tx e
      tLam n ee
    _ -> rhs old

  compilePat :: Tm -> Tm -> Tm -> Tm -> RefM Tm
  compilePat f p e m = case p of
    TDot{} -> pure m
    TVar n -> pure $ TLet n e m
    TView g p -> compilePat f p (TApp g e) m
    TApps (TVal (unWTm -> WCon _ c)) ps -> do
      let len = length ps
      ns <- sequence $ replicate len $ mkName "v"   -- TODO: better naming
      x <- foldr (\(T2 a b) m -> m >>= \x -> compilePat f a b x) (pure m) $ zip ps $ map TVar ns
      tx <- tLazy x
      ne <- mkName "v"   -- TODO: better naming
      mok <- tLams ns tx
      pure $ TLet ne e $ TMatch c (TVar ne) mok f
    TApps (TVal _) (_:._) -> undefined
    TApps v (_:._) -> fail (print (pprint v))
--    TVal WString{} -> compilePat f (TView (TVal (mkBuiltin 2 "EqStr") `TApp` p) (TVal CTrue)) e m
    TGen{} -> undefined
    TVal{} -> undefined
    TSup{} -> undefined
    TLet{} -> undefined
    p -> fail $ "TODO (13):\n  " <<>> print p <<>> "\n... =\n  " <<>> print rhs

  compilePat' :: Tm -> Tm -> Tm -> Tm -> RefM Tm
  compilePat' f p e m = case p of
    TDot{} -> pure m
    TVar n -> tOLet n e m
    TView g p -> compilePat' f p (TApp g e) m
    TApps (TVal (unWTm -> con@WCon{})) ps -> do
      let len = length ps
      ns <- sequence $ replicate len $ mkName "v"   -- TODO: better naming
      x <- foldr (\(T2 a b) m -> m >>= \x -> compilePat' f a b x) (pure m) $ zip ps $ map TVar ns
      tx <- tOLazy x
      ne <- mkName "v"   -- TODO: better naming
      mok <- tOLams ns tx
      tOLet ne e $ TVal COMatch :@. TVal con :@. TVar ne :@. mok :@. f
    TApps (TVal _) (_:._) -> undefined
    TApps v (_:._) -> fail (print (pprint v))
--    TVal WString{} -> compilePat f (TView (TVal COEqStr `TApp` p) (TVal COTrue)) e m
    TGen{} -> undefined
    TVal{} -> undefined
    TSup{} -> undefined
    TLet{} -> undefined
    p -> fail $ "TODO (23):\n  " <<>> print p <<>> "\n... =\n  " <<>> print rhs

tLets ds e = foldr (uncurry TLet) e ds

addDictSelector :: Tm -> ConInfo -> Word -> Word -> RefM Tup0
addDictSelector (TVal (unWTm -> WFun _ r)) dict args i = do
  old <- lookupRule r
  w <- mkName "_"
  d <- mkName "d"
  lold <- tLazy $ TVal old :@. TVar w :@. TVar d
  ns <- mapM mkName $ replicate args "v" -- TODO: better naming
  body <- tLams ns =<< tLazy (TRet $ TVar $ ns !! i)
  f <- tLam d $ TMatch dict (TVar d) body lold
  new <- tLam w f
  updateRule dict r =<< evalClosed new
addDictSelector _ _ _ _ = impossible

vRet v = mkValue "ret" (rigid v) (closed v) $ VRet v
vNoRet v_ = force v_ >>= \case
  WRet v -> pure v
  v -> mkValue "noret" (rigid v) (closed v) $ VNoRet v

vMatch :: ConInfo -> Val -> Val -> Val -> RefM Val
vMatch n v_ ok fail = force v_ >>= \v -> case headCon v of
  Just (T2 _{-TODO: 0-} c)
    | c == n -> vForce =<< vApps ok (spineCon v)
  Just (T2 _{-TODO: 0-} _)
                  -> vForce fail
  _ -> do
    dep <- case snd <$> metaDep v of
      Nothing -> pure Nothing
      Just d  -> do
        r <- mkMetaRef
        pure $ Just (T2 r d)
    mkValue "match" (rigid v && rigid ok && rigid fail) (closed v && closed ok && closed fail) $ VMatch n v ok fail dep

metaDep :: Val -> Maybe (Tup2 MetaRef MetaDep)
metaDep = \case
  WMeta m -> Just (T2 (metaRef m) m)
  WMetaApp_ _ _ r m -> Just (T2 r m)
  WMatch _ _ _ _ rm -> rm
  _ -> Nothing

-----------

headCon = \case
  WCon a n -> Just (T2 a n)
  WConApp _ _ a n -> Just (T2 a n)
  WTm _ _ v -> headCon v
  _ -> Nothing

matchCon' n v = force v <&> matchCon n

matchCon n v | headCon v == Just (T2 0 n) = Just $ spineCon v
matchCon _ _ = Nothing

spineCon = f Nil where

  f acc WCon{} = acc
  f acc (WConApp a b _ _) = f (b:. acc) a
  f acc (WTm _ _ v) = f acc v
  f _ e = error $ print $ pprint e

spine' v = force v <&> spine where

  spine v = case headCon v of
    Just (T2 0 n) -> Just (T2 n (spineCon v))
    _ -> Nothing

force, force_ :: Val -> RefM Val
force_ v = force__ v pure

force__ v changed = case v of
  WMeta_ _ ref -> lookupMeta ref >>= \case
    Nothing -> pure v
    Just w_ -> force__ w_ \w -> do
      updateMeta ref w
      changed w
  _ | Just (T2 ref i) <- metaDep v -> lookupMeta ref >>= \case
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
    v -> pure (T2 v v)
 where
  f w v_ = force_ v_ >>= \case
    WTm _ _ z -> f w z
    v -> pure (T2 w v)

force v = force' v <&> snd

vVal v = force' v >>= \(T2 a b) -> case b of
  -- hack?
  WFun _ ref -> lookupRule ref >>= \case
    WRet x -> vVal x
    _ -> pure a
  _ -> pure a



-------------

eval :: (Print a, Ord a, HasId a) => RefM String -> IntMap a Val -> Tm_ a -> RefM Val
eval ~err = eval_ vVal pure pure vApp vSup (\x -> fail $ "not defined(" <<>> err <<>> "): " <<>> print x) vMatch vRet vNoRet

eval' :: IntMap Name Val -> Tm -> RefM Val
eval' = eval_ vVal pure pure vApp vSup (pure . vVar) vMatch vRet vNoRet

evalClosed = eval "closed" mempty
evalClosed' v = evalClosed v >>= strictForce

quoteNF :: Val -> RefM Scoped
quoteNF = f where
  f v_ = force v_ >>= \case
    WNat n   -> pure $ RNat n
    WString n-> pure $ RString n
    WDelta n _ _ -> pure $ RVar $ n
    WCon _ n -> pure (RVar n)
    WVar n    -> pure $ RVar n
    WMeta_ n _    -> pure $ RVar n
    WFun n _  -> pure $ RVar n --lookupRule n r >>= f
    WMatch n a b c _ -> rMatch n <$> f a <*> f b <*> f c
    WRet a -> rRet <$> f a
    WNoRet a -> rNoRet <$> f a
    WApp t u -> (:@) <$> f t <*> f u
    v@(WLam _ c) -> do
      n <- (<$>) vVar c
      b <- vApp v n
      q <- f b
      pure $ Lam (name n) q
    _ -> impossible

rMatch n a b c = "match" :@ RVar n :@ a :@ b :@ c
rRet e = "return" :@ e
rNoRet e = "noreturn" :@ e

--------------------------------

quoteNF' = quoteTm >=> tmToRaw

quoteTm, quoteTm' :: Val -> RefM Tm
quoteTm  = quoteTm_ True True False
quoteTm' = quoteTm_ True True True

quoteTm_ lets vtm opt v =
  quoteTm__ lets vtm opt v <&> \(T2 vs x) -> tLets (reverse vs) x

quoteTm__ lets vtm opt v_ = do
  v <- force__ v_
  T2 ma_ vs_ <- runWriter $ go v  -- writer is needed for the right order
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
      WMatch n a b c _ -> TMatch n <$> ff' a <*> ff' b <*> ff' c
      WRet a -> TRet <$> ff' a
      WNat{} -> pure $ TVal v
      WString{} -> pure $ TVal v
      _ -> impossible

  x <- ff v
  vs' <- mapM gg vs
  pure (T2 (zip (map name vs) vs') x)
 where
  force__ = if vtm then force_ else force

  go v wst = walkIM ch share up (v :. Nil) where

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

    up v sh _ = tell wst (v :. Nil) >> pure sh

    ch v = (<$>) (T2 (sh v)) $ mapM force__ $ case v of
      _ | opt, closed v -> Nil
      WSup _ _ vs -> vs
      WApp a b -> a :. b :. Nil
      _ -> Nil

pattern CFail = WCon 0{-?-} "Fail"
pattern CWSuc = WCon 1 "WSuc"
pattern CCons = WCon 2 "ConsStr"
pattern CWSucOk = WCon 1 "WSucOk"
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
pattern CMkNat  = WCon 1 "MkOWord"
pattern COEqStr = WCon 2 "OEqStr"
pattern COEqNat = WCon 2 "OEqWord"
pattern COTrue = WCon 0 "OTrue"
pattern CErased = WCon 0 "Erased"
pattern CTopLet = WCon 5 "TopLet"

type MTT = Map Tm Tm

newCon n = mkName n <&> \n -> vCon 0 n

replaceMetas :: Either (State (Tup2 MTT (List Name))) MTT -> NameSet -> Tm -> RefM Tm
replaceMetas get_ bv tt = do
  traceShow "" $ "replaceMetas " <<>> print tt
  runReader bv ff
 where
  ff rst = f get_ tt  where

    eval' t = asks rst id >>= \bv -> eval "replaceMetas" (fromListIM (toListIS bv <&> \n -> T2 n (vVar n))) t

    f get t = case t of
      TView a b
        | Left st <- get -> gets st fst >>= \m -> TView <$> f (Right m) a <*> f get b
      TView _ _ -> undefined
      TVal (unWTm -> CWSuc) :@. n
        | Left{} <- get       -> f get n <&> \r -> TView (TVal succView) (TVal CWSucOk `TApp` r)
      TVal (unWTm -> CWSuc) :@. n
        -> f get n >>= \r -> vNat 1 <&> \one -> TVal (mkBuiltin 2 "AddWord") :@. TVal one :@. r
      TVal (unWTm -> CCons) :@. a :@. b | Left{} <- get -> f get a >>= \a -> f get b <&> \b -> TView (TVal consView) (TVal CConsOk :@. a :@. b)
      TVal (unWTm -> WNat{})    | Left{} <- get -> pure $ TView (TVal (mkBuiltin 2 "EqWord") `TApp` t) $ TVal CTrue
      TVal (unWTm -> WString{}) | Left{} <- get -> pure $ TView (TVal (mkBuiltin 2 "EqStr") `TApp` t) $ TVal CTrue
      TVal (unWTm -> CMkStr) :@. _ | Left{} <- get -> pure $ TView (TVal COEqStr `TApp` t) $ TVal COTrue
      TVal (unWTm -> CMkNat) :@. _ | Left{} <- get -> pure $ TView (TVal COEqNat `TApp` t) $ TVal COTrue

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
          t <- evalCombinatorTm c $ ts ++ TVar n :. Nil
          tLam n =<< local rst (insertIS n) (f get t)
      TGen t -> eval' t >>= force >>= \vns -> case get of
        Left st -> case vns of
           WMeta d -> do
             n <- mkName "v"
             c <- newCon "q"
             traceShow "" ("meta->var " <<>> print c <<>> "\n := " <<>> print n)
             update d c
             modify st $ first $ insertMap (TVal c) $ TVar n
             modify st $ second (n:.)
             pure $ TVar n
           WMetaApp_ _ _ _ d -> do
             n <- mkName "v"
             c <- newCon "q"
             traceShow "" ("meta->var2 " <<>> print c <<>> "\n := " <<>> print n)
             num <- metaArgNum vns
             ns <- mapM mkName $ replicate num "v"
             update d =<< vLams ns c
             modify st $ first $ insertMap (TVal c) $ TVar n
             modify st $ second (n:.)
             pure $ TVar n
           WApp ff d | ff == lookupDictFun -> do
             t <- metaToVar True (("TODO (22):\n" <>) <$> print vns) vns
             n <- mkName "v"
             modify st $ first $ insertMap t $ TVar n
             traceShow "" $ "addSuperClasses " <<>> print d
             addSuperClasses st (vVar n) d
             pure $ TVar n
           _ -> do
             t <- metaToVar True (("TODO (22):\n" <>) <$> print vns) vns
             pure $ TDot t

        Right m -> do
            ns <- metaToVar False (pure "TODO (20)") vns
            let lo = lookupMap ns m
            case lo of
              Nothing -> traceShow "" ("missed lookup: " <<>> showM' ns)
              _ -> pure T0
            pure $ TGen $ fromMaybe ns lo
      t -> fail $ "TODO(8): " <<>> print t
     where
      addSuperClasses st v d = do
                r <- getProjections =<< vApp superClassesFun d
                forM_ r \(T2 a b) -> do
                  a' <- quote =<< vApp lookupDictFun a
                  vv <- vApp b v
                  b' <- quote vv
                  traceShow "" ("superClass " <<>> showM' a' <<>> "\n  --> " <<>> print b')
                  modify st $ first $ insertMap a' b'
                  addSuperClasses st vv a

      quote = metaToVar False (pure "TODO (21)")

      metaToVar :: Bool -> RefM String -> Val -> RefM Tm
      metaToVar pat ~err = f where
       f v_ = force v_ >>= \w -> case w of
        WMeta _d | pat -> do
          pure $ TVal w
        WMetaApp_ _ _ _ _d | pat -> do
          pure $ TVal w
        WMeta{} -> fail err
        WMetaApp{} -> fail err
        WApp a b -> TApp <$> f a <*> f b
        WFun{}  -> pure $ TVal w
        WVar n  -> pure $ TVar n
        WSup _ c vs | rigidCombinator c -> TSup c <$> mapM f vs
        WSup _ c vs -> do
                n <- varName c
                t <- evalCombinator c $ vs ++ vVar n :. Nil
                tLam n =<< f t
        _ | closed w && rigid w -> pure $ TVal w
        w -> fail $ "TODO(1): " <<>> print w

getProjections :: Val -> RefM (List (Tup2 Val Val))
getProjections v = spine' v >>= \case
    Just (T2 "SuperClassCons" (_ :. a :. b :. tl :. Nil)) -> (T2 a b :.) <$> getProjections tl
    Just (T2 "SuperClassNil" (_ :. Nil)) -> pure Nil
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
    WNat n -> pprint (RNat n :: ExpTree NameStr)
    WString n -> pprint (RString n :: ExpTree NameStr)
    WVar n -> "Variable" :@ pprint n
    WSup _ c vs -> "WSup" :@ pprint c :@ pprint vs
    WCon _ n -> "Constr" :@ pprint n
    WMeta_ n _ -> "Meta" :@ pprint n
    WApp a b -> "App" :@ pprint a :@ pprint b
    WTm{} -> "Term"
    WDelta n _ _ -> "Delta" :@ pprint n
    WFun n _ -> "Funct" :@ pprint n
    _ -> "TODO"

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

{-# noinline wordToNatFun #-}
wordToNatFun = WFun "wordToNat" $ topRef CFail

mkFun = \case
  "succView"     -> pure succView
  "consView"     -> pure consView
  "lookupDict"   -> pure lookupDictFun
  "superClasses" -> pure superClassesFun
  "wordToNat"    -> pure wordToNatFun
  n -> WFun n <$> newRef CFail

-------------------

strictForce :: Val -> RefM Val
strictForce v = deepForce v >>= \case
  v | rigid v -> pure v
  v -> fail $ "meta in value:\n" <<>> print v

deepForce :: Val -> RefM Val
deepForce v_ = do
  v <- force_ v_
  m <- go (v :. Nil)
  pure $ fromJust $ lookupIM v m
 where
  go sv = downUpIM down up sv  where

    down :: Val -> RefM (Tup2 (Maybe Name) (List Val))
    down v = case v of
      _ | rigid v  -> ret Nothing Nil
      WMeta{}      -> ret Nothing Nil
      WMetaApp{}   -> ret Nothing Nil
      WFun{}      -> ret Nothing Nil   -- meta funs
      WLam _ c -> do
        u <- c
        b <- vApp v $ vVar u
        ret (Just u) (b :. Nil)
      WApp a b     -> ret Nothing (a :. b :. Nil)
      WTm _ _ b    -> ret Nothing (b :. Nil)
      WNoRet a     -> ret Nothing (a :. Nil)
      WMatch{}     -> undefined
      WRet{}       -> undefined
      _ -> impossible

    ret mn es = T2 mn <$> mapM force_ es

    up :: Val -> Maybe Name -> List (Tup2 Val Val) -> RefM Val
    up v mn (map snd -> ts) = case v of
      _ | rigid v -> pure v
      WMetaApp{}  -> pure v
      WMeta{}     -> pure v
      WFun{}     -> pure v
      WLam{}  | Just n <- mn, body :. _ <- ts -> vLam n body
      WApp{}  | a :. b :. _ <- ts -> vApp a b
      WNoRet{}| a :. _ <- ts -> vNoRet a
--      WTm n a _ | b :. _ <- ts -> if rigidTm a then vTm (nameStr n) a b else pure b
      WTm n a _ | b :. _ <- ts -> vTm (nameStr n) a b
      _ -> undefined


-------------------------


{-
updatable v _e = lookupMeta (metaRef v) >>= \case
  Just{}  -> impossible
  Nothing -> pure T0
-}
update :: MetaDep -> Val -> RefM Tup0
update v e = do
--  T0 <- updatable v e
  traceShow "1" $ "update " <<>> print v <<>> "\n ::= " <<>> print e
  updateMeta (metaRef v) e

showM' a = print (pprint a)
