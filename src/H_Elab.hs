module H_Elab
  ( check, inferTop
  , DefData (..), TmTy (..)
  , lookupDefs
  ) where

import D_Base
import E_Parse
import F_Eval
import G_Unify

-------------

pattern RVar' n = RVar (EVarStr n)
pattern REmbed a b = RVar (MkEmbedded a b)

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
pattern CONat   = WCon 0 "ONat"
pattern COString= WCon 0 "OString"
pattern CAp     = WCon 2 "Ap"
pattern CApp    = WCon 2 "App"
pattern CLam    = WCon 2 "Lam"
pattern CBool   = WCon 0 "Bool"
pattern CLet    = WCon 4 "Let"

data Icit = Impl | ImplClass | Expl
  deriving Eq

matchCode :: Val -> RefM (Tup2 (Tm -> RefM Tm) Tm)
matchCode v = matchCon' "Code" v >>= \case
  Just (a :. Nil) -> quoteTm' a <&> \a -> T2 pure a
  _ -> do
    T2 tm m <- freshMeta'
    cm <- vApp CCode m
    f <- conv v cm
    pure (T2 f tm)

matchArr :: Val -> RefM (Tup5 (Tm -> RefM Tm) Tm Val Tm Val)
matchArr v = matchCon' "Arr" v >>= \case
  Just (a :. b :. Nil) -> T5 pure <$> quoteTm' a <*> pure a <*> quoteTm' b <*> pure b
  _ -> do
    T2 m1 m1' <- freshMeta'
    T2 m2 m2' <- freshMeta'
    ar <- vApp CCode =<< vApps CArr (m1' :. m2' :. Nil)
    f <- conv ar v
    pure (T5 f m1 m1' m2 m2')

-- True:   x: t      f x: Pi
-- False:  x: Pi     f x: t
matchPi :: Bool -> Icit -> Val -> RefM (Tup4 (Tm -> RefM Tm) Icit Val Val)
matchPi cov icit v = spine' v >>= \case
  Just (T2 "Pi"  (pa :. pb :. Nil)) -> pure (T4 pure Expl      pa pb)
  Just (T2 "HPi" (pa :. pb :. Nil)) -> pure (T4 pure Impl      pa pb)
  Just (T2 "CPi" (pa :. pb :. Nil)) -> pure (T4 pure ImplClass pa pb)
  _ -> do
    T2 _ m1 <- freshMeta'
    T2 _ m2 <- freshMeta'
    let pi = case icit of Impl -> CHPi; Expl -> CPi; _ -> impossible
    v2 <- vApps pi (m1 :. m2 :. Nil)
    f <- if cov then conv v v2 else conv v2 v
    pure (T4 f icit m1 m2)

conArity :: Val -> RefM Arity
conArity v = spine' v >>= \case
  Just (T2 "Pi"  (_ :. pb :. Nil)) -> (+1) <$> f pb
  Just (T2 "HPi" (_ :. pb :. Nil)) -> (+1) <$> f pb
  Just (T2 "CPi" (_ :. pb :. Nil)) -> (+1) <$> conArity pb
  Just (T2 "IPi" (_ :. pb :. Nil)) -> (+1) <$> conArity pb
  _ -> pure 0
 where
  f g = do
    n <- mkName "r#"
    conArity =<< vApp g (vVar n)

matchHPi v = spine' v <&> \case
  Just (T2 "HPi" (pa :. pb :. Nil)) -> Just (T3 Impl      pa pb)
  Just (T2 "CPi" (pa :. pb :. Nil)) -> Just (T3 ImplClass pa pb)
  _ -> Nothing

--------------------

data TmTy = MkTmTy Tm Val{-type-}

data DefData = MkDefData
  { isConstructor :: Bool
  , tmTy          :: TmTy
  , classData     :: Maybe ClassData
  }


-- TODO: switch to Ref
{-# noinline envR #-}
envR :: State (IntMap Name DefData)
envR = topState memptyEnv

insertDefs n a m = modify envR (insertIM n a) >> m
lookupDefs n = gets envR (lookupIM n)

memptyEnv
  = def "Nat" CNat
  $ def "String" CString
  $ def "Type" CType
  $ pure mempty
 where
  def n_ v me = do
        n <- nameOf n_
        insertIM n (MkDefData False (MkTmTy (TVal v) CType) Nothing) <$> me


{-# noinline namesR #-}
namesR :: Reader (IntMap NameStr Name)
namesR = topReader initNames

initNames
  = def "Nat"
  $ def "String"
  $ def "Type"
  $ pure mempty
 where
  def n_ me = do
        n <- nameOf n_
        insertIM n_ n <$> me

-- TODO:  local --> localInv --> Ref namesR
addName_ n = local namesR (insertIM (nameStr n) n)
askName n = asks namesR (lookupIM n)


-- TODO: switch to Ref
{-# noinline localsR #-}
localsR :: Reader (IntMap Name Val)
localsR = topReader (pure mempty)

insertLocalVal n v = local localsR (insertIM n v)
getLocalVals = asks localsR id


{-# noinline lhsR #-}
lhsR :: Reader Bool
lhsR = topReader (pure False)

setLHS = local lhsR (const True)
askLHS = asks lhsR id

isOnTop :: RefM Bool
isOnTop = askBoundVars <&> null


{-# noinline bvR #-}
bvR :: Reader (List Name)
bvR = topReader (pure Nil)

addBoundVar n = local bvR (n :.)
askBoundVars = asks bvR id


data ClassData = MkClassData
  { _classVal     :: Val
  , _dictVal      :: Val
  , _superClasses :: List Val
  , _methods      :: List (Tup2 Name Val)    -- names and full (closed) types
  }

addClass :: Name -> ClassData -> RefM a -> RefM a
addClass n d m = do
  md <- askDef' n
  insertDefs n (MkDefData False{-TODO?-} (fromJust md) (Just d)) m

lookupClass n = lookupDefs n <&> (>>= classData)

notDefined n = askName n <&> isNothing

addGlobal cstr n v t = insertDefs n (MkDefData cstr (MkTmTy v t) Nothing)

defineGlob_ :: Bool -> Bool -> Bool -> Name -> Tm -> Val -> (Val -> Val -> RefM b) -> RefM b
defineGlob_ cstr haslet metatest n tv t_ cont = addName_ n do
  v <- deepForce =<< evalEnv' (nameStr n) tv
  t <- deepForce t_
  let co = cont v t
  top <- isOnTop
  case T0 of
    _ | haslet || not top -> addGlobal cstr n (if haslet then TVar n else tv) t (insertLocalVal n v co)
      | metatest && not (rigid t)
      -> errorM $ "meta in global definition:\n" <<>> print n <<>> " : " <<>> print t
      | metatest && not (rigid v), n /= "lookupDict", n /= "superClasses"
      -> errorM $ "meta in global definition:\n" <<>> print n <<>> " = " <<>> print v
    _ -> addGlobal cstr n (TVal v) t co

nameOf' n@"caseFun" = mkName n    -- hack?
nameOf' n = nameOf n

defineGlob__ :: Bool -> Bool -> NameStr -> (Name -> RefM Tm) -> Val -> (Name -> Val -> Val -> RefM b) -> RefM b
defineGlob__ cstr haslet n_ fv t_ cont = do
  n <- nameOf' n_
  v_ <- fv n
  defineGlob_ cstr haslet True n v_ t_ (cont n)

defineConstructor = defineGlob__ True False
defineGlob = defineGlob__ False False

defineGlob' :: Bool -> NameStr -> Tm -> Val -> (Name -> RefM a) -> RefM a
defineGlob' haslet n v t cont =
  defineGlob__ False haslet n (\_ -> pure v) t \n _ _ -> cont n

defineBound'_ :: Name -> Val -> RefM a -> RefM a
defineBound'_ n t cont = addName_ n . addGlobal False n (TVar n) t . addBoundVar n . insertLocalVal n (vVar n) $ cont

defineBound' :: NameStr -> Val -> (Name -> RefM a) -> RefM a
defineBound' n_ t cont = mkName n_ >>= \n -> defineBound'_ n t $ cont n

askDef  n = askName n >>= maybe (pure Nothing) askDef'
askDef' n = lookupDefs n <&> fmap tmTy

evalEnv :: Tm -> RefM Val
evalEnv t = getLocalVals >>= \ls -> eval "env" ls t

evalEnv' n t = evalEnv t >>= \v -> if closed v then vTm n t v else pure v

freshMeta_ :: RefM Tm
freshMeta_ = do
  m <- tMeta
  bv <- askBoundVars
  pure $ TApps m $ reverse $ map TVar bv

freshMeta :: RefM Tm
freshMeta = TGen <$> freshMeta_

lookupDictF a = do
  f <- mkFun "lookupDict"
  pure $ TGen $ TApp (TVal f) a

instanceMeta :: RefM (Tup2 Tm Val)
instanceMeta = do
  m <- freshMeta_
  m' <- evalEnv m
  f <- lookupDictF m
  pure (T2 f m')

freshMeta' :: RefM (Tup2 Tm Val)
freshMeta' = do
  m <- freshMeta
  T2 m <$> evalEnv m

typeName n = addSuffix n "_t#"

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
  case T2 sa sb of

    T2 (Just (T2 "Ty" Nil)) (Just (T2 "Type" Nil)) -> do
      pure $ Just \t -> pure $ TVal CCode `TApp` t

    T2 (Just (T2 "String" Nil)) (Just (T2 "Code" (m :. Nil))) -> do
      unify m COString
      pure $ Just \t -> pure $ TVal CMkStr `TApp` t

    T2 (Just (T2 "Nat" Nil)) (Just (T2 "Code" (m :. Nil))) -> do
      unify m CONat
      pure $ Just \t -> pure $ TVal CMkNat `TApp` t

    T2 (Just (T2 "IPi" (m1 :. m2 :. Nil))) (Just (T2 "Pi" (m3 :. m4 :. Nil))) -> do

      q <- conv_ m3 m1

      v <- lamName "v#" m4
      defineBound' v m3 \v -> do
        let vv = vVar v

        c2 <- vApp m4 vv
        h_v <- conv_ m2 c2{- m4 v -}

        m1' <- quoteTm' m1
        m2' <- quoteTm' m2

        pure $ case (T2 h_v q) of
          T2 Nothing Nothing -> Just \t -> pure $ TVal CAp :@. m1' :@. m2' :@. t
          _ -> Just \t -> tLam v =<< evalId h_v =<< TApp (TVal CAp :@. m1' :@. m2' :@. t) <$> evalId q (TVar v)

    T2 (Just (T2 "Pi" (m1 :. m2 :. Nil))) (Just (T2 "Pi" (m3 :. m4 :. Nil))) -> do

      q <- conv_ m3 m1

      v <- lamName "v#" m2
      defineBound' v m3 \v -> do
        let vv = vVar v

        q_v <- evalEnv =<< evalId q (TVar v)
        c1 <- vApp m2 q_v
        c2 <- vApp m4 vv
        h_v <- conv_ c1{- m2 (q v) -} c2{- m4 v -}

        pure $ case T2 h_v q of
          T2 Nothing Nothing -> Nothing
          _ -> Just \t -> tLam v =<< evalId h_v =<< TApp t <$> evalId q (TVar v)

    T2 (Just (T2 "Code" _)) (Just (T2 "Pi" (m3 :. m4 :. Nil))) -> do

      T5 f m1 m1' m2 m2' <- matchArr a

      c1 <- vApp CCode m1'
      q <- conv_ m3 c1{- Code m1 -}

      v <- lamName "v#" m4
      defineBound' v c1 \v -> do
        c2 <- vApp CCode m2'
        m4_v <- vApp m4 (vVar v)
        h_v <- conv_ c2{- Code m2 -} m4_v  --  (Code m1 -> Code m2)  ==>  (Code m1 -> m4)

        let lam t = case T2 h_v q of
              T2 Nothing Nothing -> pure t
              _ -> tLam v =<< evalId h_v =<< TApp t <$> evalId q (TVar v)

        pure $ Just \t -> f t >>= \t -> lam $ TVal CApp :@. m1 :@. m2 :@. t

    T2 (Just (T2 "Pi" (m3 :. m4 :. Nil))) (Just (T2 "Code" _)) -> do

      T5 f m1 m1' m2 m2' <- matchArr b

      c1 <- vApp CCode m1'
      q <- conv_ c1{- Code m1 -} m3

      v <- lamName "v#" m4
      defineBound' v c1 \v -> do
        let vv = vVar v

        c2 <- vApp CCode m2'
        m4_v <- vApp m4 vv
        h_v <- conv_ m4_v{- m4 v -} c2{- Code m2 -}  --  (Code m1 -> m4 v)  ==>  (Code m1 -> Code m2)

        let lam t = case T2 h_v q of
              T2 Nothing Nothing -> pure t
              _ -> tLam v =<< evalId h_v =<< TApp t <$> evalId q (TVar v)

        pure $ Just \t -> lam t >>= \t -> f $ TVal CLam :@. m1 :@. m2 :@. t

    _ -> do
      T0 <- unify a b
      pure Nothing


---------

insertH :: RefM TmTy -> RefM TmTy
insertH et = et >>= \(MkTmTy e t) -> matchHPi t >>= \case
  Nothing -> pure (MkTmTy e t)
  Just (T3 ImplClass a b) -> do
    a' <- quoteTm' a
    m <- lookupDictF a'
    insertH $ pure (MkTmTy (TApp e m) b)
  Just (T3 Impl _ b) -> do
    T2 m vm <- freshMeta'
    t' <- vApp b vm
    insertH $ pure (MkTmTy (TApp e m) t')
  _ -> undefined

unlam :: Name -> Val -> RefM (Tup2 Val Val)
unlam n' f = do
  let v = vVar n'
  t <- vApp f v
  pure (T2 v t)

getPi (RPi  (EVarStr n) a b) = Just (T4 (TVal  CPi) n a b)
getPi (RHPi (EVarStr n) a b) = Just (T4 (TVal CHPi) n a b)
getPi _ = Nothing

--------------------

check :: Raw -> Val -> RefM Tm
check r ty = do
  traceShow "4" $ "check " <<>> print r <<>> "\n :? " <<>> print ty
  tagError r $ do
    t <- check_ r ty
    traceShow "5" $ "check end " <<>> print r <<>> "\n ==> " <> print t
    pure t

check_ :: Raw -> Val -> RefM Tm
check_ r ty = case r of
  Hole -> freshMeta
  RDot t -> askLHS >>= \case
    False -> undefined
    _ -> do
      _t' <- check t ty  -- TODO: use t'
      m <- freshMeta
      pure $ TDot m
  RPi "_" a b | unWTm ty == CTy {- TODO! matchCon -} -> do
    ta <- check a CTy
    tb <- check b CTy
    pure $ TVal CArr `TApp` ta `TApp` tb
  RHLam (EVarStr n) Hole a -> do
    T4 f icit pa pb <- matchPi True Impl ty
    case icit of
      Impl -> do
        defineBound' n pa \n -> do
          T2 _ t <- unlam n pb
          ta <- check a t
          f =<< tLam n ta
      ImplClass -> do
        defineBound' n pa \n -> do   -- TODO: add superclasses to the env
          ta <- check a pb
          f =<< tLam n ta
      _ -> undefined
  RLam (EVarStr n) Hole a -> do
    T4 f icit pa pb <- matchPi True Expl ty
    case icit of
      Expl -> do
        defineBound' n pa \n -> do
          T2 _ t <- unlam n pb
          ta <- check a t
          f =<< tLam n ta
      Impl -> do
        n' <- lamName "z#" pb
        f =<< check (RHLam (EVarStr n') Hole r) ty
      _ -> undefined
  _ -> do
   lhs <- askLHS
   matchHPi ty >>= \case
    Just (T3 Impl _ pb) | not lhs -> do
      n' <- lamName "z#" pb
      check (RHLam (EVarStr n') Hole r) ty
    Just (T3 ImplClass _ _) | not lhs -> do
      check (RHLam "c#" Hole r) ty
    _ -> case r of
      RLet (EVarStr n) t a b -> do
        MkTmTy ta vta <- case t of
          Hole -> infer a
          t -> do
            vta <- checkType n t
            ta <- check a vta
            pure (MkTmTy ta vta)
        top <- isOnTop
        T2 n tb <- defineGlob' (not top) n ta vta \n -> T2 n <$> check b ty
        pure $ if top then tb else TLet n ta tb
      ROLet (EVarStr n) t a b -> isOnTop >>= \case
       True -> do
        vta <- checkType n t
        ta <- check a vta
        ar <- conArity vta
        defineGlob n (\n -> pure $ TVal $ vCon ar n) vta \_n c vta -> do
          tb <- check b ty
          T2 fa pa <- matchCode vta
          T2 fb pb <- matchCode ty
          fta <- fa ta
          ftb <- fb tb
          pure $ TVal CTopLet :@. pa :@. pb :@. TVal c :@. fta :@. ftb
       False -> do
        vta <- checkType n t
        ta <- check a vta
        T2 n tb <- defineBound' n vta \n -> do
          T2 n <$> check b ty
        T2 fa pa <- matchCode vta
        T2 fb pb <- matchCode ty
        fta <- fa ta
        l <- tLam n =<< fb tb
        pure $ TVal CLet :@. pa :@. pb :@. fta :@. l
      r -> do
        MkTmTy a t <- insertH $ infer r
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
  RVar' n -> n
  _t -> undefined

getHPi__ v = matchCon' "HPi" v <&> \case
    Just (a :. b :. Nil) -> Just (T2 a b)
    _ -> Nothing

getHPi_ :: Name -> Val -> RefM (Tup2 Val Val)
getHPi_ n v = getHPi__ v <&> fromJust >>= \(T2 a b) -> vApp b (vVar n) <&> \b -> T2 a b

getHPi :: Val -> RefM (Maybe (Tup2 (Tup2 Name Val) Val))
getHPi v = getHPi__ v >>= \case
  Nothing -> pure Nothing
  Just (T2 a b) -> do
    n <- lamName "m#" b >>= mkName
    b <- vApp b $ vVar n
    pure $ Just (T2 (T2 n a) b)

getApp :: Val -> RefM (Maybe (Tup2 Val Val))
getApp v = force v <&> \case
  WApp a b -> Just (T2 a b)
  _ -> Nothing

getConName :: Val -> RefM (Maybe Name)
getConName v = force v <&> \case
  WCon _ n -> Just n
  _ -> Nothing

getMult f v = f v >>= \case
    Just (T2 c v) -> getMult f v <&> first (c:.)
    Nothing -> pure (T2 Nil v)

getSuper :: Val -> RefM (Maybe (Tup2 Val Val))
getSuper v = matchCon' "CPi" v <&> \case
    Just (a :. b :. Nil) -> Just (T2 a b)
    _ -> Nothing

mkHPi :: Tup2 Name Val -> RefM Val -> RefM Val
mkHPi (T2 n a) b = b >>= \b -> vLam n b >>= \b -> vApps CHPi (a :. b :. Nil)

mkCPi a b = b >>= \b -> vApps CCPi (a :. b :. Nil)

mkPi a b = b >>= \b -> vConst b >>= \b -> vApps CPi (a :. b :. Nil)

mkMult :: (a -> RefM b -> RefM b) -> List a -> RefM b -> RefM b
mkMult f as m = foldr f m as

dictName :: NameStr -> NameStr
dictName n = addSuffix n "Dict"

dictType :: Val -> List Val -> RefM (Tup2 (List Val) Val)
dictType classTy methodTys = do
  T2 (T2 n parTy) classTy' <- getHPi classTy <&> fromJust
  T2 supers classTy'' <- getMult getSuper classTy'
  methodTys' <- forM methodTys \methodTy -> do
    T2 _ methodTy' <- getHPi_ n methodTy
    T2 _ methodTy'' <- getSuper methodTy' <&> fromJust
    pure methodTy''
  t <- mkHPi (T2 n parTy) $ mkMult mkPi supers $ mkMult mkPi methodTys' $ pure classTy''
  supers' <- forM supers \s -> vLam n s
  pure (T2 supers' t)

fff :: (a -> (b -> RefM c) -> RefM c) -> List a -> (List b -> RefM c) -> RefM c
fff _ Nil cont = cont Nil
fff f (a:. as) cont = f a \b -> fff f as \bs -> cont (b:. bs)

addMethodType :: List (Tup2 Name Val) -> List Val -> Val -> (Tup2 Name Val) -> (Tup2 (Tup2 NameStr Name) Val -> RefM a) -> RefM a
addMethodType ns is arg (T2 n_ t) cont = do
  n <- mkName $ tickName (nameStr n_)
  T2 (T2 vn _) t <- getHPi t <&> fromJust
  T2 _ t <- getSuper t <&> fromJust
  f <- vLam vn t
  t <- mkMult mkHPi ns $ mkMult mkCPi is $ vApp f arg
  v <- TVal <$> mkFun n
  defineGlob_ False False True n v t \mn _ -> do
    cont (T2 (T2 (nameStr n_) n) mn)

decomposeHead :: Val -> RefM (Tup3 (List (Tup2 Name Val)) (List Val) Val)
decomposeHead t = do
  T2 ns t <- getMult getHPi t
  T2 is t <- getMult getSuper t
  pure (T3 ns is t)

-- variables, instances, class name, arg type
analyzeInstanceHead :: Val -> RefM (Tup4 (List (Tup2 Name Val)) (List Val) Name Val)
analyzeInstanceHead t = do
  T2 ns t <- getMult getHPi t
  T2 is t <- getMult getSuper t
  T2 cn t <- getApp t <&> fromJust
  cn <- getConName cn <&> fromJust
  pure (T4 ns is cn t)

defineSuperclasses :: NameStr -> Val -> ConInfo -> Word -> List Val -> RefM Tup0
defineSuperclasses nclass vclass dict num supers = do
  m <- mkName "m#"
  let c = TVal vclass `TApp` TVar m
  ss <- forM (numberWith T2 0 supers) \(T2 i s) -> do
    sn <- mkName $ addSuffix (addPrefix "sel" nclass) (mkIntToken i)
    sf <- mkFun sn
    addDictSelector (TVal sf) dict num $ i + 1
    pure (T2 (TVal s :@. TVar m) (TVal sf :@. TVar m))
  let rhs = foldr (\(T2 a b) t -> TVal CSuperClassCons :@. c :@. a :@. b :@. t) (TVal CSuperClassNil `TApp` c) ss
  f <- TVal <$> mkFun "superClasses"
  compileRule (f `TApp` c) rhs

inferMethods :: (RefM Val -> RefM Val) -> Raw -> (List (Tup2 Name Val) -> RefM a) -> RefM a
inferMethods under r cont = case r of
  RLetTy (EVarStr n) t b -> do
    vta <- under $ checkType n t
    defineGlob n (fmap TVal . mkFun) vta \n _ _ -> do
      inferMethods under b \mts -> cont $ T2 n vta :. mts
  REnd -> cont Nil
  _ -> errorM "can't infer method"

inferMethodBodies :: (NameStr -> Name) -> Raw -> RefM Tup0
inferMethodBodies tickName r = case r of
  RRule a b c -> addRule' (mapHead tickName a) b >> inferMethodBodies tickName c
  RLet (EVarStr a) Hole b c -> addRule' (RVar $ EVar $ tickName a) b >> inferMethodBodies tickName c
  REnd -> pure T0
  r -> errorM $ ("can't infer method body :\n" <>) <$> print r

filterM _ Nil = pure Nil
filterM p (a :. b) = p a >>= \case
  True -> (a :.) <$> filterM p b
  False -> filterM p b

addRule' :: Raw -> Raw -> RefM Tup0
addRule' a b = do
  ns <- filterM notDefined (fvs a)
  flip (foldr addName) ns $ do
    MkTmTy lhs vta <- insertH $ setLHS $ infer a
    bv <- askBoundVars <&> fromListIS
    T2 lhs' (T2 st' vs) <- runState (T2 emptyMap Nil) \st -> replaceMetas (Left st) bv lhs
    flip (foldr addName') (reverse vs) $ do
      rhs <- check b vta
      bv <- askBoundVars <&> fromListIS
      rhs' <- replaceMetas (Right st') bv rhs
      compileRule lhs' rhs'

addLookupDictRule :: ClassData -> List (Tup2 Name Val) -> List Val -> Val -> List Val -> RefM Tup0
addLookupDictRule (MkClassData classVal dictVal supers _) (map fst -> ns) is_ arg_ mns = do
  lookupDict <- mkFun "lookupDict"
  let lookup = TApp (TVal lookupDict)
  arg <- quoteTm' arg_
  arg' <- quoteTm_ False False False arg_
  is <- mapM quoteTm' is_
  ds <- forM is \_ -> mkName "d#"
  let rhs
        = tLets (zip ds $ map lookup is)
        $ TApps (TVal dictVal)
        ( arg
        :.  (supers <&> \c -> lookup (TVal c `TApp` arg))
        ++ (mns <&> \mn -> TApps (TVal mn) $ map TVar $ ns ++ ds)
        )
  compileRule (lookup (TVal classVal `TApp` arg')) rhs
  pure T0

introClass :: Val -> RefM Val -> RefM Val
introClass c f = do
  v <- f
  vApps CCPi (c :. v :. Nil)

introType :: Tup2 Name Val -> RefM Val -> RefM Val
introType (T2 n t) f = do
  v <- defineBound'_ n t f
  f <- vLam n v
  vApps CHPi (t :. f :. Nil)

multIntro :: (a -> RefM Val -> RefM Val) -> List a -> RefM Val -> RefM Val
multIntro _ Nil g = g
multIntro f (a:. as) g = f a $ multIntro f as g

inferConstructors :: Raw -> RefM a -> RefM a
inferConstructors r cont = case r of
  RLetTy (EVarStr n) t b -> do
    vta <- checkType n t
    let ff n = do
          ar <- conArity vta
          pure $ TVal $ vCon ar n
    defineConstructor n ff vta \_ _ _ -> inferConstructors b cont
  REnd -> cont
  _ -> errorM "can't infer constructor"

assertOnTop = isOnTop >>= \case
  True -> pure T0
  False -> errorM "not on top level"

infer :: Raw -> RefM TmTy
infer r = do
  traceShow "6" $ "infer " <<>> print r
  tagError r $ do
    MkTmTy t v <- infer_ r
    traceShow "7" $ "infer end " <<>> print r <<>> "\n ==> " <<>> print t <<>> "\n :: " <<>> print v 
    pure (MkTmTy t v)

infer_ :: Raw -> RefM TmTy
infer_ r = case r of
  RClass a b e -> do
    assertOnTop
    let n_ = getVarName $ appHead $ codomain a
    vta <- checkType n_ Hole
    n <- nameOf' n_
    ct <- defineGlob_ False False False n (TVal $ vCon 1{-TODO-} n) vta \_ _ -> checkType' a
    defineGlob_ False False True n (TVal $ vCon 1{-TODO-} n) vta \tc _ -> do
     T3 is _ss cc <- decomposeHead =<< deepForce ct
     let under m = multIntro introType is $ introClass cc{-TODO: use tc-} m
     inferMethods under b \mts -> do
      T2 supers dt <- dictType ct $ map snd mts
      ar <- conArity dt
      defineGlob (dictName n_) (\n -> pure $ TVal $ vCon ar n) dt \dn dv _ -> do
       addClass n (MkClassData tc dv supers mts) do
        forM_ (numberWith T2 0 mts) \(T2 i (T2 mname _)) -> askDef' mname >>= \case
         Just (MkTmTy vf _) -> addDictSelector vf dn (1 + length supers + length mts) (1 + length supers + i)
         _ -> impossible
        defineSuperclasses n_ tc dn (1 + length supers + length mts) supers
        infer e
  RInstance a b c -> do
    assertOnTop
    ct <- checkType' a
    T4 ns is n arg <- analyzeInstanceHead ct
    lookupClass n >>= \case
      Nothing -> undefined
      Just cd@(MkClassData _ _ _ mts) -> do
        fff (addMethodType ns is arg) mts \mns -> do
          addLookupDictRule cd ns is arg (map snd mns)
          let tickName n = fromJust $ lookupIM n $ fromListIM $ map fst mns
          inferMethodBodies tickName b
        infer c
  RData (RLetTy (EVarStr n) t REnd) b c -> do
    assertOnTop
    vta <- checkType n t
    let ff n = do
          ar <- conArity vta
          pure $ TVal $ vCon ar n
    defineConstructor n ff vta \_ _ _ -> do
      inferConstructors b $ infer c
  REnd -> pure (MkTmTy (TVal CType) CType)
  RLam (EVarStr n) t a -> do
    vt <- checkType n t
    defineBound' n vt \n -> do
      MkTmTy ta va <- insertH $ infer a
      f <- vLam n va
      MkTmTy <$> tLam n ta <*> vApps CPi (vt :. f :. Nil)
  RHLam (EVarStr n) t a -> do
    vt <- checkType n t
    defineBound' n vt \n -> do
      MkTmTy ta va <- infer a
      f <- vLam n va
      MkTmTy <$> tLam n ta <*> vApps CHPi (vt :. f :. Nil)
  Hole -> do
    t <- freshMeta
    T2 _ m <- freshMeta'
    pure (MkTmTy t m)
  RNat n    -> vNat n    <&> \v -> MkTmTy (TVal v) CNat
  RString n -> vString n <&> \v -> MkTmTy (TVal v) CString
  RVar (MkEmbedded t v) -> pure (MkTmTy t v)
  RVar (EVar n) -> askDef' n >>= \case
    Just res -> pure res
    _        -> errorM $ "Not in scope: " <<>> print n
  RVar' n -> askDef n >>= \case
    Just res -> pure res
    _        -> errorM $ "Not in scope: " <<>> print n
  RConstructor (EVarStr n) t b -> do
    assertOnTop
    vta <- checkType n t
    let ff n = do
          ar <- conArity vta
          pure $ TVal $ vCon ar n
    defineConstructor n ff vta \_ _ _ -> infer b
  RBuiltin (EVarStr n) t b -> do
    assertOnTop
    vta <- checkType n t
    let ff n = do
          ar <- conArity vta
          pure $ TVal $ mkBuiltin ar n
    defineConstructor n ff vta \_ _ _ -> infer b
  RLetTy (EVarStr n) t b -> do
    inferLetTy n t \_ -> infer b
  ROLet{} -> do
    T2 _ m <- freshMeta'
    ty <- vApp CCode m
    t <- check r ty
    pure (MkTmTy t ty)
  RRule a b c -> do
    addRule' a b
    infer c
  RLet (EVarStr n) t a b | isRuleTy t -> do
    vta <- checkType n t
    defineGlob n (fmap TVal . mkFun) vta \_ _ _ -> do
      addRule' (RVar' n) a
      infer b
  RLet (EVarStr n) t a b -> do
    MkTmTy ta vta <- case t of
      Hole -> infer a
      t -> do
        vta <- checkType n t
        ta <- check a vta
        pure (MkTmTy ta vta)
    top <- isOnTop
    T2 n (MkTmTy tb vtb) <- defineGlob' (not top) n ta vta \n -> T2 n <$> infer b
    pure (MkTmTy (if top then tb else TLet n ta tb) vtb)
  (getPi -> Just (T4 pi n_@"_" a b)) -> do
    ta <- check a CType
    n <- mkName n_
    tb <- check b CType >>= tLam n
    pure (MkTmTy (pi `TApp` ta `TApp` tb) CType)
  (getPi -> Just (T4 pi n a b)) -> do
    ta <- check a CType
    va <- evalEnv' (typeName n) ta
    defineBound' n va \n -> do
      tb <- check b CType
      l <- tLam n tb
      pure (MkTmTy (pi `TApp` ta `TApp` l) CType)
  RCPi a b -> do
    ta <- check a CType
    tb <- check b CType
    pure (MkTmTy (TVal CCPi `TApp` ta `TApp` tb) CType)
  RIPi a b -> do
    ta <- check a CType
    tb <- check b CType
    pure (MkTmTy (TVal CIPi `TApp` ta `TApp` tb) CType)
  RGuard a b -> do
    tb <- check b CBool
    MkTmTy ta ty <- infer a
    pure (MkTmTy (TGuard ta tb) ty)
  RView a b -> do
    MkTmTy ta ty <- infer a
    T4 f Expl pa pb <- matchPi True Expl ty
    n <- lamName "t#" pb
    defineBound' n pa \n -> do
      T2 _ vb <- unlam n pb
      tb <- check b vb
      fta <- f ta
      pure (MkTmTy (TView fta tb) pa)
  RAnn b a -> do
    va <- checkType' a
    tb <- check b va
    pure (MkTmTy tb va)
  RHApp a b -> do
    inferApp Impl a b
  RApp a b -> do
    inferApp Expl a b
  RCaseOf a b -> inferCaseOf a b
  _ -> errorM "can't infer"
 where
  inferApp i a b = infer a >>= \(MkTmTy av ty) -> do
    T4 f icit pa pb <- matchPi True i ty
    fav <- f av
    case T0 of
     _ | icit == ImplClass, i == Impl -> do
        tb <- check b pa
        pure (MkTmTy (TApp fav tb) pb)
       | icit == i -> do
        tb <- check b pa
        n <- lamName "t#" pb
        v <- evalEnv' n tb
        b <- vApp pb v
        pure (MkTmTy (TApp fav tb) b)
       | icit == Impl -> do
        infer $ RApp (RHApp (REmbed av ty) Hole) b
       | icit == ImplClass -> do
        T2 m m' <- instanceMeta
        infer $ RApp (RHApp (REmbed av ty) $ REmbed m m') b
     _ -> errorM "baj"

inferLetTy n_ t cont = do
    top <- isOnTop
    vta <- checkType n_ t
    let mkFun' n | top = mkFun n <&> TVal
        mkFun' _ = do
          bv <- askBoundVars
          fn <- mkName n_
          mkFun fn <&> \v -> TApps (TVal v) (TVar <$> bv)
    defineGlob__ False False n_ mkFun' vta \n _ _ -> cont n

inferCaseOf a b = inferLetTy "caseFun" (RPi "_" Hole Hole) \n -> do
  let
    fn = RVar (EVar n)

    f acc (RCase a b c) = f (acc >> addRule' (RApp fn a) b) c
    f acc REnd = acc >> infer (RApp fn a)
    f _ _ = errorM "invalid case expression"

  f (pure T0) b

addName' :: Name -> RefM a -> RefM a
addName' n cont = do
  T2 _ m <- freshMeta'
  defineBound'_ n m cont

addName :: NameStr -> RefM a -> RefM a
addName n cont = do
  T2 _ m <- freshMeta'
  defineBound' n m \_ -> cont

--------------------

isRuleTy :: Raw -> Bool
isRuleTy = \case
  RHPi _ _ t -> isRuleTy t
  RCPi{} -> True
  _ -> False

ruleHead :: Raw -> Embedded
ruleHead = f where
  f = \case
    RGuard a _ -> f a
    RApp (RApp (RVar' "App") a) _ -> f a
    RApp a _ -> f a
    RVar n -> n
    _ -> undefined

mapHead :: (NameStr -> Name) -> Raw -> Raw
mapHead g = f where
  f = \case
    RGuard a b -> RGuard (f a) b
    RApp a b -> RApp (f a) b
    RVar' n -> RVar $ EVar (g n)
    _ -> undefined

tickName n = addSuffix n "'"

reverseRules :: Raw -> Raw
reverseRules = g where
  g = \case
    RRule a c b   -> f (ruleHead a) (T2 a c :. Nil) b
    RLet  n t a b -> RLet  n t a (g b)
    ROLet n t a b -> ROLet n t a (g b)
    RLetTy  n t b -> RLetTy  n t (g b)
    RConstructor n t b -> RConstructor n t (g b)
    RBuiltin     n t b -> RBuiltin     n t (g b)
    RClass    a b c -> RClass    a b $ g c
    RInstance a b c -> RInstance a (g b) $ g c
    RData     a b c -> RData     a b $ g c
    REnd -> REnd
    r -> r

  f h acc = \case
    RRule a c b | ruleHead a == h -> f h (T2 a c :. acc) b
    r -> foldr (\(T2 a c) b -> RRule a c b) (g r) acc

inferTop :: Raw -> RefM TmTy
inferTop r = do
  infer $ reverseRules r

instance Parse TmTy where
  parse = parse >=> inferTop

instance Parse Tm where
  parse s = parse s <&> \(MkTmTy t _) -> t


fvs :: Raw -> List NameStr
fvs = nub . go where
  go = \case
    Hole -> Nil
    RDot{} -> Nil
    RView _ b -> go b
    RGuard a _ -> go a
    RAnn a _ -> go a
    RHApp a b -> go a <> go b
    RApp a b -> go a <> go b
    RVar' a -> a :. Nil
    RVar{} -> Nil -- hack
    RNat{} -> Nil
    RString{} -> Nil
    x -> error $ ("fvs: " <>) <$> print x

addForalls :: Raw -> RefM Raw
addForalls r = do
  ns <- filterM notDefined (fvs' r)
  pure $ foldr (\n r -> RHPi (EVarStr n) Hole r) r ns

checkType n t = do
  t <- addForalls t
  check t CType >>= evalEnv' (typeName n)

checkType' t = do
  t <- addForalls t
  check t CType >>= evalEnv

fvs' :: Raw -> List NameStr
fvs' = nub . go where
  go = \case
    Hole -> Nil
    RDot{} -> undefined
    RView{} -> undefined
    RGuard{} -> undefined
    RRule{} -> undefined
    RAnn a b -> go b <> go a
    RHPi (EVarStr n) a b -> go a <> del n (go b)
    RPi (EVarStr n) a b -> go a <> del n (go b)
    RLet (EVarStr n) t a b -> go t <> go a <> del n (go b)
    RCPi a b -> go a <> go b
    RIPi a b -> go a <> go b
    RHApp a b -> go a <> go b
    RApp a b -> go a <> go b
    RVar' a -> a :. Nil
    RNat{} -> Nil
    RString{} -> Nil
    x -> error $ ("fvs': " <>) <$> print x

  del n = filter (/= n)
