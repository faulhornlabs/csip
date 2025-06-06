module E3_Elab
  ( check, infer
  , TmTy (..)
  , getInfos
  , CodeTm(..), PCodeTm(..)
  ) where

import D_Calculus
import E2_Conv

--------------------------------------------------

data Icit = Impl | ImplClass | Expl

instance Tag Icit where
  tag Impl      = 0
  tag ImplClass = 1
  tag Expl      = 2

instance Ord Icit where
  compare = compareTag


-------------------------------------------------------------

{-# noinline lhsR #-}
lhsR :: Reader Bool
lhsR = topReader mainReset (pure False)

setLHS = local lhsR \_ -> True
askLHS = asks lhsR id

--------------------

isOnTop :: Mem Bool
isOnTop = askBoundVars <&> null

assertOnTop = isOnTop >>= \case
  True -> pure T0
  False -> fail "not on top level"

lookupDictF a = TGen $ "lookupDict"B :@. a

instanceMeta :: Mem TmTy
instanceMeta = do
  m <- freshMeta_
  m' <- evalEnv m
  pure (MkTmTy (lookupDictF m) m')


--------------------

-- glued version of evalEnv
evalEnvGlued n t = evalEnv t >>= glued n t

glued n t v = isOnTop >>= \case
  True -> vTm (nameStr n) t v
  _    -> pure v


---------------------------------------------

{-# noinline infoTableR #-}
infoTableR :: State (List (Tup2 SName Val))
infoTableR = topState mainReset $ pure Nil

addInfo n i = modify infoTableR (T2 n i :.)
getInfos = gets infoTableR id

---------------------------------------------

addGlobal cstr n v t m = do
  case cstr of
    True -> addInfo n t
    _ -> pure T0
  insertDef n (MkTmTy v t) m

defineBound :: SName -> Val -> Mem a -> Mem a
defineBound n t cont = addGlobal False n (TVar n) t . addBoundVar n . insertLocalVal n (WVar n) $ cont

defineGlob_ :: Maybe Bool -> Bool -> Bool -> Bool -> SName -> Tm -> Val -> Mem b -> Mem b
defineGlob_ cdef cstr haslet metatest n tv t_ co = do
  df <- deepForce =<< evalEnv tv
  v <- glued n tv df
  t <- deepForce t_
  top <- isOnTop
  case cdef of
    Just c | top -> addDef c n tv
    _ -> pure T0
  case top of
    True -> insertGlobalVal n v
    _ -> pure T0
  let co' = insertLocalVal n v co
  case T0 of
    _ | haslet  -> addGlobal cstr n (TVar n) t co'
      | not top -> addGlobal cstr n tv       t co'
      | metatest && not (rigid t)
        -> fail $ "meta in global definition:\n" <> print n <> " : " <> print t
      | metatest && not (rigid v), n /= "lookupDict"B, n /= "superClasses"B
        -> fail $ "meta in global definition:\n" <> print n <> " = " <> print v
      | closed v -> addGlobal cstr n (TVal v) t co'
      | True     -> fail $ "defineGlob: " <> print v

defineConstructor  = defineGlob_ (Just True) True  False True
defineGlob'        = defineGlob_ (Just True) False True  True
defineGlob         = defineGlob_ (Just True) False False True

rEmbed tt = do
  n <- nameOf "e"B
  insertDef n tt $ pure $ RVar n

----------------

matchCode :: Val -> Mem (Tup2 (Tm -> Mem Tm) Tm)
matchCode v = matchCon' 1 "Code"B v >>= \case
  Just (a :. Nil) -> quoteLets a <&> \a -> T2 pure a
  _ -> do
    MkTmVal tm m <- freshMeta'
    cm <- vApp "Code"B m
    f <- conv v cm
    pure (T2 f tm)

matchHPi v = matchCon' 2 "HPi"B v >>= \case
  Just (pa :. pb :. INil) -> pure $ Just (T3 Impl      pa pb)
  _ -> matchCon' 2 "CPi"B v >>= \case
    Just (pa :. pb :. INil) -> pure $ Just (T3 ImplClass pa pb)
    _ -> pure Nothing

-- True:   x: t      f x: Pi
-- False:  x: Pi     f x: t
matchPi :: Bool -> Icit -> Val -> Mem (Tup4 (Tm -> Mem Tm) Icit Val Val)
matchPi cov icit v = matchCon' 2 "Pi"B v >>= \case
  Just (pa :. pb :. INil) -> pure (T4 pure Expl      pa pb)
  _ -> matchHPi v >>= \case
    Just (T3 a b c) -> pure $ T4 pure a b c
    _ -> do
      MkTmVal _ m1 <- freshMeta'
      MkTmVal _ m2 <- freshMeta'
      let pi = case icit of Impl -> "HPi"B; Expl -> "Pi"B; _ -> $impossible
      v2 <- vApps pi (m1 :. m2 :. Nil)
      f <- case cov of
        True -> conv v v2
        _    -> conv v2 v
      pure (T4 f icit m1 m2)

getPi :: Scoped -> Maybe (Tup4 Tm SName Scoped Scoped)
getPi (RPi  (RVar n) a b) = Just (T4 "Pi"B  n a b)
getPi (RHPi (RVar n) a b) = Just (T4 "HPi"B n a b)
getPi _ = Nothing

insertH :: Mem TmTy -> Mem TmTy
insertH et = et >>= \(MkTmTy e t) -> matchHPi t >>= \case
  Nothing -> pure (MkTmTy e t)
  Just (T3 ImplClass a b) -> do
    a' <- quoteLets a
    insertH $ pure (MkTmTy (e :@. lookupDictF a') b)
  Just (T3 Impl _ b) -> do
    MkTmVal m vm <- freshMeta'
    t' <- vApp b vm
    insertH $ pure (MkTmTy ((:@.) e m) t')
  _ -> $undefined

typeName :: SName -> Mem SName
typeName = mapName (<> "_t")

unlam :: SName -> Val -> Mem (Tup2 Val Val)
unlam n' f = do
  let v = WVar n'
  t <- vApp f v
  pure (T2 v t)


---------------------------------------------

check :: Scoped -> Val -> Mem Tm
check r ty = do
  traceShow "4" $ "check " <> print r <> "\n :? " <> print ty
  tagError r $ lazy do
    t <- check_ r ty
    traceShow "5" $ "check end " <> print r <> "\n ==> " <> print t
    pure t

check_ :: Scoped -> Val -> Mem Tm
check_ r ty = case r of
  "_"B -> freshMeta
  RDot t -> askLHS >>= \case
    False -> $undefined
    _ -> do
      _t' <- check t ty  -- TODO: use t'
      TDot <$> freshMeta
  -- can this be in Conv?
  RPi "_"B a b | ty === "Ty"B {- TODO! matchCon -} -> do
    ta <- check a "Ty"B
    tb <- check b "Ty"B
    pure $ "Arr"B :@. ta :@. tb
  RHLam (RVar n) "_"B a -> do
    T4 f icit pa pb <- matchPi False Impl ty
    case icit of
      Impl -> do
        defineBound n pa do
          T2 _ t <- unlam n pb
          ta <- check a t
          f =<< tLam n ta
      ImplClass -> do
        defineBound n pa do   -- TODO: add superclasses to the env
          ta <- check a pb
          f =<< tLam n ta
      _ ->  $undefined
  RLam (RVar n) "_"B a -> do
    T4 f icit pa pb <- matchPi False Expl ty
    case icit of
      Expl -> do
        defineBound n pa do
          T2 _ t <- unlam n pb
          ta <- check a t
          f =<< tLam n ta
      Impl -> do
        n' <- lamName "z"B pb
        f =<< check (RHLam (RVar n') "_"B r) ty
      _ -> $undefined
  _ -> do
   lhs <- askLHS
   matchHPi ty >>= \case
    Just (T3 Impl _ pb) | not lhs -> do
      n' <- lamName "z"B pb
      check (RHLam (RVar n') "_"B r) ty
    Just (T3 ImplClass _ _) | not lhs -> do
      check (RHLam "h"B "_"B r) ty
    _ -> case r of
      RLet (RVar n) t a b -> do
        MkTmTy ta vta <- case t of
          "_"B -> infer a
          t -> do
            vta <- checkType n t
            ta <- check a vta
            pure (MkTmTy ta vta)
        T2 n tb <- defineGlob' n ta vta $ T2 n <$> check b ty
        pure $ TLet n ta tb
      ROLet (RVar n) t a b -> isOnTop >>= \case
       True -> do
        vta <- checkType n t
        ta <- check a vta
        let c = WCon n
        defineGlob n (TVal c) vta do
          tb <- check b ty
          T2 fa pa <- matchCode vta
          T2 fb pb <- matchCode ty
          fta <- fa ta
          ftb <- fb tb
          pure $ "TopLet"B :@. pa :@. pb :@. TVal c :@. fta :@. ftb
       False -> do
        vta <- checkType n t
        ta <- check a vta
        T2 n tb <- defineBound n vta do
          T2 n <$> check b ty
        T2 fa pa <- matchCode vta
        T2 fb pb <- matchCode ty
        fta <- fa ta
        l <- tLam n =<< fb tb
        pure $ "Let"B :@. pa :@. pb :@. fta :@. l
      r -> do
        MkTmTy a t <- insertH $ infer r
        f <- conv t ty
        f a

checkType n t = do
  tn <- typeName n
  check t "Type"B >>= evalEnvGlued tn

checkType' t = do
  check t "Type"B >>= evalEnv

------------------------------------------------------------------

infer :: Scoped -> Mem TmTy
infer r = do
  traceShow "6" $ "infer " <> print r
  tagError r $ lazy do
    tt@(MkTmTy t v) <- infer_ r
    traceShow "7" $ "infer end " <> print r <> "\n ==> " <> print t <> "\n :: " <> print v 
    pure tt

infer_ :: Scoped -> Mem TmTy
infer_ r = case r of
  RClass a b e -> tagError a $ lazy do
    assertOnTop
    let n = getVarName $ appHead $ codomain a
    vta <- checkType n "_"B
    let tc = WCon n
    ct <- defineGlob_ Nothing False False False n (TVal tc) vta $ checkType' a
    defineGlob' n (TVal tc) vta do
      T3 _is _ss _cc <- decomposeHead =<< deepForce ct
      inferMethods b \mts -> do
        T2 supers dt <- dictType ct $ map snd mts
        dname <- dictName n
        let dv = WCon dname
        defineGlob' dname (TVal dv) dt do
          addClass n (MkClassData tc dv supers mts) do
            forM_ (numberWith T2 0 mts) \(T2 i (T2 mname _)) -> lookupDef mname >>= \case
              Just (MkTmTy vf _) -> addDictSelector vf dname (1 + length supers + length mts) (1 + length supers + i)
              _ -> $impossible
            defineSuperclasses n tc dname (1 + length supers + length mts) supers
            infer e
  RInstance a b c -> do
    assertOnTop
    ct <- checkType' a
    T4 ns is n arg <- analyzeInstanceHead ct
    lookupClass n >>= \case
      Nothing ->  $undefined
      Just cd@(MkClassData _ _ _ mts) -> do
        fff (addMethodType ns is arg) mts \mns -> do
          addLookupDictRule cd ns is arg (map snd mns)
          let ns = fromListIM $ map fst mns
          let replaceName n = fromMaybe (lazy (error $ "invalid method: " <> pprint' n)) $ lookupIM n ns
          inferMethodBodies replaceName b
        infer c
  REnd -> pure (MkTmTy "Type"B "Type"B)
  RLam (RVar n) t a -> do
    vt <- checkType n t
    defineBound n vt do
      MkTmTy ta va <- insertH $ infer a
      f <- vLam n va
      MkTmTy <$> tLam n ta <*> vApps "Pi"B (vt :. f :. Nil)
  RHLam (RVar n) t a -> do
    vt <- checkType n t
    defineBound n vt do
      MkTmTy ta va <- infer a
      f <- vLam n va
      MkTmTy <$> tLam n ta <*> vApps "HPi"B (vt :. f :. Nil)
  "_"B -> do
    t <- freshMeta
    MkTmVal _ m <- freshMeta'
    pure (MkTmTy t m)
  "Type"B   -> pure $ MkTmTy "Type"B "Type"B
  RVar (RNat n)    -> vNat    (force n) <&> \v -> MkTmTy (TVal v) "Word"B
  RVar (RString n) -> vString (force n) <&> \v -> MkTmTy (TVal v) "String"B
  RVar n -> lookupDef n >>= \case
    Just res -> pure res
    _        -> fail $ "Not in scope: " <> print n
  RLetTy (RConstructor (RVar n)) t b -> do
    assertOnTop
    vta <- checkType n t
    defineConstructor n (TVal $ mkBuiltin n) vta $ infer b
  RLetTy (RVar n) t b -> do
    top <- isOnTop
    vta <- checkType n t
    v <- mkFun n <&> TVal
    f <- case top of
      True -> pure v
      _ -> do
        bv <- askBoundVars
        pure $ TApps v (TVar <$> bv)
    defineGlob n f vta $ infer b
  ROLet{} -> do
    MkTmVal _ m <- freshMeta'
    ty <- vApp "Code"B m
    t <- check r ty
    pure (MkTmTy t ty)
  RLet (RVar n) t a b -> do
    MkTmTy ta vta <- case t of
      "_"B -> infer a
      t -> do
        vta <- checkType n t
        ta <- check a vta
        pure (MkTmTy ta vta)
    MkTmTy tb vtb <- defineGlob' n ta vta $ infer b
    pure $ MkTmTy (TLet n ta tb) vtb
  RDec a c -> do
    traceShow "infer RDec" $ "RDec " <> pprint' a
    addRule' a
    infer c
  (getPi -> Just (T4 pi n@"_"B a b)) -> do
    ta <- check a "Type"B
    tb <- check b "Type"B >>= tLam n
    pure (MkTmTy (pi :@. ta :@. tb) "Type"B)
  (getPi -> Just (T4 pi n a b)) -> do
    ta <- check a "Type"B
    va <- typeName n >>= \tn -> evalEnvGlued tn ta
    defineBound n va do
      tb <- check b "Type"B
      l <- tLam n tb
      pure (MkTmTy (pi :@. ta :@. l) "Type"B)
  RCPi a b -> do
    ta <- check a "Type"B
    tb <- check b "Type"B
    pure (MkTmTy ("CPi"B :@. ta :@. tb) "Type"B)
  RIPi a b -> do
    ta <- check a "Type"B
    tb <- check b "Type"B
    pure (MkTmTy ("IPi"B :@. ta :@. tb) "Type"B)
  RGuard a b -> do
    tb <- check b "Bool"B
    MkTmTy ta ty <- infer a
    pure (MkTmTy (TGuard ta tb) ty)
  RView a b -> do
    MkTmTy ta ty <- infer a
    T4 f Expl pa pb <- matchPi True Expl ty
    n <- lamName "t"B pb
    defineBound n pa do
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
  _ -> fail "can't infer" -- <> pprint' r
 where
  inferApp i a b = infer a >>= \tt@(MkTmTy av ty) -> do
    T4 f icit pa pb <- matchPi True i ty
    fav <- f av
    case T0 of
     _ | ImplClass <- icit, Impl <- i -> do
        tb <- check b pa
        pure (MkTmTy (fav :@. tb) pb)
       | icit == i -> do
        tb <- check b pa
        n <- lamName "t"B pb
        v <- evalEnvGlued n tb
        b <- vApp pb v
        pure (MkTmTy (fav :@. tb) b)
       | Impl <- icit -> do
        v <- rEmbed $ MkTmTy av ty
        infer $ RApp (RHApp v "_"B) b
       | ImplClass <- icit -> do
        v <- rEmbed tt
        w <- rEmbed =<< instanceMeta
        infer $ RApp (RHApp v w) b
     _ -> fail "baj"

instance Parse TmTy where parse = parse >=> runMem . infer

instance Parse Tm where parse s = parse s <&> \(MkTmTy t _) -> t

data CodeTm = MkCodeTm Tm

instance Parse CodeTm where parse = parse >=> runMem . checkCode

checkCode r = do
  MkTmVal _ m1 <- freshMeta'
  t <- vApp "Code"B m1
  MkCodeTm <$> check r t

data PCodeTm = MkPCodeTm Tm

instance Parse PCodeTm where parse = parse >=> runMem . checkPCode

checkPCode r = do
  MkTmVal _ m1 <- freshMeta'
  t1 <- vApp "PCode"B "Computation"B
  t <- vApp t1 m1
  MkPCodeTm <$> check r t


----------------------------------------- tools for class elaboration

                          -- class dict superclasses methods
data ClassData = MkClassData Val   Val  (List Val)   (List (Tup2 SName Val))

-- TODO: switch to Ref
{-# noinline classR #-}
classR :: State (IntMap SName ClassData)
classR = topState mainReset $ pure emptyIM

addClass :: SName -> ClassData -> Mem a -> Mem a
addClass n d m = modify classR (insertIM n d) >> m

lookupClass n = gets classR (lookupIM n)


------------------------------

codomain = \case
  RPi _ _  e -> codomain e
  RHPi _ _ e -> codomain e
  RCPi _   e -> codomain e
  RIPi _   e -> codomain e
  t -> t

appHead = \case
  RApp  a _ -> appHead a
  RHApp a _ -> appHead a
  a -> a

getVarName = \case
  RVar n -> n
  _t -> $undefined

getHPi__ v = matchCon' 2 "HPi"B v <&> \case
    Just (a :. b :. Nil) -> Just (T2 a b)
    _ -> Nothing

getHPi_ :: SName -> Val -> Mem (Tup2 Val Val)
getHPi_ n v = getHPi__ v <&> fromMaybe (lazy $impossible) >>= \(T2 a b) -> vApp b (WVar n) <&> \b -> T2 a b

getHPi :: Val -> Mem (Maybe (Tup2 (Tup2 SName Val) Val))
getHPi v = getHPi__ v >>= \case
  Nothing -> pure Nothing
  Just (T2 a b) -> do
    n <- lamName "v"B b
    b <- vApp b $ WVar n
    pure $ Just (T2 (T2 n a) b)

getApp :: Val -> Mem (Maybe (Tup2 Val Val))
getApp v = forceVal v <&> \case
  WApp a b -> Just (T2 a b)
  _ -> Nothing

getConName :: Val -> Mem (Maybe SName)
getConName v = forceVal v <&> \case
  WCon n -> Just n
  _ -> Nothing

getMult f v = f v >>= \case
    Just (T2 c v) -> getMult f v <&> first (c:.)
    Nothing -> pure (T2 Nil v)

getSuper :: Val -> Mem (Maybe (Tup2 Val Val))
getSuper v = matchCon' 2 "CPi"B v <&> \case
    Just (a :. b :. Nil) -> Just (T2 a b)
    _ -> Nothing

mkHPi :: Tup2 SName Val -> Mem Val -> Mem Val
mkHPi (T2 n a) b = b >>= \b -> vLam n b >>= \b -> vApps "HPi"B (a :. b :. Nil)

mkCPi a b = b >>= \b -> vApps "CPi"B (a :. b :. Nil)

mkPi a b = b >>= \b -> vConst b >>= \b -> vApps "Pi"B (a :. b :. Nil)

mkMult :: (a -> Mem b -> Mem b) -> List a -> Mem b -> Mem b
mkMult f as m = foldr f m as

dictName :: SName -> Mem SName
dictName = mapName (<> "Dict")

dictType :: Val -> List Val -> Mem (Tup2 (List Val) Val)
dictType classTy methodTys = do
  T2 (T2 n parTy) classTy2 <- getHPi classTy <&> fromMaybe (lazy $impossible)
  T2 supers classTy'' <- getMult getSuper classTy2
  methodTys' <- forM methodTys \methodTy -> do
    T2 _ methodTy2 <- getHPi_ n methodTy
    T2 _ methodTy3 <- getSuper methodTy2 <&> fromMaybe (lazy $impossible)
    pure methodTy3
  t <- mkHPi (T2 n parTy) $ mkMult mkPi supers $ mkMult mkPi methodTys' $ pure classTy''
  supers' <- forM supers \s -> vLam n s
  pure (T2 supers' t)

fff :: (a -> (b -> Mem c) -> Mem c) -> List a -> (List b -> Mem c) -> Mem c
fff _ Nil cont = cont Nil
fff f (a:. as) cont = f a \b -> fff f as \bs -> cont (b:. bs)

addMethodType :: List (Tup2 SName Val) -> List Val -> Val -> Tup2 SName Val -> (Tup2 (Tup2 SName SName) Val -> Mem a) -> Mem a
addMethodType ns is arg (T2 n_ t) cont = do
  n <- mapName id n_
  T2 (T2 vn _) t <- getHPi t <&> fromMaybe (lazy $impossible)
  T2 _ t <- getSuper t <&> fromMaybe (lazy $impossible)
  f <- vLam vn t
  t <- mkMult mkHPi ns $ mkMult mkCPi is $ vApp f arg
  traceShow "methodbody" $ "addMethodType " <> pprint' n <> " : " <> print t
  v <- mkFun n <&> TVal
  mn <- evalEnvGlued n v
  defineGlob n v t $ cont (T2 (T2 n_ n) mn)

decomposeHead :: Val -> Mem (Tup3 (List (Tup2 SName Val)) (List Val) Val)
decomposeHead t = do
  T2 ns t <- getMult getHPi t
  T2 is t <- getMult getSuper t
  pure (T3 ns is t)

-- variables, instances, class name, arg type
analyzeInstanceHead :: Val -> Mem (Tup4 (List (Tup2 SName Val)) (List Val) SName Val)
analyzeInstanceHead t = do
  T2 ns t <- getMult getHPi t
  T2 is t <- getMult getSuper t
  T2 cn t <- getApp t <&> fromMaybe (lazy $impossible)
  cn <- getConName cn <&> fromMaybe (lazy $impossible)
  pure (T4 ns is cn t)

defineSuperclasses :: SName -> Val -> SName -> Word -> List Val -> Mem Tup0
defineSuperclasses nclass vclass dict num supers = do
  m <- nameOf "m"B
  let c = TVal vclass :@. TVar m
  ss <- forM (numberWith T2 0 $ map TVal supers) \(T2 i s) -> do
    sn <- nameOf =<< mapName (\s -> "sel" <> s <> showWord i) nclass
    sf <- mkFun sn <&> TVal
    addDictSelector sf dict num $ i + 1
    pure (T2 (s :@. TVar m) (sf :@. TVar m))
  let rhs = foldr (\(T2 a b) t -> "SuperClassCons"B :@. c :@. a :@. b :@. t) ("SuperClassNil"B :@. c) ss
  compileRule ("superClasses"B :@. c) rhs

inferMethods :: Scoped -> (List (Tup2 SName Val) -> Mem a) -> Mem a
inferMethods r cont = tagError r $ lazy case r of
  RLetTy (RVar n) t b -> do
    vta <- checkType n t
    f <- mkFun n <&> TVal
    defineGlob n f vta $ inferMethods b \mts -> cont $ T2 n vta :. mts
  REnd -> cont Nil
  _ -> fail "can't infer method"

inferMethodBodies :: (SName -> SName) -> Scoped -> Mem Tup0
inferMethodBodies replaceName r = tagError r $ lazy case r of
  RDec (mapHead replaceName -> a) c -> do
    traceShow "methodbody" $ "inferMethodBody " <> pprint' a
    addRule' a >> inferMethodBodies replaceName c
  REnd -> pure T0
  r -> fail $ ("can't infer method body :\n" <>) <$> print r

mapHead :: (SName -> SName) -> Scoped -> Scoped
mapHead g ee = ff ee where
  ff = \case
    RHPi a b x -> RHPi a b (ff x)
    RRule a x -> RRule (f a) x
    _ -> $undefined
  f = \case
    RGuard a b -> RGuard (f a) b
    RApp a b -> RApp (f a) b
    RVar n -> RVar (g n)
    _ -> error $ "mapHead: " <> pprint' ee

addLookupDictRule :: ClassData -> List (Tup2 SName Val) -> List Val -> Val -> List Val -> Mem Tup0
addLookupDictRule (MkClassData classVal dictVal supers _) (map fst -> ns) is_ arg_ mns = do
  arg <- quoteLets arg_
  arg' <- quoteNF arg_   -- ???
  is <- mapM quoteLets is_
  ds <- forM is \_ -> nameOf "d"B
  let rhs
        = tLets (zipWith T2 ds $ map ("lookupDict"B :@.) is)
        $ TApps (TVal dictVal)
        ( arg
        :.  (map TVal supers <&> \c -> "lookupDict"B :@. (c :@. arg))
        ++ (mns <&> \mn -> TApps (TVal mn) $ map TVar $ ns ++ ds)
        )
  compileRule ("lookupDict"B :@. (TVal classVal :@. arg')) rhs
  pure T0

------------------------------------------------

addRule' :: Scoped -> Mem Tup0
addRule' (RHPi (RVar n) "_"B a) = addName n $ addRule' a
addRule' (RRule a b) = do
  MkTmTy lhs vta <- insertH $ setLHS $ infer a
  bv <- askBoundVars
  T2 lhs' (T2 st' vs) <- runState (T2 emptyMap Nil) \st -> replaceMetas (Left st) bv lhs
  flip (foldr addName) (reverse vs) $ do
    rhs <- check b vta
--    traceShow "addRule checked rhs" $ pprint' rhs
    bv <- askBoundVars
    traceShow "replaceMetasRight" $ pprint' rhs
    rhs' <- replaceMetas (Right st') bv rhs
    traceShow "replaceMetasRight" $ pprint' rhs'
    compileRule lhs' rhs'
addRule' s = fail $ "invalid rule: " <> print s

addName :: SName -> Mem a -> Mem a
addName n cont = do
  MkTmVal _ m <- freshMeta'
  defineBound n m cont
