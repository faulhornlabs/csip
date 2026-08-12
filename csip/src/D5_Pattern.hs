module D5_Pattern
  ( PTm (TView, TGuard, TDot), compileRule, replaceMetas, addDictSelector, metaArgNum
  ) where

import C_Syntax
import D1_Combinator
import D2_Tm
import D3_Val
import D4_Eval

-------------------------------

tOLam :: SName -> Tm -> Mem Tm
tOLam n t = tLam n t <&> \t -> "Lam"B :@. tErased :@. tErased :@. t

tOLams :: List SName -> Tm -> Mem Tm
tOLams Nil t = pure t
tOLams (n:. ns) t = tLams ns t >>= tOLam n

tOLet :: SName -> Tm -> Tm -> Mem Tm
tOLet n a b = do
  f <- tLam n b
  pure $ "Let"B :@. tErased :@. tErased :@. a :@. f

tOApp a b = "App"B :@. tErased :@. tErased :@. a :@. b

tErased = TVal "Erased"B

tLazy :: Tm -> Mem Tm
tLazy = tLam "_"B

tForce :: Tm -> Mem Tm
--tForce (dup -> T2 (TSup c _) (TLam g)) | isConstComb c = g <&> snd
tForce x = pure $ x :@. "X"B

tOLazy :: Tm -> Mem Tm
tOLazy = tOLam "_"B

tOForce :: Tm -> Mem Tm
--tOForce ("Lam"B :@. _ :@. _ :@. (dup -> T2 (TSup c _) (TLam g))) | isConstComb c = g <&> snd
tOForce x = pure $ tOApp x "X"B


pattern TRet   a       = "TRet"B  :@. a
pattern TView  a b     = "View"B  :@. a :@. b
pattern TGuard a b     = "Guard"B :@. a :@. b
pattern TDot   a       = "Dot"B   :@. a
pattern TMatch a b c d = b :@. ("TMatch"B :@. TVal (WCon a) :@. c :@. d)


updateRule :: SName -> RuleRef -> Tm -> Val -> Mem Tup0
{- TODO!
updateRule fn _ _ b
  | not (rigid b), fn /= "lookupDict"B, fn /= "superClasses"B
  = fail $ "rule body is not rigid:\n" <> print fn <> " = " <> print b
-}
updateRule _fn r t b = do
  addDef False (name b) t
  updateRule_ r b

compileRule :: Tm -> Tm -> Mem Tup0
compileRule lhs rhs = do
  T2 fn r <- getFun lhs
  T0 <- runState emptyIM (linear lhs) >>= \case
    T2 (Just a) _ -> fail $ "non-linear lhs: " <> print a
    _ -> pure T0
  old <- lookupRule r
  new <- compileOLHS lhs (TVal old) \_ -> pure rhs
  v <- deepForce =<< evalClosed new
  updateRule fn r new =<< vTm (nameStr fn) new v
  pure T0
 where

  getFun = \case
    TVal (WFun fn r) -> pure $ T2 fn r
    TGuard a _ -> getFun a
    TVal ("App"B) :@. _ :@. _ :@. a :@. _ -> getFun a
    (:@.) a _ -> getFun a
    TVar n -> tagError n $ lazy (fail $ "not in scope: " <> print n)  -- TODO: better highlighting
    _ -> $impossible

  linear t st = f t  where
    f :: Tm -> Mem (Maybe SName)
    f = \case
      TVal{} -> pure Nothing
      TDot{} -> pure Nothing
      TView _ b -> f b
      TGuard a _ -> f a
      TVar n -> gets st (memberIS n) >>= \case
        True -> pure $ Just n
        _ -> modify st (insertIS n) >> pure Nothing
      (:@.) a b -> f a >>= \case
        r@Just{} -> pure r
        _        -> f b
      _ -> $undefined

  compileOLHS :: Tm -> Tm -> (Tm -> Mem Tm) -> Mem Tm
  compileOLHS e old rhsf = case e of
    TVal ("App"B) :@. _ :@. _ :@. a :@. pat -> compileOLHS a old \fail -> do
      n  <- nameOf $ case pat of TVar m -> nameStr m; _ -> "v"B
      fn <- nameOf "fail"B
      ff <- tOForce fail
      tx <- tOLazy $ tOApp ff (TVar n)
      (tOLam n =<< tOLet fn tx =<< compilePat' (TVar fn) pat (TVar n) =<< rhsf (TVar fn))
    e -> compileLHS e old \fail -> do
      ff <- tOLazy =<< ("matchRet"B :@.) <$> tForce fail
      TRet <$> rhsf ff
      -- e ==>{old} rhsf       ~~> e ==>{old} \fail -> Ret $ rhsf $ olazy $ noRet $ force fail

      --  App a pat ==>{old} rhsf
      --         ~~>
      --  a ==>{old} \fail ~> \n -> fn := \tok -> fail tok n; pat <-{fn} n; rhsf fn

  compileLHS :: Tm -> Tm -> (Tm -> Mem Tm) -> Mem Tm
  compileLHS e old rhsf = case e of
    TGuard a e -> compileLHS a old \fail -> do
      tx <- pure fail
      compilePat tx "True"B e =<< rhsf fail
    (:@.) a pat -> compileLHS a old \fail -> do
      n  <- nameOf $ case pat of TVar m -> nameStr m; _ -> "v"B
      fn <- nameOf "fail"B
      ff <- tForce fail
      tx <- tLazy $ (:@.) ff $ TVar n
      tLam n =<< TLet fn tx <$> (compilePat (TVar fn) pat (TVar n) =<< rhsf (TVar fn))
      -- \n -> fn = lazy (force fail n); pat <-{fn} n; rhsf fn
    _ -> rhsf =<< tLazy old

  compilePat :: Tm -> Tm -> Tm -> Tm -> Mem Tm
  compilePat f p e m = case p of
    TDot{} -> pure m
    TVar n -> pure $ TLet n e m
    TView g p -> compilePat f p ((:@.) g e) m
    TApps (TVal (WCon c)) ps -> do
      let len = length ps
      ns <- mapM nameOf $ replicate len "v"B   -- TODO: better naming
      x <- foldr (\(T2 a b) m -> m >>= \x -> compilePat f a b x) (pure m) $ zipWith T2 ps $ map TVar ns
      tx <- tLazy x
      ne <- nameOf "v"B   -- TODO: better naming
      mok <- tLams ns tx
      pure $ TLet ne e $ TMatch c (TVar ne) mok f
    TApps (TVal _) (_:._) -> $undefined
    TApps v (_:._) -> fail $ "compilePat: " <> pprint' v
    p -> fail $ "TODO (13):\n  " <> print p <> "\n... =\n  " <> print rhs

  compilePat' :: Tm -> Tm -> Tm -> Tm -> Mem Tm
  compilePat' f p e m = case p of
    TDot{} -> pure m
    TVar n -> tOLet n e m
    TView g p -> compilePat' f p ((:@.) g e) m
    TApps (TVal (con@WCon{})) ps -> do
      let len = length ps
      ns <- mapM nameOf $ replicate len "v"B   -- TODO: better naming
      x <- foldr (\(T2 a b) m -> m >>= \x -> compilePat' f a b x) (pure m) $ zipWith T2 ps $ map TVar ns
      tx <- tOLazy x
      ne <- nameOf "v"B   -- TODO: better naming
      mok <- tOLams ns tx
      tOLet ne e $ "Match"B :@. TVal con :@. TVar ne :@. mok :@. f
    TApps (TVal _) (_:._) -> $undefined
    TApps v (_:._) -> fail $ "compilePat': " <> pprint' v
    p -> fail $ "TODO (23):\n  " <> print p <> "\n... =\n  " <> print rhs

addDictSelector :: Tm -> SName -> Word -> Word -> Mem Tup0
addDictSelector (TVal (WFun fn r)) dict args i = do
  old <- lookupRule r
  w <- nameOf "_"B
  d <- nameOf "d"B
  lold <- tLazy $ TVal old :@. TVar w :@. TVar d
  ns <- mapM nameOf $ replicate args "v"B -- TODO: better naming
  body <- tLams ns =<< tLazy (TRet $ TVar $ fromMaybe (lazy $impossible) $ ns !! i)
  f <- tLam d $ TMatch dict (TVar d) body lold
  new <- tLam w f
  v <- evalClosed new
  updateRule dict r new =<< vTm (nameStr fn) new v
addDictSelector _ _ _ _ = $impossible

--------------------------------

type MTT = Map Tm Tm

-- TODO: rewrite completely
replaceMetas :: Either (State (Tup2 MTT (List SName))) MTT -> List SName -> Tm -> Mem Tm
replaceMetas get_ bv tt = do
  traceShow "" $ "replaceMetas " <> print tt
  runReader bv ff
 where
  ff rst = f get_ tt  where

    eval' t = asks rst id >>= \bv -> eval "replaceMetas" (fromListIM (bv <&> \n -> T2 n (WVar n))) t

    f get t = case t of
      TView a b
        | Left st <- get -> gets st fst >>= \m -> TView <$> f (Right m) a <*> f get b
      TView _ _ -> $undefined
      TVal ("WSuc"B) :@. n
        | Left{} <- get       -> f get n <&> \r -> TView "SuccView"B ("WSucOk"B :@. r)
      TVal ("WSuc"B) :@. n
        -> f get n >>= \r -> vNat 1 <&> \one -> "AddWord"B :@. TVal one :@. r
      TVal ("ConsStr"B) :@. a :@. b | Left{} <- get -> f get a >>= \a -> f get b <&> \b -> TView "ConsView"B ("ConsOk"B :@. a :@. b)
      TVal (WNat{})    | Left{} <- get -> pure $ TView ("EqWord"B :@. t) "True"B
      TVal (WString{}) | Left{} <- get -> pure $ TView ("EqStr"B  :@. t) "True"B
      TVal ("MkOString"B) :@. _ | Left{} <- get -> pure $ TView ("OEqStr"B  :@. t) "OTrue"B
      TVal ("MkOWord"B)   :@. _ | Left{} <- get -> pure $ TView ("OEqWord"B :@. t) "OTrue"B

      TVal v_ -> deepForce v_ >>= \case
        v | closed v -> pure $ TVal v
          | True     -> $undefined
      TVar{} -> pure t
      TDot t | Left{} <- get -> do
        eval' t >>= metaToVar False ("TODO (34):\n" <> print t) <&> TDot
      TDot{} -> $impossible
      TLet n a b -> TLet n <$> f get a <*> local rst (n :.) (f get b)
      TGen t -> eval' t >>= forceVal >>= \vns -> case get of
        Left st -> case vns of
           WMeta d -> do
             n <- nameOf "v"B
             traceShow "" ("meta->var " <> print n <> "\n := " <> print n)
             update d $ WVar n
             modify st $ second (n:.)
             pure $ TVar n
           WApp_ _ _ (MetaApp _ d) -> do
             n <- nameOf "v"B
             traceShow "" ("meta->var2 " <> print n <> "\n := " <> print n)
             num <- metaArgNum vns
             ns <- mapM nameOf $ replicate num "v"B
             update d =<< vLams ns (WVar n)
             modify st $ second (n:.)
             pure $ TVar n
           WApp ff d | ff === "lookupDict"B -> do
             t <- metaToVar True (("TODO (22):\n" <>) <$> print vns) vns
             n <- nameOf "v"B
             modify st $ first $ insertMap t $ TVar n
             traceShow "" $ "addSuperClasses " <> print d
             addSuperClasses st (WVar n) d
             pure $ TVar n
           _ -> do
             t <- metaToVar True (("TODO (22):\n" <>) <$> print vns) vns
             pure $ TDot t

        Right m -> do
            ns <- metaToVar False (pure "TODO (20)") vns
            let lo = lookupMap ns m
            case lo of
              Nothing -> traceShow "" ("missed lookup: " <> pprint' ns)
              _ -> pure T0
            pure $ TGen $ fromMaybe' ns lo
      a :@. b -> (:@.) <$> f get a <*> f get b
      TSup c ts | rigid c  -> TSup c <$> mapM (f get) ts
      TLam g -> g >>= \(T2 n t) -> tLam n =<< local rst (n :.) (f get t)

     where
      addSuperClasses st v d = do
        r <- getProjections =<< vApp "superClasses"B d
        forM_ r \(T2 a b) -> do
          a' <- quote =<< vApp "lookupDict"B a
          vv <- vApp b v
          b' <- quote vv
          traceShow "" ("superClass " <> pprint' a' <> "\n  --> " <> print b')
          modify st $ first $ insertMap a' b'
          addSuperClasses st vv a

      quote = metaToVar False (pure "TODO (21)")

      metaToVar :: Bool -> Mem String -> Val -> Mem Tm
      metaToVar pat err = f where
       f v_ = forceVal v_ >>= \w -> case w of
        WMeta{}    | pat -> pure $ TVar $ name w
--        WApp_ _ _ MetaApp{} | pat -> pure $ TVal w
        WMeta{}    -> fail err
--        WApp_ _ _ MetaApp{} -> fail err
        WApp a b   -> (:@.) <$> f a <*> f b
        WFun{}     -> pure $ TVal w
        WVar n     -> pure $ TVar n
        WSup _ c vs | rigid c -> TSup c <$> mapM f vs
        WSup _ c vs | Just m <- varName c -> do
          n <- m
          t <- evalCombinator c vs $ WVar n
          tLam n =<< f t
        _ | closed w && rigid w -> pure $ TVal w
        w -> fail $ "TODO(1): " <> print w

getProjections :: Val -> Mem (List (Tup2 Val Val))
getProjections v = matchCon' 4 "SuperClassCons"B v >>= \case
  Just (_ :. a :. b :. tl :. INil) -> (T2 a b :.) <$> getProjections tl
  _ -> matchCon' 1 "SuperClassNil"B v >>= \case
    Just (_ :. INil) -> pure Nil
    _ -> $undefined

metaArgNum v_ = forceVal v_ >>= \case
  WMeta _     -> pure 0
  WApp_ a _ MetaApp{} -> (+1) <$> metaArgNum a
  _ -> $undefined
