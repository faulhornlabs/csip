module E2_Conv
  ( conv
  , TmVal (MkTmVal)
  , addBoundVar, askBoundVars, freshMeta, freshMeta_, freshMeta'
  , insertLocalVal, evalEnv
  ) where

import D_Calculus
import E1_Unify

-------------

data TmVal = MkTmVal Tm Val   -- the same value in two different representation

--------------

{-# noinline bvR #-}
bvR :: Reader (List SName)
bvR = topReader mainReset (pure Nil)

addBoundVar n = local bvR (n :.)
askBoundVars = asks bvR id

freshMeta_ :: Mem Tm
freshMeta_ = do
  m <- tMeta
  bv <- askBoundVars
  pure $ TApps m $ reverse $ map TVar bv

freshMeta :: Mem Tm
freshMeta = TGen <$> freshMeta_

freshMeta' :: Mem TmVal
freshMeta' = do
  m <- freshMeta
  MkTmVal m <$> evalEnv m

matchArr :: Bool -> Val -> Mem (Tup3 (Tm -> Mem Tm) TmVal TmVal)
matchArr cov v = do
  ma@(MkTmVal _ m1') <- freshMeta'
  mb@(MkTmVal _ m2') <- freshMeta'
  ar <- vApp "Code"B =<< vApps "Arr"B (m1' :. m2' :. Nil)
  f <- case cov of True -> conv ar v; False -> conv v ar
  pure (T3 f ma mb)

matchPArr :: Bool -> Val -> Mem (Tup4 (Tm -> Mem Tm) TmVal TmVal TmVal)
matchPArr cov v = do
  mp@(MkTmVal _ mp') <- freshMeta'
  ma@(MkTmVal _ m1') <- freshMeta'
  mb@(MkTmVal _ m2') <- freshMeta'
  ar <- vApps "PArr"B (mp' :. m1' :. m2' :. Nil) >>= \v -> vApps "PCode"B ("Computation"B :. v :. Nil)
  f <- case cov of True -> conv ar v; False -> conv v ar
  pure (T4 f mp ma mb)

--------------------

{-# noinline localsR #-}
localsR :: Reader (IntMap SName Val)
localsR = topReader mainReset (pure emptyIM)

insertLocalVal n v = local localsR (insertIM n v)
getLocalVals = asks localsR id

evalEnv :: Tm -> Mem Val
evalEnv t = getLocalVals >>= \ls -> eval "env" ls t


---------------------------------------------

defineBound :: SName -> Val -> Mem a -> Mem a
defineBound n _t cont = {-addGlobal False n (TVar n) t . -} addBoundVar n . insertLocalVal n (WVar n) $ cont

------------------------------------------------------

evalId :: Maybe (a -> Mem a) -> a -> Mem a
evalId = fromMaybe' pure

conv
  :: Val                  -- actual type
  -> Val                  -- expected type
  -> Mem (Tm -> Mem Tm) -- transformation from actual to expected
conv a b = evalId <$> conv_ a b

conv_
  :: Val
  -> Val
  -> Mem (Maybe (Tm -> Mem Tm))
conv_ a b = do
  let
    match na ca nb cb m next = matchCon' na ca a >>= \case
      Nothing -> next
      Just as -> matchCon' nb cb b >>= \case
        Nothing -> next
        Just bs -> m as bs

  match 0 "Ty"B 0 "Type"B (\INil INil -> do
      pure $ Just \t -> pure $ "Code"B :@. t) do

  match 0 "Polarity"B 0 "Type"B (\INil INil -> do
      pure $ Just \t -> pure $ "PTy"B :@. t) do

  match 1 "PTy"B 0 "Type"B (\case
    p :. INil -> \case
      INil -> do
        p' <- quoteLets p
        pure $ Just \t -> pure $ "PCode"B :@. p' :@. t
    _ -> $impossible
    ) do

  match 0 "String"B 1 "Code"B (\INil -> \case
    m :. INil -> do
      unify m "OString"B
      pure $ Just \t -> pure $ "MkOString"B :@. t
    _ -> $impossible
    ) do

  match 0 "String"B 2 "PCode"B (\INil -> \case
    mp :. m :. INil -> do
      unify mp "Value"B
      unify m "PString"B
      pure $ Just \t -> pure $ "MkPString"B :@. t
    _ -> $impossible
    ) do

  match 0 "Word"B 0 "Nat"B (\INil INil -> do
    pure $ Just \t -> pure $ TVal "wordToNat"B :@. t) do

  match 0 "Word"B 1 "Code"B (\INil -> \case
    m :. INil -> do
      unify m "OWord"B
      pure $ Just \t -> pure $ "MkOWord"B :@. t
    _ -> $impossible
    ) do

  match 0 "Word"B 2 "PCode"B (\INil -> \case
    mp :. m :. INil -> do
      unify mp "Value"B
      unify m "PWord"B
      pure $ Just \t -> pure $ "MkPWord"B :@. t
    _ -> $impossible
    ) do

  match 2 "IPi"B 2 "Pi"B (\case
    m1 :. m2 :. INil -> \case
      m3 :. m4 :. INil -> do
        q <- conv_ m3 m1
        v <- lamName "z"B m4
        defineBound v m3 do
          c2 <- vApp m4 $ WVar v
          h_v <- conv_ m2 c2
          m1' <- quoteLets m1
          m2' <- quoteLets m2
          pure $ case (T2 h_v q) of
            T2 Nothing Nothing -> Just \t -> pure $ "Ap"B :@. m1' :@. m2' :@. t
            _ -> Just \t -> tLam v =<< evalId h_v =<< (:@.) ("Ap"B :@. m1' :@. m2' :@. t) <$> evalId q (TVar v)
      _ -> $impossible
    _ -> $impossible
    ) do

  match 2 "Pi"B 2 "Pi"B (\case
    m1 :. m2 :. INil -> \case
      m3 :. m4 :. INil -> do
        q <- conv_ m3 m1
        v <- lamName "z"B m2
        defineBound v m3 do
          q_v <- evalEnv =<< evalId q (TVar v)
          c1 <- vApp m2 q_v
          c2 <- vApp m4 $ WVar v
          h_v <- conv_ c1 c2
          pure $ case T2 h_v q of
            T2 Nothing Nothing -> Nothing
            _ -> Just \t -> tLam v =<< evalId h_v =<< (:@.) t <$> evalId q (TVar v)
      _ -> $impossible
    _ -> $impossible
    ) do

  match 1 "Code"B 2 "Pi"B (\_ -> \case
    m3 :. m4 :. INil -> do
      T3 f (MkTmVal m1 m1') (MkTmVal m2 m2') <- matchArr False a
      c1 <- vApp "Code"B m1'
      q <- conv_ m3 c1
      v <- lamName "z"B m4
      defineBound v m3 do
        c2 <- vApp "Code"B m2'
        m4_v <- vApp m4 (WVar v)
        h_v <- conv_ c2 m4_v
        let lam t = case T2 h_v q of
              T2 Nothing Nothing -> pure t
              _ -> tLam v =<< evalId h_v =<< (:@.) t <$> evalId q (TVar v)
        pure $ Just \t -> f t >>= \t -> lam $ "App"B :@. m1 :@. m2 :@. t
    _ -> $impossible
    ) do

  match 2 "PCode"B 2 "Pi"B (\case
    p :. _ :. INil -> \case
      m3 :. m4 :. INil -> do
        unify p "Computation"B
        T4 f (MkTmVal mp mp') (MkTmVal m1 m1') (MkTmVal m2 m2') <- matchPArr False a
        c1 <- vApp "PCode"B "Value"B >>= \v -> vApp v m1'
        q <- conv_ m3 c1
        v <- lamName "z"B m4
        defineBound v m3 do
          c2 <- vApp "PCode"B mp' >>= \v -> vApp v m2'
          m4_v <- vApp m4 (WVar v)
          h_v <- conv_ c2 m4_v
          let lam t = case T2 h_v q of
                T2 Nothing Nothing -> pure t
                _ -> tLam v =<< evalId h_v =<< (:@.) t <$> evalId q (TVar v)
          pure $ Just \t -> f t >>= \t -> lam $ "PApp"B :@. mp :@. m1 :@. m2 :@. t
      _ -> $impossible
    _ -> $impossible
    ) do

  match 2 "Pi"B 1 "Code"B (\case
    m3 :. m4 :. INil -> \_ -> do
      T3 f (MkTmVal m1 m1') (MkTmVal m2 m2') <- matchArr True b
      c1 <- vApp "Code"B m1'
      q <- conv_ c1 m3
      v <- lamName "z"B m4
      defineBound v c1 do
        qv <- evalEnv =<< evalId q (TVar v)
        c2 <- vApp "Code"B m2'
        m4_qv <- vApp m4 qv
        h_v <- conv_ m4_qv c2
        let lam t = case T2 h_v q of
              T2 Nothing Nothing -> pure t
              _ -> tLam v =<< evalId h_v =<< (:@.) t <$> evalId q (TVar v)
        pure $ Just \t -> lam t >>= \t -> f $ "Lam"B :@. m1 :@. m2 :@. t
    _ -> $impossible
    ) do

  match 2 "Pi"B 2 "PCode"B (\case
    m3 :. m4 :. INil -> \case
      p :. _ :. INil -> do
        unify p "Computation"B
        T4 f (MkTmVal mp mp') (MkTmVal m1 m1') (MkTmVal m2 m2') <- matchPArr True b
        c1 <- vApps "PCode"B ("Value"B :. m1' :. Nil)
        q <- conv_ c1 m3
        v <- lamName "z"B m4
        defineBound v c1 do
          qv <- evalEnv =<< evalId q (TVar v)
          c2 <- vApps "PCode"B (mp' :. m2' :. Nil)
          m4_qv <- vApp m4 qv
          h_v <- conv_ m4_qv c2
          let lam t = case T2 h_v q of
                T2 Nothing Nothing -> pure t
                _ -> tLam v =<< evalId h_v =<< (:@.) t <$> evalId q (TVar v)
          pure $ Just \t -> lam t >>= \t -> f $ "PLam"B :@. mp :@. m1 :@. m2 :@. t
      _ -> $impossible
    _ -> $impossible
    ) do

  unify a b
  pure Nothing
