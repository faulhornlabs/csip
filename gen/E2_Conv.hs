
{-# LINE 1 "src/E2_Conv.hs" #-}
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
  ar <- vApp N133 =<< vApps N134 (m1' :. m2' :. Nil)
  f <- case cov of True -> conv ar v; False -> conv v ar
  pure (T3 f ma mb)

matchPArr :: Bool -> Val -> Mem (Tup4 (Tm -> Mem Tm) TmVal TmVal TmVal)
matchPArr cov v = do
  mp@(MkTmVal _ mp') <- freshMeta'
  ma@(MkTmVal _ m1') <- freshMeta'
  mb@(MkTmVal _ m2') <- freshMeta'
  ar <- vApps N135 (mp' :. m1' :. m2' :. Nil) >>= \v -> vApps N136 (N137 :. v :. Nil)
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

  match 0 N138 0 N139 (\INil INil -> do
      pure $ Just \t -> pure $ N133 :@. t) do

  match 0 N140 0 N139 (\INil INil -> do
      pure $ Just \t -> pure $ N141 :@. t) do

  match 1 N141 0 N139 (\case
    p :. INil -> \case
      INil -> do
        p' <- quoteLets p
        pure $ Just \t -> pure $ N136 :@. p' :@. t
    _ -> (impossible "src/E2_Conv.hs" 107)
    ) do

  match 0 N142 1 N133 (\INil -> \case
    m :. INil -> do
      unify m N143
      pure $ Just \t -> pure $ N125 :@. t
    _ -> (impossible "src/E2_Conv.hs" 114)
    ) do

  match 0 N142 2 N136 (\INil -> \case
    mp :. m :. INil -> do
      unify mp N144
      unify m N145
      pure $ Just \t -> pure $ N146 :@. t
    _ -> (impossible "src/E2_Conv.hs" 122)
    ) do

  match 0 N147 0 N148 (\INil INil -> do
    pure $ Just \t -> pure $ TVal N95 :@. t) do

  match 0 N147 1 N133 (\INil -> \case
    m :. INil -> do
      unify m N149
      pure $ Just \t -> pure $ N128 :@. t
    _ -> (impossible "src/E2_Conv.hs" 132)
    ) do

  match 0 N147 2 N136 (\INil -> \case
    mp :. m :. INil -> do
      unify mp N144
      unify m N150
      pure $ Just \t -> pure $ N151 :@. t
    _ -> (impossible "src/E2_Conv.hs" 140)
    ) do

  match 2 N61 2 N58 (\case
    m1 :. m2 :. INil -> \case
      m3 :. m4 :. INil -> do
        q <- conv_ m3 m1
        v <- lamName N152 m4
        defineBound v m3 do
          c2 <- vApp m4 $ WVar v
          h_v <- conv_ m2 c2
          m1' <- quoteLets m1
          m2' <- quoteLets m2
          pure $ case (T2 h_v q) of
            T2 Nothing Nothing -> Just \t -> pure $ N153 :@. m1' :@. m2' :@. t
            _ -> Just \t -> tLam v =<< evalId h_v =<< (:@.) (N153 :@. m1' :@. m2' :@. t) <$> evalId q (TVar v)
      _ -> (impossible "src/E2_Conv.hs" 156)
    _ -> (impossible "src/E2_Conv.hs" 157)
    ) do

  match 2 N58 2 N58 (\case
    m1 :. m2 :. INil -> \case
      m3 :. m4 :. INil -> do
        q <- conv_ m3 m1
        v <- lamName N152 m2
        defineBound v m3 do
          q_v <- evalEnv =<< evalId q (TVar v)
          c1 <- vApp m2 q_v
          c2 <- vApp m4 $ WVar v
          h_v <- conv_ c1 c2
          pure $ case T2 h_v q of
            T2 Nothing Nothing -> Nothing
            _ -> Just \t -> tLam v =<< evalId h_v =<< (:@.) t <$> evalId q (TVar v)
      _ -> (impossible "src/E2_Conv.hs" 173)
    _ -> (impossible "src/E2_Conv.hs" 174)
    ) do

  match 1 N133 2 N58 (\_ -> \case
    m3 :. m4 :. INil -> do
      T3 f (MkTmVal m1 m1') (MkTmVal m2 m2') <- matchArr False a
      c1 <- vApp N133 m1'
      q <- conv_ m3 c1
      v <- lamName N152 m4
      defineBound v m3 do
        c2 <- vApp N133 m2'
        m4_v <- vApp m4 (WVar v)
        h_v <- conv_ c2 m4_v
        let lam t = case T2 h_v q of
              T2 Nothing Nothing -> pure t
              _ -> tLam v =<< evalId h_v =<< (:@.) t <$> evalId q (TVar v)
        pure $ Just \t -> f t >>= \t -> lam $ N57 :@. m1 :@. m2 :@. t
    _ -> (impossible "src/E2_Conv.hs" 191)
    ) do

  match 2 N136 2 N58 (\case
    p :. _ :. INil -> \case
      m3 :. m4 :. INil -> do
        unify p N137
        T4 f (MkTmVal mp mp') (MkTmVal m1 m1') (MkTmVal m2 m2') <- matchPArr False a
        c1 <- vApp N136 N144 >>= \v -> vApp v m1'
        q <- conv_ m3 c1
        v <- lamName N152 m4
        defineBound v m3 do
          c2 <- vApp N136 mp' >>= \v -> vApp v m2'
          m4_v <- vApp m4 (WVar v)
          h_v <- conv_ c2 m4_v
          let lam t = case T2 h_v q of
                T2 Nothing Nothing -> pure t
                _ -> tLam v =<< evalId h_v =<< (:@.) t <$> evalId q (TVar v)
          pure $ Just \t -> f t >>= \t -> lam $ N154 :@. mp :@. m1 :@. m2 :@. t
      _ -> (impossible "src/E2_Conv.hs" 210)
    _ -> (impossible "src/E2_Conv.hs" 211)
    ) do

  match 2 N58 1 N133 (\case
    m3 :. m4 :. INil -> \_ -> do
      T3 f (MkTmVal m1 m1') (MkTmVal m2 m2') <- matchArr True b
      c1 <- vApp N133 m1'
      q <- conv_ c1 m3
      v <- lamName N152 m4
      defineBound v c1 do
        qv <- evalEnv =<< evalId q (TVar v)
        c2 <- vApp N133 m2'
        m4_qv <- vApp m4 qv
        h_v <- conv_ m4_qv c2
        let lam t = case T2 h_v q of
              T2 Nothing Nothing -> pure t
              _ -> tLam v =<< evalId h_v =<< (:@.) t <$> evalId q (TVar v)
        pure $ Just \t -> lam t >>= \t -> f $ N112 :@. m1 :@. m2 :@. t
    _ -> (impossible "src/E2_Conv.hs" 229)
    ) do

  match 2 N58 2 N136 (\case
    m3 :. m4 :. INil -> \case
      p :. _ :. INil -> do
        unify p N137
        T4 f (MkTmVal mp mp') (MkTmVal m1 m1') (MkTmVal m2 m2') <- matchPArr True b
        c1 <- vApps N136 (N144 :. m1' :. Nil)
        q <- conv_ c1 m3
        v <- lamName N152 m4
        defineBound v c1 do
          qv <- evalEnv =<< evalId q (TVar v)
          c2 <- vApps N136 (mp' :. m2' :. Nil)
          m4_qv <- vApp m4 qv
          h_v <- conv_ m4_qv c2
          let lam t = case T2 h_v q of
                T2 Nothing Nothing -> pure t
                _ -> tLam v =<< evalId h_v =<< (:@.) t <$> evalId q (TVar v)
          pure $ Just \t -> lam t >>= \t -> f $ N155 :@. mp :@. m1 :@. m2 :@. t
      _ -> (impossible "src/E2_Conv.hs" 249)
    _ -> (impossible "src/E2_Conv.hs" 250)
    ) do

  unify a b
  pure Nothing
