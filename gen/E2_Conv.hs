
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

matchArr :: Val -> Mem (Tup3 (Tm -> Mem Tm) TmVal TmVal)
matchArr v = matchCon' 2 N133 v >>= \case
  Just (a :. b :. Nil) -> T3 pure <$> (MkTmVal <$> quoteLets a <*> pure a) <*> (MkTmVal <$> quoteLets b <*> pure b)
  _ -> do
    ma@(MkTmVal _ m1') <- freshMeta'
    mb@(MkTmVal _ m2') <- freshMeta'
    ar <- vApp N134 =<< vApps N133 (m1' :. m2' :. Nil)
    f <- conv ar v
    pure (T3 f ma mb)

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

  match 0 N135 0 N136 (\INil INil -> do
      pure $ Just \t -> pure $ N134 :@. t) do

  match 0 N137 1 N134 (\INil -> \case
    m :. INil -> do
      unify m N138
      pure $ Just \t -> pure $ N125 :@. t
    _ -> (impossible "src/E2_Conv.hs" 96)
    ) do

  match 0 N139 0 N140 (\INil INil -> do
    pure $ Just \t -> pure $ TVal N95 :@. t) do

  match 0 N139 1 N134 (\INil -> \case
    m :. INil -> do
      unify m N141
      pure $ Just \t -> pure $ N128 :@. t
    _ -> (impossible "src/E2_Conv.hs" 106)
    ) do

  match 2 N61 2 N58 (\case
    m1 :. m2 :. INil -> \case
      m3 :. m4 :. INil -> do
        q <- conv_ m3 m1
        v <- lamName N142 m4
        defineBound v m3 do
          c2 <- vApp m4 $ WVar v
          h_v <- conv_ m2 c2{- m4 v -}
          m1' <- quoteLets m1
          m2' <- quoteLets m2
          pure $ case (T2 h_v q) of
            T2 Nothing Nothing -> Just \t -> pure $ N143 :@. m1' :@. m2' :@. t
            _ -> Just \t -> tLam v =<< evalId h_v =<< (:@.) (N143 :@. m1' :@. m2' :@. t) <$> evalId q (TVar v)
      _ -> (impossible "src/E2_Conv.hs" 122)
    _ -> (impossible "src/E2_Conv.hs" 123)
    ) do

  match 2 N58 2 N58 (\case
    m1 :. m2 :. INil -> \case
      m3 :. m4 :. INil -> do
        q <- conv_ m3 m1
        v <- lamName N142 m2
        defineBound v m3 do
          q_v <- evalEnv =<< evalId q (TVar v)
          c1 <- vApp m2 q_v
          c2 <- vApp m4 $ WVar v
          h_v <- conv_ c1{- m2 (q v) -} c2{- m4 v -}
          pure $ case T2 h_v q of
            T2 Nothing Nothing -> Nothing
            _ -> Just \t -> tLam v =<< evalId h_v =<< (:@.) t <$> evalId q (TVar v)
      _ -> (impossible "src/E2_Conv.hs" 139)
    _ -> (impossible "src/E2_Conv.hs" 140)
    ) do

  match 1 N134 2 N58 (\_ -> \case
    m3 :. m4 :. INil -> do
      T3 f (MkTmVal m1 m1') (MkTmVal m2 m2') <- matchArr a
      c1 <- vApp N134 m1'
      q <- conv_ m3 c1{- Code m1 -}
      v <- lamName N142 m4
      defineBound v c1 do
        c2 <- vApp N134 m2'
        m4_v <- vApp m4 (WVar v)
        h_v <- conv_ c2{- Code m2 -} m4_v  --  (Code m1 -> Code m2)  ==>  (Code m1 -> m4)
        let lam t = case T2 h_v q of
              T2 Nothing Nothing -> pure t
              _ -> tLam v =<< evalId h_v =<< (:@.) t <$> evalId q (TVar v)
        pure $ Just \t -> f t >>= \t -> lam $ N57 :@. m1 :@. m2 :@. t
    _ -> (impossible "src/E2_Conv.hs" 157)
    ) do

  match 2 N58 1 N134 (\case
    m3 :. m4 :. INil -> \_ -> do
      T3 f (MkTmVal m1 m1') (MkTmVal m2 m2') <- matchArr b
      c1 <- vApp N134 m1'
      q <- conv_ c1{- Code m1 -} m3
      v <- lamName N142 m4
      defineBound v c1 do
        c2 <- vApp N134 m2'
        m4_v <- vApp m4 $ WVar v
        h_v <- conv_ m4_v{- m4 v -} c2{- Code m2 -}  --  (Code m1 -> m4 v)  ==>  (Code m1 -> Code m2)
        let lam t = case T2 h_v q of
              T2 Nothing Nothing -> pure t
              _ -> tLam v =<< evalId h_v =<< (:@.) t <$> evalId q (TVar v)
        pure $ Just \t -> lam t >>= \t -> f $ N112 :@. m1 :@. m2 :@. t
    _ -> (impossible "src/E2_Conv.hs" 174)
    ) do

  unify a b
  pure Nothing
