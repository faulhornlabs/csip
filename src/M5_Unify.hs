module M5_Unify
  ( unify
  , deepForce
  ) where

import M1_Base
import M3_Parse
import M4_Eval

---------------------------
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

updateClosed a b = do
  traceShow "2" $ "update " <<>> showM a <<>> "\n := " <<>> showM b
  v <- closeTm b
--  v' <- forceClosed v   -- TODO
  fe <- deepForce v
  case fe of
    WMeta r | a == r -> impossible
    _ -> update a fe


type SVal = (Val, IntSet Name)

type Indices = IntSet Int
type PruneSet_ = IntMap MetaDep Indices
type PruneSet = Maybe PruneSet_

(<.>) :: PruneSet_ -> PruneSet_ -> PruneSet_
(<.>) = unionWithIM (<>)

pruneMeta :: MetaDep -> Indices -> RefM ()
pruneMeta m (toListIS -> is) = do
  m' <- tMeta
  let
    mk _ [] vs = pure $ TApps m' $ reverse vs
    mk n (i: is) vs | n == i = do
      v <- mkName "_"
      tLam v =<< mk (n+1) is vs
    mk n (i: is) vs = do
      v <- mkName "v"{-TODO: better name-}
      tLam v =<< mk (n+1) (i: is) (TVar v: vs)
  t <- mk 0 is []
  v <- eval mempty t
  update m v

-------------------

closeTm :: Val -> RefM Val
closeTm v_ = do
  v <- force v_
  let sv = (v, mempty)
  m <- go [sv]
  () <- case fromJust $ lookup sv m of
    Just s -> forM_ (assocsIM s) \(v, s) -> pruneMeta v s
    Nothing -> undefined
  pure v_
 where
  go sv = downUp down up sv
   where
    down :: SVal -> RefM ((), [SVal])
    down (v, allowed) = case v of
      _ | closed v -> ret allowed []
      WLam c -> do
        u <- c
        b <- vApp v $ vVar u
        ret (insertIS u allowed) [b]
      WApp a b     -> ret allowed [a, b]
      WSel{}   -> undefined
      WMatch{} -> undefined
      WRet{}   -> undefined
      _            -> ret allowed []
     where
      ret allowed es = (,) () . map (\v -> (v, allowed)) <$> mapM force es

    up :: SVal -> () -> [(SVal, PruneSet)] -> RefM PruneSet
    up (v, allowed) _ ts = case v of
      _ | closed v  -> pure $ Just mempty
      WLam{} -> case sequence (map snd ts) of
        Nothing -> pure Nothing
        Just [sa] -> pure $ Just sa
        _ -> impossible
      WVar | name v `memberIS` allowed -> pure $ Just mempty
           | otherwise               -> pure Nothing
      WMetaApp_ _ _ _ dep -> case map snd ts of
        [Nothing, _] -> pure Nothing
        [Just sa, Nothing] -> do
           n <- metaArgNum v
           pure $ Just $ sa <.> singletonIM dep (singletonIS $ n - 1)
        [Just sa, Just sb] -> pure $ Just (sa <.> sb)
        _ -> impossible
      WApp{} -> case sequence (map snd ts) of
        Nothing -> pure Nothing
        Just [sa, sb] -> pure $ Just (sa <.> sb)
        _ -> impossible
      WDelta{} -> pure $ Just mempty
      WCon{}   -> pure $ Just mempty
      WFun{}   -> pure $ Just mempty
      _ -> undefined

-------------

expr a = foreground yellow a

unify :: Val -> Val -> RefM ()
unify aa{-actual-} bb{-expected-} = do
  traceShow "3" $ "conv " <<>> showM aa <<>> "\n ==? " <<>> showM bb
  go aa bb
 where
 ff v@(WMetaApp _ b) = do
   b <- force b
   pure (v, case b of WVar -> Just $ name b; _ -> Nothing)
 ff v = pure (v, Nothing)

 go :: Val -> Val -> RefM ()
 go a_ b_ = do
  (fa, va) <- force' a_
  (fb, vb) <- force' b_
  case (va, vb) of
   _ | va == vb -> pure ()
   (WMeta d, _) -> updateClosed d fb >> pure ()
   (_, WMeta d) -> updateClosed d fa >> pure ()
   _ -> do
    (va, arga) <- ff va
    (vb, argb) <- ff vb
    case (va, vb) of
     (WMetaApp a _, _) | Just u <- arga -> vLam u fb >>= \x -> go a x
     (_, WMetaApp a _) | Just u <- argb -> vLam u fa >>= \x -> go x a
     (WMetaApp a _, _) -> vConst fb >>= \x -> go a x
     (_, WMetaApp a _) -> vConst fa >>= \x -> go x a
     (WLam c, _) -> do
       v <- c <&> vVar
       va' <- vApp fa v
       vb' <- vApp fb v
       go va' vb'
     (_, WLam c) -> do
       v <- c <&> vVar
       va' <- vApp fa v
       vb' <- vApp fb v
       go va' vb'
     (WApp f a, WApp g b) -> go f g >> go a b
     _ -> do
      sa <- print =<< force_ aa
      sb <- print =<< force_ bb
      error $ fromString $ chars $ "Expected type\n " <> expr sb <> "\ninstead of\n " <> expr sa
