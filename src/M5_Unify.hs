module M5_Unify
  ( unify
  ) where

import M1_Base
import M3_Parse
import M4_Eval

---------------------------

updatable v _e = lookupMeta v >>= \case
  Just{}  -> impossible
  Nothing -> case v of
--    FVar   | closed e, rigid e -> pure ()
--    FVar   -> undefined
    WMeta {- | closed e -}       -> pure ()
--    VMeta   -> error' $ ("not closed:\n" <>) <$> (quoteNF' e <&> pprint >>= print)
--    VMetaApp{} -> pure ()
    _ -> impossible

update v e = do
  () <- updatable v e
  traceShow $ "update " <<>> showM v <<>> "\n ::= " <<>> showM e
  updateMeta v e

metaArgNum v_ = force v_ >>= \case
  WMeta           -> pure 0
  WMetaApp_ a _ _ -> (+1) <$> metaArgNum a
  _ -> undefined

updateClosed a b = do
  traceShow $ "update " <<>> showM a <<>> "\n := " <<>> showM b
  closeTm b >>= update a


type SVal = (Val, Set Name)

type Indices = Set Int
type PruneSet = Maybe (Map Val Indices)

(<.>) = unionWith (<>)

pruneMeta :: Val -> Indices -> RefM ()
pruneMeta m (toList -> is) = do
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

closeTm :: Val -> RefM Val
closeTm v_ = do
  v <- force v_
  let sv = (v, mempty)
  m <- go [sv]
  () <- case fromJust $ lookup sv m of
    Just s -> forM_ (assocs s) \(v, s) -> pruneMeta v s
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
        ret (insertSet u allowed) [b]
      WApp a b     -> ret allowed [a, b]
      _            -> ret allowed []
     where
      ret allowed es = (,) () . map (\v -> (v, allowed)) <$> mapM force es

    up :: SVal -> () -> [(SVal, PruneSet)] -> RefM PruneSet
    up (v, allowed) _ ts = case v of
      _ | closed v  -> pure $ Just mempty
      WSup{} -> case sequence (map snd ts) of
        Nothing -> pure Nothing
        Just [sa] -> pure $ Just sa
        _ -> impossible
      WVar | name v `member` allowed -> pure $ Just mempty
           | otherwise               -> pure Nothing
      Delta _ -> pure $ Just mempty
      WCon -> pure $ Just mempty
      WFun -> pure $ Just mempty
      WMetaApp dep -> case map snd ts of
        [Nothing, _] -> pure Nothing
        [Just sa, Nothing] -> do
           n <- metaArgNum v
           pure $ Just $ sa <.> singleton dep (singletonSet $ n - 1)
        [Just sa, Just sb] -> pure $ Just (sa <.> sb)
        _ -> impossible
      WApp{} -> case sequence (map snd ts) of
        Nothing -> pure Nothing
        Just [sa, sb] -> pure $ Just (sa <.> sb)
        _ -> impossible
      _ -> undefined

-------------

expr a = foreground yellow a

unify :: Val -> Val -> RefM ()
unify aa{-actual-} bb{-expected-} = do
  traceShow $ "conv " <<>> showM aa <<>> "\n ==? " <<>> showM bb
  go aa bb
 where
 ff v@(WMetaApp_ _ b _) = do
   b <- force b
   pure (v, case b of WVar -> Just b; _ -> Nothing)
 ff v = pure (v, Nothing)

 go :: Val -> Val -> RefM ()
 go a_ b_ = do
  (fa, va) <- force' a_
  (fb, vb) <- force' b_
  case (va, vb) of
   _ | va == vb -> pure ()
   (WMeta, _) -> updateClosed va fb >> pure ()
   (_, WMeta) -> updateClosed vb fa >> pure ()
   _ -> do
    (va, arga) <- ff va
    (vb, argb) <- ff vb
    case (va, vb) of
     (WMetaApp_ a _ _, _) | Just u <- arga -> vLam u fb >>= \x -> go a x
     (_, WMetaApp_ a _ _) | Just u <- argb -> vLam u fa >>= \x -> go x a
     (WMetaApp_ a _ _, _) -> vConst fb >>= \x -> go a x
     (_, WMetaApp_ a _ _) -> vConst fa >>= \x -> go x a
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
