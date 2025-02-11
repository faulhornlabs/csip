module M5_Unify
  ( conv
  ) where

import M1_Base
import M3_Parse
import M4_Eval

---------------------------

updatable v e = lookupMeta v >>= \case
  Just{}  -> impossible
  Nothing -> case view v of
--    FVar   | closed e, rigid e -> pure ()
--    FVar   -> undefined
    VMeta | closed e        -> pure ()
    VMeta   -> error' $ ("not closed:\n" <>) <$> (quoteNF' e <&> pprint >>= print)
--    VMetaApp{} -> pure ()
    _ -> impossible

update v e = do
  () <- updatable v e
  updateMeta v e



metaSpine v_ = force v_ >>= \v -> case view v of
  VMeta          -> pure (v, [])
  VApp_ a b _ Just{} -> force b >>= \case
    u@(view -> VVar) -> metaSpine a <&> second (name u:)
    _ -> undefined
  _ -> impossible

solveMeta a b = do
  (h, reverse -> vs) <- metaSpine a
  b' <- closeTm (fromListSet vs) b
  update h =<< vLams (map vVar vs) b'


closeTm :: Set Name -> Val -> RefM Val
closeTm allowed v_ = do
  v <- force_ v_
  m <- go v
  pure $ snd $ fromJust $ lookup v m
 where
  go v = downUp down up [v]
   where
    ret es = (,) [] <$> mapM force_ es

    down v = case view v of
      _ | closed v -> ret []
      VApp a b -> ret [a, b]
      VTm _ v -> ret [v]
      VSup c _ -> do
        let u = varName c
        b <- vApp v $ vVar u
        first ((u, b):) <$> down b
      _ -> ret []

    up :: Val -> [(Name, Val)] -> [(Val, (Set Name, Val))] -> RefM (Set Name, Val)
    up _ ((u, b): vs) m = do
      (s, x) <- up b vs m
      (,) (delete u s) <$> vLam (vVar u) x
    up v [] ts
     | closed v  = pure (mempty, v)
     | otherwise = case view v of
      VSup{} -> impossible
      VVar -> pure (singletonSet (name v), v)
      VCon -> pure (mempty, v)
      VFun -> pure (mempty, v)
      VTm t _ | [(sa, a)] <- map snd ts -> (,) sa <$> vTm (name v) t a
      VMetaApp{} | [(sa, a), (sb, b)] <- map snd ts, isSubsetOf sb allowed -> (,) (sa <> sb) <$> vApp a b
      VMetaApp{} | [_, (sb, _)] <- map snd ts -> error' $ fmap ("TODO: " <>) $ print $ pprint (toList sb, toList allowed)
      VApp{} | [(sa, a), (sb, b)] <- map snd ts -> (,) (sa <> sb) <$> vApp a b
      _ -> undefined

updateClosed a b = closeTm mempty b >>= update a


-------------

expr a = foreground yellow a

conv  :: Val -> Val -> RefM ()
conv aa bb = go aa bb where

 go a_ b_ = do
  (fa, va) <- force' a_
  (fb, vb) <- force' b_
  case (view va, view vb) of
    _ | va == vb -> pure ()
    (VMeta, _) -> updateClosed va fb
    (_, VMeta) -> updateClosed vb fa
    (VSup c _, _) -> do
      v <- mkName (varName c) <&> vVar
      va' <- vApp fa v
      vb' <- vApp fb v
      go va' vb'
    (_, VSup c _) -> do
      v <- mkName (varName c) <&> vVar
      va' <- vApp fa v
      vb' <- vApp fb v
      go va' vb'
    (VMetaApp{}, VMetaApp{}) -> solveMeta va fb  -- TODO!
    (VMetaApp{}, _) -> solveMeta va fb
    (_, VMetaApp{}) -> solveMeta vb fa
    (VApp f a, VApp g b) -> go f g >> go a b
    _ -> do
      sa <- print =<< force_ aa
      sb <- print =<< force_ bb
      error $ fromString $ chars $ "Expected type\n " <> expr sb <> "\ninstead of\n " <> expr sa
