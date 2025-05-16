module G_Unify
  ( unify
  , deepForce
  ) where

import B_Base
import E_Parse
import F_Eval

---------------------------

updateClosed a b = do
  traceShow "2" $ "update " <<>> print a <<>> "\n := " <<>> print b
  v <- closeTm b
  fe <- deepForce v
  case fe of
    WMeta r | a == r -> impossible
    _ -> update a fe


type SVal = Tup2 Val (IntSet Name)

type Indices = IntSet Word
type PruneSet_ = IntMap MetaDep Indices
type PruneSet = Maybe PruneSet_

(<.>) :: PruneSet_ -> PruneSet_ -> PruneSet_
(<.>) = unionWithIM (<>)

pruneMeta :: MetaDep -> Indices -> RefM Tup0
pruneMeta m (toListIS -> is) = do
  m' <- tMeta
  let
    mk _ Nil vs = pure $ TApps m' $ reverse vs
    mk n (i:. is) vs | n == i = do
      v <- mkName "_"
      tLam v =<< mk (n+1) is vs
    mk n (i:. is) vs = do
      v <- mkName "v#"{-TODO: better name-}
      tLam v =<< mk (n+1) (i:. is) (TVar v:. vs)
  t <- mk 0 is Nil
  v <- eval "prune" mempty t
  update m v

-------------------

closeTm :: Val -> RefM Val
closeTm v_ = do
  v <- force v_
  let sv = T2 v mempty
  m <- go (sv :. Nil)
  T0 <- case fromJust $ lookupMap sv m of
    Just s -> forM_ (assocsIM s) \(T2 v s) -> pruneMeta v s
    Nothing -> fail $ ("could not close meta solution:\n" <>) <$> print v
  pure v_
 where
  go sv = downUp down up sv where

    down :: SVal -> RefM (Tup2 Tup0 (List SVal))
    down (T2 v allowed) = case v of
      _ | closed v -> ret allowed Nil
      WLam _ c -> do
        u <- c
        b <- vApp v $ vVar u
        ret (insertIS u allowed) (b :. Nil)
      WApp a b     -> ret allowed (a :. b :. Nil)
      WMatch{} -> undefined
      WRet{}   -> undefined
      WNoRet{} -> undefined
      _            -> ret allowed Nil
     where
      ret allowed es = T2 T0 . map (\v -> T2 v allowed) <$> mapM force es

    up :: SVal -> Tup0 -> List (Tup2 SVal PruneSet) -> RefM PruneSet
    up (T2 v allowed) _ ts = case v of
      _ | closed v  -> pure $ Just mempty
      WLam{} -> case sequence (map snd ts) of
        Nothing -> pure Nothing
        Just (sa :. Nil) -> pure $ Just sa
        _ -> impossible
      WVar n | n `memberIS` allowed -> pure $ Just mempty
             | True                    -> pure Nothing
      WMetaApp_ _ _ _ dep -> case map snd ts of
        Nothing :. _ :. Nil -> pure Nothing
        Just sa :. Nothing :. Nil -> do
           n <- metaArgNum v
           pure $ Just $ sa <.> singletonIM dep (singletonIS $ intToWord $ n - 1)
        Just sa :. Just sb :. Nil -> pure $ Just (sa <.> sb)
        _ -> impossible
      WApp{} -> case sequence (map snd ts) of
        Nothing -> pure Nothing
        Just (sa :. sb :. Nil) -> pure $ Just (sa <.> sb)
        _ -> impossible
      WDelta{} -> pure $ Just mempty
      WCon{}   -> pure $ Just mempty
      WFun{}   -> pure $ Just mempty
      _ -> undefined


-------------

expr a = foreground yellow <$> a

unify :: Val -> Val -> RefM Tup0
unify aa{-actual-} bb{-expected-} = do
  traceShow "3" $ "conv " <<>> print aa <<>> "\n ==? " <<>> print bb
  go aa bb
 where
 ff v@(WMetaApp _ b) = do
   b <- force b
   pure (T2 v (case b of WVar n -> Just n; _ -> Nothing))
 ff v = pure (T2 v Nothing)

 go :: Val -> Val -> RefM Tup0
 go a_ b_ = do
  T2 fa va <- force' a_
  T2 fb vb <- force' b_
  case T2 va vb of
   _ | va == vb -> pure T0
   T2 (WMeta d) _ -> updateClosed d fb >> pure T0
   T2 _ (WMeta d) -> updateClosed d fa >> pure T0
   _ -> do
    T2 va arga <- ff va
    T2 vb argb <- ff vb
    case T2 va vb of
     T2 (WMetaApp a _) _ | Just u <- arga -> vLam u fb >>= \x -> go a x
     T2 _ (WMetaApp a _) | Just u <- argb -> vLam u fa >>= \x -> go x a
     T2 (WMetaApp a _) _ -> vConst fb >>= \x -> go a x
     T2 _ (WMetaApp a _) -> vConst fa >>= \x -> go x a
     T2 (WLam _ c) _ -> do
       v <- c <&> vVar
       va' <- vApp fa v
       vb' <- vApp fb v
       go va' vb'
     T2 _ (WLam _ c) -> do
       v <- c <&> vVar
       va' <- vApp fa v
       vb' <- vApp fb v
       go va' vb'
     T2 (WApp f a) (WApp g b) -> go f g >> go a b
     _ -> fail $ "Expected type\n " <<>> expr (print =<< force_ bb) <<>> "\ninstead of\n " <<>> expr (print =<< force_ aa)
