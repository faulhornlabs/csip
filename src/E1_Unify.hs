module E1_Unify
  ( unify
  ) where

import D_Calculus

---------------------------

updateClosed a b = do
  traceShow "2" $ "update " <> print a <> "\n := " <> print b
  v <- closeTm b
  fe <- deepForce v
  case fe of
    WMeta r | a === r -> $impossible
    _ -> update a fe

type Indices = BitSet

pruneMeta :: MetaDep -> Indices -> Mem Tup0
pruneMeta m (toListBS -> is) = do
  m' <- tMeta
  let
    mk _ Nil vs = pure $ TApps m' $ reverse vs
    mk n (i:. is) vs | n == i = do
      v <- nameOf "_"B
      tLam v =<< mk (n+1) is vs
    mk n (i:. is) vs = do
      v <- nameOf "v"B
      tLam v =<< mk (n+1) (i:. is) (TVar v:. vs)
  t <- mk 0 is Nil
  v <- evalClosed t
  update m =<< vTm "p"B t v

-------------------

-- TODO: use Tree
type Prunes = List (Tup2 SName (List (Tup2 MetaDep Word)))

filterPrunes :: SName -> Prunes -> Prunes
filterPrunes n ps = filter ((/= n) . fst) ps

mapPrunes :: MetaDep -> Word -> Prunes -> Prunes
mapPrunes dep i ps = map (\(T2 n l) -> T2 n (T2 dep i :. l)) ps

varPrunes :: SName -> Prunes
varPrunes n = T2 n Nil :. Nil

computePrunes :: Prunes -> Maybe (List (Tup2 MetaDep Indices))
computePrunes ps = f Nil emptyIM ps  where
  f acc m Nil = Just $ map (\d -> T2 d $ fromMaybe (lazy $impossible) $ lookupIM d m) acc
  f _   _ (T2 _ Nil :. _) = Nothing
  f acc m (T2 _ is :. ps) | p is = f acc m ps
   where
    p Nil = False
    p (T2 dep i :. is) = maybe False (memberBS i) (lookupIM dep m) || p is
  f acc m (T2 _ (T2 dep i :. _) :. ps)    -- TODO: better selection?
    = f (dep :. acc) (insertIM dep (singletonBS i) m) ps

closeTm :: Val -> Mem Val
closeTm v_ = do
  v <- forceVal v_
  m <- go (v :. Nil)
  case computePrunes $ fromMaybe (lazy $impossible) $ lookupIM v m of
    Nothing -> fail $ "could not close meta solution:\n" <> print v
    Just s -> forM_ s \(T2 v s) -> pruneMeta v s
  pure v_
 where
  go = downUpIM down (\_ -> pure) (\_ -> pure) up where

    down :: Val -> Mem (Tup2 (Maybe SName) (List Val))
    down = \case
      v | closed v -> ret Nil
      v@(WLam c) -> do
        u <- c
        b <- vApp v $ WVar u
        T2 (Just u) <$> mapM forceVal (b :. Nil)
      WApp a b     -> ret (a :. b :. Nil)
      _ -> ret Nil
     where
      ret es = T2 Nothing <$> mapM forceVal es

    up :: Val -> Maybe SName -> List (Tup2 Val Prunes) -> Mem Prunes
    up v ln (map snd -> ts) = case v of
      _ | closed v  -> pure mempty
      WVar n -> pure $ varPrunes n
      WLam{} | sa :. _ <- ts, Just n <- ln -> pure $ filterPrunes n sa
      WApp_ a _ (MetaApp _ dep) | sa :. sb :. _ <- ts -> do
        n <- metaArgNum a
        pure $ sa <> mapPrunes dep n sb
      WApp{} | sa :. sb :. _ <- ts -> pure $ sa <> sb
      WMeta{} -> pure mempty
      _ -> $impossible

-------------

expr a = foreground yellow <$> a

unify :: Val -> Val -> Mem Tup0
unify aa{-actual-} bb{-expected-} = do
  traceShow "3" $ "conv " <> print aa <> "\n ==? " <> print bb
  go aa bb
 where
 ff v@(WApp_ _ b MetaApp{}) = do
   b <- forceVal b
   pure (T2 v (case b of WVar n -> Just n; _ -> Nothing))
 ff v = pure (T2 v Nothing)

 go :: Val -> Val -> Mem Tup0
 go a_ b_ = do
  va <- forceVal a_
  vb <- forceVal b_
  case T2 va vb of
   _ | va === vb -> pure T0
   T2 (WMeta d) _ -> updateClosed d vb >> pure T0
   T2 _ (WMeta d) -> updateClosed d va >> pure T0
   _ -> do
    T2 va arga <- ff va
    T2 vb argb <- ff vb
    case T2 va vb of
     T2 (WApp_ a _ MetaApp{}) _ | Just u <- arga -> vLam u vb >>= \x -> go a x
     T2 _ (WApp_ a _ MetaApp{}) | Just u <- argb -> vLam u va >>= \x -> go x a
     T2 (WApp_ a _ MetaApp{}) _ -> vConst vb >>= \x -> go a x
     T2 _ (WApp_ a _ MetaApp{}) -> vConst va >>= \x -> go x a
     T2 (WLam c) _ -> do
       v <- c <&> WVar
       va' <- vApp va v
       vb' <- vApp vb v
       go va' vb'
     T2 _ (WLam c) -> do
       v <- c <&> WVar
       va' <- vApp va v
       vb' <- vApp vb v
       go va' vb'
     T2 (WApp f a) (WApp g b) -> go f g >> go a b
     _ -> fail $ "Expected type\n " <> expr (print =<< forceVal bb) <> "\ninstead of\n " <> expr (print =<< forceVal aa)
