module D4_Eval
  ( evalCombinator{-TODO: remove-}
  , matchCon, matchCon', vApp, vApps, forceVal
  , vLam, vLams, vConst, isConst
  , deepForce, strictForce
  , eval, evalClosed, evalClosed'
  , quoteLets, quoteNF, tmToRaw, walkTm
  , lamName, update
  ) where

import C_Syntax
import D1_Combinator
import D2_Tm
import D3_Val

-----------------------

metaDep :: Val -> Maybe (Tup2 MetaRef MetaDep)
metaDep = \case
  WMeta m -> Just (T2 (metaRef m) m)
  WApp_ _ _ (MetaApp r m) -> Just (T2 r m)
  _ -> Nothing

evalCombinator :: Combinator Val -> List Val -> Val -> Mem Val
evalCombinator = evalCombinator_ f where
  f c vs = case c of
    CVal v -> forceVal v
    CApp | a :. b :. INil <- vs -> vApp a b
    _ -> vSup c vs

spineCon :: Val -> List Val
spineCon = f Nil where

  f acc WCon_{} = acc
  f acc (WApp_ a b ConApp{}) = f (b:. acc) a
  f _ e = error $ "spineCon: " <> pprint' e

matchCon 0 n v@(WCon_ n' True) | n' == n = Just $ spineCon v
matchCon k n v@(WApp_ _ _ (ConApp n' True k')) | n' == n, k' == k = Just $ spineCon v
matchCon _ _ _ = Nothing

matchCon' :: Word -> SName -> Val -> Mem (Maybe (List Val))
matchCon' k n v = forceVal v <&> matchCon k n

vForce :: Val -> Mem Val
vForce x = vApp x "X"B

-----------------------

vApp :: Val -> Val -> Mem Val
vApp a_ u = do
  a <- forceVal a_
  let
    conApp n c@True ar = matchCon' 3 "TMatch"B u >>= \case
      Nothing -> mkApp_ a u $ ConApp n c (ar + 1)
      Just (WCon c :. ok :. fail :. INil)
        | c == n -> vForce =<< vApps ok (spineCon a)
        | True   -> vForce fail
      _ -> $impossible
    conApp n c ar = mkApp_ a u $ ConApp n c (ar + 1)

    funApp f = vApp f u >>= \x -> case matchCon 1 "TRet"B x of
      Just (x :. _) -> pure x
      _ -> mkApp_ a u $ FunApp x

    metaApp x = mkMetaRef >>= \r -> mkApp_ a u (MetaApp r x)

    primOpApp n ra ar = forceVal u >>= \u -> case T0 of
      _ | not (closed u && rigid u) -> mkApp
        | ar > ra' -> mkApp_ a u $ PrimOpApp n ra' ar
        | True     -> evalPrimOp a (u :. Nil)
     where
      ra' = ra + 1

      mkApp = case snd <$> metaDep u of
        Just x  -> metaApp x
        Nothing -> mkApp_ a u $ ConApp n False{-why?-} ra'

      evalPrimOp (WApp a v) us = evalPrimOp a (v :. us)
      evalPrimOp (WPrimOp _ _ g) us = g mkApp us
      evalPrimOp _ _ = $impossible

  case a of
    WSup _ c vs    -> evalCombinator c vs u
    WCon_ n c      -> conApp n c 0
    WPrimOp n ar _ -> primOpApp n 0 ar
    WFun _ r       -> lookupRule r >>= funApp
    WMeta m        -> metaApp m

    WApp_ _ _ (ConApp n c a)      -> conApp n c a
    WApp_ _ _ (PrimOpApp n ra ar) -> primOpApp n ra ar
    WApp_ _ _ (FunApp f)          -> funApp f
    WApp_ _ _ (MetaApp _ m)       -> metaApp m

    _ -> $impossible


vApps :: Val -> List Val -> Mem Val
vApps v Nil = pure v
vApps v (a:. as) = vApp v a >>= \x -> vApps x as

------------------

forceVal :: Val -> Mem Val
forceVal v = forceVal__ v pure
 where
  forceVal__ v changed = case v of
    WMeta (metaRef -> ref) -> lookupMeta ref >>= \case
      Nothing -> pure v
      Just w_ -> forceVal__ w_ \w -> do
        updateMeta ref w
        changed w
    _ | Just (T2 ref i) <- metaDep v -> lookupMeta ref >>= \case
      Just w_ -> forceVal__ w_ \w -> do
        updateMeta ref w
        changed w
      Nothing -> lookupMeta (metaRef i) >>= \case
        Nothing -> pure v
        Just{} -> do
            r <- case v of
              WApp a b -> vApp a b
              _ -> $impossible
            updateMeta ref r
            changed r
    _ -> pure v


-------------------------------------------------------------------

lookupGlobalTm = \case
  TVal v -> Just <$> forceVal v
  TVar x -> lookupGlobalVal x >>= \case
    Just v -> Just <$> forceVal {- pure-} v
    _ -> pure Nothing
  _ -> pure Nothing

eval_ :: (SName -> Mem Val) -> IntMap SName Val -> Tm -> Mem Val
eval_ var = go where

  go env t = lookupGlobalTm t >>= \case
    Just v -> pure v
    _ -> case t of
      TGen x     -> go env x
      TVar x     -> case lookupIM x env of
        Just z -> pure z
        _ -> var x
      TLet x t u -> go env t >>= \v -> go (insertIM x v env) u
      t :@. u    -> go env t >>= \t -> go env u >>= \u -> vApp t u
      TSup c ts  -> vSup c =<< mapM (go env) ts

eval :: Mem String -> IntMap SName Val -> Tm -> Mem Val
eval err = eval_ \x -> fail $ "not defined(" <> err <> "): " <> print x

eval' :: IntMap SName Val -> Tm -> Mem Val
eval' = eval_ (pure . WVar)

evalClosed = eval "closed" emptyIM


------------------------------------------------------------------

quoteNF :: Val -> Mem Tm
quoteNF = f where
  f v_ = forceVal v_ >>= \case
    WVar n       -> pure $ TVar n
    WApp t u     -> (:@.) <$> f t <*> f u
    v@(WLam c)   -> c >>= \n -> vApp v (WVar n) >>= f >>= tLam n
    v@WMeta{}    -> pure $ TVar $ name v
    v            -> pure $ TVal v

quoteLets :: Val -> Mem Tm
quoteLets v_ = do
  v <- forceVal v_
  T2 map nodes <- runWriter \wst -> do  -- writer is needed for the right order
    let
      ch :: Val -> Mem (Tup2 Bool (List Val))
      ch v = (T2 False <$>) $ mapM forceVal $ case v of
        _ | closed v -> Nil
        WSup _ _ vs  -> vs
        WApp a b     -> a :. b :. Nil
        _            -> Nil

      share v _ = pure $ case v of
         _ | closed v -> False
         WVar{}       -> False
         _            -> True

      up v sh _ = tell wst (v :. Nil) >> pure sh

    walkIM ch share up (v :. Nil)

  let
    shared v = fromMaybe' False $ lookupIM v map

    ff = forceVal >=> \case
      v | closed v -> pure $ TVal v
      v | shared v -> pure $ TVar $ name v
      v            -> gg v

    gg v = getGlue (name v) >>= \case
      Just t -> pure t
      _ -> case v of
        WSup _ c vs -> TSup c <$> mapM ff vs
        WApp a b    -> (:@.) <$> ff a <*> ff b
        WVar n      -> pure $ TVar n
        v@WMeta{}   -> pure $ TVar $ name v
        v           -> pure $ TVal v

  vs <- mapM (\v -> T2 (name v) <$> gg v) $ reverse $ filter shared nodes
  tLets vs <$> ff v

-------------------

vLam :: SName -> Val -> Mem Val
vLam n v = forceVal v >>= \case
  WApp a b -> forceVal b >>= \case
    WCon_ vn _ | vn == n -> do
      ta <- quoteLets a
      T2 c _ <- mkCombinator n ta
      case isConstComb c of
        True -> pure a
        False -> def   -- TODO: optimize this
    _ -> def
  _ -> def
 where
  def = vLam_ n =<< quoteLets v

vConst :: Val -> Mem Val
vConst v = do
  n <- nameOf "_"B
  vLam n v

isConst :: Val -> Bool
isConst = \case
  WSup _ c _ -> isConstComb c
  _ -> False

vLams Nil x = pure x
vLams (v:. vs) x = vLams vs x >>= vLam v


-------------------

-- substitute all solved metas in a value  (= zonking?)
deepForce :: Val -> Mem Val
deepForce v_ = do
  v <- forceVal v_
  m <- go (v :. Nil)
  pure $ fromMaybe (lazy $impossible) $ lookupIM v m
 where
  go sv = downUpIM down (\_ -> pure) (\_ -> pure) up sv  where

    down :: Val -> Mem (Tup2 (Maybe SName) (List Val))
    down v = case v of
      _ | rigid v  -> ret Nothing Nil
      WMeta{}      -> ret Nothing Nil
      WFun{}       -> ret Nothing Nil   -- needed for meta funs
      WApp a b     -> ret Nothing (a :. b :. Nil)
      WSup _ _ vs  -> ret Nothing vs
{-      
      WLam c -> do
        u <- c
        b <- vApp v $ WVar u
        ret (Just u) (b :. Nil)
-}
      _ -> $undefined
     where
      ret mn es = T2 mn <$> mapM forceVal es

    up :: Val -> Maybe SName -> List (Tup2 Val Val) -> Mem Val
    up v _mn (map snd -> ts) = case v of
      _ | rigid v -> pure v
      WMeta{}     -> pure v
      WFun{}      -> pure v
      WApp{}    | a :. b :. _ <- ts -> renameVal (name v) <$> vApp a b
      WSup _ c _ -> renameVal (name v) <$> vSup c ts
--      WSup{}    | Just n <- mn, body :. _ <- ts -> vLam n body
      _ -> $undefined

strictForce :: Val -> Mem Val
strictForce v = deepForce v >>= \case
  v {- TODO! | rigid v -} -> pure v
--  v -> fail $ "meta in value:\n" <> print v

evalClosed' v = evalClosed v >>= strictForce

------------------------------- Show

tmToRaw :: Tm -> Mem Scoped
tmToRaw = go where
  go = \case
    TVar n     -> var n
    TLet n a b -> RLet (RVar n) "_"B  <$> go a <*> go b
    TGen e     -> "{ }"B <@> (eval' emptyIM e >>= quoteNF >>= go)
    a :@. b    -> RApp <$> go a <*> go b
    TLam g     -> g >>= \(T2 n t) -> Lam n <$> go t
    TVal v     -> forceVal v >>= \case
      WNat i    -> pprint i
      WString i -> pprint i
      _         -> var $ name v

  var n = pure $ case isInfix n of True -> "( )"B :@ RVar n ; _ -> RVar n

instance Print Tm  where print = walkTm False >=> unscope False >=> print
instance Print Val where print = quoteNF >=> print


------------- utils

lamName :: NameStr -> Val -> Mem SName
lamName n x = (forceVal x <&> \case
  WSup _ c _ | Just m <- varName_ n c -> m
  _ -> n) >>= nameOf

-- update(solve) a meta
update :: MetaDep -> Val -> Mem Tup0
update v e = do
  traceShow "1" $ "update " <> print v <> "\n ::= " <> print e
  updateMeta (metaRef v) e

------------------------------------------------

walkTm :: Bool -> Tm -> Mem Scoped
walkTm sh t = do
  ts <- reverse <$> getDefs
  foldr (\(T3 cstr n a) t -> tLet cstr n a t) (tmToRaw t) ts
 where
  tLet _    n _ t | not sh = RLetTy (RVar n) "IGNORE"B <$> t
  tLet True n _ t = RLetTy (RVar n) "_"B <$> t
  tLet _    n a t = RLet   (RVar n) "_"B <$> tmToRaw a <*> t
