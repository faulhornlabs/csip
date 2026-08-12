
{-# LINE 1 "src/C5_Scope.hs" #-}
module C5_Scope
  ( ExpTree
    ( Lam, RLam, RHLam, RPi, RHPi, RCPi, RIPi, RLet, ROLet, RLetTy, RConstructor
    , RRule, RDec, RDot, RHApp, RView, RGuard
    , RClass, RInstance, REnd, RAnn, RCase, RCaseOf)
  , PPrint, pprint, pprint', unscope
  ) where

import B_Base
import C1_Name
import C2_NameLiterals
import C3_Parse
import C4_Desug ()

--------------- Raw syntax constructors ---------------

pattern RConstructor n = N43 :@ n
pattern RHApp a b      = RApp a (N27 :@ b)
pattern RAnn e t       = N30 :@ e :@ t
pattern RLam   n t   e = N37  :@ (N30 :@ n :@ t) :@ e
pattern Lam    n     e = RLam (RVar n) N39 e
pattern RHLam  n t   e = N37  :@ (N29 :@ n :@ t) :@ e
pattern RPi    n t   e = N38     :@ (N30 :@ n :@ t) :@ e
pattern RHPi   n t   e = N38     :@ (N29 :@ n :@ t) :@ e
pattern RCPi     t   e = N44     :@                   t  :@ e
pattern RIPi     t   e = N45     :@                   t  :@ e
pattern RDec  a      e = N21     :@ a :@ e
pattern RLet   n t d e = RDec (N32  :@ (N28 :@ n :@ t) :@ d) e
pattern ROLet  n t d e = RDec (N33 :@ (N28 :@ n :@ t) :@ d) e
pattern RLetTy n t   e = RDec (          N28 :@ n :@ t)       e
pattern RRule_ a b   e = RDec (N40 :@ a :@ b) e
pattern RRule  a b     = N46  :@ a :@ b
pattern RDot   a       = N47   :@ a       -- .a   (in lhs)
pattern RView  a b     = N48   :@ a :@ b
pattern RGuard a b     = N49     :@ a :@ b
pattern RClass    a b c = RDec (N35 :@ (N50    :@ a) :@ b) c
pattern RInstance a b c = RDec (N35 :@ (N51 :@ a) :@ b) c
pattern RData     a b c = RDec (N35 :@ (N52     :@ a) :@ b) c
pattern RCase     a b c = RDec (N36        :@ a :@ b) c
pattern RCaseOf   a b   = N53 :@ (N54 :@ a) :@ b
pattern REnd            = N20


--------------- scope and unscope ---------------

scope :: ExpTree' Import -> Mem (ExpTree' Scope)
scope t = runReader emptyIM ff  where
  ff r = f' t  where

    f' t = f t pure

    f :: ExpTree' Import -> (ExpTree' Scope -> Mem (ExpTree' Scope)) -> Mem (ExpTree' Scope)
    f t cont = case t of
      RRule_{} -> scopeRule t >>= \t -> f t cont
      RLet  n t a b | isRuleTy t -> f (RLetTy n t $ RRule_ n a b) cont
      RLet  n t d e -> scopeType t >>= \t -> f' d >>= \d -> addName n \n -> f e \e -> cont (RLet n t d e)
      ROLet n t d e -> scopeType t >>= \t -> f' d >>= \d -> addName n \n -> f e \e -> cont (ROLet n t d e)
      RLetTy  n t e -> scopeType t >>= \t -> addName  n \n -> f e \e -> cont (RLetTy n t e)
      RLam    n t e -> scopeType t >>= \t -> addName  n \n -> f e \e -> cont (RLam n t e)
      RHLam   n t e -> scopeType t >>= \t -> addName  n \n -> f e \e -> cont (RHLam n t e)
      RPi     n t e -> scopeType t >>= \t -> addName  n \n -> f e \e -> cont (RPi n t e)
      RHPi    n t e -> scopeType t >>= \t -> addName  n \n -> f e \e -> cont (RHPi n t e)
      RAnn      a b -> f' a >>= \a -> scopeType b >>= \b -> cont (RAnn a b)
      RData   a b c -> f (desugData a b c) cont
      RCaseOf a b -> desugCase a b cont
      RClass a b c
        -> addName (appHead $ codomain a) \_ -> addForalls' a >>= \a -> f' a >>= \a' -> f2 a b \b -> f c \c -> cont $ RClass a' b c
      RInstance a b c -> scopeType a >>= \a -> f3 b >>= \b -> f c \c -> cont $ RInstance a b c
      RVar n -> asks r (lookupIM n) >>= \case
        Just m  -> cont $ RVar $ rename n m
        Nothing -> cont $ RVar $ coerce n
      a :@ b -> ((:@) <$> f' a <*> f' b) >>= cont

    scopeRule t@(RRule_ a _ _) | T2 rs end <- getRules (ruleHead a) Nil t = ff end rs  where
      ff end (T2 a b :. c) = addForalls (fvs a) (RRule a b) >>= \t -> RDec t <$> ff end c
      ff end Nil = pure end
    scopeRule _ = (impossible "src/C5_Scope.hs" 77)

    f3 = \case
      t@RRule_{} -> scopeRule t >>= f3
      RLet l N39 r b -> f' (RRule l r) >>= \a -> f3 b >>= \b -> pure $ RDec a b
      RDec a b -> f' a >>= \a -> f3 b >>= \b -> pure $ RDec a b
      REnd -> pure REnd
      a -> fail $ "mailformed instance body: " <> print a

    f2 :: ExpTree' Import -> ExpTree' Import -> (ExpTree' Scope -> Mem (ExpTree' Scope)) -> Mem (ExpTree' Scope)
    f2 aa t cont = case t of
      RLetTy n t e -> scopeType2 aa t pure >>= \t -> addName n \n -> f2 aa e \e -> cont (RLetTy n t e)
      REnd -> cont REnd
      _ -> (undefined "src/C5_Scope.hs" 90)
     where
      scopeType2 :: ExpTree' Import -> ExpTree' Import -> (ExpTree' Scope -> Mem (ExpTree' Scope)) -> Mem (ExpTree' Scope)
      scopeType2 aa tt cont = case aa of
        RHPi n t e -> f' t >>= \t -> addName n \n -> scopeType2 e tt \e -> cont (RHPi n t e)
        RCPi _ e -> scopeType2 e tt \e -> cont e
        RPi{} -> (undefined "src/C5_Scope.hs" 96)
        t -> f' t >>= \t -> scopeType tt >>= \tt -> cont (RCPi t tt)

    addName' n@N39 cc = cc $ coerce n
    addName' n cc | isScoped n = addBuiltin n $ cc $ coerce n
    addName' n cc = do
      m <- nameOf n
      local r (insertIM n m) $ cc m

    addName (RConstructor n) cc = addName n \n -> cc $ RConstructor n
    addName (N55 :@ RVar n) cc = addBuiltin n $ cc $ RVar $ coerce n
    addName (RVar n) cc = addName' n \n -> cc $ RVar n
    addName k _ = fail $ "addName: " <> print k

    addBuiltin n = local r (insertIM n $ coerce n)

    addForalls ns r = do
      ns <- filterM notDefined ns
      pure $ foldr (\n r -> RHPi (RVar n) N39 r) r ns

    addForalls' a = addForalls (fvs' a) a
    scopeType t = f' =<< addForalls' t

    notDefined n | ConsChar c _ <- showName n, isLower c = asks r (lookupIM n) <&> not . isJust
    notDefined _ = pure False

    desugCase a b cont = do
      cf <- nameOf N56 <&> coerce
      let
        fn = RVar cf

        f acc (RCase a b c) = f (RRule_ (RApp fn a) b:. acc) c
        f acc REnd = foldr (\f c -> f c) (RApp fn a) acc
        f _ x = error $ "invalid case expression: " <> print x

      x <- f' $ RLetTy fn (RPi N39 N39 N39) $ f Nil b
      cont x

    desugData (RLetTy n t REnd) b c = RLetTy (RConstructor n) t $ f b c  where

      f (RLetTy n t b) c = RLetTy (RConstructor n) t $ f b c
      f REnd c = c
      f a _ = error $ "mailformed data constructor: " <> print a

    desugData a _ _ = error $ "mailformed data type constructor: " <> print a

  codomain = \case
    RPi _ _  e -> codomain e
    RHPi _ _ e -> codomain e
    RCPi _   e -> codomain e
    RIPi _   e -> codomain e
    t -> t

  appHead = \case
    RApp  a _ -> appHead a
    RHApp a _ -> appHead a
    a -> a

  isRuleTy = \case
    RHPi _ _ t -> isRuleTy t
    RCPi{} -> True
    _ -> False

  fvs, fvs' :: (IsName a, HasId a, HasArity a, Print (ExpTree a)) => ExpTree a -> List a
  fvs = nub . go where
    go = \case
      N39 -> Nil
      RDot{} -> Nil
      RView _ b -> go b
      RGuard a _ -> go a
      RAnn a _ -> go a
      RHApp a b -> go a <> go b
      RApp a b -> go a <> go b
      RVar a -> a :. Nil
      x -> error $ "fvs: " <> print x

  fvs' = nub . go where
    go = \case
      N39 -> Nil
      RPi   (RVar n) a b -> go a <> del n (go b)
      RHPi  (RVar n) a b -> go a <> del n (go b)
      RLam  (RVar n) a b -> go a <> del n (go b)
      RHLam (RVar n) a b -> go a <> del n (go b)
      RLet  (RVar n) t a b -> go t <> go a <> del n (go b)
      ROLet (RVar n) t a b -> go t <> go a <> del n (go b)
      RAnn  a b -> go b <> go a
      RCPi  a b -> go a <> go b
      RIPi  a b -> go a <> go b
      RHApp a b -> go a <> go b
      RApp  a b -> go a <> go b
      RVar  a -> a :. Nil
      x -> error $ "fvs': " <> print x

    del n = filter (not . (=== n))

  getRules h acc (RRule_ a b c) | ruleHead a === h = getRules h (T2 a b :. acc) c
  getRules _ acc e = T2 acc e

  ruleHead = f where
    f = \case
      RGuard a _ -> f a
      RApp (RApp (RVar N57) a) _ -> f a
      RApp a _ -> f a
      RVar n -> n
      e -> error $ "mailformed lhs: " <> print e

-----------------

unscope :: Bool -> ExpTree' Scope -> Mem (ExpTree' Import)
unscope checked t
  = runReader (emptyIM :: IntMap SName Word) \r1 ->
    newStringMap >>= \sm ->
    ff r1 sm
 where
  addIndex n 0 = pure $ nameStr n
  addIndex n i = mapName f n where
    f s@(revTakeStr 1 -> ConsChar d _) | isDigit d = s <> "_" <> showWord i
    f s = s <> showWord i

  ff r1 sm = f t where

    f :: ExpTree SName -> Mem (ExpTree' Import)
    f = \case
      -- TODO: move these?
      N58  :@ a :@ Lam n e -> f $ RPi  (RVar n) a e
      N59 :@ a :@ Lam n e -> f $ RHPi (RVar n) a e
      N60 :@ a :@       e -> f $ RCPi   a e
      N61 :@ a :@       e -> f $ RIPi   a e

      RVar n | not $ isScoped n -> pure $ RVar $ coerce n   -- TODO: be more scrict?
      RVar v -> asks r1 ((case checked of True -> id; _ -> Just . fromMaybe' 0) . lookupIM v) >>= \case
        Nothing -> fail $ "unscope: not in scope: " <> print v -- <> "\n" <> pprint' t
        Just k -> RVar <$> addIndex v k
      (unGLam -> Just (T4 cc es (RVar v) a))
        | n@N39 <- v -> cc <$> mapM f es <*> pure (RVar $ nameStr n) <*> f a
        | True -> asks r1 (lookupIM v) >>= \case
          Nothing -> do
            let sn = showName v
            k <- fromMaybe' 0 <$> lookupSM sn sm
            m <- addIndex v k
            es <- mapM f es
            local r1 (insertIM v k) $ do
              insertSM sn (1 + k) sm
              a <- f a
              case k of
                0 -> deleteSM sn sm    -- needed?
                i -> insertSM sn i sm
              pure $ cc es (RVar m) a
          Just k -> do                     -- TODO: this case is needed?
            m <- addIndex v k
            es <- mapM f es
            a <- f a
            pure $ cc es (RVar m) a

      a :@ b -> (:@) <$> f a <*> f b

  unGLam = \case
    ROLet a b c d -> Just (T4 (\case (b :. c :. INil) -> \a d -> ROLet a b c d; _ -> (impossible "src/C5_Scope.hs" 253)) (b :. c :. Nil) a d)
    RLet  a b c d -> Just (T4 (\case (b :. c :. INil) -> \a d -> RLet  a b c d; _ -> (impossible "src/C5_Scope.hs" 254)) (b :. c :. Nil) a d)
    RLetTy  a N62 d -> Just (T4 (\case    INil  -> \_ d ->             d)                              Nil  a d)
    RLetTy  a b d -> Just (T4 (\case (b :.      INil) -> \a d -> RLetTy  a b d; _ -> (impossible "src/C5_Scope.hs" 256)) (b :.      Nil) a d)
    RLam    a b d -> Just (T4 (\case (b :.      INil) -> \a d -> RLam    a b d; _ -> (impossible "src/C5_Scope.hs" 257)) (b :.      Nil) a d)
    RHLam   a b d -> Just (T4 (\case (b :.      INil) -> \a d -> RHLam   a b d; _ -> (impossible "src/C5_Scope.hs" 258)) (b :.      Nil) a d)
    RPi     a b d -> Just (T4 (\case (b :.      INil) -> \a d -> RPi     a b d; _ -> (impossible "src/C5_Scope.hs" 259)) (b :.      Nil) a d)
    RHPi    a b d -> Just (T4 (\case (b :.      INil) -> \a d -> RHPi    a b d; _ -> (impossible "src/C5_Scope.hs" 260)) (b :.      Nil) a d)
    _ -> Nothing


instance Parse (ExpTree' Scope) where  parse = parse >=> runMem . scope
instance Print (ExpTree' Scope) where  print = unscope False >=> print


--------------- PPrint ---------------

class PPrint a where
  pprint :: a -> Mem (ExpTree SName)

pprint' = pprint >=> print

instance IsName a => IsName (Mem a) where
  fromName t = pure (fromName t)
  eqName _ _ = False -- ?

instance PPrint Tup0 where  pprint T0 = N63

instance (PPrint a, PPrint b) => PPrint (Tup2 a b) where
  pprint (T2 a b) = N64 <@> pprint a <@> pprint b

instance PPrint a => PPrint (List a) where
  pprint as = case map pprint as of
    Nil -> N65
    a :. as -> N47 <@> foldr1 (\x y -> pure N66 <@> x <@> y) a as

instance PPrint Word where
  pprint w = RVar <$> newName (showWord w)

instance PPrint String where
  pprint = \case
    ConsChar '\n' s -> N67 .@ s
    ConsChar '\t' s -> N68   .@ s
    ConsChar '\r' s -> N69     .@ s
    ConsChar '\"' s -> N70   .@ s
    (spanStr (\c -> not $ c == '\n' || c == '\t' || c == '\r' || c == '\"') -> T2 as bs)
                    -> (RVar <$> newName ("\"" <> as <> "\"")) .@ bs
   where
    a .@ NilStr = a
    a .@ b = N71 <@> a <@> pprint b

instance PPrint IString where
  pprint = pprint . unIString

instance (HasPrecedences a, PPrint a) => PPrint (OpSeq a) where
  pprint Empty = N39
  pprint (Node2 Empty a Empty) = pprint a
  pprint x = case foldMapTopOp (\x -> pprint x :. Nil) (\x -> pprint x :. Nil) x of
    x :. xs -> N47 <@> foldl (<@>) x xs
    _ -> (impossible "src/C5_Scope.hs" 312)

instance PPrint (Name a) where
  pprint t = pprint $ showName t

instance PPrint a => PPrint (ExpTree a) where
  pprint = \case
    RVar n -> pprint n
    EApp _ a b -> pprint a <@> pprint b
