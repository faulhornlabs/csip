
{-# LINE 1 "src/D1_Combinator.hs" #-}
module D1_Combinator
  ( Rigid, IsRigid (..), Closed, IsClosed (..)
  , PTm (..), tLets, getTLam_
  , Program, runProgram, mkProg, constProg
  ) where

import C_Syntax

----------------------

-- True: can not change; False: may be changed by force
-- force may change it from False to True
type Rigid = Bool

class IsRigid a where rigid :: a -> Rigid

-- force may change it from False to True if not rigid
type Closed = Bool

class IsClosed a where closed :: a -> Closed


-------------------------- term representation

data PTm c
  = TVar SName
  | TSup c (List (PTm c))
  | TLet SName (PTm c) (PTm c)

---------

-- TODO: remove
instance Tag (PTm c) where
  tag TSup{}  = 0
  tag TVar{}  = 1
  tag TLet{}  = 2

-- TODO: remove
instance Ord c => Ord (PTm c) where
  compare (TSup a b)   (TSup a' b')    = compare a a' &&& lazy (compare b b')
  compare (TVar a)     (TVar a')       = compare a a'
  compare (TLet a b c) (TLet a' b' c') = compare a a' &&& lazy (compare b b' &&& lazy (compare c c'))
  compare a b = compareTag a b

instance IsRigid c => IsRigid (PTm c) where
  rigid = \case
    TVar{}     -> True
    TLet _ a b -> rigid a && rigid b
    TSup c ts  -> rigid c && all rigid ts

instance IsClosed c => IsClosed (PTm c) where
  closed = \case
    TVar{}     -> False
    TLet _ a b -> closed a && closed b
    TSup c ts  -> closed c && all closed ts

instance PPrint c => PPrint (PTm c) where
  pprint = \case
    TVar n     -> N72 <@> pprint n
    TLet n a b -> N73 <@> pprint n <@> pprint a <@> pprint b
    TSup c ts  -> foldl (<@>) (pprint c) $ map pprint ts

---------

tLets ds e = foldr (\(T2 a b) t -> TLet a b t) e ds


-------------------------- graph term representation

data GTm c
  = GVar SName
  | GSup c (List (GTm c)) SName

---------

instance HasName (GTm c) where
  name = \case
    GVar n -> n
    GSup _ _ n -> n

instance HasId (GTm c) where getId   = getId . name

create :: c -> List (GTm c) -> Mem (GTm c)
create a b = nameOf N74 <&> GSup a b
{-
evalTm_ :: PTm c -> Mem (GTm c)
evalTm_ t = go emptyIM t
 where
  go env = \case
    TVar x     -> case lookupIM x env of Just z -> pure z; _ -> pure $ GVar x
    TLet x t u -> go env t >>= \v -> go (insertIM x v env) u
    TSup c ts  -> create c =<< mapM (go env) ts
-}
quoteLets_ :: GTm c -> Mem (PTm c)
quoteLets_ v = do
  T2 map nodes <- runWriter \wst -> do  -- writer is needed for the right order
    let
      ch v = case v of
        GSup _ vs _  -> vs
        _            -> Nil

      share v _ = pure $ case v of
         GVar{}       -> False
         GSup _ Nil _ -> False
         _            -> True

      up v sh _ = tell wst (v :. Nil) >> pure sh

    walkIM (pure . T2 False . ch) share up (v :. Nil)

  let
    shared v = fromMaybe' False $ lookupIM v map

    ff = \case
      v | shared v -> pure $ TVar $ name v
      v            -> gg v

    gg = \case
      GVar n      -> pure $ TVar n
      GSup c vs _ -> TSup c <$> mapM ff vs

  vs <- mapM (\v -> T2 (name v) <$> gg v) $ reverse $ filter shared nodes
  tLets vs <$> ff v

--getTLam_ :: HasName c => SName -> (forall v . (c -> List v -> Mem v) -> List v -> v -> Mem v) -> List (PTm c) -> Mem (PTm c)
getTLam_ n eval ts = do
  let
    inlinable = \case
      TVar n     -> Just $ GVar n
      TSup c Nil -> Just $ GSup c Nil $ name c
      _ -> Nothing

    ff Nil = pure $ T2 Nil Nil
    ff (t :. ts) = do
      T2 ds ts <- ff ts
      case inlinable t of
        Just z -> pure $ T2 ds (z :. ts)
        _ -> nameOf N75 <&> \n -> T2 (T2 n t :. ds) (GVar n :. ts)

  T2 ds ts <- ff ts

  t <- eval create ts (GVar n)
  tLets ds <$> quoteLets_ t


-------------------------------- programs (combinators)

type Length = Word

data Op k = Create Word k (List Word)

data Program k = MkProg Bool (List (Op k)) Length Word

------------

constProg (MkProg c _ _ _) = c

instance PPrint v => PPrint (Program v) where
  pprint _ = N76     -- TODO

runProgram :: (k -> List e -> Mem e) -> Program k -> List e -> e -> Mem e
runProgram create (MkProg co ops maxlength res) args_ arg = do
  v <- newArray_ maxlength
  forM_ (numberWith (writeArray v) 0 args) id
  let
    go (Create loc k args) = do
      vs <- mapM (readArray v) args
      r <- create k vs
      writeArray v loc r
  forM_ ops go
  readArray v res
 where
  args = case co of True -> args_; _ -> arg :. args_

-------------

data Op' c = Create' SName c (List SName) | Free SName

instance HasName (Op' c) where
  name (Free n) = n
  name (Create' n _ _) = n

mkProg :: SName -> PTm c -> Mem (Tup2 (Program c) (List SName))
mkProg n t_ = do
  T3 a b s <- flatTm t_
  let co = all (/= n) s
      args = filter (/= n) s
      T2 ops (T2 size fin) = mapProg a b $ case co of True -> args; _ -> n :. args
  pure (T2 (MkProg co ops size fin) args)
 where

  flatTm :: PTm c -> Mem (Tup3 (List (Op' c)) SName (List SName))
  flatTm t = runState Nil ff <&> frees
   where
    ff st = f emptyIM t  where
      f m = \case
        TVar n -> pure $ fromMaybe' n $ lookupIM n m
        TSup c ts -> nameOf N74 >>= \n -> mapM (f m) ts >>= \ts -> modify st (Create' n c ts :.) >> pure n
        TLet n a b -> f m a >>= \a -> f (insertIM n a m) b

    frees (T2 main ops) = T3 ops' main $ filter (`memberIS` is) vs  where
      T3 is vs ops' =  foldr free (T3 (insertIS main emptyIS) (main :. Nil) Nil) $ reverse ops

    free n st@(T3 m _ _) | not $ memberIS (name n) m = st
    free cr@(Create' n _ ts) st | T3 m' vs l' <- f ts st = T3 (deleteIS n m') vs (cr :. l')
    free _ _ = (impossible "src/D1_Combinator.hs" 206)

    f Nil st = st
    f (n :. ts) (T3 m vs l)
      | memberIS n m = f ts $ T3 m vs l
      | True         = f ts $ T3 (insertIS n m) (n :. vs) $ Free n :. l

  mapProg p res args = go (fromListIM $ numberWith (flip T2) 0 args) (T2 (length args) Nil) p
   where
    go m fs Nil = T2 Nil $ T2 (fst fs) $ fromMaybe (lazy (impossible "src/D1_Combinator.hs" 215)) $ lookupIM res m 
    go m fs (op :. ops) = case op of
      Free g
        | Just i <- lookupIM g m -> go m (free i fs) ops
      Create' g k xs
        | T2 i fs <- newReg fs
        , is <- xs <&> \x -> fromMaybe (lazy (impossible "src/D1_Combinator.hs" 221)) $ lookupIM x m
        -> add (Create i k is) $ go (insertIM g i m) fs ops
      _ -> (impossible "src/D1_Combinator.hs" 223)

    add i (T2 is m) = T2 (i :. is) m

    free j (T2 i js) = T2 i (j :. js)

    newReg (T2 i (j :. js)) = T2 j (T2 i     js)
    newReg (T2 i _)         = T2 i (T2 (i+1) Nil)
