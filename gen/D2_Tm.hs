
{-# LINE 1 "src/D2_Tm.hs" #-}
module D2_Tm
  ( Combinator (..), varName, varName_, isConstComb, evalCombinator_, mkCombinator

  , PTm (TVar, (:@.), TApps, TLet, TVal, TSup, TLam)
  , Tm, tLam, tLams, tLets

  , TmTy (..), insertDef, lookupDef
  , insertGlobalVal, lookupGlobalVal
  ) where

import C_Syntax
import D1_Combinator
import {-# SOURCE #-} D3_Val

--------------------------

data TmTy = MkTmTy Tm Val{-type-}

{-# noinline envR #-}
envR :: State (IntMap SName TmTy)
envR = topState mainReset $ pure emptyIM

insertDef n a m = modify envR (insertIM n a) >> m
lookupDef n = gets envR (lookupIM n)


--------------------------

{-# noinline globalsR #-}
globalsR :: State (IntMap SName Val)
globalsR = topState mainReset (pure emptyIM)

insertGlobalVal n v = modify globalsR (insertIM n v)
lookupGlobalVal n = gets globalsR (lookupIM n)


--------------------------

data Combinator v
  = MkCombinator SName Rigid NameStr (Program (Combinator v))
  | CApp
  | CVal v

instance HasName v => HasName (Combinator v) where
  name = \case
    MkCombinator n _ _ _ -> n
    CApp -> N77
    CVal c -> name c

instance HasName v => HasId (Combinator v) where getId = getId . name
instance HasName v => Ord   (Combinator v) where compare = compare `on` getId

instance (HasName v, PPrint v) => PPrint (Combinator v) where
  pprint = \case
    MkCombinator _ _ _ p -> pprint p
    CVal v -> N27 <@> pprint (name v)
    c -> pprint $ name c

instance IsRigid v => IsRigid (Combinator v) where
  rigid = \case
    MkCombinator _ r _ _ -> r
    CApp -> True
    CVal v -> rigid v

instance IsClosed v => IsClosed (Combinator v) where
  closed = \case
    MkCombinator{} -> True
    CApp -> True
    CVal v -> closed v

evalCombinator_ :: (Combinator w -> List v -> Mem v) -> Combinator w -> List v -> v -> Mem v
evalCombinator_ force c vs v = case c of
  MkCombinator _ _ _ t -> runProgram force t vs v
  _ -> force c (vs ++ v :. Nil)      -- TODO: (v :. vs)

varName_ :: NameStr -> Combinator v -> Maybe NameStr
varName_ d (MkCombinator _ _ n _) = Just $ case n == N39 of True -> d; _ -> n
varName_ _ _ = Nothing

varName :: Combinator v -> Maybe (Mem SName)
varName c = nameOf <$> varName_ N75{-TODO?-} c

isConstComb (MkCombinator _ _ _ p) = constProg p
isConstComb _ = False

--              lambda param name
mkCombinator :: SName ->           Tm -> Mem (Tup2 (Combinator Val) (List SName))
mkCombinator n t_ = do
  cname <- nameOf N78
  t <- insertVal t_
  T2 prog args <- mkProg n t
  let lastname = case constProg prog of True -> N39; _ -> n
  pure $ T2 (MkCombinator cname (rigid t) (nameStr lastname) prog) args
 where
  insertVal = \case
    TVar n -> lookupGlobalVal n <&> \case
      Just v | rigid v -> TVal v
      _ -> TVar n
    TSup c ts -> TSup c <$> mapM insertVal ts
    TLet n a b -> TLet n <$> insertVal a <*> insertVal b


-------------------
{-
type LTm
  = LVar SName
  | LLet
  | LLam SName LTm
  | LApp LTm LTm
-}


-------------------


type Tm = PTm (Combinator Val)

infixl 9 :@.

pattern (:@.) :: Tm -> Tm -> Tm
pattern a :@. b = TSup CApp (a :. b :. INil)

pattern TVal :: Val -> Tm
pattern TVal v = TSup (CVal v) INil

getTLam (TSup c ts) | Just m <- varName c = Just $ m >>= \n -> T2 n <$> getTLam_ n (\create -> evalCombinator_ create c) ts
getTLam _ = Nothing

pattern TLam :: Mem (Tup2 SName Tm) -> Tm
pattern TLam e <- (getTLam -> Just e)

{-# COMPLETE TLam, TVar, TLet, (:@.), TVal #-}

getTApps ((getTApps -> T2 a es) :@. e) = T2 a (e:. es)
getTApps e = T2 e Nil

pattern TApps :: Tm -> List Tm -> Tm
pattern TApps e es <- (getTApps -> T2 e (reverse -> es))
  where TApps e es = foldl (:@.) e es

tLam :: SName -> Tm -> Mem Tm
tLam n t = do
--  traceShow "57" $ "tLam begin " <> print n -- <> "  -->  " <> print t
  T2 c ns' <- mkCombinator n t
  let r = TSup c $ map TVar ns'
--  traceShow "57" $ "tLam end " <> print r
  pure r

tLams :: List SName -> Tm -> Mem Tm
tLams Nil      t = pure t
tLams (n:. ns) t = tLam n =<< tLams ns t
