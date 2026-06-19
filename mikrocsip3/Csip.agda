{-

Developed with Agda version 2.9.0

Compile as

    agda --compile Csip.agda

Try as

    ./Csip <test/basic.csip
    ./Csip hs <test/power.csip >power.hs && runhaskell power.hs

-}

{-# OPTIONS --type-in-type --no-positivity-check --no-termination-check --rewriting --prop --injective-type-constructors --hidden-argument-puns #-}

open import Prelude
open import Model
open import Parser

-------------------------------------------------------

data Tys : Set    -- Ctx
Tms : Tys -> Set  -- Env

data Tys where
  []   :                                 Tys
  _>>_ : (ts : Tys) -> (Tms ts -> Ty) -> Tys

Tms []        = T
Tms (ts >> t) = Tms ts ** \xs -> Tm (t xs)

variable ts : Tys

---------------

-- type depending on context (second order representation)
CTy : Tys -> Set
CTy ts = Tms ts -> Ty

-- term depending on context
CTm : (ts : Tys) -> CTy ts -> Set
CTm ts t = (xs : Tms ts) -> Tm (t xs)

---------------

data Ns : Tys -> Set where
  []   : Ns []
  _>>_ : {t : _} -> (ns : Ns ts) -> (n : Name) -> Ns (ts >> t)

variable ns : Ns ts

---------------

-- open types and terms
OTy = Ty
OTm = Tm
OSpine = Spine

------------

[[_,_]]u : (ns : Ns ts) -> OTy -> CTy ts

[[_,_]]  : {a : _} -> (ns : Ns ts) -> OTm a    -> CTm ts [[ ns , a ]]u
[[_,_]]s : {a : _} -> (ns : Ns ts) -> OSpine a -> CTm ts [[ ns , a ]]u

[[ _ , U   ]]u = \_ -> U
[[ _ , Top ]]u = \_ -> Top
[[ _ , Bot ]]u = \_ -> Bot
[[ ns , a => a' ]]u = [[ ns , a ]]u & \ae -> [[ ns , a' ]]u & \ae' -> \xs -> ae xs => ae' xs
[[ ns , a *  a' ]]u = [[ ns , a ]]u & \ae -> [[ ns , a' ]]u & \ae' -> \xs -> ae xs *  ae' xs
[[ ns , a \/ a' ]]u = [[ ns , a ]]u & \ae -> [[ ns , a' ]]u & \ae' -> \xs -> ae xs \/  ae' xs
[[ ns , Pi    a b ]]u = [[ ns , a ]]u &in \ae e -> [[ ns , b ]] & \be -> \xs -> Pi    (ae xs) (subst (\k -> k xs =>U) e (be xs))
[[ ns , Sigma a b ]]u = [[ ns , a ]]u &in \ae e -> [[ ns , b ]] & \be -> \xs -> Sigma (ae xs) (subst (\k -> k xs =>U) e (be xs))
[[ ns , Id x y    ]]u = [[ ns , x ]] & \xe -> [[ ns , y ]] & \ye -> \xs -> Id (xe xs) (ye xs)
[[ ns , Rec rc ps ]]u = [[ ns , ps ]] & \ps' -> \xs -> Rec rc (subst Tm believeMe~ (ps' xs))
[[ ns , NU (NeU' {s} _) ]]u = [[ ns , s ]]s


[[]]u# : {a : _} {ns : _} (b : a =>U) {x : Tm a} (xs : Tms ts) -> [[ ns , b # x ]]u xs ~ [[ ns , b ]] xs # [[ ns , x ]] xs
[[]]u# b xs = believeMe~

[[]]u[] : [[_,_]]u {ts = []} [] a _ ~ a
[[]]u[] = believeMe~

[[_,_]] {a = U}    ns t = [[ ns , t ]]u
[[_,_]] {a = NU _} ns TT = \xs -> TT
[[_,_]] {a = NU _} ns (x ,  y) = [[ ns , x ]] & \xe -> [[ ns , y ]] & \ye -> \xs -> xe xs , ye xs
[[_,_]] {a = NU _} ns (_,,_ {b} x y) = [[ ns , x ]] &in \xe e -> match e & \{Refl -> [[ ns , y ]] & \ye -> \xs -> xe xs ,, subst Tm ([[]]u# b xs) (ye xs)}
[[_,_]] {a = NU _} ns (Left  x) = [[ ns , x ]] & \xe -> \xs -> Left  (xe xs)
[[_,_]] {a = NU _} ns (Right x) = [[ ns , x ]] & \xe -> \xs -> Right (xe xs)
[[_,_]] {a = NU _} ns Refl = \xs -> Refl
[[_,_]] {a = NU _} ns (Wrap {rc} args) = [[ ns , args ]] & \args' -> \xs -> Wrap (subst Tm believeMe~ (args' xs))
[[_,_]] {a = NU _} ns (NeNU {s} _) = [[ ns , s ]]s

weaken     : {n : _} {t : CTy ts} {xs : Tms ts} {x : Tm (t xs)} (a : _) -> [[ ns , a ]]u xs ~ [[_,_]]u {ts = ts >> t} (ns >> n) a (xs ,, x)
weaken a = believeMe~

strengthen : {n : _} {t : CTy ts} {xs : Tms ts} {x : Tm (t xs)} (a : _) -> [[_,_]]u {ts = ts >> t} (ns >> n) a (xs ,, x) ~ [[ ns , a ]]u xs
strengthen a = sym (weaken a)

indexTms : {ns : _} -> TName a -> CTm ts [[ ns , a ]]u
indexTms {ts = []} (MkTName n) = \_ -> var (MkTName n)
indexTms {a} {ts = ts >> t} {ns = ns >> n'} n =
  indexTms {a = a} {ts = ts} {ns = ns} n & \f ->
    decName n' (tName n) & \where
      (Just _) -> \(xs ,, x) -> coe believeMe~ x
      Nothing  -> \(xs ,, x) -> subst Tm believeMe~ (f xs)

NamedTmLClosed : {xs : Tms ts} -> NamedTmL ([[ ns , a ]]u xs) ~ NamedTmL a
NamedTmLClosed = believeMe~

closedTy' : {xs : Tms ts} -> [[ ns , a ]]u xs ~ a
closedTy' = believeMe~


[[ ns , Head {a} (named n Stuck) ]]s = indexTms {a = a} (MkTName n)
[[ ns , Head h@(named _ (Lam  _)) ]]s = spineToTm (Head h) & \f -> \xs -> subst Tm (sym closedTy') f
[[ ns , Head h@(named _ (DLam _)) ]]s = spineToTm (Head h) & \f -> \xs -> subst Tm (sym closedTy') f
[[ ns , s $ x ]]s = [[ ns , s ]]s & \se -> [[ ns , x ]] & \xe -> \xs -> se xs # xe xs
[[ ns , _$$_ {b} s x ]]s = [[ ns , s ]]s & \se -> [[ ns , x ]] &in \xe e -> match e & \{Refl -> \xs -> subst Tm (sym ([[]]u# b xs)) (se xs ## xe xs)}


---------

TysN : Set          -- context with names
TysN = Tys ** Ns

infixl 3 _>>p_::_
infixl 3 _>>>_

_>>p_::_ : ((ts ,, ns) : TysN) -> Name -> CTy ts -> TysN
_>>p_::_ (ts ,, ns) n t = (ts >> t) ,, (ns >> n)

_>>>_ : (ts : TysN) -> TName a -> TysN
_>>>_ {a} (ts ,, ns) n = (ts ,, ns) >>p tName n :: [[ ns , a ]]u


-------------------------------------------------

NameMap : (Ty -> Set) -> Set
NameMap P = List (Ty ** \a -> Pair (TName a) (P a))

variable W : Ty -> Set

emptySM     : NameMap W
emptySM = []

insertSM    : TName a -> W a -> NameMap W -> NameMap W
insertSM s a m = (_ ,, s , a) :: m

deleteSM    : TName a ->        NameMap W -> NameMap W
deleteSM s [] = []
deleteSM s ((_ ,, n , x) :: sm) = decTName n s & \where
  (Just _) -> deleteSM s sm
  Nothing  -> (_ ,, n , x) :: deleteSM s sm

lookupSM    : TName a ->        NameMap W -> Maybe (W a)
lookupSM s [] = Nothing
lookupSM s ((_ ,, n , x) :: sm) = decTName n s & \where
  (Just e) -> match' e & \{Refl -> Just x}
  Nothing  -> lookupSM s sm

lookupSMStr : String ->         NameMap W -> Maybe (Ty ** \a -> Pair (TName a) (W a))
lookupSMStr s [] = Nothing
lookupSMStr s ((_ ,, n , x) :: sm) = s == nameStr (tName n) & \where
  True  -> Just (_ ,, n , x)
  False -> lookupSMStr s sm


---------------------

data IsSigs : Tys -> Ty -> Set

sigsToTms : {ts : Tys} -> IsSigs ts a -> Tm a -> Tms ts

data IsSigs where
  IS[] : IsSigs [] Top
  IS>> : {t : _} (is : IsSigs ts a) {f : _} -> ({xs : _} -> f # xs ~ t (sigsToTms is xs)) -> IsSigs (ts >> t) (Sigma a f)

sigsToTms IS[]        = \xs -> tt
sigsToTms (IS>> is e) = \xs -> f (fstSigma xs) ,, subst Tm e (sndSigma xs)  where
  f = sigsToTms is

LCtx' : Set
LCtx' = Tys ** \ts -> Pair (Ns ts) (Ty ** \a -> Pair (IsSigs ts a) (Tm a))

emptyLCtx' : LCtx'
emptyLCtx' = [] ,, [] , Top ,, IS[] , TT

addLCtx' : Name -> TName a -> LCtx' -> LCtx'
addLCtx' {a} ln n (ts ,, ns , aa ,, is , vars)
  = ts >> t ,, ns >> tName n , Sigma aa (MkTName ln := Lam' \xs -> RHS (t (ff xs))) ,, IS>> is Refl , vars ,, subst Tm believeMe~ (var n)
 where
  t = [[ ns , a ]]u
  ff = sigsToTms is


----------------------------------

Error : Set
Error = StringBuilder

TyTm : Set
TyTm = Ty ** Tm

Ctx : Set
Ctx = NameMap Tm

LCtx = NameMap \a -> Maybe (Tm a)

St : Set
St = Tys ** \ts -> Pair (Ns ts) (Tms ts)

mkSt : LCtx -> St
mkSt [] = [] ,, [] , tt
mkSt ((t ,, n , x) :: ctx) = mkSt ctx & \(ts ,, ns , tms) ->
  (ts >> [[ ns , t ]]u) ,, (ns >> tName n) , tms ,, [[ ns , fromMaybe (var n) x ]] tms


Fill : Ty -> Set
Fill a = (C : Set) -> FTmLR a -> C -> C

Fills = NameMap Fill

ShowEnv = NameMap \_ -> Doc

AtExpEnv : Nat -> Set
AtExpEnv = Vec (NameMap Tm)

postulate impossible : A

tail : {n : Nat} -> AtExpEnv (Suc n) -> AtExpEnv n
tail (_ :: as) = as

addAtExp' : TName a -> Tm a -> {n : Nat} -> AtExpEnv (Suc n) -> AtExpEnv (Suc n)
addAtExp' n t (ns :: nss) = ((_ ,, n , t) :: ns) :: nss

record TCState : Set where
  constructor MkTCState
  field
    counter   : Nat
    showEnv   : ShowEnv
    atExpEnv  : Nat ** AtExpEnv

open TCState

record TCEnv : Set where
  constructor MkTCEnv
  field
    globalEnv : Ctx
    localEnv  : LCtx
    localEnv' : LCtx'
    fillEnv   : Fills

open TCEnv

-- type checking monad
record TC (A : Set) : Set where
  coinductive
  field
    getTC : TCEnv -> TCState -> Pair TCState (Either Error A)

open TC

runTC : TC A -> Either Error A
runTC tc = Pair.snd (getTC tc (MkTCEnv emptySM emptySM emptyLCtx' emptySM) (MkTCState 100 emptySM (0 ,, [])))

newPName : String -> TC Name
getTC (newPName s) ctx (MkTCState c se ae) = MkTCState (Suc c) se ae , Right (MkName s c)

open import TCMonad

addLocal' : Name -> TName a -> Maybe (Tm a) ->  TC A -> TC A
getTC (addLocal' ln n d m) (MkTCEnv g l l' f) = getTC m (MkTCEnv g (insertSM n d l) (addLCtx' ln n l') f)

updateAtEnv : (Nat ** AtExpEnv -> Nat ** AtExpEnv) -> TC T
getTC (updateAtEnv tr) ctx (MkTCState c se ae) = MkTCState c se (tr ae) , Right tt

instance
  Monad[TC] : Monad TC
  getTC (Monad[TC] .pure x) _ c = c , Right x
  getTC (Monad[TC] ._>>=_ m f) ctx c = getTC m ctx c & \where
    (c , Left  e) -> c , Left e
    (c , Right x) -> getTC (f x) ctx c
  MonadError[TC] : MonadError StringBuilder TC
  getTC (MonadError[TC] .throwError e) _ c = c , Left e

instance
  TCM : TCMonad TC
  TCM .lookupShow s .getTC env c = lookupSM s (showEnv c) & \where
    (Just x) -> c , Right True
    Nothing  -> c , Right False
  TCM .addShow s d .getTC e (MkTCState c se ae) = MkTCState c (insertSM s d se) ae , Right tt
  TCM .delShow s .getTC e (MkTCState c se ae) = MkTCState c (deleteSM s se) ae , Right tt
  TCM .newNameT s = do
    n <- newPName s
    pure (MkTName n)
  TCM .addLocal n m = do
    _ <- updateAtEnv \ where (n ,, xs) -> (Suc n) ,, [] :: xs
    ln <- newPName "lam"
    r <- addLocal' ln n Nothing m
    _ <- updateAtEnv λ where
      (Zero ,, _) → impossible
      (Suc n ,, _ :: xs) → n ,, xs
    pure r

open import Printer TC
open import Conversion TC

catchError : TC A -> (Error -> TC A) -> TC A
getTC (catchError m f) ctx c = getTC m ctx c & \where
  (c , Left  e) -> getTC (f e) ctx c
  (c , Right x) -> c , Right x

newPPName : String -> TC String
getTC (newPPName s) ctx (MkTCState c se ae) = MkTCState (Suc c) se ae , Right (s <> showNat c)

addGlobal : TName a -> TmLR a -> TC A -> TC A
getTC (addGlobal s d m) (MkTCEnv g l l' f) = getTC m (MkTCEnv (insertSM s (s := d) g) l l' f)

addLocal'' : TName a -> Tm a -> TC A -> TC A
getTC (addLocal'' n t m) (MkTCEnv g l l' f) =
  mkSt l & \(ts ,, ns , tms) -> getTC m (MkTCEnv g (insertSM (coe believeMe~ n) (Just ([[ ns , t ]] tms)) l) l' f)

futureTC : TName a -> (FTmLR a -> TC A) -> TC A
futureTC n f = future \get set -> addFill n set (f get)  where
  addFill : TName a -> Fill a -> TC A -> TC A
  getTC (addFill s d m) (MkTCEnv g l l' f) = getTC m (MkTCEnv g l l' (insertSM s d f))

lookupFill' : String -> (Ty ** Fill -> TC A) -> TC A -> TC A
lookupFill' n cont err = do
  Just (_ ,, n , f) <- lookupFill n  where
    Nothing -> err
  delFill n (cont (_ ,, f))
 where
  delFill : TName a -> TC A -> TC A
  getTC (delFill s m) (MkTCEnv g l l' f) = getTC m (MkTCEnv g l l' (deleteSM s f))

  lookupFill : String -> TC (Maybe (Ty ** \a -> Pair (TName a) (Fill a)))
  getTC (lookupFill s) env c = c , Right (lookupSMStr s (fillEnv env))

appFill : Fill a -> FTmLR a -> TC TyTm -> TC TyTm
appFill f x = f _ x

addAtExp : TName a -> Tm a -> TC T
addAtExp n t = updateAtEnv \ where
  (Zero ,, _) -> impossible
  (m@(Suc _) ,, xs) -> m ,, addAtExp' n t xs

getShows : TC ShowEnv
getTC getShows env c = c , Right (showEnv c)

locals : TC LCtx
getTC locals env c = c , Right (localEnv env)

locals' : TC LCtx'
getTC locals' env c = c , Right (localEnv' env)

evalTC : {A : Set} -> TCEnv → TCState → TC A → Pair TCState (Either Error A)
evalTC x x₁ x₂ = getTC x₂ x x₁

showLocals : LCtx -> TC StringBuilder
showLocals [] = ""
showLocals ((a ,, n , Nothing) :: ls) = showLocals ls <>m "\n" <>m showDoc <$>  (printName (tName n) [ ":" ]m printTm a)
showLocals ((a ,, n , Just t)  :: ls) = showLocals ls <>m "\n" <>m showDoc <$> ((printName (tName n) [ ":" ]m printTm a) [ "=" ]m printTm t)

showContext : Ctx -> TC StringBuilder
showContext [] = ""
showContext ((a ,, n , x) :: ls) = showContext ls <>m "\n" <>m showDoc <$> (printName (tName n) [ ":" ]m printTm a) [ "=" ]m printTm x

lookupTm : String -> TC TyTm
getTC (lookupTm s) env c = lookupSMStr s (localEnv env) & \where
  (Just (_ ,, n , Nothing))  -> c , Right (_ ,, var n)
  (Just (_ ,, n , Just d ))  -> c , Right (_ ,, d)
  Nothing -> lookupSMStr s (concat' (snd (atExpEnv c))) & \where
    (Just (_ ,, n , x))  -> c , Right (_ ,, x)
    Nothing              -> lookupSMStr s (globalEnv env) & \where
      (Just (_ ,, n , x))  -> c , Right (_ ,, x)
      Nothing              -> evalTC env c (do
          loc <- showLocals (env .localEnv)
          at <- showContext (concat' (snd (atExpEnv c)))
          throwError ("Not defined: " <> fromString s <>
            "\n local context: " <> loc <>
            "\n at context: " <> at ))

--------------------


newTName : Doc -> TC (TName a)
newTName (Var n) = newNameT n
newTName d = throwError ("variable name expected instead of: " <> showDoc d)

--------------------

mkLam : TName a -> Tm a' -> TC (Tm (a => a'))
mkLam {a} {a'} n e = do
  ts ,, ns , aa ,, is , vars <- locals'
  n1 <- newNameT "lam"
  n2 <- newNameT "lam"

  let e' : CTm (ts >> [[ ns , a ]]u) [[ ns >> tName n , a' ]]u
      e' = [[_,_]] {ts = ts >> [[ ns , a ]]u} (ns >> tName n) e

      e'' : (xs : Tms (ts >> [[ ns , a ]]u)) -> Tm ([[ ns , a' ]]u (fst xs))
      e'' = coe believeMe~ e'

      ff = sigsToTms is

      t = [[ ns , a => a' ]]u

      up : Tm (Pi aa (n1 := Lam' \xs -> RHS (t (ff xs))))
      up = n2 := DLam' \xs -> Lam' \x -> RHS (e'' (ff xs ,, x))

  pure (coe believeMe~ (up ## vars))

mkDLam : (n : TName a) -> Tm (b # var n) -> TC (Tm (Pi a b))
mkDLam {a} {b} n e = do
  ts ,, ns , aa ,, is , vars <- locals'
  n1 <- newNameT "lam"
  n2 <- newNameT "lam"

  let e' : CTm (ts >> [[ ns , a ]]u) [[ ns >> tName n , b # var n ]]u
      e' = [[_,_]] {ts = ts >> [[ ns , a ]]u} (ns >> tName n) e

      e'' : ((xs ,, x) : Tms (ts >> [[ ns , a ]]u)) -> Tm ([[ ns , b ]] xs # x)
      e'' = coe believeMe~ e'

      ff = sigsToTms is

      t = [[ ns , Pi a b ]]u

      up : Tm (Pi aa (n1 := Lam' \xs -> RHS (t (ff xs))))
      up = n2 := DLam' \xs -> DLam' \x -> RHS (e'' (ff xs ,, x))

  pure (coe believeMe~ (up ## vars))

------------------------


printGoal : Ty -> TC A

infer : Doc -> TC TyTm

check : Doc -> (a : Ty) -> TC (Tm a)
check (n [ "@" ] e) a = do
  n <- newTName {a} n
  g <- check e a
  _ <- addAtExp n g
  pure g
check (KW "Paren" (x :: [])) a = check x a
check (KW "Left" (x :: [])) (a \/ a') = do
  x <- check x a
  pure (Left x)
check (KW "Right" (x :: [])) (a \/ a') = do
  x <- check x a'
  pure (Right x)
check (sn [ "." ] e) (a => a') = do
  n <- newTName sn
  e <- addLocal n (check e a')
  mkLam n e
check (sn [ "." ] e) (Pi a b)  = do
  n <- newTName sn
  e <- addLocal n (check e (b # var n))
  mkDLam n e
check (x [ "," ] x') (a * a') = do
  x  <- check x  a
  x' <- check x' a'
  pure (x , x')
check (x [ "," ] y) (Sigma a b) = do
  x <- check x  a
  y <- check y (b # x)
  pure (x ,, y)
check (KW "Refl" []) (Id x y) = do
  Refl <- convert x y <&> match'
  pure Refl
check (KW "Wrap" (x :: [])) (Rec rc ps) = do
  x <- check x (rFields rc # ps)
  pure (Wrap x)
check (KW "?" []) a = printGoal a
check d a = do
  a' ,, t <- infer d
  Refl <- convert a' a <&> match'
  pure t

infer (KW "Paren" (x :: [])) = infer x
infer (n [ "@" ] d) = do
  (_ ,, t) <- infer d
  n <- newTName n
  _ <- addAtExp n t
  pure (_ ,, t)
infer (KW "U" []) = do
  pure (U ,, U)
infer (KW "Bot" []) = do
  pure (U ,, Bot)
infer (KW "Top" []) = do
  pure (U ,, Top)
infer (a [ "*" ] a') = do
  a  <- check a  U
  a' <- check a' U
  pure (U ,, a * a')
infer (a [ "+" ] a') = do
  a  <- check a  U
  a' <- check a' U
  pure (U ,, a \/ a')
infer (a [ "->" ] a') = do
  a  <- check a  U
  a' <- check a' U
  pure (U ,, a => a')
infer (KW "Pi" (a :: b :: [])) = do
  a <- check a U
  b <- check b (a => U)
  pure (U ,, Pi a b)
infer (KW "Sigma" (a :: b :: [])) = do
  a <- check a U
  b <- check b (a => U)
  pure (U ,, Sigma a b)
infer (x [ "==" ] y) = do
  a ,, x <-  catchError (infer x) \ x₁ -> do
    b ,, y <- catchError (infer y) λ x₂ → throwError (x₁ <> fromString "\n\nAND\n\n" <> x₂)
    x <- check x b
    pure (U ,, Id x y)
  y <- check y a
  pure (U ,, Id x y)
infer (KW "TT" []) = do
  pure (Top ,, TT)
infer (x [ "," ] x') = do
  a  ,, x  <- infer x
  a' ,, x' <- infer x'
  pure (a * a' ,, (x , x'))
infer (f $d x) = infer f >>= matchPi  where
  matchPi : TyTm -> TC TyTm
  matchPi (a => a' ,, f) = do
    x <- check x a
    pure (a' ,, f # x)
  matchPi (Pi a b ,, f) = do
    x <- check x a
    pure (b # x ,, f ## x)
  matchPi (t ,, _) = throwErrorM ("matchPi: " <>m showTm t)
infer (Var n) = lookupTm n
infer d = throwError ("infer: " <> showDoc d)

------------------------

CTmLR : (ts : Tys) -> CTy ts -> Set
CTmLR ts t = (xs : Tms ts) -> TmLR (t xs)

mkId : {x x' : Tm a} -> x ~ x' -> Tm (Id x x')
mkId e = match e & \{Refl -> Refl}

quoteTmLR : {a : Ty} -> FTmLR a -> ((ts ,, ns) : TysN) -> CTmLR ts [[ ns , a ]]u
quoteTmLR (Lam {a} {a'} n t) ts'@(ts ,, ns) = \xs -> Lam' \x -> t' (xs ,, x)
 where
  t' : ((xs ,, x) : Tms (ts >> [[ ns , a ]]u)) -> TmLR ([[ ns , a' ]]u xs)
  t' = coe believeMe~ (quoteTmLR t (ts' >>> n))
quoteTmLR (DLam {a} {b} n t) ts'@(ts ,, ns) = \xs -> DLam' \x -> t' (xs ,, x)
 where
  t' : ((xs ,, x) : Tms (ts >> [[ ns , a ]]u)) -> TmLR ([[ ns , b ]] xs # x)
  t' = coe believeMe~ (quoteTmLR t (ts' >>> n))
quoteTmLR (MatchEither {a} {a'} {a''} p n k e n' k' e') ts'@(ts ,, ns)
  = \xs -> p' xs &in \where
    (Left  x) ee -> subst TmLR (strengthen a'' *~ strengthen a'') (t1 ((xs ,, x) ,, mkId (sym ee)))
    (Right x) ee -> subst TmLR (strengthen a'' *~ strengthen a'') (t2 ((xs ,, x) ,, mkId (sym ee)))
    _ _ -> stuckTmLR
 where
  p' = [[ ns , p ]]
  t1 = quoteTmLR e  (ts' >>> n  >>p tName k  :: (\(xs' ,, y) -> Id (Left  y) (p' xs')))
  t2 = quoteTmLR e' (ts' >>> n' >>p tName k' :: (\(xs' ,, y) -> Id (Right y) (p' xs')))
quoteTmLR (MatchBot p) ts
  = \xs -> stuckTmLR
quoteTmLR (MatchJ tm p lhs) ts'@(ts ,, ns)
  = \xs -> subst TmLR believeMe~ (jRule (tm' xs) (\y e -> p' xs ## y # e) (subst TmLR believeMe~ (lhs' xs)))
 where
  p'   = [[ ns , p ]]
  tm'  = [[ ns , tm ]]
  lhs' = quoteTmLR lhs ts'
quoteTmLR (MatchK tm p lhs) ts'@(ts ,, ns)
  = \xs -> subst TmLR believeMe~ (kRule (tm' xs) (\e -> p' xs # e) (subst TmLR believeMe~ (lhs' xs)))
 where
  p'   = [[ ns , p ]]
  tm'  = [[ ns , tm ]]
  lhs' = quoteTmLR lhs ts'
quoteTmLR (RHS t) (ts ,, ns) = \xs -> RHS (t' xs)
 where
  t' = [[ ns , t ]]

quoteFTmLR : FTmLR a -> TmLR a
quoteFTmLR t = subst TmLR [[]]u[] (quoteTmLR t ([] ,, []) tt)

newTName' : Doc -> TC (Pair (TName a) Doc)
newTName' (Paren d) = newTName' d
newTName' (n [ "." ] d) = do
  n <- newTName n
  pure (n , d)
newTName' d = throwError ("lambda expected instead of: " <> showDoc d)

----------------------------------------

checkLHS : Doc -> (a : Ty) -> TC (FTmLR a)
checkLHS (n [ "." ] t) (a => a') = do
  n <- newTName n
  t <- addLocal n (checkLHS t a')
  pure (Lam n t)
checkLHS (n [ "." ] t) (Pi a b) = do
  n <- newTName n
  t <- addLocal n (checkLHS t (b # var n))
  pure (DLam n t)
checkLHS ((p [ "=>" ] ds) $d e) a'' = checkMatch (optEq ds) a''
 where
  checkMatch : Doc -> (a : Ty) -> TC (FTmLR a)
  checkMatch (KW "Wrap" (n :: [])) a'' = do
    Rec _ _ ,, p <- infer p where  
      r ,, _ -> throwErrorM ("unwrap: " <>m showTm r)
    n <- newTName n
    addLocal'' n (proj p) (checkLHS e a'')
  checkMatch (n [ "," ] n') a'' = do
    _ * _ ,, p <- infer p where
      Sigma _ _ ,, p -> do
        n   <- newTName n
        n'  <- newTName n'
        addLocal'' n (fstSigma p) (addLocal'' n' (sndSigma p) (checkLHS e a''))
      r ,, _ -> throwErrorM ("pair: " <>m showTm r)
    n   <- newTName n
    n'  <- newTName n'
    addLocal'' n (fst* p) (addLocal'' n' (snd* p) (checkLHS e a''))
  checkMatch d _ = throwError ("checkMatch: " <> showDoc d)
checkLHS (KW "either" (p :: e :: e' :: [])) a'' = do
  _ \/ _ ,, p <- infer p where
    r ,, _ -> throwErrorM ("either: " <>m showTm r)
  n , e <- newTName' e
  k , e <- newTName' e
  e <- addLocal n (addLocal k (checkLHS e a''))
  n' , e' <- newTName' e'
  k' , e' <- newTName' e'
  e' <- addLocal n' (addLocal k' (checkLHS e' a''))
  pure (MatchEither p n k e n' k' e')
checkLHS (KW "absurd" (p :: [])) a'' = do
  Bot ,, p <- infer p where
    r ,, _ -> throwErrorM ("absurd: " <>m showTm r)
  pure (MatchBot p)
checkLHS (KW "jRule" (e :: P :: w :: [])) a'' = do
  NU (Id' x y) ,, e <- infer e  where
    r ,, _ -> throwErrorM ("jRule: " <>m showTm r)
  P <- check P (jPTy x)
  Refl <- convert a'' (P ## y # e) <&> match'
  w <- checkLHS w (P ## x # Refl)
  pure (MatchJ e P w)
checkLHS (KW "kRule" (e :: P :: w :: [])) a'' = do
  NU (Id' x y) ,, e <- infer e  where
    r ,, _ -> throwErrorM ("kRule: " <>m showTm r)
  Refl <- convert x y <&> match'
  P <- check P (kPTy x)
  Refl <- convert a'' (P # e) <&> match'
  w <- checkLHS w (P # Refl)
  pure (MatchK e P w)
checkLHS d a = do
  t <- check d a
  pure (RHS t)

addFFI : String -> TC T
addFFI s = addShow (MkTName {a = Top} (MkName "FFI" 0)) (FFI s)

inferTop : Doc -> TC TyTm
inferTop (FFI hs [ ";" ] ds) = do
  _ <- addFFI hs
  inferTop ds
inferTop (((n [ ":" ] a) [ "=" ] t) [ ";" ] ds) = do
  _ <- updateAtEnv \ where (n ,, xs) -> (Suc n) ,, [] :: xs
    --(_::_ [])
  a <- check a U
  _ <- updateAtEnv \ where (n ,, xs) -> (Suc n) ,, [] :: xs
    --(_::_ [])
  t <- checkLHS t a
  _ <- updateAtEnv λ where
    (Zero ,, _) → impossible
    (Suc n ,, _ :: xs) → n ,, xs
  _ <- updateAtEnv λ where
    (Zero ,, _) → impossible
    (Suc n ,, _ :: xs) → n ,, xs
  n <- newTName n
  addGlobal n (quoteFTmLR t) (inferTop ds)
inferTop ((n [ "=" ] KW "record" (ps :: fs :: [])) [ ";" ] ds') = do
  ps <- check ps U
  dn <- newTName n
  fs <- check fs (ps => U)
  let desc = named (tName dn) (ps ,, fs)
  addGlobal dn (Lam' \x -> RHS (Rec desc x)) (inferTop ds')
inferTop ((n [ ":" ] a) [ ";" ] ds) = do
  _ <- updateAtEnv \ where (n ,, xs) -> (Suc n) ,, [] :: xs
    --(_::_ [])
  a <- check a U
  _ <- updateAtEnv λ where
    (Zero ,, _) → impossible
    (Suc n ,, _ :: xs) → n ,, xs
  n <- newTName {a = a} n
  --TODO: Add back the at-context to future
  futureTC n \t' -> addGlobal n (quoteFTmLR t') (inferTop ds)
inferTop ((n [ "::" ] a) [ ";" ] ds) = do
  a <- check a U
  n <- newTName {a = a} n
  addGlobal n stuckTmLR (inferTop ds)
inferTop ((Var n [ "=" ] t) [ ";" ] ds) = do
  lookupFill' n (\(a ,, fill) -> do
    t <- checkLHS t a
    appFill fill t (inferTop ds)
   ) (do
    a ,, t <- infer t
    n <- newNameT n
    addGlobal n (RHS t) (inferTop ds)
   )
inferTop (t [ ":" ] a) = do
  _ <- updateAtEnv \ where (n ,, xs) -> (Suc n) ,, [] :: xs
    --(_::_ [])
  a <- check a U
  t <- check t a
  _ <- updateAtEnv λ where
    (Zero ,, _) → impossible
    (Suc n ,, _ :: xs) → n ,, xs
  pure (a ,, t)
inferTop t = do
  _ <- updateAtEnv \ where (n ,, xs) -> (Suc n) ,, [] :: xs
    --(_::_ [])
  g <- infer t
  _ <- updateAtEnv λ where
    (Zero ,, _) → impossible
    (Suc n ,, _ :: xs) → n ,, xs
  pure g

tc : String -> Either Error TyTm
tc s = runTC (parse s >>= inferTop)

tc' : (s : String) -> {{IsRight (tc s)}} -> TyTm
tc' s = fromRight (tc s)

--------

testTC : tc' "f : Top -> U  = x. Top;  U : U"
       ~ (U ,, U)
testTC = Refl

testTC3 : tc' "id : U -> U  = x. x;  id U : U"
       ~ (U ,, U)
testTC3 = Refl

testTC4 : tc' "idFun : U -> U  = A. A -> A;  id : Pi U idFun  = A. x. x;  id U U : U"
       ~ (U ,, U)
testTC4 = Refl

renderHS : Doc -> Doc
renderHS (FFI s) = FFI s
renderHS d@(KW s x) = d
renderHS d@(Var s) = d
renderHS (a [ "." ] b) = _[_]_ (FFI "") "\\" {{Refl}} (_[_]_ (renderHS a) "->" {{Refl}} (renderHS b))
renderHS (a [ s ] b) = renderHS a [ s ] renderHS b

render : ShowEnv -> StringBuilder
render [] = ""
render ((_ ,, MkTName (MkName "FFI" 0) , FFI def) :: m) = render m <> "\n" <> fromString (stringFromList (trim (stringToList def))) where
  trim : List Char -> List Char
  trim (' ' :: cs) = trim cs
  trim cs = cs
render ((_ ,, n , def) :: m) = render m <> "\n" <> showDoc (printName' (tName n)) <> " = " <> showDoc (renderHS def)

render' : ShowEnv -> StringBuilder
render' [] = ""
render' ((_ ,, MkTName (MkName "FFI" 0) , Var def) :: m) = render' m
render' ((_ ,, n , def) :: m) = render' m <> "\n" <> showDoc (printName' (tName n)) <> " = " <> showDoc def

printGoal a = do
  ls <- locals
  ls <- showLocals ls
  a <- showTm a
  ss <- getShows
  throwError (render' ss <> "\n----------------\n" <> ls <> "\n----------------\n? : " <> a)

mainTC : List String -> String -> TC StringBuilder
mainTC ("hs" :: []) s = do
  d <- parse s
  a ,, t <- inferTop d
  t <- printTm t
  ss <- getShows
  pure (render ss <> "\nmain = " <> showDoc (renderHS t))
mainTC args s = do
  d <- parse s
  a ,, t <- inferTop d
  a <- printTm a
  t <- printTm t
  ss <- getShows
  pure (render' ss <> "\n------------------------------------------------\n" <> showDoc t <> "\n : " <> showDoc a)

main : IO T
main = do
  args <- getArgs
  interact \s -> runStringBuilder (fromEither (runTC (mainTC args s)) <> "\n")


