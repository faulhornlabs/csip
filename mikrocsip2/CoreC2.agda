{-
Same as CoreB.agda but neutral terms are added.
Printing is now possible.
Lam and ifTag is not a netural term; to achieve this LHS terms are separated from terms.
-}


{-# OPTIONS --type-in-type --rewriting --prop #-}

open import Agda.Builtin.String using (String; primStringAppend)
open import Agda.Builtin.Nat using (Nat) renaming (suc to S; zero to Z)


-------------------

infixl 9 _∙_     -- non-dependent application
infixl 9 _∙∙_    -- dependent application
infixl 9 _$_     -- non-dependent application
infixl 9 _$$_    -- dependent application
infixr 8 _∘~_    -- transitivity for _~_
infixr 8 _∘≈_    -- transitivity for _≈_
infixr 6 _=>_    -- non-dependent function type
infixr 6 _×_     -- non-dependent pair type
infixr 6 _::_    -- list/vector constructor
infix  3 _~_     -- inhomogenous Prop equality
infix  3 _≈_     -- homogenous Prop equality
infixr 3 _&_     -- flipped application for Prop
infixr 2 _+++_   -- string concatenation
infixr 2 _**_    -- dependent pair type (infix Σ)
infixr 0 _,_     -- non-dependent pair constructor
infixr 0 _,,_    -- dependent pair constructor


-------------------

record _**_ (A : Set) (B : A -> Set) : Set where
  constructor _,,_
  field
    fst : A
    snd : B fst

open _**_


data Sing {A : Set} : A -> Set where
  sing : (x : A) -> Sing x


---------------------

private variable
  A B C : Set
  P Q   : Prop

_&_ : P -> (P -> Q) -> Q
x & f = f x

------------------

data ⊥ : Prop where

exfalsoP : ⊥ -> P
exfalsoP ()

exfalso : ⊥ -> A
exfalso ()

not : Prop -> Prop
not P = P -> ⊥

---------------------

data _≈_ {A : Set} (a : A) : A -> Prop where
  Refl : a ≈ a

{-# BUILTIN REWRITE _≈_ #-}

sym≈ : {a a' : A} -> a ≈ a' -> a' ≈ a
sym≈ Refl = Refl

_∘≈_ : {a a' a'' : A} -> a ≈ a' -> a' ≈ a'' -> a ≈ a''
Refl ∘≈ e = e


---------------------

data _~_ {A : Set} (a : A) : {B : Set} -> B -> Prop where
  refl : a ~ a

sym~ : {a : A} {b : B} -> a ~ b -> b ~ a
sym~ refl = refl

cong~ : {B : A -> Set} {a a' : A} -> (f : (a : A) -> B a) -> a ~ a' -> f a ~ f a'
cong~ _ refl = refl

cong2~ : {B : A -> Set} {C : (a : A) -> B a -> Set} {a a' : A} {b : B a} {b' : B a'} -> (f : (a : A) (b : B a) -> C a b) -> a ~ a' -> b ~ b' -> f a b ~ f a' b'
cong2~ _ refl refl = refl

_∘~_ : {a : A} {b : B} {c : C} -> a ~ b -> b ~ c -> a ~ c
refl ∘~ e = e

coeP : P ~ Q → P → Q
coeP refl a = a

postulate
  coe~     : A ~ B → A → B
  coe~refl : {a : A} → coe~ refl a ≈ a

{-# REWRITE coe~refl #-}

coh : {a : A} {e : A ~ B} -> coe~ e a ~ a
coh {e = refl} = refl

-----------------------

homog : {a a' : A} -> a ~ a' -> a ≈ a'
homog refl = Refl

inhomog : {a a' : A} -> a ≈ a' -> a ~ a'
inhomog Refl = refl

coe≈ : A ≈ B → A → B
coe≈ e = coe~ (inhomog e)

cong≈ : {B : A -> Set} {a a' : A} -> (f : (a : A) -> B a) -> a ≈ a' -> f a ~ f a'
cong≈ _ Refl = refl

cong≈' : {a a' : A} -> (f : A -> B) -> a ≈ a' -> f a ≈ f a'
cong≈' f e = homog (cong≈ f e)


---------------------

data Fin : Nat -> Set where
  FZ : ∀ {n} -> Fin (S n)
  FS : ∀ {n} -> Fin n -> Fin (S n)

pattern 0f = FZ
pattern 1f = FS FZ
pattern 2f = FS (FS FZ)

---------------

data Dec (P : Prop) : Set where
  Yes : P     -> Dec P
  No  : not P -> Dec P

decFin : ∀ {n} -> (i j : Fin n) -> Dec (i ≈ j)
decFin FZ     FZ     = Yes Refl
decFin FZ     (FS _) = No \()
decFin (FS _) FZ     = No \()
decFin (FS n) (FS m) with decFin n m
... | Yes e = Yes (e & \{Refl -> Refl})
... | No  f = No \{Refl -> f Refl}

data FinVec : (n : Nat) (P : Fin n -> Prop) -> Prop where
  []   : ∀ {P} ->                                        FinVec Z     P
  _::_ : ∀ {n P} -> P FZ -> FinVec n (\f -> P (FS f)) -> FinVec (S n) P

indexFinVec : ∀ {n P} -> FinVec n P -> (f : Fin n) -> P f
indexFinVec (v :: vs) FZ     = v
indexFinVec (v :: vs) (FS s) = indexFinVec vs s

--------------------------------------------

record Named (A : Set) : Set where
  constructor named
  field
    name    : String
    unnamed : A

open Named

postulate
  -- True because 'named' is called only at the top level with distinct strings
  uniqueNames : {a a' : Named A} -> name a ≈ name a' -> a ≈ a'

----------------------

data Ty : Set

Tm : Ty -> Set

-- forward declaration of Ty constructors
u   : Ty
arr : Ty -> Ty -> Ty    -- _=>_

-- record description
record UnnamedRDesc : Set where
  constructor RD
  field
    rParams : Ty
    rFields : Tm (arr rParams u)

RDesc = Named UnnamedRDesc

rParams : RDesc -> Ty
rParams (named _ r) = UnnamedRDesc.rParams r

rFields : (r : RDesc) -> Tm (arr (rParams r) u)
rFields (named _ r) = UnnamedRDesc.rFields r

private variable
  a a' a'' : Ty
  t t'     : Tm a
  b        : Tm (arr a u)
  rc       : RDesc
  ps       : Tm (rParams rc)

data Spine  : Ty -> Set
data Lambda : Ty -> Set
data Glued  : Spine a -> Lambda a -> Prop

data TyNU : Set where
  Top'       :                              TyNU
  _=>'_ _×'_ _⊎'_ : Ty -> Ty ->             TyNU
  Pi' Sigma' : (a : Ty) -> Tm (arr a u) ->  TyNU
  Id'        : Tm a -> Tm a ->              TyNU
  RTC'       : ∀ rc -> Tm (rParams   rc) -> TyNU
  TLHS       : {s : Spine u} (l : Lambda u) -> Glued s l -> TyNU

data Ty where
  U   :         Ty
  NU  : TyNU -> Ty

pattern Top       = NU Top'
pattern _=>_ a a' = NU (a =>' a')
pattern _×_  a a' = NU (a ×'  a')
pattern _⊎_  a a' = NU (a ⊎'  a')
pattern Pi    a b = NU (Pi'    a b)
pattern Sigma a b = NU (Sigma' a b)
pattern Id   b c  = NU (Id' b c)
pattern RTC rc p  = NU (RTC' rc p)

u   = U
arr = _=>_

data TmNU : TyNU -> Set

Tm U      = Ty
Tm (NU a) = TmNU a

_∙_ : Tm (a => a') -> Tm a -> Tm  a'

data TmNU where
  TT    :                                                 Tm Top
  _,_   : Tm a -> Tm a' ->                                Tm (a × a')
  _,,_  : (x : Tm a) -> Tm (b ∙ x) ->                     Tm (Sigma a b)
  Left  : Tm a ->                                         Tm (a ⊎ a')
  Right : Tm a' ->                                        Tm (a ⊎ a')
  Refl  : (x : Tm a) ->                                   Tm (Id x x)
  RDC   : {ps : _} (args : Tm (rFields rc ∙ ps)) ->       Tm (RTC rc ps)
  LHS   : ∀ {a} {s : Spine (NU a)} (l : Lambda (NU a)) -> Glued s l -> Tm (NU a)


gLHS : {s : Spine a} (l : Lambda a) -> Glued s l -> Tm a
gLHS {a = U}    l g = NU (TLHS l g)
gLHS {a = NU _} l g =      LHS l g

-- LHS Terms
data TmL : Ty -> Set  where
  RHS   : Tm     a -> TmL a
  NoRHS : Lambda a -> TmL a

{-# NO_POSITIVITY_CHECK #-}
data Lambda where
  Lam   : (Tm a -> TmL a') ->            Lambda (a => a')
  DLam  : ((x : Tm a) -> TmL (b ∙ x)) -> Lambda (Pi a b)
  Stuck :                                Lambda a

neutToTm : Spine a -> Tm a

fstΣ : Tm (Sigma a b) -> Tm a

data Spine where
  Head : Named (Lambda a) ->             Spine a
  _$_  : Spine (a => a') -> Tm a ->      Spine a'
  _$$_ : Spine (Pi a b) -> (x : Tm a) -> Spine (b ∙ x)
  Fst× : Spine (a × a') ->               Spine a
  Snd× : Spine (a × a') ->               Spine a'
  FstΣ : Spine (Sigma a b) ->            Spine a
  SndΣ : (s : Spine (Sigma a b)) ->      Spine (b ∙ fstΣ (neutToTm s))
  Proj : ∀ {ps} -> Spine (RTC rc ps) ->  Spine (rFields rc ∙ ps)

data Glued where
  CHead : (t : Named (Lambda a)) ->                                                 Glued (Head t) (unnamed t)
  CLam  : ∀ {s : Spine (a => a')} {f x fx} -> Glued s (Lam  f) -> f x ≈ NoRHS fx -> Glued (s $  x) fx
  CDLam : ∀ {s : Spine (Pi a b)}  {f x fx} -> Glued s (DLam f) -> f x ≈ NoRHS fx -> Glued (s $$ x) fx
  C$    : ∀ {s : Spine (a => a')} {x} ->      Glued s Stuck ->                      Glued (s $  x) Stuck
  C$$   : ∀ {s : Spine (Pi a b)}  {x} ->      Glued s Stuck ->                      Glued (s $$ x) Stuck
  CFst× : ∀ {s : Spine (a × a')} ->           Glued s Stuck ->                      Glued (Fst× s) Stuck
  CSnd× : ∀ {s : Spine (a × a')} ->           Glued s Stuck ->                      Glued (Snd× s) Stuck
  CFstΣ : ∀ {s : Spine (Sigma a b)} ->        Glued s Stuck ->                      Glued (FstΣ s) Stuck
  CSndΣ : ∀ {s : Spine (Sigma a b)} ->        Glued s Stuck ->                      Glued (SndΣ s) Stuck
  CProj : ∀ {ps} {s : Spine (RTC rc ps)} ->   Glued s Stuck ->                      Glued (Proj s) Stuck

lhs∙ : ∀ {s : Spine (a => a')} {f x} -> Glued s (Lam f) -> (r : _) -> f x ≈ r -> Tm a'
lhs∙ c (RHS t)   e = t
lhs∙ c (NoRHS t) e = gLHS t (CLam c e)

LHS (Lam f) c ∙ x = lhs∙ c (f x) Refl
LHS Stuck   c ∙ x = gLHS {s = _ $ x} Stuck (C$ c)

----------------

lhs∙∙ : ∀ {s : Spine (Pi a b)} {f x} -> Glued s (DLam f) -> (r : _) -> f x ≈ r -> Tm (b ∙ x)
lhs∙∙ c (RHS t)   e = t
lhs∙∙ c (NoRHS t) e = gLHS t (CDLam c e)

_∙∙_ : Tm  (Pi a b) -> (x : Tm a) -> Tm (b ∙ x)
LHS (DLam {b = b} f) c ∙∙ x = lhs∙∙ c (f x) Refl
LHS Stuck            c ∙∙ x = gLHS Stuck (C$$ c)

fst× : Tm (a × a') -> Tm a
fst× (x , y) = x
fst× (LHS Stuck g) = gLHS Stuck (CFst× g)

snd× : Tm (a × a') -> Tm a'
snd× (x , y) = y
snd× (LHS Stuck g) = gLHS Stuck (CSnd× g)

fstΣ (x ,, y) = x
fstΣ (LHS Stuck g) = gLHS Stuck (CFstΣ g)

{-# TERMINATING #-}
glued : {s : Spine a} (t : Lambda a) (g : Glued s t) -> neutToTm s ≈ gLHS t g

sndΣ : (t : Tm (Sigma a b)) -> Tm (b ∙ fstΣ t)
sndΣ (x ,, y) = y
sndΣ {b = b} (LHS Stuck g) = coe≈ (cong≈' (\k -> Tm (b ∙ fstΣ k)) (glued Stuck g)) (gLHS Stuck (CSndΣ g))

proj : ∀ {ps} -> Tm (RTC rc ps) -> Tm (rFields rc ∙ ps)
proj (RDC args) = args
proj (LHS Stuck g) = gLHS Stuck (CProj g)


---------------------

neutToTm (Head f) = gLHS (unnamed f) (CHead f)
neutToTm (f $  x) = neutToTm f ∙  x
neutToTm (f $$ x) = neutToTm f ∙∙ x
neutToTm (Fst× t) = fst× (neutToTm t)
neutToTm (Snd× t) = snd× (neutToTm t)
neutToTm (FstΣ t) = fstΣ (neutToTm t)
neutToTm (SndΣ t) = sndΣ (neutToTm t)
neutToTm (Proj t) = proj (neutToTm t)

glued {s = Head _} _ (CHead _) = Refl
glued {s = s $  x} _ (C$ c) = cong≈' (\f -> f ∙ x) (glued Stuck c)
glued {s = s $  x} t (CLam {f = f} c e) = helper Refl e (cong≈' (\f -> f ∙ x) (glued (Lam _) c))
   where
    helper : {fx : _} (ee : f x ≈ fx) -> fx ≈ NoRHS t -> neutToTm s ∙ x ≈ lhs∙ c fx ee -> neutToTm s ∙ x ≈ gLHS t (CLam c e)
    helper _ Refl cc = cc
glued {s = s $$ x} _ (C$$ c) = cong≈' (\f -> f ∙∙ x) (glued Stuck c)
glued {s = s $$ x} t (CDLam {a = a} {b = b} {f = f} c e) = helper Refl e (cong≈' (\f -> f ∙∙ x) (glued (DLam _) c))
   where
    helper : {fx : _} (ee : f x ≈ fx) -> fx ≈ NoRHS t -> neutToTm s ∙∙ x ≈ lhs∙∙ c fx ee -> neutToTm s ∙∙ x ≈ gLHS t (CDLam c e)
    helper _ Refl cc = cc
glued {s = Fst× s} _ (CFst× c) = cong≈' fst× (glued Stuck c)
glued {s = Snd× s} _ (CSnd× c) = cong≈' snd× (glued Stuck c)
glued {s = FstΣ s} _ (CFstΣ c) = cong≈' fstΣ (glued Stuck c)
glued {s = SndΣ s} _ (CSndΣ c) = homog (cong≈ sndΣ (glued Stuck c) ∘~ coh)
glued {s = Proj s} _ (CProj c) = cong≈' proj (glued Stuck c)

-----------------------

onLHS : Tm a -> (Tm a -> TmL a) -> TmL a
onLHS {a = NU _} (LHS _ _) match = NoRHS Stuck
onLHS t match = match t

-----------------------

elimSigma : ∀ {r} ->
  (tm : Tm (Sigma a b)) -> 
  (match : (x : Tm a) (y : Tm (b ∙ x)) -> (x ,, y) ≈ tm -> TmL r) ->
    TmL r
elimSigma (x ,, y)  match = match x y Refl
elimSigma (LHS _ _) match = NoRHS Stuck

-----------------------

elimRDC : ∀ {a} {params : _} ->
  (tm    : Tm (RTC rc params)) ->
  (match : (args : Tm (rFields rc ∙ params)) -> RDC args ≈ tm -> TmL a) ->
    TmL a
elimRDC (RDC args) match = match args Refl
elimRDC (LHS _ _)  match = NoRHS Stuck

-----------------------

elim⊎ :
  (tm : Tm (a ⊎ a')) ->
  ((t : Tm a)  -> Left  t ≈ tm -> TmL a'') ->
  ((t : Tm a') -> Right t ≈ tm -> TmL a'') ->
    TmL a''
elim⊎ (Left  t) l r = l t Refl
elim⊎ (Right t) l r = r t Refl
elim⊎ (LHS _ _) _ _ = NoRHS Stuck

-----------------------

elimId :
  {x y : Tm a} ->
  (tm : Tm (Id x y)) ->
  ((t : Tm a) -> Refl t ~ tm -> TmL a') ->
    TmL a'
elimId (Refl x)  match = match x refl
elimId (LHS _ _) match = NoRHS Stuck


--------------------

record T : Set where
  constructor tt

record Emb (P : Prop) : Set where
  constructor emb
  field
    getProp : P

data Either (A B : Set) : Set where
  Left  : A -> Either A B
  Right : B -> Either A B

⟦_⟧ : Ty -> Set
⟦_⟧ₜ : Tm a -> ⟦ a ⟧
⟦_⟧ₛ : Spine a -> ⟦ a ⟧
⟦_⟧ₐ : Lambda a -> ⟦ a ⟧

⟦ U   ⟧ = Set
⟦ Top ⟧ = T
⟦ a => a' ⟧ = ⟦ a ⟧ -> ⟦ a' ⟧
⟦ a ×  a' ⟧ = ⟦ a ⟧ ** \_ -> ⟦ a' ⟧
⟦ a ⊎  a' ⟧ = Either ⟦ a ⟧ ⟦ a' ⟧
⟦ Pi    a b ⟧ = (x : ⟦ a ⟧) -> ⟦ b ⟧ₜ x
⟦ Sigma a b ⟧ = ⟦ a ⟧ ** \x -> ⟦ b ⟧ₜ x
⟦ Id x y ⟧   = Emb (⟦ x ⟧ₜ ≈ ⟦ y ⟧ₜ)
⟦ RTC rc x ⟧ = ⟦ rFields rc ⟧ₜ ⟦ x ⟧ₜ 
⟦ NU (TLHS {s = s} _ _) ⟧ = ⟦ s ⟧ₛ

he : (f : Tm (a => U)) (x : Tm a) -> ⟦ f ∙ x ⟧ ≈ ⟦ f ⟧ₜ ⟦ x ⟧ₜ
he (LHS (Lam f) g) x = {!!}
he (LHS Stuck g) x = {!!}

{-# TERMINATING #-}
⟦_⟧ₜ {a = U}    t = ⟦ t ⟧
⟦_⟧ₜ {a = NU _} TT = tt
⟦_⟧ₜ {a = NU _} (x ,  y) = ⟦ x ⟧ₜ ,, ⟦ y ⟧ₜ
⟦_⟧ₜ {a = NU _} (_,,_ {b = b} x y) = ⟦ x ⟧ₜ ,, coe≈ (he b x) ⟦ y ⟧ₜ
⟦_⟧ₜ {a = NU _} (Left  x) = Left  ⟦ x ⟧ₜ
⟦_⟧ₜ {a = NU _} (Right x) = Right ⟦ x ⟧ₜ
⟦_⟧ₜ {a = NU _} (Refl _) = emb Refl
⟦_⟧ₜ {a = NU _} (RDC {rc = rc} args) = coe≈ (he (rFields rc) _) ⟦ args ⟧ₜ
⟦_⟧ₜ {a = NU _} (LHS {s = s} _ _) = ⟦ s ⟧ₛ

⟦ Head (named _ f) ⟧ₛ = ⟦ f ⟧ₐ
⟦ s $  x ⟧ₛ = ⟦ s ⟧ₛ ⟦ x ⟧ₜ
⟦ _$$_ {b = b} s x ⟧ₛ = coe≈ (sym≈ (he b x)) (⟦ s ⟧ₛ ⟦ x ⟧ₜ)
⟦ Fst× s ⟧ₛ = fst ⟦ s ⟧ₛ
⟦ Snd× s ⟧ₛ = snd ⟦ s ⟧ₛ
⟦ FstΣ s ⟧ₛ = fst ⟦ s ⟧ₛ
⟦ SndΣ {b = b}   s ⟧ₛ = coe≈ (sym≈ {!!}) (snd ⟦ s ⟧ₛ)
⟦ Proj {rc = rc} s ⟧ₛ = coe≈ (sym≈ (he (rFields rc) _)) ⟦ s ⟧ₛ

-- TODO: add Env
⟦ Lam  f ⟧ₐ = \x -> {!!}
⟦ DLam f ⟧ₐ = \x -> {!!}
⟦ Stuck  ⟧ₐ = {!!}   -- postulated -- should be impossible?


--------------------
{-
data Bool : Set where True False : Bool

_&&_ : Bool -> Bool -> Bool
False && _ = False
True  && a = a

data Dec' (A : Set) : Set where
  Yes : A -> Dec' A
  No  :      Dec' A

-- convertible types
data Ty~ : Ty -> Ty -> Set where
  -- TODO

coeTm : Ty~ a a' -> Tm a -> Tm a'
coeTm = {!!} -- TODO

data Tm~' : {a : TyNU} -> TmNU a -> TmNU a -> Set where
  EtaTT : ∀ {t t'} -> Tm~' {a = Top'} t t'
  -- ...

Tm~  : {a : Ty} -> Tm a -> Tm a -> Set
Tm~ {a = U} t t' = Ty~ t t'
Tm~ {a = Top} t t' = Tm~' t t'
Tm~ {a = a => a₁} t t' = Tm~' t t'
Tm~ {a = a × a₁} t t' = Tm~' t t'
Tm~ {a = Pi a x} t t' = Tm~' t t'
Tm~ {a = Sigma a x} t t' = Tm~' t t'
Tm~ {a = RTC rc x} t t' = Tm~' t t'
Tm~ {a = TC tc x} t t' = Tm~' t t'
Tm~ {a = TLHS l x} t t' = Tm~' t t'

convTy  : Nat -> (a a' : Ty) -> Dec' (Ty~ a a')
convTmNU : ∀ {a} -> Nat -> (t t' : TmNU a) -> Dec' (Tm~' t t')
convTm  : Nat -> (t t' : Tm  a) -> Dec' (Tm~ t t')

convTy i U U = Yes {!!}
convTy i Top Top = Yes {!!}
convTy i (a => b) (a' => b') with convTy i a a' | convTy i b b'
... | Yes e | Yes e' = Yes {!!}
... | e | e' = {!!}
convTy i (a × b) (a' × b') = {!!}
convTy i (Pi a b) (Pi a' b') with convTy i a a'
... | Yes e = {!!}
... | No = {!!}
convTy i (Sigma a b) (Sigma a' b') = {!!}
convTy i (RTC rc x) (RTC rc' x') = {!!}
convTy i (TC tc x) (TC tx' x') = {!!}
convTy i (TLHS l g) (TLHS l' g') = {!!}
convTy i _ _ = {!!}

convTmNU {a = Top'} i _ _ = Yes EtaTT
convTmNU {a = a =>' a'} i t t' = {!!}
convTmNU {a = a ×' a'} i t t' = {!!} -- with convTm i (fst× t) (fst× t') | convTm i (snd× t) (snd× t')
-- ... | Yes e | Yes e' = {!!}
convTmNU {a = Pi' a b} i t t' = {!!}
convTmNU {a = Sigma' a b} i t t' = {!!}
convTmNU {a = RTC' rc x} i t t' = {!!}
convTmNU {a = TC' tc x} i t t' = {!!}
convTmNU {a = TLHS l g} i t t' = {!!}

convTm {a = U} i t t' = convTy i t t'
convTm {a = Top} i t t' = convTmNU i t t'
convTm {a = a => a'} i t t' = convTmNU i t t'
convTm {a = a × a'} i t t' = convTmNU i t t'
convTm {a = Pi a b} i t t' = convTmNU i t t'
convTm {a = Sigma a b} i t t' = convTmNU i t t'
convTm {a = RTC rc x} i t t' = convTmNU i t t'
convTm {a = TC tc x} i t t' = convTmNU i t t'
convTm {a = TLHS l g} i t t' = convTmNU i t t'
-}

-------------------------------------

_+++_ : String -> String -> String
a +++ b = primStringAppend a b

parens : String -> String
parens a = "(" +++ a +++ ")"

data Doc : Set where
  DVar : String ->        Doc
  DLam : String -> Doc -> Doc
  _$_  : Doc -> Doc ->    Doc

showDoc' : Nat -> Nat -> Doc -> String
showDoc' _ _ (DVar n)   = n
showDoc' p 1 (DLam n d) = parens ("\\" +++ n +++ " -> " +++ showDoc' 0 0 d)
showDoc' p q (DLam n d) =         "\\" +++ n +++ " -> " +++ showDoc' 0 q d
showDoc' 1 q (a $ b)    = parens (showDoc' 0 1 a +++ " " +++ showDoc' 1 0 b)
showDoc' p q (a $ b)    =         showDoc' p 1 a +++ " " +++ showDoc' 1 q b

showDoc = showDoc' Z Z

testDoc : showDoc (DLam "a" (DVar "a" $ DVar "b") $ (DVar "c" $ DVar "e") $ DVar "d" $ DLam "a" (DLam "b" (DVar "a")))
        ≈ "(\\a -> a b) (c e) d \\a -> \\b -> a"
testDoc = Refl


printTy    : Ty -> Doc
printTm    : Tm a -> Doc
printSpine : Spine a -> Doc

printSpine (Head x) = DVar (name x)
printSpine (s $  x) = printSpine s $ printTm x
printSpine (s $$ x) = printSpine s $ printTm x
printSpine (Fst× s) = DVar "fst"   $ printSpine s
printSpine (Snd× s) = DVar "snd"   $ printSpine s
printSpine (FstΣ s) = DVar "fstΣ"  $ printSpine s
printSpine (SndΣ s) = DVar "sndΣ"  $ printSpine s
printSpine (Proj s) = DVar "proj"  $ printSpine s

printTy U           = DVar "U"
printTy Top         = DVar "Top"
printTy (t => x)    = DVar "_=>_"    $ printTy t $ printTy x
printTy (a × a')    = DVar "_×_"     $ printTy a $ printTy a'
printTy (a ⊎ a')    = DVar "_⊎_"     $ printTy a $ printTy a'
printTy (Pi t x)    = DVar "Pi"      $ printTy t $ printTm x
printTy (Sigma a b) = DVar "_,_"     $ printTy a $ printTm b
printTy (Id x y)    = DVar "Id"      $ printTm x $ printTm y
printTy (RTC rc x)  = DVar (name rc) $ printTm x
printTy (NU (TLHS {s = s} _ _)) = printSpine s

printTm {a = U}    t  = printTy   t
printTm {a = NU _} TT = DVar "tt"
printTm {a = NU _} (x ,  y)  = DVar "_,_"   $ printTm x $ printTm y
printTm {a = NU _} (x ,, y)  = DVar "_,,_"  $ printTm x $ printTm y
printTm {a = NU _} (Left  x) = DVar "Left"  $ printTm x
printTm {a = NU _} (Right x) = DVar "Right" $ printTm x
printTm {a = NU _} (Refl x)  = DVar "Refl"  $ printTm x
printTm {a = NU _} (RDC {rc = rc} args) = DVar ("Mk" +++ name rc) $ printTm args
printTm {a = NU _} (LHS {s = s} _ _)    = printSpine s


showTm : Tm a -> String
showTm t = showDoc (printTm t)


----------------

pattern Lam'  f = NoRHS (Lam  f)
pattern DLam' f = NoRHS (DLam f)

def : String -> Lambda a -> Tm a
def n t = gLHS t (CHead (named n t))

var : String -> Tm a
var n = gLHS Stuck (CHead (named n Stuck))

{-


-}

lam' : String -> (Tm a -> TmL a') -> Tm (a => a')
lam' n f = def n (Lam f)

lam : String -> (Tm a -> Tm a') -> Tm (a => a')
lam n f = lam' n \t -> RHS (f t)

betaPi : ∀ {f : Tm a -> Tm a'} {x : _} -> lam "l" f ∙ x ≈ f x
betaPi = Refl

-- not True
-- etaPi : ∀ {f : Tm (a => a')} ->  f  ≈  lam "l" \x -> f ∙ x


const : Tm (a' => a => a')
const = def "const" (Lam \x -> Lam' \_ -> RHS x)

pi : (A : Ty) -> (Tm A -> Ty) -> Ty
pi A B = Pi A (lam "piLam" \a -> B a)

module _ where

  {-# TERMINATING #-}
  Nat' : Ty

  NatDesc = named "Nat" (RD Top (const ∙ (Top ⊎ Nat')))

  Nat' = RTC NatDesc TT

  Zero : Tm Nat'
  Zero = RDC (Left TT)

  Suc : Tm (Nat' => Nat')
  Suc = def "Suc" (Lam \n -> RHS (RDC (Right n)))

  {-# TERMINATING #-}
  add : Tm (Nat' => Nat' => Nat')
  add = def "add" (Lam \n -> Lam' \m -> elim⊎ (proj n)
      (\_ _ -> RHS m                     )
      (\k _ -> RHS (Suc ∙ (add ∙ k ∙ m)) )
    )

  addTest : add ∙ (Suc ∙ Zero) ∙ (Suc ∙ Zero) ≈ Suc ∙ (Suc ∙ Zero)
  addTest = Refl

  addTest' : (\n -> add ∙ (Suc ∙ Zero) ∙ n)    ≈ \n -> Suc ∙ n
  addTest' = Refl

  testQuote  : showTm {a = Nat'} (add ∙ (Suc ∙ Zero) ∙ (Suc ∙ Zero)) ≈ "MkNat (Right (MkNat (Right (MkNat (Left tt)))))"
  testQuote = Refl

  testQuote2 : showTm {a = Nat'} (add ∙ (Suc ∙ var {a = Nat'} "n") ∙ var {a = Nat'} "m")   ≈ "MkNat (Right (add n m))"
  testQuote2 = Refl


  {-# TERMINATING #-}
  Fin' : Tm (Nat' => U)

  FinDesc = named "Fin" (RD Nat' (lam "FinLam" \p ->
       Sigma Nat' (lam "Fin2" \n -> Id p (Suc ∙ n))
     ⊎ Sigma Nat' (lam "Fin3" \n -> Id p (Suc ∙ n) × Fin' ∙ n)
    ))

  Fin' = def "Fin" (Lam \n -> RHS (RTC FinDesc n))

  testQuote' : showTm (Pi Nat' (lam "f" \n -> Fin' ∙ (add ∙ (Suc ∙ n) ∙ n)))
                 ≈ "Pi (Nat tt) f"   -- could be:  "Pi (Nat tt) \\v0 -> Fin (add (Suc v0) v0)"
  testQuote' = Refl

  --------------------------------------

  SigmaDesc = named "Sigma" (RD
       (Sigma U (lam "SigL" \a -> a => U))
       (lam' "SigL2" \t -> elimSigma t \a b _ -> RHS (Sigma a (lam "SigL3" \x -> b ∙ x)))
    )

  Sigma'' : Tm (Pi U (lam "SL" \a -> (a => U) => U))
  Sigma'' = def "Sigma" (DLam \a -> Lam' \b -> RHS (RTC SigmaDesc (a ,, b)))

  Pair : Tm (pi U \a -> pi (a => U) \b -> pi (a) \x -> b ∙ x => (Sigma'' ∙∙ a ∙ b))
  Pair = def "Pair" (DLam \a -> DLam' \b -> DLam' \x -> Lam' \y -> RHS (RDC (x ,, y)))

  Fst' : Tm (pi U \a -> pi (a => U) \b -> (Sigma'' ∙∙ a ∙ b) => a)
  Fst' = def "fst" (DLam \a -> DLam' \b -> Lam' \p -> elimSigma (proj p) \a _ _ -> RHS a)

  Snd' : Tm (pi U \a -> pi (a => U) \b -> pi ((Sigma'' ∙∙ a ∙ b)) \t -> (b ∙ (Fst' ∙∙ a ∙∙ b ∙ t)))
  Snd' = def "snd" (DLam \A -> DLam' \B -> DLam' \p -> elimRDC p \p e -> elimSigma p \_ b e' -> RHS (coe~ (e & e' & \{Refl Refl -> refl}) b))

  betaFst : ∀ {a b} {x : Tm (a)} {y : Tm (b ∙ x)} -> Fst' ∙∙ a ∙∙ b ∙ (Pair ∙∙ a ∙∙ b ∙∙ x ∙ y) ≈ x
  betaFst = Refl

  betaSnd : ∀ {a b} {x : Tm (a)} {y : Tm (b ∙ x)} -> Snd' ∙∙ a ∙∙ b ∙∙ (Pair ∙∙ a ∙∙ b ∙∙ x ∙ y) ≈ y
  betaSnd = Refl
{-
  curry : {c : Ty} -> Tm ((Sigma' a b => c) => Pi a (lam "curryFun" \x -> code (b ∙ x => c)))
  curry = def "curry" (Lam' \f -> DLam' \x -> Lam \y -> RHS (f ∙ Pair x y))

  uncurry : {c : Ty} -> Tm (Pi a (lam "uncurryFun" \x -> code (b ∙ x => c)) => Sigma' a b => c)
  uncurry = def "uncurry" (Lam' \f -> Lam \p -> elimRDC p \p e -> elimSigma p \x y _ -> RHS (f ∙∙ x ∙ y))

  uncurry' : {c : Ty} -> Tm (Pi a (lam "uncurryFun'" \x -> code (b ∙ x => c)) => Sigma' a b => c)
  uncurry' = def "uncurry" (Lam' \f -> Lam \p -> RHS (f ∙∙ (Fst' ∙ p) ∙ (Snd' ∙∙ p)))
-}
  -------------------------

  etaSigma : Tm (pi U \a -> pi (a => U) \b -> pi ((Sigma'' ∙∙ a ∙ b)) \t ->
     Id t (Pair ∙∙ a ∙∙ b ∙∙ (Fst' ∙∙ a ∙∙ b ∙ t) ∙ (Snd' ∙∙ a ∙∙ b ∙∙ t)))
  etaSigma = def "etaSigma" (DLam \a -> DLam' \b -> DLam' \t ->
    elimRDC t \t' e -> elimSigma t' \x y e' -> RHS (coe~ (e & e' & \{Refl Refl -> refl}) (Refl (Pair ∙∙ a ∙∙ b ∙∙ x ∙ y)))
    )



