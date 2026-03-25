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
infixr 2 _**_    -- dependent pair type (infix Σ)
infixr 0 _,_     -- non-dependent pair constructor
infixr 0 _,,_    -- dependent pair constructor

infixr 2 _+++_


-------------------

record _**_ (A : Set) (B : A -> Set) : Set where
  pattern
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
opaque
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

subst≈ : (P : A -> Set) -> {a a' : A} -> a ≈ a' -> P a -> P a'
subst≈ P x x₁ = coe≈ (homog (cong≈ P x)) x₁

subst≈' : (P : A -> Prop) -> {a a' : A} -> a ≈ a' -> P a -> P a'
subst≈' _ Refl x₁ = x₁
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
  pattern
  constructor named
  field
    name    : String
    unnamed : A

open Named

postulate
  -- True because 'named' is called only at the top level with distinct strings
  uniqueNames : {a a' : Named A} -> name a ≈ name a' -> a ≈ a'

----------------------

data Ty :       Set

Tm : Ty -> Set

-- forward declaration of Ty constructors
u   : Ty
arr : Ty -> Ty -> Ty    -- _=>_

-- record description
record UnnamedRDesc : Set where
  inductive
  pattern
  constructor RD
  field
    rParams : Ty
    rFields : Tm (arr rParams u)

RDesc = Named UnnamedRDesc

rParams : RDesc -> Ty
rParams r = UnnamedRDesc.rParams (unnamed r)

rFields : (r : RDesc) -> Tm (arr (rParams r) u)
rFields r = UnnamedRDesc.rFields (unnamed r)

-- data constructor description
record DCDesc (indices : Ty) : Set where
  inductive
  pattern
  constructor DCD
  field
    dcName     : String   -- used only for pretty printing
    dcArgs     : Ty
    dcCodomain : Tm (arr dcArgs indices)

-- type constructor description
record UnnamedTCDesc : Set where
  inductive
  pattern
  constructor TCD
  field
    tcIndices  : Ty
    numOfCstrs : Nat
    dcDescs    : Fin numOfCstrs -> DCDesc tcIndices

TCDesc = Named UnnamedTCDesc

tcIndices : TCDesc -> Ty
tcIndices tc = UnnamedTCDesc.tcIndices (unnamed tc)

numOfCstrs : TCDesc -> Nat
numOfCstrs tc = UnnamedTCDesc.numOfCstrs (unnamed tc)

dcDescs : (tc : TCDesc) -> Fin (numOfCstrs tc) -> DCDesc (tcIndices tc)
dcDescs tc f = UnnamedTCDesc.dcDescs (unnamed tc) f

dcFin : TCDesc -> Set
dcFin tc = Fin (numOfCstrs tc)

dcArgs : (tc : TCDesc) -> dcFin tc -> Ty
dcArgs tc n = DCDesc.dcArgs (dcDescs tc n)

dcCodomain : (tc : TCDesc) -> (c : dcFin tc) -> Tm (arr (dcArgs tc c) (tcIndices tc))
dcCodomain tc n = DCDesc.dcCodomain (dcDescs tc n)

private variable
  a a' a'' : Ty
  t t'     : Tm a
  b        : Tm (arr a u)
  tc       : TCDesc
  rc       : RDesc

data Spine  : Ty -> Set
data Lambda : Ty -> Set
data Glued  : {a a' : Ty} -> Spine a -> Lambda a' -> Prop

Glued≈ : Spine a -> Lambda a -> Prop
Glued≈ = Glued

data Ty where
  U Top     :                              Ty
  _=>_ _×_  : Ty -> Ty ->                  Ty
  Pi Sigma  : (a : Ty) -> Tm (a => U) ->   Ty
  RTC       : ∀ rc -> Tm (rParams   rc) -> Ty
  TC        : ∀ tc -> Tm (tcIndices tc) -> Ty

  TLHS : {s : Spine U} (l : Lambda U) -> Glued≈ s l -> Ty

NotU : Ty -> Prop
NotU a = a ≈ U -> ⊥

u   = U
arr = _=>_

_∙_ : Tm (a => a') -> Tm a -> Tm  a'

data Tm' : Ty -> Set

Tm U = Ty
Tm a = Tm' a

data Tm' where
  TT   :                                                 Tm Top
  _,_  : Tm a -> Tm a' ->                                Tm (a × a')
  _,,_ : (x : Tm a) -> Tm (b ∙ x) ->                     Tm (Sigma a b)
  RDC  : {is : _} (args : Tm (rFields rc ∙ is)) ->       Tm (RTC rc is)
  DC   : (tag : dcFin tc) (args : Tm (dcArgs tc tag)) -> Tm (TC tc (dcCodomain tc tag ∙ args))

  TLHS : {s : Spine a} (l : Lambda a) -> Glued≈ s l -> NotU a -> Tm' a

destr : {a : Ty} -> {A : Tm a -> Set} -> (f : (c : Ty -> Tm a) -> (a' : Ty) -> A (c a')) -> (g : (c : Tm' a -> Tm a) -> (a' : Tm' a) -> A (c a')) -> (a' : Tm a) -> A a'
destr {U} {A} f g x = f (λ z → z) x
destr {Top} {A} f g x = g (λ z → z) x
destr {a => a₁} {A} f g x = g (λ z → z) x
destr {a × a₁} {A} f g x = g (λ z → z) x
destr {Pi a x₁} {A} f g x = g (λ z → z) x
destr {Sigma a x₁} {A} f g x = g (λ z → z) x
destr {RTC rc x₁} {A} f g x = g (λ z → z) x
destr {TC tc x₁} {A} f g x = g (λ z → z) x
destr {TLHS l x₁} {A} f g x = g (λ z → z) x

destr' : {a : Ty} -> {A : Ty -> Set} -> (f : {equ : a ≈ U}(c : Ty -> Tm a) -> A a) -> (g : {equ : not (a ≈ U)}(c : Tm' a -> Tm a) -> A a) -> A a
destr' {U} {A} f g = f {Refl} λ z → z
destr' {Top} {A} f g = g {λ ()} λ z → z
destr' {a => a₁} {A} f g = g {λ ()} λ z → z
destr' {a × a₁} {A} f g = g {λ ()} λ z → z
destr' {Pi a x} {A} f g = g {λ ()} λ z → z
destr' {Sigma a x} {A} f g = g {λ ()} λ z → z
destr' {RTC rc x} {A} f g = g {λ ()} λ z → z
destr' {TC tc x} {A} f g = g {λ ()} λ z → z
destr' {TLHS l x} {A} f g = g {λ ()} λ z → z

data Embe (A : Set) : Prop where
  Emb : A -> Embe A

data Ebme (A : Prop) : Set where
  Ebm : A -> Ebme A


LHS : {s : Spine a} (l : Lambda a) -> Glued≈ s l -> Tm a
--LHS {a} {s} l g = destr' {a} {Tm} (λ {eq} c → c (TLHS (subst≈  (λ x → Lambda x) eq l) (subst≈' (λ x →  Glued≈ {x} _ _) eq g))) λ {eq} c → c (TLHS l g eq)
--LHS {a} l g = destr' {a} (\{ {e} x -> coe≈ (sym≈ x) (TLHS (subst≈ Lambda e l) (subst≈' (\ u -> Glued≈ {u} _ _) e g))}) λ {equ} eq → coe≈ (sym≈ eq) (TLHS l g equ)

LHS {a = U}         l g = TLHS l g
LHS {a = Top}       l g = TLHS l g \()
LHS {a = _ => _}    l g = TLHS l g \()
LHS {a = _ × _}     l g = TLHS l g \()
LHS {a = Pi _ _}    l g = TLHS l g \()
LHS {a = Sigma _ _} l g = TLHS l g \()
LHS {a = RTC _ _}   l g = TLHS l g \()
LHS {a = TC _ _}    l g = TLHS l g \()
LHS {a = TLHS _ _}  l g = TLHS l g \()

-- LHS Terms
data TmL : Ty -> Set  where
  RHS   : Tm a ->     TmL a
  NoRHS : Lambda a -> TmL a

{-# NO_POSITIVITY_CHECK #-}
data Lambda where
  Lam   : (Tm a -> TmL a') ->            Lambda (a => a')
  DLam  : ((x : Tm a) -> TmL (b ∙ x)) -> Lambda (Pi a b)
  Stuck :                                Lambda a

fstSigma : Tm (Sigma a b) -> Tm a

data Spine where
  Head : Named (Lambda a) ->             Spine a
  _$_  : Spine (a => a') -> Tm a ->      Spine a'
  _$$_ : Spine (Pi a b) -> (x : Tm a) -> Spine (b ∙ x)
  Fst× : Spine (a × a') ->               Spine a
  Snd× : Spine (a × a') ->               Spine a'
  FstSigma : Spine (Sigma a b) ->        Spine a
  SndSigma : Spine (Sigma a b) ->  (s : Tm (Sigma a b)) -> Spine (b ∙ fstSigma s) --TODO: ???
  Proj : {rc : _}{t : Tm (rParams rc)}  -> Spine (RTC rc t) -> Spine (rFields rc ∙ t)
  --TODO: ?

data Glued where
  CHead    : (t : Named (Lambda a)) ->                                                  Glued≈ (Head t) (unnamed t)
  CStuck$  : ∀ {s : Spine (a => a')} {x} ->      Glued≈ s Stuck ->                      Glued≈ (s $  x) Stuck
  CStuck$$ : ∀ {s : Spine (Pi a b)}  {x} ->      Glued≈ s Stuck ->                      Glued≈ (s $$ x) Stuck
  CLam     : ∀ {s : Spine (a => a')} {f x fx} -> Glued≈ s (Lam  f) -> f x ≈ NoRHS fx -> Glued≈ (s $  x) fx
  CDLam    : ∀ {s : Spine (Pi a b)}  {f x fx} -> Glued≈ s (DLam f) -> f x ≈ NoRHS fx -> Glued≈ (s $$ x) fx
  CFst×    : ∀ {s : Spine (a × a')}   -> Glued≈ s Stuck -> Glued≈ (Fst× s) Stuck
  CSnd×    : ∀ {s : Spine (a × a')}   -> Glued≈ s Stuck -> Glued≈ (Snd× s) Stuck
  CFstSigma : ∀ {s : Spine (Sigma a b)} -> Glued≈ s Stuck -> Glued≈ (FstSigma s) Stuck
  CSndSigma : ∀ {s : Spine (Sigma a b)} {ba} -> Glued≈ s Stuck -> Glued≈ (SndSigma s ba ) Stuck
  CProj : ∀ {rc} {t : Tm (rParams rc)} {s : Spine (RTC rc t)} -> Glued≈ s Stuck -> Glued≈ (Proj s) Stuck
  -- TODO: ...


lhs∙ : ∀ {s : Spine (a => a')} {f x} -> Glued≈ s (Lam f) -> (r : _) -> f x ≈ r -> Tm a'
lhs∙ c (RHS t)   e = t
lhs∙ c (NoRHS t) e = LHS t (CLam c e)

TLHS         (Lam f) c _ ∙ x = lhs∙ c (f x) Refl
TLHS {s = s} Stuck   c _ ∙ x = LHS {s = s $ x} Stuck (CStuck$ c)

----------------

lhs∙∙ : ∀ {s : Spine (Pi a b)} {f x} -> Glued≈ s (DLam f) -> (r : _) -> f x ≈ r -> Tm (b ∙ x)
lhs∙∙ c (RHS t)   e = t
lhs∙∙ c (NoRHS t) e = LHS t (CDLam c e)

_∙∙_ : Tm  (Pi a b) -> (x : Tm a) -> Tm (b ∙ x)
TLHS (DLam {b = b} f) c _ ∙∙ x = lhs∙∙ c (f x) Refl
TLHS Stuck            c _ ∙∙ x = LHS Stuck (CStuck$$ c)

fst× : Tm (a × a') -> Tm a
fst× (x , y) = x
fst× (TLHS Stuck g nu) = LHS Stuck (CFst× g)

snd× : Tm (a × a') -> Tm a'
snd× (x , x₁) = x₁
snd× (TLHS Stuck g nu) = LHS Stuck (CSnd× g)

fstSigma (x ,, x₁) = x
fstSigma (TLHS Stuck x x₁) = LHS Stuck (CFstSigma x)

sndSigma : (t : Tm (Sigma a b)) -> Tm (b ∙ fstSigma t )
sndSigma (x ,, x₁) = x₁
sndSigma s@(TLHS Stuck x x₁) = LHS Stuck (CSndSigma {ba = s} x)

proj : ∀ {rc} {t : Tm (rParams rc)} -> Tm (RTC rc t) -> Tm (rFields rc ∙ t)
proj (RDC args) = args
proj {rc} {t} (TLHS {s = s} Stuck x x₁) = LHS {rFields rc ∙ t} Stuck (CProj x)

-- TODO: ?

---------------------

neutToTm : Spine a -> Tm a
neutToTm (Head f) = LHS (unnamed f) (CHead f)
neutToTm (f $  x) = neutToTm f ∙  x
neutToTm (f $$ x) = neutToTm f ∙∙ x
neutToTm (Fst× t) = fst× (neutToTm t)
neutToTm (Snd× t) = snd× (neutToTm t)
neutToTm (FstSigma t) = fstSigma (neutToTm t)
neutToTm (SndSigma _ s) = sndSigma s
neutToTm (Proj t) = proj (neutToTm t)
-- ...

nn : (s : Spine a) (t : Lambda a) (g : Glued≈ s t) -> neutToTm s ≈ LHS t g
nn s t g = homog (nn' s t g Refl)
 where
  nn' : ∀ {a a' : Ty} (n : Spine a) (t : Lambda a') (c : Glued n t) (e : a' ≈ a) ->
    let t' = coe~ (cong≈ Lambda e) t in
    let c' = coeP {Q = Glued n t'} (e & \{Refl -> refl}) c in
    neutToTm n ~ LHS t' c'
  nn' (Head _) _ (CHead _) Refl = refl
  nn' (s $ x) t (CLam {f = f} c e) Refl
    = helper Refl e (cong~ (\f -> f ∙ x) (nn' s (Lam _) c Refl))
   where
    helper : {fx : _} (ee : f x ≈ fx) -> fx ≈ NoRHS t -> neutToTm s ∙ x ~ lhs∙ c fx ee -> neutToTm s ∙ x ~ LHS t (CLam c e)
    helper _ Refl cc = cc
  nn' (s $ x) Stuck (CStuck$ c) Refl = cong~ (\f -> f ∙ x) (nn' s Stuck c Refl)
  nn' (n $$ x) t (CDLam {a = a} {b = b} {f = f} c e) Refl
    = helper Refl e (cong~ (\f -> f ∙∙ x) (nn' n (DLam _) c Refl))
   where
    helper : {fx : _} (ee : f x ≈ fx) -> fx ≈ NoRHS t -> neutToTm n ∙∙ x ~ lhs∙∙ c fx ee -> neutToTm n ∙∙ x ~ LHS t (CDLam c e)
    helper _ Refl cc = cc
  nn' (s $$ x) Stuck (CStuck$$ c) Refl = cong~ (\f -> f ∙∙ x) (nn' s Stuck c Refl)
  nn' (Fst× s) Stuck (CFst× x) Refl = cong~ (λ a₂ → fst× a₂) (nn' s Stuck x Refl)
  nn' (Snd× t) Stuck (CSnd× x) Refl = cong~ (λ f → snd× f) (nn' t Stuck x Refl)
  nn' (FstSigma t) Stuck (CFstSigma x) Refl = cong~ (λ f → fstSigma f) (nn' t Stuck x Refl)
  nn' (SndSigma {a} {b} t t'@(_ ,, k)) .Stuck (CSndSigma {i} {j} {é} {ba} x) Refl = {!  !}
  nn' (SndSigma t (TLHS {a''} {s} Stuck x₁ x₂)) .Stuck (CSndSigma {a'} x) Refl = {!  !}
  nn' (Proj t) .Stuck (CProj x) Refl = cong~ (λ f → proj f) (nn' t Stuck x Refl)
  -- ...


-----------------------

elimSigma : ∀ {r} ->
  (tm : Tm (Sigma a b)) -> 
  (match : (x : Tm a) (y : Tm (b ∙ x)) -> (x ,, y) ≈ tm -> TmL r) ->
    TmL r
elimSigma (x ,, y)     match = match x y Refl
elimSigma (TLHS _ _ _) match = NoRHS Stuck

-----------------------

elimRDC : ∀ {a} {params : _} ->
  (tm    : Tm (RTC rc params)) ->
  (match : (args : Tm (rFields rc ∙ params)) -> RDC args ≈ tm -> TmL a) ->
    TmL a
elimRDC (RDC args)   match = match args Refl
elimRDC (TLHS _ _ _) match = NoRHS Stuck

-----------------------

data TagIs {tc : TCDesc} : {indices : Tm (tcIndices tc)} -> Tm (TC tc indices) -> dcFin tc -> Prop where
  DCTag : ∀ {t args} -> TagIs (DC t args) t

elimDC : ∀ {indices} ->
  (tag   : dcFin tc) ->
  (tm    : Tm (TC tc indices)) ->
  (match : (args : Tm (dcArgs tc tag)) -> DC {tc} tag args ~ tm -> TmL a) ->
  (fail  : not (TagIs tm tag) -> TmL a) ->
    TmL a
elimDC {tc = tc} tag (DC tag' l) match fail with decFin tag' tag
... | Yes e = match (coe~ (e & \{Refl -> refl}) l) (e & \{Refl -> refl})
... | No  f = fail \{DCTag -> f Refl}
elimDC _ (TLHS _ _ _) _ _ = NoRHS Stuck

coveredBy : ∀ {a} {indices : _} {t : Tm (TC tc indices)} -> FinVec (numOfCstrs tc) (\f -> not (TagIs t f)) -> TmL a
coveredBy {t = DC tag args} vs = exfalso (indexFinVec {P = λ f → not (TagIs _ f)} vs tag DCTag)
coveredBy {t = TLHS _ _ _} vs = NoRHS Stuck

--------------------

data Bool : Set where True False : Bool

_&&_ : Bool -> Bool -> Bool
False && _ = False
True  && a = a

data Dec' (A : Set) : Set where
  Yes : A -> Dec' A
  No  :      Dec' A

-- convertible types
data Ty~ : Ty -> Ty -> Set where
  refl : {a : Ty} -> Ty~ a a

symTy~ : {a b : Ty} -> Ty~ a b -> Ty~ b a
symTy~ refl = refl
--symTy~ (arrRefl x x₁) = arrRefl (symTy~ x) (symTy~ x₁)

coeTm : Ty~ a a' -> Tm a -> Tm a'
coeTm refl x₁ = x₁
--coeTm (arrRefl {a} {a'} {b} {b'} y z) (TLHS {s = s} (Lam x₂) x x₁) = {!  !}
--coeTm (arrRefl {a} {a'} {b} {b'} y z) (TLHS {s = s} Stuck x x₁) = TLHS {a' => b'} {{!  !}} Stuck {!  !} \()
-- TLHS {a' => b'} {{!  !}} (Lam (λ x₁ → RHS (coeTm z (_∙_ x (coeTm (symTy~ y) x₁))))) {!  !} λ ()


Tm~  : {a : Ty} -> Tm a -> Tm a -> Set

data Tm~' : {a : Ty} -> Tm' a -> Tm' a -> Set where
  EtaTT : ∀ {t t'} -> Tm~' {a = Top} t t'
  Eta× : {a : _}{a' : _} -> {t t' : Tm (a × a')} -> Tm~ (fst× t) (fst× t') -> Tm~ (snd× t) (snd× t') -> Tm~' t t'
  EtaRDC : {h : RDesc}{g : Tm (rParams h)} -> {t t' : Tm (rFields h ∙ g )} -> Tm~ t t' -> Tm~' {RTC h g} (RDC t) (RDC t')
  EtaArr : {a a' : _}{b b' : _} -> Tm~ a a' -> Tm~ b b' -> {arr  arr' : Tm' (a => b)} -> ((x : Tm a) -> Tm~ (arr ∙ x) (arr' ∙ x)) -> Tm~' arr arr'
--  EtaSigma : {a a' : _}{b : _}{b' : _} -> Tm~ a a' -> {va : Tm a}{va' : Tm a'} -> Tm~ (b ∙ va) (b' ∙ va') -> {sig : Tm' (Sigma a b)} -> Tm~' sig sig
  -- ...

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
convTm' : Nat -> (t t' : Tm' a) -> Dec' (Tm~' t t')
convTm  : Nat -> (t t' : Tm  a) -> Dec' (Tm~ t t')

convTy i U U = Yes refl
convTy i Top Top = Yes refl
convTy i (a => b) (a' => b') with convTy i a a' | convTy i b b'
... | Yes refl | Yes refl = Yes refl
... | e | e' = No
convTy i (a × b) (a' × b') with convTy i a a' | convTy i b b'
... | Yes refl | Yes refl = Yes refl
... | Yes x | No = No
... | No | bq = No
convTy i (Pi a b) (Pi a' b') with convTy i a a'
... | No = No
... | Yes refl with convTm' i b b'
... | No = No
... | Yes (EtaArr refl refl x₂) = Yes {! refl !}
convTy i (Sigma a b) (Sigma a' b') with convTy i a a'
... | No = No
... | Yes refl with convTm' i b b'
... | Yes (EtaArr refl refl g) = Yes {!  !}
... | No = No
convTy i (RTC rc x) (RTC rc' x') = {!  !}
convTy i (TC tc x) (TC tx' x') = {!  !}
convTy i (TLHS Stuck g) (TLHS Stuck g') = Yes {! refl !}
convTy i _ _ = No

convTm' {a = Top} i _ _ = Yes EtaTT
convTm' {a = a => a'} i (TLHS (Lam x₄) x x₁) (TLHS (Lam x₅) x₂ x₃) = {!  !}
convTm' {a = a => a'} i (TLHS (Lam x₄) x x₁) (TLHS Stuck x₂ x₃) = No
convTm' {a = a => a'} i (TLHS Stuck x x₁) (TLHS l₁ x₂ x₃) = No
convTm' {a = a × a'} i t t' with convTm i (fst× t) (fst× t') | convTm i (snd× t) (snd× t')
... | Yes x | Yes x₁ = Yes (Eta× x x₁)
... | Yes x | No = No
... | No | e' = No
convTm' {a = Pi a b} i (TLHS l x x₁) (TLHS l₁ x₂ x₃) = {!  !}
convTm' {a = Sigma a b} i (x ,, x₁) (x₂ ,, x₃) with convTm i x x₂
... | Yes x₄ = {!  !}
... | No = No
convTm' {a = Sigma a b} i (_ ,, _) (TLHS _ _ _) = {!  !} --No
convTm' {a = Sigma a b} i (TLHS _ _ _) (_ ,, _) = {!  !} --No
convTm' {a = Sigma a b} i (TLHS l x x₁) (TLHS l₁ x₂ x₃) = {!  !}
convTm' {a = RTC rc x} i (RDC args) (RDC args₁) with convTm i args args₁
... | Yes x₁ = Yes (EtaRDC x₁)
... | No = No
convTm' {a = RTC rc x} i (RDC args) (TLHS l x₁ x₂) = {!  !}
convTm' {a = RTC rc x} i (TLHS l x₁ x₂) (RDC args) = {!  !}
convTm' {a = RTC rc x} i (TLHS l x₁ x₂) (TLHS l₁ x₃ x₄) = {!  !}
convTm' {a = TC tc x} i (DC tag args) t' = {! t' !}
convTm' {a = TC tc x} i (TLHS l x₁ x₂) (DC tag args) = {!  !}
convTm' {a = TC tc x} i (TLHS l x₁ x₂) (TLHS l₁ x₃ x₄) = {!  !}
convTm' {a = TLHS l g} i (TLHS Stuck x x₁) (TLHS Stuck x₂ x₃) = {!  !}
convTm' {a = U} i (TLHS _ _ e) _ = exfalso (e Refl)

convTm {a = U} i t t' = convTy i t t'
convTm {a = Top} i t t' = convTm' i t t'
convTm {a = a => a'} i t t' = convTm' i t t'
convTm {a = a × a'} i t t' = convTm' i t t'
convTm {a = Pi a b} i t t' = convTm' i t t'
convTm {a = Sigma a b} i t t' = convTm' i t t'
convTm {a = RTC rc x} i t t' = convTm' i t t'
convTm {a = TC tc x} i t t' = convTm' i t t'
convTm {a = TLHS l g} i t t' = convTm' i t t'


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
printTm'   : Tm' a -> Doc
printSpine : Spine a -> Doc

printSpine (Head x)   = DVar (name x)
printSpine (s $ x) = printSpine s $ printTm x
printSpine (s $$ x) = printSpine s $ printTm x
printSpine (Fst× x) = printSpine x
printSpine (Snd× s) = printSpine s
printSpine (FstSigma s) = printSpine s
printSpine (SndSigma s s₁) = printSpine s
printSpine (Proj s) = printSpine s
-- ...

printTy U = DVar "U"
printTy Top = DVar "Top"
printTy (t => x)   = DVar "Arr" $ printTy t $ printTy x
printTy (Pi t x)   = DVar "Pi" $ printTy t $ printTm' x
printTy (TC tc x)  = DVar (name tc) $ printTm x
printTy (RTC rc x) = DVar (name rc) $ printTm x
printTy (a × a') = DVar "_×_" $ printTy a $ printTy a'
printTy (Sigma a b) = DVar "_,_" $ printTy a $ printTm' b
printTy (TLHS {s = s} l x) = printSpine s

printTm' {a = U} (TLHS _ _ e) = exfalso (e Refl)
printTm' {a = a} (TLHS {s = s} _ _ _) = printSpine s
printTm' (DC {tc = tc} tag args) = DVar (DCDesc.dcName (dcDescs tc tag)) $ printTm args
printTm' (RDC {rc = rc} args)    = DVar (name rc) $ printTm args
printTm' TT = DVar "tt"
printTm' (x , y) = DVar "_,_" $ printTm x $ printTm y
printTm' (x ,, y) = DVar "_,,_" $ printTm x $ printTm y

printTm {a = U} t = printTy t
printTm {a = Top} t = printTm' t
printTm {a = a => a₁} t = printTm' t
printTm {a = a × a₁} t = printTm' t
printTm {a = Pi a x} t = printTm' t
printTm {a = Sigma a x} t = printTm' t
printTm {a = RTC rc x} t = printTm' t
printTm {a = TC tc x} t = printTm' t
printTm {a = TLHS l x} t = printTm' t

showTm : Tm a -> String
showTm t = showDoc (printTm t)


----------------

pattern Lam'  f = NoRHS (Lam  f)
pattern DLam' f = NoRHS (DLam f)

def : String -> Lambda a -> Tm a
def n t = LHS t (CHead (named n t))

var : String -> Tm a
var n = LHS Stuck (CHead (named n Stuck))

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

  NatDesc = named "Nat" (TCD Top 2 \where
      0f -> DCD "Zero" Top   (const ∙ TT)
      1f -> DCD "Suc"  Nat'  (const ∙ TT)
    )
    
  Nat' = TC NatDesc TT

  Zero : Tm Nat'
  Zero = DC {NatDesc} 0f TT

  Suc : Tm (Nat' => Nat')
  Suc = def "Suc" (Lam \n -> RHS (DC {NatDesc} 1f n))

  {-# TERMINATING #-}
  add : Tm (Nat' => Nat' => Nat')
  add = def "add" (Lam \n -> Lam' \m ->
    elimDC 0f n (\{ _ e -> RHS m                     }) \f0 ->
    elimDC 1f n (\{ k e -> RHS (Suc ∙ (add ∙ k ∙ m)) }) \f1 ->
    coveredBy (f0 :: f1 :: [])
    )

  addTest : add ∙ (Suc ∙ Zero) ∙ (Suc ∙ Zero) ≈ Suc ∙ (Suc ∙ Zero)
  addTest = Refl

  addTest' : (\n -> add ∙ (Suc ∙ Zero) ∙ n)    ≈ \n -> Suc ∙ n
  addTest' = Refl

  testQuote  : showTm {a = Nat'} (add ∙ (Suc ∙ Zero) ∙ (Suc ∙ Zero)) ≈ "Suc (Suc (Zero tt))"
  testQuote = Refl

  testQuote2 : showTm {a = Nat'} (add ∙ (Suc ∙ var {a = Nat'} "n") ∙ var {a = Nat'} "m")   ≈ "Suc (add n m)"
  testQuote2 = Refl


  {-# TERMINATING #-}
  Fin' : Tm (Nat' => U)

  FinDesc = named "Fin" (TCD Nat' 2 \where
      0f -> DCD "FZ" Nat' Suc
      1f -> DCD "FS" (Sigma Nat' (lam "FSFun" \n -> Fin' ∙ n × Fin' ∙ (Suc ∙ n))) (lam' "FSsub" \p -> elimSigma p \a _ _ -> RHS a)
    )

  Fin' = def "Fin" (Lam \n -> RHS (TC FinDesc n))

  testQuote' : showTm (Pi Nat' (lam "f" \n -> Fin' ∙ (add ∙ (Suc ∙ n) ∙ n)))
                 ≈ "Pi (Nat tt) f"   -- could be:  "Pi (Nat tt) \\v0 -> Fin (add (Suc v0) v0)"
  testQuote' = Refl

  --------------------------------------

  SigmaDesc = named "Sigma" (RD
       (Sigma U (lam "SigL" \a -> a => U))
       (lam' "SigL2" \t -> elimSigma t \a b _ -> RHS (Sigma a (lam "SigL3" \x -> b ∙ x)))
    )

  Sigma' : Tm (Pi U (lam "SL" \a -> (a => U) => U))
  Sigma' = def "Sigma" (DLam \a -> Lam' \b -> RHS (RTC SigmaDesc (a ,, b)))

  Pair : Tm (pi U \a -> pi (a => U) \b -> pi (a) \x -> b ∙ x => (Sigma' ∙∙ a ∙ b))
  Pair = def "Pair" (DLam \a -> DLam' \b -> DLam' \x -> Lam' \y -> RHS (RDC (x ,, y)))

  Fst' : Tm (pi U \a -> pi (a => U) \b -> (Sigma' ∙∙ a ∙ b) => a)
  Fst' = def "fst" (DLam \a -> DLam' \b -> Lam' \p -> elimRDC p \p e -> elimSigma p \a _ _ -> RHS a)

  Snd' : Tm (pi U \a -> pi (a => U) \b -> pi ((Sigma' ∙∙ a ∙ b)) \t -> (b ∙ (Fst' ∙∙ a ∙∙ b ∙ t)))
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

  IdDesc = named "Id" (TCD (Sigma U (lam "IdLam" \a -> a × a)) 1 \where
      0f -> DCD "Refl" (Sigma U (lam "IdLam2" \a -> a)) (lam' "IdLam3" \p -> elimSigma p \a x _ -> RHS (a ,, x , x))
    )

  Id : {a : Ty} -> Tm a -> Tm a -> Ty
  Id {a} x y = TC IdDesc (a ,, x , y)

  Refl'' : {x : Tm a} -> Tm (Id x x)
  Refl'' = DC {IdDesc} 0f (_ ,, _)

  etaSigma : Tm (pi U \a -> pi (a => U) \b -> pi ((Sigma' ∙∙ a ∙ b)) \t -> Id {Sigma' ∙∙ _ ∙ _} t (Pair ∙∙ a ∙∙ b ∙∙ (Fst' ∙∙ a ∙∙ b ∙ t) ∙ (Snd' ∙∙ a ∙∙ b ∙∙ t)))
  etaSigma = def "etaSigma" (DLam \a -> DLam' \b -> DLam' \t ->
    elimRDC t \t' e -> elimSigma t' \x y e' -> RHS (coe~ (e & e' & \{Refl Refl -> refl}) (Refl'' {Sigma' ∙∙ _ ∙ _} {x = Pair ∙∙ a ∙∙ b ∙∙ x ∙ y}))
    )

