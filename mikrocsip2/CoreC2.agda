{-
Same as CoreB.agda but neutral terms are added.
Printing is now possible.
Lam and ifTag is not a netural term; to achieve this LHS terms are separated from terms.
-}


{-# OPTIONS --type-in-type --rewriting --prop --erasure --with-K --injective-type-constructors #-}

open import Agda.Builtin.Bool using (Bool) renaming (true to True; false to False)
open import Agda.Builtin.Char using (Char; primIsLower; primIsDigit; primIsAlpha; primIsSpace; primCharEquality)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe) renaming (just to Just; nothing to Nothing)
open import Agda.Builtin.String using (String; primStringAppend; primStringToList; primStringFromList; primStringEquality; primShowNat)
open import Agda.Builtin.Nat using (Nat) renaming (suc to S; zero to Z)
open import Agda.Builtin.Equality renaming (_≡_ to Eq; refl to Refl)

-------------------

infixl 9 _∙_     -- non-dependent application
infixl 9 _∙∙_    -- dependent application
infixl 9 _$_     -- non-dependent application
infixl 9 _$$_    -- dependent application
infixr 8 _∘~_    -- transitivity for _~_
infixr 8 _∘≈_    -- transitivity for _≈_
infixr 7 _×_     -- non-dependent pair type
infixr 6 _=>_    -- non-dependent function type
infixr 5 _&&_
infixr 4 _||_
infix  3 _~_     -- inhomogenous Prop equality
infix  3 _≈_     -- homogenous Prop equality
infix  3 _≡_     -- homogenous Set equality
infixr 2 _+++_   -- string concatenation
infixr 2 _::_
infixr 2 _**_    -- dependent pair type (infix Σ)
infixr 0 _,_     -- non-dependent pair constructor
infixr 0 _,,_    -- dependent pair constructor
infix -1 _:=_

_+++_ : String -> String -> String
a +++ b = primStringAppend a b

pattern _::_ a as = a ∷ as

---------------------

private variable
  A A' B C : Set
  P Q : Prop

-------------------

data Sing {A : Set} : A -> Set where
  sing : (x : A) -> Sing x

data Either (A B : Set) : Set where
  Left  : A -> Either A B
  Right : B -> Either A B

record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open Pair

record _**_ (A : Set) (B : A -> Set) : Set where
  pattern
  constructor _,,_
  field
    fst : A
    snd : B fst

open _**_

Σ = _**_
syntax Σ A (λ x → B) = x :: A ** B

------------------

record T : Prop where
  constructor tt

data ⊥ : Prop where

exfalsoP : ⊥ -> P
exfalsoP ()

exfalso : ⊥ -> A
exfalso ()

not : Prop -> Prop
not P = P -> ⊥

record Emb (P : Prop) : Set where
  constructor emb
  field
    getProp : P


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
  Refl : a ~ a

sym~ : {a : A} {b : B} -> a ~ b -> b ~ a
sym~ Refl = Refl

cong~ : {B : A -> Set} {a a' : A} -> (f : (a : A) -> B a) -> a ~ a' -> f a ~ f a'
cong~ _ Refl = Refl

cong2~ : {B : A -> Set} {C : (a : A) -> B a -> Set} {a a' : A} {b : B a} {b' : B a'} -> (f : (a : A) (b : B a) -> C a b) -> a ~ a' -> b ~ b' -> f a b ~ f a' b'
cong2~ _ Refl Refl = Refl

_∘~_ : {a : A} {b : B} {c : C} -> a ~ b -> b ~ c -> a ~ c
Refl ∘~ e = e

coeP : P ~ Q → P → Q
coeP Refl a = a

postulate
  coe~     : A ~ B → A → B
  coe~Refl : {a : A} → coe~ Refl a ≈ a

{-# REWRITE coe~Refl #-}
opaque
  coh~ : {a : A} {e : A ~ B} -> coe~ e a ~ a
  coh~ {e = Refl} = Refl

-----------------------

  homog : {a a' : A} -> a ~ a' -> a ≈ a'
  homog Refl = Refl

  inhomog : {a a' : A} -> a ≈ a' -> a ~ a'
  inhomog Refl = Refl

eqt : {a : A}{b : B} -> a ~ b -> A ≈ B
eqt Refl = Refl

coe≈ : A ≈ B → A → B
coe≈ e = coe~ (inhomog e)

coh≈ : {a : A} {e : A ≈ B} -> coe≈ e a ~ a
coh≈ {e = Refl} = Refl

cong≈~ : {B : A -> Set} {a a' : A} -> (f : (a : A) -> B a) -> a ≈ a' -> f a ~ f a'
cong≈~ _ Refl = Refl

cong≈ : {a a' : A} -> (f : A -> B) -> a ≈ a' -> f a ≈ f a'
cong≈ _ Refl = Refl

subst≈ : (P : A -> Set) -> {a a' : A} -> a ≈ a' -> P a -> P a'
subst≈ P x x₁ = coe≈ (homog (cong≈~ P x)) x₁

subst≈' : (P : A -> Prop) -> {a a' : A} -> a ≈ a' -> P a -> P a'
subst≈' _ Refl x₁ = x₁

subst~' : {a : A}{b : B}(P : A -> Prop) -> a ~ b -> (eq : B ≈ A) -> P a -> P (coe≈ (eq) b)
subst~' _ Refl Refl x₁ = x₁

subst~ : {a : A}{b : B}(P : A -> Set) -> a ~ b -> (eq : B ≈ A) -> P a -> P (coe≈ (eq) b)
subst~ {b = b} P x eq x₁ = subst≈ P (sym≈ (homog (coh≈ {e = eq} ∘~ sym~ x))) x₁
---------------------

cong≈' : {a a' : A} -> (f : A -> B) -> a ≈ a' -> f a ≈ f a'
cong≈' f e = homog (cong≈~ f e)

cong2≈ : {a a' : A} {b b' : B} -> (f : A -> B -> C) -> a ≈ a' -> b ≈ b' -> f a b ≈ f a' b'
cong2≈ _ Refl Refl = Refl

------------------

_≡_ = Eq

propEq : {x y : A} -> x ≡ y -> x ≈ y
propEq Refl = Refl

setEq : {a a' : A} -> a ≈ a' -> a ≡ a'
setEq {a = a} e = coe≈ (cong≈ (\x -> a ≡ x) e) Refl

cong≡ : {a a' : A} -> (f : A -> B) -> a ≡ a' -> f a ≡ f a'
cong≡ f Refl = Refl

cong2≡ : {a a' : A} {b b' : B} -> (f : A -> B -> C) -> a ≡ a' -> b ≡ b' -> f a b ≡ f a' b'
cong2≡ _ Refl Refl = Refl


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

_=>U : Ty -> Set

-- record description
record UnnamedRDesc : Set where
  inductive
  pattern
  constructor RD
  field
    rParams : Ty
    rFields : rParams =>U

RDesc = Named UnnamedRDesc

rParams : RDesc -> Ty
rParams r = UnnamedRDesc.rParams (unnamed r)


rFields : (r : RDesc) -> rParams r =>U
rFields r = UnnamedRDesc.rFields (unnamed r)

private variable
  a a' a'' : Ty
  b        : a =>U
  rc       : RDesc

data Spine  : Ty -> Set
data Lambda : Ty -> Set
data Glued  : Spine a -> Lambda a -> Prop

data TyNU : Set

data Ty where
  U   :         Ty
  NU  : TyNU -> Ty


data TmNU : TyNU -> Set

Tm : Ty -> Set
Tm U      = Ty       -- definitional equality between (Tm U) and Ty; proposed by Bálint Török
Tm (NU a) = TmNU a


data TyNU where
  Top' Bot'  :                                     TyNU
  _=>'_ _×'_ _⊎'_ : Ty -> Ty ->                    TyNU
  Pi' Sigma' : (a : Ty) -> a =>U ->                TyNU
  Id'        : Tm a -> Tm a ->                     TyNU
  RTC'       : ∀ rc -> Tm (rParams rc) ->          TyNU
  NeU'       : ∀ {s : Spine U} {l} -> Glued s l -> TyNU

pattern Top       = NU Top'
pattern Bot       = NU Bot'
pattern _=>_ a a' = NU (a =>' a')
pattern _×_  a a' = NU (a ×'  a')
pattern _⊎_  a a' = NU (a ⊎'  a')
pattern Pi    a b = NU (Pi'    a b)
pattern Sigma a b = NU (Sigma' a b)
pattern Id x y    = NU (Id' x y)
pattern RTC rc ps = NU (RTC' rc ps)
pattern NeU g     = NU (NeU' g)

a =>U = Tm (a => U)

_∙_ : Tm (a => a') -> Tm a -> Tm  a'

data TmNU where
  TT    :                                              Tm Top
  _,_   : Tm a -> Tm a' ->                             Tm (a × a')
  _,,_  : (x : Tm a) -> Tm (b ∙ x) ->                  Tm (Sigma a b)
  Left  : Tm a  ->                                     Tm (a ⊎ a')
  Right : Tm a' ->                                     Tm (a ⊎ a')
  Refl  : {x : Tm a} ->                                Tm (Id x x)
  RDC   : ∀ {ps} (args : Tm (rFields rc ∙ ps)) ->      Tm (RTC rc ps)
  NeNU  : ∀ {a} {s : Spine (NU a)} {l} -> Glued s l -> Tm (NU a)

Ne : {s : Spine a} {l : Lambda a} -> Glued s l -> Tm a
Ne {a = U}    g = NeU  g
Ne {a = NU _} g = NeNU g

data LHS : Ty -> Set  where
  RHS   : Tm     a -> LHS a
  NoRHS : Lambda a -> LHS a

VarName : Set

private variable
  n        : VarName

{-# NO_POSITIVITY_CHECK #-}
data Lambda where
  Lam   : (Tm a -> LHS a') ->            Lambda (a => a')
  DLam  : ((x : Tm a) -> LHS (b ∙ x)) -> Lambda (Pi a b)
  Stuck : VarName ->                     Lambda a              -- stuck by var

NamedLambda : Ty -> Set
NamedLambda a = Named (Lambda a)

data Spine where
  Head : NamedLambda a ->                                        Spine a
  _$_  : Spine (a => a') -> Tm a ->                              Spine a'
  DApp : ∀ {bx} -> Spine (Pi a b) -> (x : Tm a) -> b ∙ x ≡ bx -> Spine bx

pattern _$$_ f x = DApp f x Refl

data Glued where
  CHead : (t : NamedLambda a) ->                                                  Glued (Head t) (unnamed t)
  CLam  : ∀ {s : Spine (a => a')} {f x l} -> Glued s (Lam  f) -> f x ≈ NoRHS l -> Glued (s $  x) l
  CDLam : ∀ {s : Spine (Pi a b)}  {f x l} -> Glued s (DLam f) -> f x ≈ NoRHS l -> Glued (s $$ x) l
  C$    : ∀ {s : Spine (a => a')} {x} ->     Glued s (Stuck n) ->                 Glued (s $  x) (Stuck n)
  C$$   : ∀ {s : Spine (Pi a b)}  {x} ->     Glued s (Stuck n) ->                 Glued (s $$ x) (Stuck n)

lhs∙ : ∀ {s : Spine (a => a')} {f x} -> Glued s (Lam f) -> (r : _) -> f x ≈ r -> Tm a'
lhs∙ c (RHS   t) e = t
lhs∙ c (NoRHS t) e = Ne (CLam c e)

NeNU {l = Lam f}   c ∙ x = lhs∙ c (f x) Refl
NeNU {l = Stuck _} c ∙ x = Ne (C$ {x = x} c)

lhs∙∙ : ∀ {s : Spine (Pi a b)} {f x} -> Glued s (DLam f) -> (r : _) -> f x ≈ r -> Tm (b ∙ x)
lhs∙∙ c (RHS   t) e = t
lhs∙∙ c (NoRHS t) e = Ne (CDLam c e)

_∙∙_ : Tm  (Pi a b) -> (x : Tm a) -> Tm (b ∙ x)
NeNU {l = DLam f}  c ∙∙ x = lhs∙∙ c (f x) Refl
NeNU {l = Stuck _} c ∙∙ x = Ne (C$$ c)


---------------------

neutToTm : Spine a -> Tm a
neutToTm (Head f) = Ne (CHead f)
neutToTm (f $  x) = neutToTm f ∙  x
neutToTm (f $$ x) = neutToTm f ∙∙ x

glued : {s : Spine a} {l : Lambda a} (g : Glued s l) -> neutToTm s ≈ Ne g
glued {s = Head _} (CHead _) = Refl
glued {s = s $ x} (C$ c) = cong≈ (\k -> k ∙ x) (glued c)
glued {s = s $ x} {l = l} (CLam {f = f} c e) = helper e (cong≈ (\k -> k ∙ x) (glued c))  where
  helper : {fx : _} {ee : f x ≈ fx} -> fx ≈ NoRHS l -> neutToTm s ∙ x ≈ lhs∙ c fx ee -> neutToTm s ∙ x ≈ Ne (CLam c e)
  helper Refl cc = cc
glued {s = s $$ x} (C$$ c) = cong≈ (\k -> k ∙∙ x) (glued c)
glued {s = s $$ x} {l = l} (CDLam {f = f} c e) = helper e (cong≈ (\k -> k ∙∙ x) (glued c))  where
  helper : {fx : _} {ee : f x ≈ fx} -> fx ≈ NoRHS l -> neutToTm s ∙∙ x ≈ lhs∙∙ c fx ee -> neutToTm s ∙∙ x ≈ Ne (CDLam c e)
  helper Refl cc = cc

-----------------------

elimBot : (tm : Tm Bot) -> LHS a
elimBot (NeNU {l = Stuck n} _) = NoRHS (Stuck n)

elim× :
  (tm : Tm (a × a')) -> 
  ((x : Tm a) (y : Tm a') -> (x , y) ≡ tm -> LHS a'') ->
    LHS a''
elim× (x , y) f = f x y Refl
elim× (NeNU {l = Stuck n} _) f = NoRHS (Stuck n)

elimSigma :
  (tm : Tm (Sigma a b)) -> 
  ((x : Tm a) (y : Tm (b ∙ x)) -> (x ,, y) ≡ tm -> LHS a') ->
    LHS a'
elimSigma (x ,, y) f = f x y Refl
elimSigma (NeNU {l = Stuck n} _) f = NoRHS (Stuck n)

elimR : ∀ {ps} ->
  (tm : Tm (RTC rc ps)) ->
  ((args : Tm (rFields rc ∙ ps)) -> RDC args ≡ tm -> LHS a) ->
    LHS a
elimR (RDC args) f = f args Refl
elimR (NeNU {l = Stuck n} _) f = NoRHS (Stuck n)

elim⊎ :
  (tm : Tm (a ⊎ a')) ->
  ((t : Tm a)  -> Left  t ≡ tm -> LHS a'') ->
  ((t : Tm a') -> Right t ≡ tm -> LHS a'') ->
    LHS a''
elim⊎ (Left  t) l r = l t Refl
elim⊎ (Right t) l r = r t Refl
elim⊎ (NeNU {l = Stuck n} _) _ _ = NoRHS (Stuck n)

elimId : {x y : Tm a} ->
  (tm : Tm (Id x y)) ->
  ({t : Tm a} -> TmNU.Refl {x = t} ~ tm -> LHS a') ->
    LHS a'
elimId Refl f = f Refl
elimId (NeNU {l = Stuck n} _) f = NoRHS (Stuck n)

--------------------

_:=_ : String -> LHS a -> Tm a
n := RHS   t = t
n := NoRHS t = Ne (CHead (named n t))

pattern Lam'  f = NoRHS (Lam  f)
pattern DLam' f = NoRHS (DLam f)

lam' : String -> (Tm a -> LHS a') -> Tm (a => a')
lam' n f = n := Lam' f

lam : String -> (Tm a -> Tm a') -> Tm (a => a')
lam n f = lam' n \t -> RHS (f t)

------------------

fst× : Tm (a × a' => a)
fst× = "fst×" := Lam' \p -> elim× p \x y _ -> RHS x

snd× : Tm (a × a' => a')
snd× = "snd×" := Lam' \p -> elim× p \x y _ -> RHS y

fstΣ : Tm (Sigma a b => a)
fstΣ = "fstΣ" := Lam' \p -> elimSigma p \x y _ -> RHS x

sndΣ : Tm (Pi (Sigma a b) (lam "sndΣLam" \t -> b ∙ (fstΣ ∙ t)))
sndΣ = "sndΣ" := DLam' \p -> elimSigma p \{x y Refl -> RHS y}

either' : {c : Ty} -> Tm ((a => c) => (a' => c) => a ⊎ a' => c)
either' = "either" := (Lam' (λ f → NoRHS (Lam (λ g → NoRHS (Lam (λ x → elim⊎ x (λ t x₁ → RHS (f ∙ t)) λ t x₁ → RHS (g ∙ t)))))))

proj : ∀ {ps} -> Tm (RTC rc ps => rFields rc ∙ ps)
proj {rc = rc} = ("proj" +++ name rc) := Lam' \t -> elimR t \t _ -> RHS t

{-
proj' : Tm (Pi (rParams rc) (lam "projLam" \ps -> RTC rc ps => rFields rc ∙ ps))
proj' {rc = rc} = def ("proj" +++ name rc)  (DLam' \_ -> Lam' \t -> elimR t \t _ -> RHS t)
-}

-------------------- nonstandard model

record Wrap (⟦_⟧ : Ty -> Set) (rc : RDesc) (ps : Tm (rParams rc)) : Set where
  inductive
  pattern
  constructor wrap
  field
    unwrap : ⟦ rFields rc ∙ ps ⟧

open Wrap

-------------------

⟦_⟧ : Ty -> Set

⟦_⟧ₜ    : Tm a  -> ⟦ a ⟧
quoteTm : ⟦ a ⟧ -> Tm a

evalQuote : {x : Tm a} -> x ≈ quoteTm ⟦ x ⟧ₜ

-------------- not interpreted types
⟦ t@U        ⟧ = Tm t
⟦ t@(_ => _) ⟧ = Tm t
⟦ t@(Pi _ _) ⟧ = Tm t
-------------- interpreted types
⟦ Top        ⟧ = Emb T
⟦ Bot        ⟧ = Emb ⊥
⟦ a ⊎  a'    ⟧ = Either ⟦ a ⟧ ⟦ a' ⟧
⟦ a ×  a'    ⟧ = Pair   ⟦ a ⟧ ⟦ a' ⟧
⟦ Sigma a b  ⟧ = ⟦ a ⟧ ** \x -> ⟦ b ∙ quoteTm x ⟧
⟦ Id x y     ⟧ = ⟦ x ⟧ₜ ≡ ⟦ y ⟧ₜ
⟦ RTC rc x   ⟧ = Wrap ⟦_⟧ rc x
⟦ t@(NeU _)  ⟧ = Emb ⊥

postulate
  -- True for closed terms
  noVars : VarName -> ⊥

{-# TERMINATING #-}
⟦_⟧ₜ {a = U   } t  = t
⟦_⟧ₜ {a = NU _} TT = emb tt
⟦_⟧ₜ {a = NU _} (x ,  y) = ⟦ x ⟧ₜ , ⟦ y ⟧ₜ
⟦_⟧ₜ {a = NU _} (_,,_ {b = b} x y) = ⟦ x ⟧ₜ ,, coe≈ (cong≈ (\k -> ⟦ b ∙ k ⟧) evalQuote) ⟦ y ⟧ₜ
⟦_⟧ₜ {a = NU _} (Left  x) = Left  ⟦ x ⟧ₜ
⟦_⟧ₜ {a = NU _} (Right x) = Right ⟦ x ⟧ₜ
⟦_⟧ₜ {a = NU _} Refl = Refl
⟦_⟧ₜ {a = NU _} (RDC args) = wrap ⟦ args ⟧ₜ
⟦_⟧ₜ {a = NU _} f@(NeNU {l = Lam  _} _) = f
⟦_⟧ₜ {a = NU _} f@(NeNU {l = DLam _} _) = f
⟦_⟧ₜ {a = NU _} (NeNU {l = Stuck n} _) = exfalso (noVars n)

quoteTm {a = U}       t = t
quoteTm {a = a => a'} t = t
quoteTm {a = Pi a b}  t = t
quoteTm {a = Top}     t = TT
quoteTm {a = a ⊎  a'} (Left  x) = Left  (quoteTm x)
quoteTm {a = a ⊎  a'} (Right y) = Right (quoteTm y)
quoteTm {a = a ×  a'}   (x ,  y) = quoteTm x ,  quoteTm y
quoteTm {a = Sigma a b} (x ,, y) = quoteTm x ,, quoteTm y
quoteTm {a = Id x y} e with setEq (evalQuote {x = x} ∘≈ cong≈ quoteTm (propEq e) ∘≈ sym≈ evalQuote)
... | Refl = Refl
quoteTm {a = RTC rc x} args = RDC (quoteTm (unwrap args))
quoteTm {a = NeU g} ()

evalQuote {a = U} = Refl
evalQuote {a = NU _} {x = NeNU {l = Stuck n} _} = exfalsoP (noVars n)
evalQuote {a = Top}  {x = TT} = Refl
evalQuote {a = a => a'} {x = NeNU {l = Lam  _} _} = Refl
evalQuote {a = Pi a b}  {x = NeNU {l = DLam _} _} = Refl
evalQuote {a = a × a'} {x = _ , _} = cong2≈ _,_ evalQuote evalQuote
evalQuote {a = a ⊎ a'} {x = Left  _} = cong≈ Left  evalQuote
evalQuote {a = a ⊎ a'} {x = Right _} = cong≈ Right evalQuote
evalQuote {a = Sigma a b} {x = x ,, y} = helper Refl evalQuote evalQuote  where
  helper :
    {x' : Tm a} (e : x' ≈ x) (r' : x ≈ quoteTm ⟦ x' ⟧ₜ) ->
    {y' : Tm (b ∙ x')} -> (y ≈ quoteTm (coe≈ (cong≈ (\k -> ⟦ b ∙ k ⟧) e) ⟦ y' ⟧ₜ)) ->
    _≈_ {A = Tm (Sigma a b)}
      (x ,, y)
      (quoteTm ⟦ x' ⟧ₜ ,, quoteTm (coe≈ (cong≈ (\k -> ⟦ b ∙ k ⟧) (e ∘≈ r')) ⟦ y' ⟧ₜ))
  helper _ Refl Refl = Refl
evalQuote {a = Id y z} {x = Refl} = Refl
evalQuote {a = RTC rc y} {x = RDC _} = cong≈ RDC evalQuote


--------------------

⟦_⟧'  : Ty -> Set
⟦_⟧ₜ' : Tm a -> ⟦ a ⟧'

⟦ U         ⟧' = Set
⟦ Top       ⟧' = Emb T
⟦ Bot       ⟧' = Emb ⊥
⟦ a ⊎ a'    ⟧' = Either ⟦ a ⟧' ⟦ a' ⟧'
⟦ a × a'    ⟧' = Pair   ⟦ a ⟧' ⟦ a' ⟧'
⟦ a => a'   ⟧' = ⟦ a ⟧ -> ⟦ a' ⟧'
⟦ Sigma a b ⟧' = ⟦ a ⟧ ** \x -> ⟦ b ∙ quoteTm x ⟧'
⟦ Pi a b    ⟧' = (x : ⟦ a ⟧) -> ⟦ b ∙ quoteTm x ⟧'
⟦ Id x y    ⟧' = ⟦ x ⟧ₜ' ≡ ⟦ y ⟧ₜ'
⟦ RTC rc x  ⟧' = Wrap ⟦_⟧' rc x
⟦ t@(NeU _) ⟧' = Emb ⊥

{-# TERMINATING #-}
⟦_⟧ₜ' {a = U}    t  = ⟦ t ⟧
⟦_⟧ₜ' {a = NU _} TT = emb tt
⟦_⟧ₜ' {a = NU _} (x ,  y) = ⟦ x ⟧ₜ' , ⟦ y ⟧ₜ'
⟦_⟧ₜ' {a = NU _} (_,,_ {b = b} x y) = ⟦ x ⟧ₜ ,, coe≈ (cong≈ (\k -> ⟦ b ∙ k ⟧') evalQuote) ⟦ y ⟧ₜ'
⟦_⟧ₜ' {a = NU _} (Left  x) = Left  ⟦ x ⟧ₜ'
⟦_⟧ₜ' {a = NU _} (Right x) = Right ⟦ x ⟧ₜ'
⟦_⟧ₜ' {a = NU _} Refl = Refl
⟦_⟧ₜ' {a = NU _} (RDC args) = wrap ⟦ args ⟧ₜ'
⟦_⟧ₜ' {a = NU _} f@(NeNU {l = Lam  _} _) x = ⟦ f ∙  quoteTm x ⟧ₜ'
⟦_⟧ₜ' {a = NU _} f@(NeNU {l = DLam _} _) x = ⟦ f ∙∙ quoteTm x ⟧ₜ'
⟦_⟧ₜ' {a = NU _} (NeNU {l = Stuck n} x) = exfalso (noVars n)

postulate
  TODO : A

--------------------

data Dec' (A : Set) : Set where
  Yes : A -> Dec' A
  No  :      Dec' A

Tm~  : {a : Ty} -> Tm a -> {b : Ty} -> Tm b -> Set
data TmNU~ : {a : TyNU} -> TmNU a -> {b : TyNU} -> TmNU b -> Set
-- convertible types
data Ty~ : Ty -> Ty -> Set where
  U : Ty~ U U
  Bot' : Ty~ Bot Bot
  Top' : Ty~ Top Top
  Arr : {a a' : _}{b b' : _} -> Tm~ a a' -> Tm~ b b' -> Ty~ (a => b) (a' => b')
  Tuple : {a a' : _}{b b' : _} -> Tm~ a a' -> Tm~ b b' -> Ty~ (a × b) (a' × b')
  Either' : {a a' : _}{b b' : _} -> Tm~ a a' -> Tm~ b b' -> Ty~ (a ⊎ b) (a' ⊎ b')
  Pi' : {a a' : _}{b : _}{b' : _} -> Tm~ a a' -> Tm~ b b' -> Ty~ (Pi a b) (Pi a' b')
  Sigma' : {a a' : _}{b : _}{b' : _} -> Tm~ a a' -> Tm~ b b' -> Ty~ (Sigma a b) (Sigma a' b')
  Id' : {t : Ty}{a b a' b' : Tm t} -> Tm~ a a' -> Tm~ b b' -> Ty~ (Id a b) (Id a' b')
  RTC' : {desc desc' : _} -> (eq : desc' ≈ desc) -> {p : Tm (rParams desc)}{p' : Tm (rParams desc')} -> Tm~ p p' -> Ty~ (RTC desc p) (RTC desc' p')
  NeU' : {s : _}{l : _}{g : Glued s l} -> Ty~ (NeU g) (NeU g)

Tm~ {a = U} t {b = U} t' = Ty~ t t'
Tm~ {a = NU _} t {b = NU _} t' = TmNU~ t t'
Tm~ {a = U} _ {b = NU _} _ = Emb ⊥
Tm~ {a = NU _} _ {b = U} _ = Emb ⊥
symTm~ : {a' b' : Ty} {a : Tm a'}{b : Tm b'} -> Tm~ a b -> Tm~ b a
coeTm : Tm~ a a' -> Tm a -> Tm a'

data TmNU~ where
  EtaTT : ∀ {t t'} -> TmNU~ {a = Top'} t {b = Top'} t'
  EtaBot : ∀ {t t'} -> TmNU~ {a = Bot'} t {b = Bot'} t'
  Eta× : {a : _}{a' : _} -> {t t' : Tm (a × a')} -> Tm~ (fst× ∙ t) (fst× ∙ t') -> Tm~ (snd× ∙ t) (snd× ∙ t') -> TmNU~ t t'
  Eta⊎ : {a b : _}{t t' : Tm (a ⊎ b)} -> ({c : _}(f : Tm (a => c))(g : Tm (b => c)) -> Tm~ (either' ∙ f ∙ g ∙ t ) (either' ∙ f ∙ g ∙ t')) -> TmNU~ t t'
  EtaRDC : {h : RDesc}{g : Tm (rParams h)} -> {m m' : Tm (RTC h g)} -> Tm~ (proj {h} {g} ∙ m) (proj {h} {g} ∙ m') -> TmNU~ m m'
  EtaArr : {a : _}{b : _} -> {arr arr' : TmNU (a =>' b)} -> ((x : _) -> Tm~ (arr ∙ x) (arr' ∙ x)) -> TmNU~ arr arr'
  EtaSigma : {a : _}{b : _}{b' : _}{sig : Tm (Sigma a b)}{sig' : Tm (Sigma a b')} -> (e : Tm~ (fstΣ ∙ sig) (fstΣ ∙ sig')) -> (eq : Ty~ (b ∙ (fstΣ ∙ sig)) (b' ∙ (fstΣ ∙ sig'))) -> Tm~ (sndΣ ∙∙ sig) (sndΣ ∙∙ sig') -> TmNU~ sig sig'
  EtaPi : {a : _}{b : _}{b' : _}{pi : Tm (Pi a b)}{pi' : Tm (Pi a b')} -> (Tm~ b b') -> ((x : Tm a) -> Tm~ (pi ∙∙ x) (pi' ∙∙ x)) -> TmNU~ pi pi'
  EtaId : {t : _}{a b : Tm t}{id id' : Tm (Id a b)} -> TmNU~ id id' -- Use J instead?
--  EtaVar : {s : _}{n : _}{g g' : Glued s (Stuck n)} -> TmNU~ (NeNU g) (NeNU g')
  -- ...

data Spine~ : {a : Ty} -> Spine a -> Spine a -> Set where
  Head : {a : Ty}{l l' : NamedLambda a} -> name l ≡ name l' -> Spine~ (Head l) (Head l')
  App : {a b : Ty}{s : Spine (b => a)}{s' : Spine (b => a)} -> Spine~ s s' -> {x : Tm b}{x' : Tm b} -> Tm~ x x' -> Spine~ (s $ x) (s' $ x')
  DApp' : {c : Ty}{b : Tm (c => U)}{s s' : Spine (Pi c b)} -> Spine~ s s' -> {x x' : Tm c}(eq : Tm~ x x')(proof : b ∙ x ≡ a) -> Spine~ (DApp s x proof) (DApp s' x' {!  !})

reflTm~ : {a : Ty}(a' : Tm a) -> Tm~ a' a'
reflTm~ {U} U = U
reflTm~ {U} Top = Top'
reflTm~ {U} Bot = Bot'
reflTm~ {U} (x => x₁) = Arr (reflTm~ x) (reflTm~ x₁)
reflTm~ {U} (x × x₁) = Tuple (reflTm~ x) (reflTm~ x₁)
reflTm~ {U} (x ⊎ x₁) = Either' (reflTm~ x) (reflTm~ x₁)
reflTm~ {U} (Pi a x) = Pi' (reflTm~ a) (reflTm~ x)
reflTm~ {U} (Sigma a x) = Sigma' (reflTm~ a) (reflTm~ x)
reflTm~ {U} (Id x x₁) = Id' (reflTm~ x) (reflTm~ x₁)
reflTm~ {U} (RTC rc x) = RTC' Refl (reflTm~ x)
reflTm~ {U} (NeU x) = NeU'
reflTm~ {Top} a' = EtaTT
reflTm~ {Bot} a' = EtaBot
reflTm~ {x => x₁} a' = EtaArr (λ x₂ → reflTm~ (a' ∙ x₂))
reflTm~ {x × x₁} a' = Eta× (reflTm~ (fst× ∙ a')) (reflTm~ (snd× ∙ a'))
reflTm~ {x ⊎ x₁} a' = Eta⊎ (λ f g → reflTm~ (either' ∙ f ∙ g ∙ a'))
reflTm~ {Pi a x} a' = EtaPi (reflTm~ x) λ x₁ → reflTm~ (a' ∙∙ x₁)
reflTm~ {Sigma a x} a' = EtaSigma (reflTm~ (fstΣ ∙ a')) (reflTm~ (x ∙ (fstΣ ∙ a'))) (reflTm~ (sndΣ ∙∙ a'))
reflTm~ {Id x x₁} a' = EtaId
reflTm~ {RTC rc x} r = EtaRDC (reflTm~ (proj ∙ r))
reflTm~ {NeU x} (NeNU {s = s} {l = Stuck x₂} x₁) = {! EtaVar !}

subst≡ : {A : Set}(@0 P : (a : A) -> Set){a a' : A} -> (@0 eq : a ≡ a') -> P a -> P a'
subst≡ _ Refl x = x

injTm : {t t' : Ty} -> Tm t ≈ Tm t' -> t ≈ t'

postulate
  funExt : {A : Set}{B : A -> Set}{f g : (a : A) -> B a} -> ((x : A) -> f x ≡ g x) -> f ≡ g
  inj∙ : {a b : _}(b b' : Tm (a => b)) -> _∙_ b ≡ _∙_ b' -> b ≡ b'

inhomtoTy~ : {t t' : Ty}{a : Tm t}{b : Tm t'} -> a ~ b -> Ty~ t t'
Ty~Toeq : {t t' : Ty} -> Ty~ t t' -> t ≡ t'
inhomtoTy~ {t} x with setEq (injTm (eqt x))
inhomtoTy~ {t} x | Refl = reflTm~ t

Ty~Toeq U = Refl
Ty~Toeq Top' = Refl
Ty~Toeq (Arr x x₁) with (Ty~Toeq x) | (Ty~Toeq x₁)
... | Refl | Refl = Refl
Ty~Toeq (Tuple x x₁) with (Ty~Toeq x) | (Ty~Toeq x₁)
... | Refl | Refl = Refl
Ty~Toeq (Pi' x x₁) with (Ty~Toeq x)
Ty~Toeq (Pi' {b = b} {b' = b'} x (EtaArr k)) | Refl with inj∙ b b' (funExt (λ x₁ → Ty~Toeq (k x₁)))
... | Refl = Refl
Ty~Toeq (Sigma' x x₁) with (Ty~Toeq x)
Ty~Toeq (Sigma' {b = b} {b' = b'} x (EtaArr k)) | Refl with inj∙ b b' (funExt (λ x₁ → Ty~Toeq (k x₁)))
... | Refl = Refl
Ty~Toeq (Id' x x₁) = TODO
Ty~Toeq (RTC' eq {p} {p'} x) with setEq eq
... | Refl = TODO
Ty~Toeq (Either' x x₁) with Ty~Toeq x | Ty~Toeq x₁
... | Refl | Refl = Refl
Ty~Toeq Bot' = Refl
Ty~Toeq NeU' = Refl


symTm~ {U} {U} {U} {U} x = x
symTm~ {U} {U} {Bot} {Bot} x = x
symTm~ {U} {U} {NeU y} {NeU z} NeU' = NeU'
symTm~ {U} {U} {Top} {Top} x = x
symTm~ {U} {U} {x₁ => x₃} {x₂ => x₄} (Arr x x₅) = Arr (symTm~ x) (symTm~ x₅)
symTm~ {U} {U} {x₁ × x₃} {x₂ × x₄} (Tuple x x₅) = Tuple (symTm~ x) (symTm~ x₅)
symTm~ {U} {U} {Pi a x₁} {Pi a₁ x₂} (Pi' x x₃) = Pi' (symTm~ x) (symTm~ x₃)
symTm~ {U} {U} {Sigma a x₁} {Sigma a₁ x₂} (Sigma' x x₃) = Sigma' (symTm~ x) (symTm~ x₃)
symTm~ {U} {U} {Id x₁ x₃} {Id x₂ x₄} (Id' x x₅) = Id' (symTm~ x) (symTm~ x₅)
symTm~ {U} {U} {_ ⊎ _} {_ ⊎ _} (Either' y y₁) = Either' (symTm~ y) (symTm~ y₁)
symTm~ {U} {U} {RTC rc x₁} {RTC rc₁ x₂} (RTC' eq x) with setEq eq
... | Refl = RTC' eq (symTm~ x)
symTm~ {Top} {Top} {a} {b} EtaTT = EtaTT
symTm~ {_ => _} {_ => _} {a} {b} (EtaArr x) = EtaArr (λ x₃ → symTm~ (x x₃))
symTm~ {_ × _} {_ × _} {a} {b} (Eta× x x₁) = Eta× (symTm~ x) (symTm~ x₁)
symTm~ {Pi _ _} {Pi _ _} {a} {b} (EtaPi f x) = EtaPi (symTm~ f) λ x₃ → symTm~ (x x₃)
symTm~ {Sigma _ _} {Sigma _ _} {a} {b} (EtaSigma e eq x) = EtaSigma (symTm~ e) (symTm~ eq) (symTm~ x)
symTm~ {Id _ _} {Id _ _} {a} {b} EtaId = EtaId
symTm~ {RTC _ _} {RTC _ _} {a} {b} (EtaRDC x) = EtaRDC (symTm~ x)
symTm~ {Bot} {Bot} {a} {b} EtaBot = EtaBot
symTm~ {x ⊎ x₁} {x₂ ⊎ x₃} (Eta⊎ x₄) = Eta⊎ (λ f g → symTm~ (x₄ f g))


{-# TERMINATING #-}
coeM : {t : Ty}{b b' : Tm (t => U)}{a : Tm t} -> Tm~ b b' -> Tm (b ∙ a) -> Tm (b' ∙ a)
coeM {a = a} (EtaArr x) x₁ with x a
... | g = coeTm g x₁


coeApp : {t : Ty}{b : Tm (t => U)}(a a' : Tm t) -> Tm~ a a' -> Tm (b ∙ a) -> Tm (b ∙ a')
coeApp {U} a a' x x₁ with Ty~Toeq x
... | Refl = x₁
coeApp {NU x₂} a a' x x₁ = {!  !}

coeTm {U} U x₁ = x₁
coeTm {Top} Top' x₁ = x₁
coeTm {Bot} Bot' y = y
coeTm {x₂ => x₃} (Arr x x₄) l = lam "" λ x₁ → coeTm x₄ (l ∙ (coeTm (symTm~ x) x₁))
coeTm {x₂ × x₃} (Tuple x x₄) y = coeTm x (fst× ∙ y ) , coeTm x₄ (snd× ∙ y)
coeTm {Pi a x₂} (Pi' {b' = b'} x (EtaArr f)) x₁ = NeNU (CHead (named "" (DLam (λ i → RHS (coeM {b = x₂} {b' = b'} {a = i} (EtaArr f) (x₁ ∙∙ i))))))
coeTm {Sigma a x₂} (Sigma' {b' = b'} x (EtaArr f)) x₁ = fstΣ ∙ x₁ ,, coeM {_} {x₂} {b'} {fstΣ ∙ x₁} (EtaArr f) (sndΣ ∙∙ x₁)
coeTm {Id x₂ x₃} (Id' x x₄) r with elimId r (λ {x₁ → RHS {! subst~ ? x₁ (eqt x₁) ?  !}})
... | RHS x₁ = x₁
... | NoRHS (Stuck x₁) = {!  !}
coeTm {a ⊎ b} (Either' y y₁) z = either' ∙ lam "f" (λ x → Left (coeTm y x)) ∙ lam "g" (λ x → Right (coeTm y₁ x)) ∙ z
coeTm {RTC rc x₂} (RTC' eq x) y with setEq eq
... | Refl = RDC (coeApp {b = rc .unnamed .UnnamedRDesc.rFields} _ _ x (proj ∙ y))
coeTm {NeU _} NeU' x = x

postulate decString : (str str' : String) -> Dec' (str ≡ str')

{-# TERMINATING #-}
convTy  : Nat -> (a a' : Ty) -> Dec' (Ty~ a a')
convTmNU : ∀ {a a'} -> Nat -> (t : TmNU a)(t' : TmNU a') -> Dec' (TmNU~ t t')
convTm  : Nat -> (t : Tm  a)(t' : Tm a') -> Dec' (Tm~ t t')
convSpine : Nat -> (s : Spine a)(s' : Spine a) -> Dec' (Spine~ s s')

convTy x U U = Yes U
convTy i Top Top = Yes Top'
convTy i (a => b) (a' => b') with convTy i a a' | convTy i b b'
... | Yes x | Yes x₁ = Yes (Arr x x₁)
... | Yes x | No = No
... | No | _ = No
convTy i (a × b) (a' × b') with convTy i a a' | convTy i b b'
... | Yes x | Yes x₁ = Yes (Tuple x x₁)
... | Yes x | No = No
... | No | bq = No
convTy i (a ⊎ b) (a' ⊎ b') with convTy i a a' | convTy i b b'
... | Yes x | Yes x₁ = Yes (Either' x x₁)
... | Yes x | No = No
... | No | bq = No
convTy i (Pi a x) (Pi a' x') with convTy i a a'
... | No = No
... | Yes x₁ with convTm i x x'
... | No = No
... | Yes x₂ = Yes (Pi' x₁ x₂)
convTy i (Sigma a x) (Sigma a' x') with convTy i a a'
... | No = No
... | Yes x₁ with convTm i x x'
... | Yes x₂ = Yes (Sigma' x₁ x₂)
... | No = No
convTy i (Id x x₁) (Id x₂ x₃) with convTm i x x₂ | convTm i x₁ x₃
... | Yes x₄ | Yes x₅ = Yes {! Id' {?} ? ? !}
... | Yes x₄ | No = No
... | No | bq = No
convTy i (RTC rc x) (RTC rc₁ x₁) with decString (name rc) (name rc₁)
... | No = No
... | Yes eq with setEq (uniqueNames {_} {rc} {rc₁} (propEq eq))
... | Refl with convTm i x x₁
... | Yes x₂ = Yes (RTC' Refl x₂)
... | No = No
convTy i (NU (NeU' x)) (NU (NeU' y)) = TODO --Spline conversion
convTy _ _ _ = No

convTmNU {a = Top'} {a' = Top'} i t t' = Yes EtaTT
convTmNU {a = x =>' x₁} {a' = x' =>' x₁'} i t t' = {!  !}
convTmNU {a = x ×' x₁} {a' = x' ×' x₁'} i t t'
    with convTy i x x' | convTy i x₁ x₁' | convTm i (fst× ∙ t) (fst× ∙ t') | convTm i (snd× ∙ t) (snd× ∙ t')
... | Yes x₂ | Yes x₃ | Yes x₄ | Yes x₅ = Yes {! x₂ !}
... | Yes x₂ | Yes x₃ | Yes x₄ | No = No
... | Yes x₂ | Yes x₃ | No | bq = No
... | Yes x₂ | No | aq | bq = No
... | No | bq' | aq | bq = No
convTmNU {a = x ⊎' x₁} {a' = x' ⊎' x₁'} i t t' = {!  !}
convTmNU {a = Pi' a x} {a' = Pi' a' x'} i t t' = {!  !}
convTmNU {a = Sigma' a x} {a' = Sigma' a' x'} i t t' = {!  !}
convTmNU {a = Id' x x₁} {a' = Id' x' x₁'} i t t' = {!  !}
convTmNU {a = RTC' rc x} {a' = RTC' rc' x'} i t t' = {!  !}
--convTmNU {a = TLHS x} {a' = TLHS x'} i t t' = {!  !}
convTmNU {a = _} {a' = _} _ _ _ = No

convSpine x (Head x₁) (Head x₂) with decString (name x₁) (name x₂)
... | No = No
... | Yes Refl = Yes (Head Refl)
convSpine x (_$_ {a = a} {a' = a'} s x₁) (_$_ {a = b} {a' = b'} s' x₂) with convTy x a b | convTy x a' b'
... | No | bq = No
... | Yes x₃ | No = No
... | Yes x₃ | Yes x₄ = {!  !}
convSpine x (DApp s x₁ x₂) (DApp s' x₃ x₄) = {!  !}
convSpine x _ _ = No

convTm {a = U} {a' = U} i t t' = convTy i t t'
convTm {a = NU _} {a' = NU _} i t t' = convTmNU i t t'
convTm {a = _} {a' = _} _ _ _ = No

{-
convTm  : Nat -> (t t' : _ ** Tm) -> Dec' (t ≡ t')
convTm x (U ,, U) (U ,, U) = Yes Refl
convTm x (U ,, Top) (U ,, Top) = Yes Refl
convTm x (U ,, Bot) (U ,, Bot) = Yes Refl
convTm x (U ,, x₁ => x₃) (U ,, x₂ => x₄) with convTm x (U ,, x₁) (U ,, x₂) | convTm x (U ,, x₃) (U ,, x₄)
... | Yes Refl | Yes Refl = Yes Refl
... | Yes x₅ | No = No
... | No | bq = No
convTm x (U ,, x₁ × x₃) (U ,, x₂ × x₄) with convTm x (U ,, x₁) (U ,, x₂) | convTm x (U ,, x₃) (U ,, x₄)
... | Yes Refl | Yes Refl = Yes Refl
... | Yes x₅ | No = No
... | No | bq = No
convTm x (U ,, (x₁ ⊎ x₃)) (U ,, (x₂ ⊎ x₄)) with convTm x (U ,, x₁) (U ,, x₂) | convTm x (U ,, x₃) (U ,, x₄)
... | Yes Refl | Yes Refl = Yes Refl
... | Yes x₅ | No = No
... | No | bq = No
convTm x (U ,, Pi a x₁) (U ,, Pi a₁ x₂) with convTm x (U ,, a) (U ,, a₁)
... | No = No
... | Yes Refl with convTm x (a => U ,, x₁) (a => U ,, x₂)
... | Yes Refl = Yes Refl
... | No = No
convTm x (U ,, Sigma a x₁) (U ,, Sigma a' x') with convTm x (U ,, a) (U ,, a')
... | No = No
... | Yes Refl with convTm x (a => U ,, x₁) (a => U ,, x')
... | Yes Refl = Yes Refl
... | No = No
convTm x (U ,, Id x₁ x₃) (U ,, Id x₂ x₄) with convTm x (_ ,, x₁) (_ ,, x₂) | convTm x (_ ,, x₃) (_ ,, x₄)
... | Yes Refl | Yes Refl = Yes Refl
... | Yes x₅ | No = No
... | No | bq = No
convTm x (U ,, RTC rc x₁) (U ,, RTC rc₁ x₂) with decString (name rc) (name rc₁)
... | No = No
... | Yes eq with setEq (uniqueNames {_} {rc} {rc₁} (propEq eq))
... | Refl with convTm x (_ ,, x₁) (_ ,, x₂)
... | Yes Refl = Yes Refl
... | No = No
convTm x (U ,, NeU x₁) (U ,, NeU x₂) = {!  !}
convTm x (U ,, _) (U ,, _) = No
convTm x (NU x₁ ,, TT) (NU x₂ ,, TT) = Yes Refl
convTm x (NU x₁ ,, x₃ , x₄) (NU x₂ ,, x₅ , x₆) with convTm x (_ ,, x₃) (_ ,, x₅) | convTm x (_ ,, x₄) (_ ,, x₆)
... | Yes Refl | Yes Refl = Yes Refl
... | Yes x₁ | No = No
... | No | bq = No
convTm x (NU x₁ ,, (_,,_ x₃  x₄)) (NU x₂ ,, x₅ ,, x₆) with convTm x (_ ,, x₃) (_ ,, x₅)
... | No = No
convTm x (NU (Sigma' _ b) ,, x₃ ,, x₄) (NU (Sigma' _ b') ,, x₅ ,, x₆) | Yes Refl with convTm x (_ ,, x₄) (_ ,, x₆) | convTm x (_ ,, b) (_ ,, b')
... | Yes Refl | Yes Refl = Yes Refl
... | Yes y | No = No
... | No | _ = No
convTm x ((_ ⊎ a') ,, Left x₃) ((_ ⊎ a'') ,, Left x₄) with convTm x (_ ,, x₃) (_ ,, x₄) | convTm x (_ ,, a') (_ ,, a'')
... | Yes Refl | Yes Refl = Yes Refl
... | Yes Refl | No = No
... | No | _ = No
convTm x ((a' ⊎ _) ,, Right x₃) ((a'' ⊎ _) ,, Right x₄) with convTm x (_ ,, x₃) (_ ,, x₄) | convTm x (_ ,, a') (_ ,, a'')
... | Yes Refl | Yes Refl = Yes Refl
... | Yes Refl | No = No
... | No | _ = No
convTm x ((Id a b) ,, Refl) ((Id a' b') ,, Refl) with convTm x (_ ,, a) (_ ,, a') | convTm x (_ ,, b) (_ ,, b')
... | Yes Refl | Yes Refl = Yes Refl
... | Yes x₁ | No = No
... | No | bq = No
convTm x (RTC rc y ,, RDC args) (NU (RTC' rc' y') ,, RDC args₁) with decString (name rc) (name rc')
... | No = No
... | Yes x₁ with setEq (uniqueNames {_} {rc} {rc'} (propEq x₁))
... | Refl with convTm x (_ ,, y) (_ ,, y')
... | No = No
... | Yes Refl with convTm x (_ ,, args) (_ ,, args₁)
... | Yes Refl = Yes Refl
... | No = No
convTm x (Top ,, NeNU x₃) (Top ,, NeNU x₄) = No
convTm x (Bot ,, NeNU x₃) (NU x₂ ,, NeNU x₄) = No
convTm x (x₁ => x₅ ,, NeNU x₃) (NU x₂ ,, NeNU x₄) = No
convTm x (x₁ × x₅ ,, NeNU x₃) (NU x₂ ,, NeNU x₄) = No
convTm x ((x₁ ⊎ x₅) ,, NeNU x₃) (NU x₂ ,, NeNU x₄) = No
convTm x (Pi a x₁ ,, NeNU x₃) (NU x₂ ,, NeNU x₄) = No
convTm x (Sigma a x₁ ,, NeNU x₃) (NU x₂ ,, NeNU x₄) = No
convTm x (Id x₁ x₅ ,, NeNU x₃) (NU x₂ ,, NeNU x₄) = No
convTm x (RTC rc x₁ ,, NeNU x₃) (NU x₂ ,, NeNU x₄) = No
convTm x (NeU x₁ ,, NeNU x₃) (NeU x₂ ,, NeNU x₄) = No
convTm x (NU x₁ ,, _) (NU x₂ ,, _) = No
convTm x (U ,, t) (NU x₁ ,, t') = No
convTm x (NU x₁ ,, t) (U ,, t') = No
-}
-------------------------------------

_||_ : Bool -> Bool -> Bool
True  || _ = True
False || b = b

_&&_ : Bool -> Bool -> Bool
False && _ = False
True  && b = b


groupBy : (A -> A -> Bool) -> List A -> List (List A)
groupBy f [] = []
groupBy {A = A} f (a :: as) = h a as _::_  where
  h : A -> List A -> (List A -> List (List A) -> B) -> B
  h a [] c = c (a :: []) []
  h a (b :: bs) c with f a b
  ... | True  = h b bs \r rs -> c (a :: r) rs
  ... | False = c (a :: []) (h b bs _::_)

foldr : (A -> B -> B) -> B -> List A -> B
foldr c n [] = n
foldr c n (x :: as) = c x (foldr c n as)

map : (A -> B) -> List A -> List B
map f []        = []
map f (a :: as) = f a :: map f as 

all : (A -> Bool) -> List A -> Bool
all p as = foldr _&&_ True (map p as)

filter : (A -> Bool) -> List A -> List A
filter p [] = []
filter p (a :: as) with p a
... | False = filter p as
... | True  = a :: filter p as

isAlphaNumeric : Char -> Bool
isAlphaNumeric '_' = True
isAlphaNumeric a = primIsAlpha a || primIsDigit a

isGraphic : Char -> Bool
isGraphic '=' = True
isGraphic '>' = True
isGraphic c = False

glueChar : Char -> Char -> Bool
glueChar a b
   = isAlphaNumeric a && isAlphaNumeric b
  || isGraphic a      && isGraphic      b

tokens : String -> List String
tokens s = map primStringFromList (filter f (groupBy glueChar (primStringToList s)))  where
  f : List Char -> Bool
  f (' ' :: _) = False
  f _          = True

isVarToken : String -> Bool
isVarToken s = all isAlphaNumeric (primStringToList s)

testTokens : tokens "(a + bc)" ≡ ("(" :: "a" :: "+" :: "bc" :: ")" :: [])
testTokens = Refl

----------------------------------

record Monad (M : Set -> Set) : Set where
  field
    _>>=_ : M A -> (A -> M B) -> M B
    pure  : A -> M A

open Monad {{...}}

instance
  MaybeMonad : Monad Maybe

  _>>=_ {{MaybeMonad}} (Just x) f = f x
  _>>=_ {{MaybeMonad}} Nothing  _ = Nothing

  pure {{MaybeMonad}} = Just

instance
  EitherMonad : Monad (Either A)

  _>>=_ {{EitherMonad}} (Right x) f = f x
  _>>=_ {{EitherMonad}} (Left e)  _ = Left e

  pure {{EitherMonad}} = Right

----------------------------------

TC : Set -> Set
TC = Either String

throwError : String -> TC A
throwError = Left

-------------------------------------

data Doc : Set where
  DVar : String ->     Doc
  _$_  : Doc -> Doc -> Doc

parse : String -> TC Doc
parse s = h0 end (tokens s)  where

  X = List String -> TC Doc

  end : Doc -> X
  end d [] = pure d
  end d _  = throwError "End expected"

  expect : String -> X -> X
  expect t r (t' :: ts) with primStringEquality t' t
  ... | True  = r ts
  ... | False = throwError (t +++ " expected instead of " +++ t')
  expect t _ [] = throwError (t +++ " expected instead of end")

  h0 : (Doc -> X) -> X

  h9 : (Doc -> X) -> X -> X
  h9 r _ ("(" :: ts) = h0 (\b -> expect ")" (r b)) ts
  h9 r z (t :: ts) with isVarToken t
  ... | True  = r (DVar t) ts
  ... | False = z (t :: ts)
  h9 _ z ts = z ts

  h8' : (Doc -> X) -> Doc -> X
  h8' r a ts = h9 (\b -> h8' r (a $ b)) (r a) ts

  h8 : (Doc -> X) -> X
  h8 r = h9 (h8' r) \_ -> throwError "unknown token"

  hn : String -> ((Doc -> X) -> X) -> (Doc -> X) -> X
  hn t g r = g (hn' r) where
    hn' : (Doc -> X) -> Doc -> X
    hn' r a (t' :: ts) with primStringEquality t' t
    ... | True = hn t g (\b -> r (DVar t $ a $ b)) ts
    ... | False = r a (t' :: ts)
    hn' r a ts = r a ts

  h0 = hn ";"
      (hn "="
      (hn "."
      (hn ":"
      (hn ","
      (hn "=>"
      (hn "⊎"
      (hn "×"
       h8)))))))

testParse : parse "f (b a × c) d" ≡ pure (DVar "f" $ (DVar "×" $ (DVar "b" $ DVar "a") $ DVar "c") $ DVar "d")
testParse = Refl

TyTm : Set
TyTm = Ty ** \a -> Tm a

convert : (x : Tm a) (y : Tm a) -> TC (x ≡ y)
convert {a = U} U U = pure Refl
convert x y = throwError "TODO0"

----------------------------------

infer : Doc -> TC TyTm

check : Doc -> (a : Ty) -> TC (Tm a)
check (DVar "Refl") (Id x y) = do
  Refl <- convert x y
  pure Refl
check (DVar "," $ x $ x') (a × a') = do
  x  <- check x  a
  x' <- check x' a'
  pure (x , x')
check (DVar "," $ x $ y) (Sigma a b) = do
  x <- check x  a
  y <- check y (b ∙ x)
  pure (x ,, y)
check (DVar "." $ DVar n $ e) (a => b) = throwError "TODO1"
check d a = do
  a' ,, x <- infer d
  Refl <- convert a a'
  pure x

infer (DVar "U")   = pure (U ,, U)
infer (DVar "Top") = pure (U ,, Top)
infer (DVar "tt")  = pure (Top ,, TT)
infer (DVar "Bot") = pure (U ,, Bot)
infer (DVar "×" $ a $ a') = do
  a  <- check a  U
  a' <- check a' U
  pure (U ,, a × a')
infer (DVar "⊎" $ a $ a') = do
  a  <- check a  U
  a' <- check a' U
  pure (U ,, a ⊎ a')
infer (DVar "=>" $ a $ a') = do
  a  <- check a  U
  a' <- check a' U
  pure (U ,, a => a')
infer (DVar "Pi" $ a $ b) = do
  a <- check a U
  b <- check b (a => U)
  pure (U ,, Pi a b)
infer (DVar "Sigma" $ a $ b) = do
  a <- check a U
  b <- check b (a => U)
  pure (U ,, Sigma a b)
infer (DVar "Id" $ x $ y) = do
  a ,, x <- infer x
  y <- check y a
  pure (U ,, Id x y)
infer _ = throwError "infer"

checkLHS : Doc -> (a : Ty) -> TC (LHS a)
checkLHS (DVar "." $ DVar n $ t) (a => a') = do
  throwError "TODO2"
checkLHS d a = throwError "checkLHS"

inferTop : Doc -> TC TyTm
inferTop (DVar ";" $ (DVar "=" $ (DVar ":" $ DVar n $ a) $ t) $ ds) = do
  a <- check a U
  t <- checkLHS t a
  -- TODO: store the definition
  inferTop ds
inferTop d = infer d


tc : String -> TC TyTm
tc s = parse s >>= inferTop

-- te = tc "Pi Top (Lam x x)"


test = tc "f : Top => U = x. Top; Pi Top f"

-------------------------------------

var : String -> Tm a

parens : String -> String
parens a = "(" +++ a +++ ")"

pattern SLam n d = DVar "λ" $ DVar n $ d

showDoc' : Nat -> Nat -> Doc -> String
showDoc' _ _ (DVar n)   = n
showDoc' p 1 (SLam n d) = parens ("λ" +++ n +++ " -> " +++ showDoc' 0 0 d)
showDoc' p q (SLam n d) =         "λ" +++ n +++ " -> " +++ showDoc' 0 q d
showDoc' 1 q (a $ b)    = parens (showDoc' 0 1 a +++ " " +++ showDoc' 1 0 b)
showDoc' p q (a $ b)    =         showDoc' p 1 a +++ " " +++ showDoc' 1 q b

showDoc = showDoc' Z Z

testDoc : showDoc (SLam "a" (DVar "a" $ DVar "b") $ (DVar "c" $ DVar "e") $ DVar "d" $ SLam "a" (SLam "b" (DVar "a")))
        ≈ "(λa -> a b) (c e) d λa -> λb -> a"
testDoc = Refl


printTy'    : Nat -> Ty -> Doc
printTm'    : Nat -> Tm a -> Doc
printSpine' : Nat -> Spine a -> Doc

printTy    : Ty -> Doc
printTy = printTy' Z
printTm    : Tm a -> Doc
printTm = printTm' Z
printSpine : Spine a -> Doc
printSpine = printSpine' Z

printSpine' _ (Head x) = DVar (name x)
printSpine' i (s $  x) = printSpine' i s $ printTm' i x
printSpine' i (s $$ x) = printSpine' i s $ printTm' i x

printTy' _ U = DVar "U"
printTy' _ Top = DVar "Top"
printTy' i (t => x)   = DVar "Arr" $ printTy' i t $ printTy' i x
printTy' i (Pi t x)   = DVar "Pi" $ printTy' i t $ printTm' i x
printTy' i (RTC rc x) = DVar (name rc) $ printTm' i x
printTy' i (a × a') = DVar "_×_" $ printTy' i a $ printTy' i a'
printTy' i (Sigma a b) = DVar "_,_" $ printTy a $ printTm b
printTy' i (x ⊎ y) = DVar "_⊎_" $ printTy' i x $ printTy' i y
printTy' i (Id x y) = DVar "Id" $ printTm' i y $ printTm' i y
printTy' i Bot = DVar "Bot"
printTy' i (NU (NeU' {s = s} x)) = printSpine' i s

{-# TERMINATING #-}
printTm' {a = U}      i  t        = printTy' i t
printTm' {a = NU _}   i TT        = DVar "tt"
printTm' {a = a => b} i f         = let sv = "v" +++ primShowNat i in SLam sv ((printTm' i (f ∙ var sv))) --DLam sv 
printTm' {a = NU _}   i (x ,  y)  = DVar "_,_"   $ printTm' i x $ printTm' i y
printTm' {a = NU _}   i (x ,, y)  = DVar "_,,_"  $ printTm' i x $ printTm' i y
printTm' {a = NU _}   i (Left  x) = DVar "Left"  $ printTm' i x
printTm' {a = NU _}   i (Right x) = DVar "Right" $ printTm' i x
printTm' {a = NU _}   i Refl      = DVar "Refl"
printTm' {a = NU _}   i (RDC {rc = rc} args) = DVar ("Mk" +++ name rc) $ printTm' i args
printTm' {a = NU _}   i (NeNU {s = s} x) = printSpine' i s


showTm : Tm a -> String
showTm t = showDoc (printTm t)


----------------

betaPi : ∀ {f : Tm a -> Tm a'} {x : _} -> lam "l" f ∙ x ≈ f x
betaPi = Refl

-- not True
-- etaPi : ∀ {f : Tm (a => a')} ->  f  ≈  lam "l" \x -> f ∙ x


const : Tm (a' => a => a')
const = "const" := Lam' \x -> Lam' \_ -> RHS x

pi : (A : Ty) -> (Tm A -> Ty) -> Ty
pi A B = Pi A (lam "piLam" \a -> B a)

VarName = String

var n = n := NoRHS (Stuck n)


module _ where

  BoolDesc = named "Bool" (RD Top (const ∙ (Top ⊎ Top)))

  Bool' = RTC BoolDesc TT

  False' : Tm Bool'
  False' = RDC (Left TT)

  True' : Tm Bool'
  True' = RDC (Right TT)

  and : Tm (Bool' => Bool' => Bool')
  and = "and" := Lam' \a -> Lam' \b -> elimR a \a _ -> elim⊎ a
       (\_ _ -> RHS False')
       (\_ _ -> RHS b)

  mkBool : Bool -> ⟦ Bool' ⟧
  mkBool False = wrap (Left  (emb tt))
  mkBool True  = wrap (Right (emb tt))

  getBool : ⟦ Bool' ⟧' -> Bool
  getBool (wrap (Left  _)) = False
  getBool (wrap (Right _)) = True

  andM : Bool -> Bool -> Bool
  andM a b = getBool (⟦ and ⟧ₜ' (mkBool a) (mkBool b))

  andTest : andM True True ≡ True
  andTest = Refl

  andTest' : andM False True ≡ False
  andTest' = Refl

  {-# TERMINATING #-}
  Nat' : Ty

  NatDesc = named "Nat" (RD Top (const ∙ (Top ⊎ Nat')))

  Nat' = RTC NatDesc TT

  Zero : Tm Nat'
  Zero = RDC (Left TT)

  Suc : Tm (Nat' => Nat')
  Suc = "Suc" := Lam' \n -> RHS (RDC (Right n))

  {-# TERMINATING #-}
  add : Tm (Nat' => Nat' => Nat')
  add = "add" := Lam' \n -> Lam' \m -> elimR n \n _ -> elim⊎ n
      (\_ _ -> RHS m                     )
      (\k _ -> RHS (Suc ∙ (add ∙ k ∙ m)) )

  mkNat : Nat -> ⟦ Nat' ⟧
  mkNat Z     = wrap (Left (emb tt))
  mkNat (S n) = wrap (Right (mkNat n))

  getNat : ⟦ Nat' ⟧' -> Nat
  getNat (wrap (Left  _)) = Z
  getNat (wrap (Right x)) = S (getNat x)

  addM : Nat -> Nat -> Nat
  addM a b = getNat (⟦ add ⟧ₜ' (mkNat a) (mkNat b))

  testAdd : addM (S (S Z)) (S (S Z)) ≡  S (S (S (S Z)))
  testAdd = Refl

  addTest : add ∙ (Suc ∙ Zero) ∙ (Suc ∙ Zero) ≈ Suc ∙ (Suc ∙ Zero)
  addTest = Refl

  addTest' : (\n -> add ∙ (Suc ∙ Zero) ∙ n)    ≈ \n -> Suc ∙ n
  addTest' = Refl

  testQuote  : showTm {a = Nat'} (add ∙ (Suc ∙ Zero) ∙ (Suc ∙ Zero)) ≈ "MkNat (Right (MkNat (Right (MkNat (Left tt)))))"
  testQuote = Refl

  testQuote2 : showTm {a = Nat'} (add ∙ (Suc ∙ var {a = Nat'} "n") ∙ var {a = Nat'} "m") ≈ "MkNat (Right (add n m))"
  testQuote2 = Refl


  {-# TERMINATING #-}
  Fin' : Nat' =>U

  FinDesc = named "Fin" (RD Nat' (lam "FinLam" \p ->
       Sigma Nat' (lam "Fin2" \n -> Id p (Suc ∙ n))
     ⊎ Sigma Nat' (lam "Fin3" \n -> Id p (Suc ∙ n) × Fin' ∙ n)
    ))

  Fin' = "Fin" := Lam' \n -> RHS (RTC FinDesc n)

  testQuote' : showTm (Pi Nat' (lam "f" \n -> Fin' ∙ (add ∙ (Suc ∙ n) ∙ n)))
                 ≈ "Pi (Nat tt) λv0 -> Fin (MkNat (Right (add v0 v0)))"
                 -- could be:  "Pi (Nat tt) \\v0 -> Fin (add (Suc v0) v0)"
  testQuote' = Refl

  ss = showTm (Pi Nat' (lam "f" (λ n → Fin' ∙ (add ∙ (Suc ∙ n) ∙ n))))

  --------------------------------------

  SigmaDesc = named "Sigma" (RD
       (Sigma U (lam "SigL" \a -> a => U))
       (lam' "SigL2" \t -> elimSigma t \a b _ -> RHS (Sigma a (lam "SigL3" \x -> b ∙ x)))
    )

  Sigma'' : Tm (Pi U (lam "SL" \a -> (a => U) => U))
  Sigma'' = "Sigma" := DLam' \a -> Lam' \b -> RHS (RTC SigmaDesc (a ,, b))

  Pair' : Tm (pi U \a -> pi (a => U) \b -> pi (a) \x -> b ∙ x => (Sigma'' ∙∙ a ∙ b))
  Pair' = "Pair" := DLam' \a -> DLam' \b -> DLam' \x -> Lam' \y -> RHS (RDC (x ,, y))

  Fst' : Tm (pi U \a -> pi (a => U) \b -> (Sigma'' ∙∙ a ∙ b) => a)
  Fst' = "fst" := DLam' \a -> DLam' \b -> Lam' \p -> elimR p \p _ -> elimSigma p \a _ _ -> RHS a

  Snd' : Tm (pi U \a -> pi (a => U) \b -> pi ((Sigma'' ∙∙ a ∙ b)) \t -> (b ∙ (Fst' ∙∙ a ∙∙ b ∙ t)))
  Snd' = "snd" := DLam' \A -> DLam' \B -> DLam' \p -> elimR p \{p Refl -> elimSigma p \{_ b Refl -> RHS b}}

  betaFst : ∀ {a b} {x : Tm (a)} {y : Tm (b ∙ x)} -> Fst' ∙∙ a ∙∙ b ∙ (Pair' ∙∙ a ∙∙ b ∙∙ x ∙ y) ≈ x
  betaFst = Refl

  betaSnd : ∀ {a b} {x : Tm (a)} {y : Tm (b ∙ x)} -> Snd' ∙∙ a ∙∙ b ∙∙ (Pair' ∙∙ a ∙∙ b ∙∙ x ∙ y) ≈ y
  betaSnd = Refl
{-
  curry : {c : Ty} -> Tm ((Sigma' a b => c) => Pi a (lam "curryFun" \x -> code (b ∙ x => c)))
  curry = def "curry" (Lam' \f -> DLam' \x -> Lam \y -> RHS (f ∙ Pair x y))

  uncurry : {c : Ty} -> Tm (Pi a (lam "uncurryFun" \x -> code (b ∙ x => c)) => Sigma' a b => c)
  uncurry = def "uncurry" (Lam' \f -> Lam \p -> elimR p \p e -> elimSigma p \x y _ -> RHS (f ∙∙ x ∙ y))

  uncurry' : {c : Ty} -> Tm (Pi a (lam "uncurryFun'" \x -> code (b ∙ x => c)) => Sigma' a b => c)
  uncurry' = def "uncurry" (Lam' \f -> Lam \p -> RHS (f ∙∙ (Fst' ∙ p) ∙ (Snd' ∙∙ p)))
-}
  -------------------------

  etaSigma : Tm (pi U \a -> pi (a => U) \b -> pi ((Sigma'' ∙∙ a ∙ b)) \t ->
     Id t (Pair' ∙∙ a ∙∙ b ∙∙ (Fst' ∙∙ a ∙∙ b ∙ t) ∙ (Snd' ∙∙ a ∙∙ b ∙∙ t)))
  etaSigma = "etaSigma" := DLam' \a -> DLam' \b -> DLam' \t ->
    elimR t \{t' Refl -> elimSigma t' \{x y Refl -> RHS Refl}}


