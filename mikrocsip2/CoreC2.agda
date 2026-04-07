{-
Same as CoreB.agda but neutral terms are added.
Printing is now possible.
Lam and ifTag is not a netural term; to achieve this LHS terms are separated from terms.
-}


{-# OPTIONS --type-in-type --rewriting --prop #-}

open import Agda.Builtin.String using (String; primStringAppend; primShowNat)
open import Agda.Builtin.Nat using (Nat) renaming (suc to S; zero to Z)

-------------------

infixl 9 _∙_     -- non-dependent application
infixl 9 _∙∙_    -- dependent application
infixl 9 _$_     -- non-dependent application
infixl 9 _$$_    -- dependent application
infixr 8 _∘~_    -- transitivity for _~_
infixr 8 _∘≈_    -- transitivity for _≈_
infixr 7 _×_     -- non-dependent pair type
infixr 6 _=>_    -- non-dependent function type
infix  3 _~_     -- inhomogenous Prop equality
infix  3 _≈_     -- homogenous Prop equality
infix  3 _≡_     -- homogenous Set equality
infixr 2 _+++_   -- string concatenation
infixr 2 _**_    -- dependent pair type (infix Σ)
infixr 0 _,_     -- non-dependent pair constructor
infixr 0 _,,_    -- dependent pair constructor

-------------------

record _**_ (A : Set) (B : A -> Set) : Set where
  pattern
  constructor _,,_
  field
    fst : A
    snd : B fst

open _**_

---------------------

private variable
  A A' B C : Set
  P Q : Prop

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
  coh : {a : A} {e : A ~ B} -> coe~ e a ~ a
  coh {e = Refl} = Refl

-----------------------

  homog : {a a' : A} -> a ~ a' -> a ≈ a'
  homog Refl = Refl

  inhomog : {a a' : A} -> a ≈ a' -> a ~ a'
  inhomog Refl = Refl

coe≈ : A ≈ B → A → B
coe≈ e = coe~ (inhomog e)

cong≈ : {B : A -> Set} {a a' : A} -> (f : (a : A) -> B a) -> a ≈ a' -> f a ~ f a'
cong≈ _ Refl = Refl

subst≈ : (P : A -> Set) -> {a a' : A} -> a ≈ a' -> P a -> P a'
subst≈ P x x₁ = coe≈ (homog (cong≈ P x)) x₁

subst≈' : (P : A -> Prop) -> {a a' : A} -> a ≈ a' -> P a -> P a'
subst≈' _ Refl x₁ = x₁
---------------------

cong≈' : {a a' : A} -> (f : A -> B) -> a ≈ a' -> f a ≈ f a'
cong≈' f e = homog (cong≈ f e)

cong2≈ : {a a' : A} {b b' : B} -> (f : A -> B -> C) -> a ≈ a' -> b ≈ b' -> f a b ≈ f a' b'
cong2≈ _ Refl Refl = Refl

------------------

data _≡_ {A : Set} (a : A) : A -> Set where
  Refl : a ≡ a

propEq : {x y : A} -> x ≡ y -> x ≈ y
propEq Refl = Refl

setEq : {a a' : A} -> a ≈ a' -> a ≡ a'
setEq {a = a} e = coe≈ (cong≈' (\x -> a ≡ x) e) Refl


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

data Ty : Set

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
  Top'       :                                     TyNU
  _=>'_ _×'_ _⊎'_ : Ty -> Ty ->                    TyNU
  Pi' Sigma' : (a : Ty) -> Tm (arr a u) ->         TyNU
  Id'        : Tm a -> Tm a ->                     TyNU
  RTC'       : ∀ rc -> Tm (rParams rc) ->          TyNU
  TLHS       : ∀ {s : Spine u} {l} -> Glued s l -> TyNU

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
  TT    :                                              Tm Top
  _,_   : Tm a -> Tm a' ->                             Tm (a × a')
  _,,_  : (x : Tm a) -> Tm (b ∙ x) ->                  Tm (Sigma a b)
  Left  : Tm a ->                                      Tm (a ⊎ a')
  Right : Tm a' ->                                     Tm (a ⊎ a')
  Refl  : {x : Tm a} ->                                Tm (Id x x)
  RDC   : ∀ {ps} (args : Tm (rFields rc ∙ ps)) ->      Tm (RTC rc ps)
  LHS   : ∀ {a} {s : Spine (NU a)} {l} -> Glued s l -> Tm (NU a)

gLHS : {s : Spine a} {l : Lambda a} -> Glued s l -> Tm a
gLHS {a = U}    g = NU (TLHS g)
gLHS {a = NU _} g =      LHS g

-- LHS Terms
data TmL : Ty -> Set  where
  RHS   : Tm     a -> TmL a
  NoRHS : Lambda a -> TmL a

{-# NO_POSITIVITY_CHECK #-}
data Lambda where
  Lam   : (Tm a -> TmL a') ->            Lambda (a => a')
  DLam  : ((x : Tm a) -> TmL (b ∙ x)) -> Lambda (Pi a b)
  Stuck :                                Lambda a

data Spine where
  Head : Named (Lambda a) ->                                     Spine a
  _$_  : Spine (a => a') -> Tm a ->                              Spine a'
  DApp : ∀ {bx} -> Spine (Pi a b) -> (x : Tm a) -> b ∙ x ≡ bx -> Spine bx

pattern _$$_ f x = DApp f x Refl


data Glued where
  CHead : (t : Named (Lambda a)) ->                                                 Glued (Head t) (unnamed t)
  CLam  : ∀ {s : Spine (a => a')} {f x fx} -> Glued s (Lam  f) -> f x ≈ NoRHS fx -> Glued (s $  x) fx
  CDLam : ∀ {s : Spine (Pi a b)}  {f x fx} -> Glued s (DLam f) -> f x ≈ NoRHS fx -> Glued (s $$ x) fx
  C$    : ∀ {s : Spine (a => a')} {x} ->      Glued s Stuck ->                      Glued (s $  x) Stuck
  C$$   : ∀ {s : Spine (Pi a b)}  {x} ->      Glued s Stuck ->                      Glued (s $$ x) Stuck

lhs∙ : ∀ {s : Spine (a => a')} {f x} -> Glued s (Lam f) -> (r : _) -> f x ≈ r -> Tm a'
lhs∙ c (RHS   t) e = t
lhs∙ c (NoRHS t) e = gLHS (CLam c e)

LHS {l = Lam f} c ∙ x = lhs∙ c (f x) Refl
LHS {l = Stuck} c ∙ x = gLHS (C$ {x = x} c)

lhs∙∙ : ∀ {s : Spine (Pi a b)} {f x} -> Glued s (DLam f) -> (r : _) -> f x ≈ r -> Tm (b ∙ x)
lhs∙∙ c (RHS   t) e = t
lhs∙∙ c (NoRHS t) e = gLHS (CDLam c e)

_∙∙_ : Tm  (Pi a b) -> (x : Tm a) -> Tm (b ∙ x)
LHS {l = DLam f} c ∙∙ x = lhs∙∙ c (f x) Refl
LHS {l = Stuck}  c ∙∙ x = gLHS (C$$ c)


---------------------

neutToTm : Spine a -> Tm a
neutToTm (Head f) = gLHS (CHead f)
neutToTm (f $  x) = neutToTm f ∙  x
neutToTm (f $$ x) = neutToTm f ∙∙ x

glued : {s : Spine a} {t : Lambda a} (g : Glued s t) -> neutToTm s ≈ gLHS g
glued {s = Head _} (CHead _) = Refl
glued {s = s $  x} (C$ c) = cong≈' (\f -> f ∙ x) (glued c)
glued {s = s $  x} {t = t} (CLam {f = f} c e) = helper Refl e (cong≈' (\f -> f ∙ x) (glued c))
   where
    helper : {fx : _} (ee : f x ≈ fx) -> fx ≈ NoRHS t -> neutToTm s ∙ x ≈ lhs∙ c fx ee -> neutToTm s ∙ x ≈ gLHS (CLam c e)
    helper _ Refl cc = cc
glued {s = s $$ x} (C$$ c) = cong≈' (\f -> f ∙∙ x) (glued c)
glued {s = s $$ x} {t = t} (CDLam {a = a} {b = b} {f = f} c e) = helper Refl e (cong≈' (\f -> f ∙∙ x) (glued c))
   where
    helper : {fx : _} (ee : f x ≈ fx) -> fx ≈ NoRHS t -> neutToTm s ∙∙ x ≈ lhs∙∙ c fx ee -> neutToTm s ∙∙ x ≈ gLHS (CDLam c e)
    helper _ Refl cc = cc

-----------------------

elim× : ∀ {r} ->
  (tm : Tm (a × a')) -> 
  (match : (x : Tm a) (y : Tm a') -> (x , y) ≡ tm -> TmL r) ->
    TmL r
elim× (x , y) match = match x y Refl
elim× (LHS _) match = NoRHS Stuck

elimSigma : ∀ {r} ->
  (tm : Tm (Sigma a b)) -> 
  (match : (x : Tm a) (y : Tm (b ∙ x)) -> (x ,, y) ≡ tm -> TmL r) ->
    TmL r
elimSigma (x ,, y) match = match x y Refl
elimSigma (LHS _)  match = NoRHS Stuck

elimRDC : ∀ {a} {params : _} ->
  (tm    : Tm (RTC rc params)) ->
  (match : (args : Tm (rFields rc ∙ params)) -> RDC args ≡ tm -> TmL a) ->
    TmL a
elimRDC (RDC args) match = match args Refl
elimRDC (LHS _)    match = NoRHS Stuck

elim⊎ :
  (tm : Tm (a ⊎ a')) ->
  ((t : Tm a)  -> Left  t ≡ tm -> TmL a'') ->
  ((t : Tm a') -> Right t ≡ tm -> TmL a'') ->
    TmL a''
elim⊎ (Left  t) l r = l t Refl
elim⊎ (Right t) l r = r t Refl
elim⊎ (LHS _)   _ _ = NoRHS Stuck

elimId :
  {x y : Tm a} ->
  (tm : Tm (Id x y)) ->
  ((t : Tm a) -> TmNU.Refl {x = t} ~ tm -> TmL a') ->
    TmL a'
elimId Refl    match = match _ Refl
elimId (LHS _) match = NoRHS Stuck

--------------------

def : String -> Lambda a -> Tm a
def n t = gLHS (CHead (named n t))

lam' : String -> (Tm a -> TmL a') -> Tm (a => a')
lam' n f = def n (Lam f)

lam : String -> (Tm a -> Tm a') -> Tm (a => a')
lam n f = lam' n \t -> RHS (f t)

pattern Lam'  f = NoRHS (Lam  f)
pattern DLam' f = NoRHS (DLam f)

------------------

fst× : Tm (a × a' => a)
fst× = def "fst×" (Lam \p -> elim× p \x _ _ -> RHS x)

snd× : Tm (a × a' => a')
snd× = def "snd×" (Lam \p -> elim× p \_ y _ -> RHS y)

fstΣ : Tm (Sigma a b => a)
fstΣ = def "fstΣ" (Lam \p -> elimSigma p \x _ _ -> RHS x)

sndΣ : Tm (Pi (Sigma a b) (lam "sndΣLam" \t -> b ∙ (fstΣ ∙ t)))
sndΣ = def "sndΣ" (DLam \p -> elimSigma p \{x y Refl -> RHS y})

either' : {c : Ty} -> Tm ((a => c) => (a' => c) => a ⊎ a' => c)
either' = def "either" (Lam (λ f → NoRHS (Lam (λ g → NoRHS (Lam (λ x → elim⊎ x (λ t x₁ → RHS (f ∙ t)) λ t x₁ → RHS (g ∙ t)))))))

_+++_ : String -> String -> String
a +++ b = primStringAppend a b

proj : ∀ {ps} -> Tm (RTC rc ps => rFields rc ∙ ps)
proj {rc = rc} = def ("proj" +++ name rc) (Lam \t -> elimRDC t \t _ -> RHS t)
{-
proj' : Tm (Pi (rParams rc) (lam "projLam" \ps -> RTC rc ps => rFields rc ∙ ps))
proj' {rc = rc} = def ("proj" +++ name rc)  (DLam \_ -> Lam' \t -> elimRDC t \t _ -> RHS t)
-}

--------------------

record T : Prop where
  constructor tt

record Emb (P : Prop) : Set where
  constructor emb
  field
    getProp : P

data Either (A B : Set) : Set where
  Left  : A -> Either A B
  Right : B -> Either A B

record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

either : (A -> Tm a) -> (A' -> Tm a') -> Either A A' -> Tm (a ⊎ a')
either f g (Left  x) = Left  (f x)
either f g (Right x) = Right (g x)

pair : (A -> Tm a) -> (A' -> Tm a') -> Pair A A' -> Tm (a × a')
pair f g (x , y) = f x , g y

fun : (Tm a -> A) -> (A' -> Tm a') -> (A -> A') -> Tm (a => a')
fun f g h = lam "OK?" \x -> g (h (f x))

top : Emb T -> Tm Top
top _ = TT

postulate
  impossibleP : P
  impossible : A
  TODOP : P
  TODO : A

⟦_⟧  : (a : Ty) -> Set
⟦_⟧ₜ : Tm a    -> ⟦ a ⟧
⟦_⟧ₛ : Spine a -> ⟦ a ⟧

⟦ U         ⟧ = Set ** \A -> Ty ** \t -> A ≡ ⟦ t ⟧
⟦ Top       ⟧ = Emb T
⟦ a => a'   ⟧ = ⟦ a ⟧ -> ⟦ a' ⟧ -- ) ** \f -> Tm (a => a') ** \t -> ((x : Tm a) -> f ⟦ x ⟧ₜ ≡ ⟦ t ∙ x ⟧ₜ)
⟦ a ×  a'   ⟧ = Pair ⟦ a ⟧ ⟦ a' ⟧
⟦ a ⊎  a'   ⟧ = Either ⟦ a ⟧ ⟦ a' ⟧
⟦ Pi    a b ⟧ = (x : ⟦ a ⟧) -> fst (⟦ b ⟧ₜ x)
⟦ Sigma a b ⟧ = ⟦ a ⟧ ** \x -> fst (⟦ b ⟧ₜ x)
⟦ Id x y    ⟧ = ⟦ x ⟧ₜ ≡ ⟦ y ⟧ₜ
⟦ RTC rc x  ⟧ = fst (⟦ rFields rc ⟧ₜ ⟦ x ⟧ₜ)
⟦ NU (TLHS {s = s} _) ⟧ = fst (⟦ s ⟧ₛ)

he : (f : Tm (a => U)) (x : Tm a) -> ⟦ f ∙ x ⟧ ≈ fst (⟦ f ⟧ₜ ⟦ x ⟧ₜ)

{-# TERMINATING #-}
⟦_⟧ₜ {a = U}    t  = ⟦ t ⟧ ,, t ,, Refl
⟦_⟧ₜ {a = NU _} TT = emb tt
⟦_⟧ₜ {a = NU _} (x ,  y) = ⟦ x ⟧ₜ , ⟦ y ⟧ₜ
⟦_⟧ₜ {a = NU _} (_,,_ {b = b} x y) = ⟦ x ⟧ₜ ,, coe≈ (he b x) ⟦ y ⟧ₜ
⟦_⟧ₜ {a = NU _} (Left  x) = Left  ⟦ x ⟧ₜ
⟦_⟧ₜ {a = NU _} (Right x) = Right ⟦ x ⟧ₜ
⟦_⟧ₜ {a = NU _} Refl = Refl
⟦_⟧ₜ {a = NU _} (RDC {rc = rc} args) = coe≈ (he (rFields rc) _) ⟦ args ⟧ₜ
⟦_⟧ₜ {a = NU _} (LHS {s = s} _) = ⟦ s ⟧ₛ

⟦_⟧ₐ : Lambda a -> ⟦ a ⟧
⟦_⟧ₗ : TmL a    -> ⟦ a ⟧

quoteTm : ⟦ a ⟧ -> Tm a

{-
⟦ Head (named n (Lam  f)) ⟧ₛ = (\x -> ⟦ f (quoteTm x) ⟧ₗ) ,, LHS {s = Head (named n (Lam f))} (Lam f) (CHead (named n (Lam f))) ,, {!!}
⟦ Head (named n (DLam f)) ⟧ₛ = TODO
⟦ Head (named n Stuck) ⟧ₛ = impossible
-}
{-
⟦ Head (named n l) ⟧ₛ = ⟦ l ⟧ₐ
⟦ s $  x ⟧ₛ = fst ⟦ s ⟧ₛ ⟦ x ⟧ₜ
⟦ DApp {b = b} s x Refl ⟧ₛ = coe≈ (sym≈ (he b x)) (⟦ s ⟧ₛ ⟦ x ⟧ₜ)
-}
⟦ s ⟧ₛ = {!!}


quoteTm {a = U} (_ ,, t ,, _) = t
quoteTm {a = Top}       = top
quoteTm {a = a => a'} f = fun ⟦_⟧ₜ quoteTm f --lam "???" \x -> quoteTm {a = a'} (f ⟦ x ⟧ₜ)
quoteTm {a = a ×  a'}   = pair   (quoteTm {a = a}) (quoteTm {a = a'})
quoteTm {a = a ⊎  a'}   = either (quoteTm {a = a}) (quoteTm {a = a'})
quoteTm {a = Pi    a b} = TODO
quoteTm {a = Sigma a b} = TODO
quoteTm {a = Id x y}    = TODO
quoteTm {a = RTC rc x}  = TODO
quoteTm {a = NU (TLHS g)} = TODO

evalQuote : {x : Tm a} -> x ≈ quoteTm ⟦ x ⟧ₜ
evalQuote {a = U} {x = x} = Refl
evalQuote {a = Top} {x = TT} = Refl
evalQuote {a = Top} {x = LHS _} = impossibleP
evalQuote {a = a => a'} {x = LHS {s = s} {l = Stuck} x} = impossibleP
evalQuote {a = a => a'} {x = LHS {s = Head (named name₁ unnamed₁)} {l = Lam f} x} = {!!}
evalQuote {a = a => a'} {x = LHS {s = s $ x₁} {l = Lam f} x} = impossibleP
evalQuote {a = a => a'} {x = LHS {s = DApp s x₁ x₂} {l = Lam f} x} = impossibleP
evalQuote {a = a × a'} {x = x , y} = cong2≈ _,_ (evalQuote {a = a} {x = x}) (evalQuote {a = a'} {x = y})
evalQuote {a = a × a'} {x = LHS _} = impossibleP
evalQuote {a = a ⊎ a'} {x = Left  x} = cong≈' Left  (evalQuote {a = a}  {x = x})
evalQuote {a = a ⊎ a'} {x = Right x} = cong≈' Right (evalQuote {a = a'} {x = x})
evalQuote {a = a ⊎ a'} {x = LHS _} = impossibleP
evalQuote {a = Pi    a b} {x = x} = TODOP
evalQuote {a = Sigma a b} {x = x} = TODOP
evalQuote {a = Id y z} {x = x} = TODOP
evalQuote {a = RTC rc y} {x = x} = TODOP
evalQuote {a = NU (TLHS g)} {x = x} = TODOP


⟦ Lam  f ⟧ₐ = \x -> ⟦ f (quoteTm x) ⟧ₗ
⟦ DLam f ⟧ₐ = \x -> TODO
⟦ Stuck  ⟧ₐ = impossible

⟦ RHS   x ⟧ₗ = ⟦ x ⟧ₜ
⟦ NoRHS x ⟧ₗ = ⟦ x ⟧ₐ

he (LHS {s = s} {l = Stuck} g) x = impossibleP
he (LHS {s = Head (named _ (Lam f'))} {l = Lam f} g) x = {!!}
he (LHS {s = s $ y} {l = Lam f} g) x = TODOP
he (LHS {s = DApp s y e} {l = Lam f} g) x = TODOP


--------------------

data Bool : Set where True False : Bool

_&&_ : Bool -> Bool -> Bool
False && _ = False
True  && a = a

data Dec' (A : Set) : Set where
  Yes : A -> Dec' A
  No  :      Dec' A

Tm~  : {a : Ty} -> Tm a -> {b : Ty} -> Tm b -> Set
data TmNU~ : {a : TyNU} -> TmNU a -> {b : TyNU} -> TmNU b -> Set
-- convertible types
data Ty~ : Ty -> Ty -> Set where
  U : Ty~ U U
  Top' : Ty~ Top Top
  Arr : {a a' : _}{b b' : _} -> Ty~ a a' -> Ty~ b b' -> Ty~ (a => b) (a' => b')
  Tuple : {a a' : _}{b b' : _} -> Ty~ a a' -> Ty~ b b' -> Ty~ (a × b) (a' × b')
  Either' : {a a' : _}{b b' : _} -> Ty~ a a' -> Ty~ b b' -> Ty~ (a ⊎ b) (a' ⊎ b')
  Pi' : {a a' : _}{b : _}{b' : _} -> Ty~ a a' -> TmNU~ b b' -> Ty~ (Pi a b) (Pi a' b')
  Sigma' : {a a' : _}{b : _}{b' : _} -> Ty~ a a' -> TmNU~ b b' -> Ty~ (Sigma a b) (Sigma a' b')
  Id' : {t : Ty}{a b a' b' : Tm t} -> Tm~ a a' -> Tm~ b b' -> Ty~ (Id a b) (Id a' b')
  RTC' : {desc desc' : _} -> (eq : desc' ≈ desc) -> {p : Tm (rParams desc)}{p' : Tm (rParams desc')} -> Tm~ p p' -> Ty~ (RTC desc p) (RTC desc' p')

Tm~ {a = U} t {b = U} t' = Ty~ t t'
Tm~ {a = NU _} t {b = NU _} t' = TmNU~ t t'
Tm~ {a = U} _ {b = NU _} _ = Emb ⊥
Tm~ {a = NU _} _ {b = U} _ = Emb ⊥
symTm~ : {a' b' : Ty} {a : Tm a'}{b : Tm b'} -> Tm~ a b -> Tm~ b a
coeTm : Tm~ a a' -> Tm a -> Tm a'

data TmNU~ where
  EtaTT : ∀ {t t'} -> TmNU~ {a = Top'} t {b = Top'} t'
  Eta× : {a : _}{a' : _} -> {t t' : Tm (a × a')} -> Tm~ (fst× ∙ t) (fst× ∙ t') -> Tm~ (snd× ∙ t) (snd× ∙ t') -> TmNU~ t t'
  EtaRDC : {h : RDesc}{g : Tm (rParams h)} -> {t t' : Tm (rFields h ∙ g )} -> Tm~ t t' -> TmNU~ (RDC {rc = h} t) (RDC {rc = h} t')
  EtaArr : {a : _}{b : _} -> {arr arr' : TmNU (a =>' b)} -> ((x : _) -> Tm~ (arr ∙ x) (arr' ∙ x)) -> TmNU~ arr arr'
  EtaSigma : {a : _}{b : _}{b' : _}{sig : Tm (Sigma a b)}{sig' : Tm (Sigma a b')} -> (e : Tm~ (fstΣ ∙ sig) (fstΣ ∙ sig')) -> (eq : Ty~ (b ∙ (fstΣ ∙ sig)) (b' ∙ (fstΣ ∙ sig'))) -> Tm~ (sndΣ ∙∙ sig) (sndΣ ∙∙ sig') -> TmNU~ sig sig'
  EtaPi : {a : _}{b : _}{b' : _}{pi : Tm (Pi a b)}{pi' : Tm (Pi a b')} -> (f : (x : Tm a) -> Tm~ (b ∙ x) (b' ∙ x)) -> ((x : Tm a) -> Tm~ (pi ∙∙ x) (pi' ∙∙ x)) -> TmNU~ pi pi'
  EtaId : {t : _}{a b : Tm t}{id id' : Tm (Id a b)} -> TmNU~ id id' -- Use J instead?
  -- ...


inhomtoTy~ : {t t' : Ty}{a : Tm t}{b : Tm t'} -> a ~ b -> Ty~ t t'
Ty~Toeq : Ty~ t t' -> t ≡ t'
inhomtoTy~ x = {!  !}
Ty~Toeq U = Refl
Ty~Toeq Top' = Refl
Ty~Toeq (Arr x x₁) with (Ty~Toeq x) | (Ty~Toeq x₁)
... | Refl | Refl = Refl
Ty~Toeq (Tuple x x₁) with (Ty~Toeq x) | (Ty~Toeq x₁)
... | Refl | Refl = Refl
Ty~Toeq (Pi' x x₁) with (Ty~Toeq x)
Ty~Toeq (Pi' x (EtaArr x₁)) | Refl = {!  !}
Ty~Toeq (Sigma' x x₁) = {!  !}
Ty~Toeq (Id' x x₁) = {!  !}
Ty~Toeq (RTC' eq x) = {!  !}
Ty~Toeq (Either' x x₁) = {!  !}


symTm~ {U} {U} {U} {U} x = x
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
symTm~ {Pi _ _} {Pi _ _} {a} {b} (EtaPi f x) = EtaPi (λ x₁ → symTm~ (f x₁)) λ x₃ → symTm~ (x x₃)
symTm~ {Sigma _ _} {Sigma _ _} {a} {b} (EtaSigma e eq x) = EtaSigma (symTm~ e) (symTm~ eq) (symTm~ x)
symTm~ {Id _ _} {Id _ _} {a} {b} EtaId = EtaId
symTm~ {RTC _ _} {RTC _ _} {a} {b} (EtaRDC x) = EtaRDC (symTm~ x)


{-# TERMINATING #-}
coeM : {t : Ty}{b b' : Tm (t => U)}{a : Tm t} -> Tm~ b b' -> Tm (b ∙ a) -> Tm (b' ∙ a)
coeM {a = a} (EtaArr x) x₁ with x a
... | g = coeTm g x₁


coeApp : {t : Ty}{b : Tm (t => U)}(a a' : Tm t) -> Tm~ a a' -> Tm (b ∙ a) -> Tm (b ∙ a')
coeApp {U} a a' U x₁ = x₁
coeApp {U} a a' Top' x₁ = x₁
coeApp {U} a a' (Arr x x₂) x₁ = {!  !}
coeApp {U} a a' (Tuple x x₂) x₁ = {!  !}
coeApp {U} a a' (Pi' x x₂) x₁ = {!  !}
coeApp {U} a a' (Sigma' x x₂) x₁ = {!  !}
coeApp {U} a a' (Id' x x₂) x₁ = {!  !}
coeApp {U} a a' (RTC' eq x) x₁ = {!  !}
coeApp {U} a a' (Either' y y₁) k = {!  !}
coeApp {NU x₂} a a' x x₁ = {!  !}

coeTm {U} U x₁ = x₁
coeTm {Top} Top' x₁ = x₁
coeTm {x₂ => x₃} (Arr x x₄) l = lam "" λ x₁ → coeTm x₄ (l ∙ (coeTm (symTm~ x) x₁))
coeTm {x₂ × x₃} (Tuple x x₄) y = coeTm x (fst× ∙ y ) , coeTm x₄ (snd× ∙ y)
coeTm {Pi a x₂} (Pi' {b' = b'} x (EtaArr f)) x₁ = LHS (CHead (named "" (DLam (λ i → RHS (coeM {b = x₂} {b' = b'} {a = i} (EtaArr f) (x₁ ∙∙ i))))))
coeTm {Sigma a x₂} (Sigma' {b' = b'} x (EtaArr f)) x₁ = fstΣ ∙ x₁ ,, coeM {_} {x₂} {b'} {fstΣ ∙ x₁} (EtaArr f) (sndΣ ∙∙ x₁)
coeTm {Id x₂ x₃} (Id' x x₄) r = TODO
coeTm {a ⊎ b} (Either' y y₁) z = either' ∙ lam "f" (λ x → Left (coeTm y x)) ∙ lam "g" (λ x → Right (coeTm y₁ x)) ∙ z
coeTm {RTC rc x₂} (RTC' eq x) y with setEq eq
... | Refl = RDC (coeApp {b = rc .unnamed .UnnamedRDesc.rFields} _ _ x (proj ∙ y))


postulate decString : (str str' : String) -> Dec' (str ≡ str')
{-# TERMINATING #-}
convTy  : Nat -> (a a' : Ty) -> Dec' (Ty~ a a')
convTmNU : ∀ {a a'} -> Nat -> (t : TmNU a)(t' : TmNU a') -> Dec' (TmNU~ t t')
convTm  : Nat -> (t : Tm  a)(t' : Tm a') -> Dec' (Tm~ t t')

decUnnamedRDesc : (rc rc' : UnnamedRDesc) -> Dec' (rc ≡ rc')
decUnnamedRDesc (RD rParams₁ rFields₁) (RD rParams₂ rFields₂) with convTy 0 rParams₁ rParams₂
... | prms = {!  !}

decDesc : (rc rc' : RDesc) -> Dec' (rc ≡ rc')
decDesc (named name₁ unnamed₁) (named name₂ unnamed₂) with decString name₁ name₂ | decUnnamedRDesc unnamed₁ unnamed₂
... | No | _ = No
... | Yes _ | No = No
... | Yes Refl | Yes Refl = Yes Refl

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
... | Yes x₄ | Yes x₅ = Yes TODO
... | Yes x₄ | No = No
... | No | bq = No
convTy i (RTC rc x) (RTC rc₁ x₁) = {!  !}
convTy i (NU (TLHS {l = Stuck} x)) (NU (TLHS {l = Stuck} x₁)) = TODO --Spline conversion
convTy _ _ _ = No

convTmNU {a = Top'} {a' = Top'} i t t' = Yes EtaTT
convTmNU {a = x =>' x₁} {a' = x' =>' x₁'} i t t' = {!  !}
convTmNU {a = x ×' x₁} {a' = x' ×' x₁'} i t t'
    with convTy i x x' | convTy i x₁ x₁' | convTm i (fst× ∙ t) (fst× ∙ t') | convTm i (snd× ∙ t) (snd× ∙ t')
... | Yes x₂ | Yes x₃ | Yes x₄ | Yes x₅ = Yes {!  !}
... | Yes x₂ | Yes x₃ | Yes x₄ | No = No
... | Yes x₂ | Yes x₃ | No | bq = No
... | Yes x₂ | No | aq | bq = No
... | No | bq' | aq | bq = No
convTmNU {a = x ⊎' x₁} {a' = x' ⊎' x₁'} i t t' = {!  !}
convTmNU {a = Pi' a x} {a' = Pi' a' x'} i t t' = {!  !}
convTmNU {a = Sigma' a x} {a' = Sigma' a' x'} i t t' = {!  !}
convTmNU {a = Id' x x₁} {a' = Id' x' x₁'} i t t' = {!  !}
convTmNU {a = RTC' rc x} {a' = RTC' rc' x'} i t t' = {!  !}
convTmNU {a = TLHS x} {a' = TLHS x'} i t t' = {!  !}
convTmNU {a = _} {a' = _} _ _ _ = No

convTm {a = U} {a' = U} i t t' = convTy i t t'
convTm {a = NU _} {a' = NU _} i t t' = convTmNU i t t'
convTm {a = _} {a' = _} _ _ _ = No

-------------------------------------

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

var : String -> Tm a
var n = gLHS (CHead (named n Stuck))


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
printTy' i (NU (TLHS {s = s} {l = Stuck} x)) = printSpine' i s

{-# TERMINATING #-}
printTm' {a = U}      i  t        = printTy' i t
printTm' {a = NU _}   i TT        = DVar "tt"
printTm' {a = a => b} i f         = let sv = "v" +++ primShowNat i in DLam sv (printTm' i (f ∙ var sv))
printTm' {a = NU _}   i (x ,  y)  = DVar "_,_"   $ printTm' i x $ printTm' i y
printTm' {a = NU _}   i (x ,, y)  = DVar "_,,_"  $ printTm' i x $ printTm' i y
printTm' {a = NU _}   i (Left  x) = DVar "Left"  $ printTm' i x
printTm' {a = NU _}   i (Right x) = DVar "Right" $ printTm' i x
printTm' {a = NU _}   i Refl      = DVar "Refl"
printTm' {a = NU _}   i (RDC {rc = rc} args) = DVar ("Mk" +++ name rc) $ printTm' i args
printTm' {a = NU _}   i (LHS {s = s} _) = printSpine' i s


showTm : Tm a -> String
showTm t = showDoc (printTm t)


----------------


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
  add = def "add" (Lam \n -> Lam' \m -> elimRDC n \n _ -> elim⊎ n
      (\_ _ -> RHS m                     )
      (\k _ -> RHS (Suc ∙ (add ∙ k ∙ m)) )
    )

  addTest : add ∙ (Suc ∙ Zero) ∙ (Suc ∙ Zero) ≈ Suc ∙ (Suc ∙ Zero)
  addTest = Refl

  addTest' : (\n -> add ∙ (Suc ∙ Zero) ∙ n)    ≈ \n -> Suc ∙ n
  addTest' = Refl

  testQuote  : showTm {a = Nat'} (add ∙ (Suc ∙ Zero) ∙ (Suc ∙ Zero)) ≈ "MkNat (Right (MkNat (Right (MkNat (Left tt)))))"
  testQuote = Refl

  testQuote2 : showTm {a = Nat'} (add ∙ (Suc ∙ var {a = Nat'} "n") ∙ var {a = Nat'} "m") ≈ "MkNat (Right (add n m))"
  testQuote2 = Refl


  {-# TERMINATING #-}
  Fin' : Tm (Nat' => U)

  FinDesc = named "Fin" (RD Nat' (lam "FinLam" \p ->
       Sigma Nat' (lam "Fin2" \n -> Id p (Suc ∙ n))
     ⊎ Sigma Nat' (lam "Fin3" \n -> Id p (Suc ∙ n) × Fin' ∙ n)
    ))

  Fin' = def "Fin" (Lam \n -> RHS (RTC FinDesc n))

  testQuote' : showTm (Pi Nat' (lam "f" \n -> Fin' ∙ (add ∙ (Suc ∙ n) ∙ n)))
                 ≈ "Pi (Nat tt) \\v0 -> Fin (MkNat (Right (add v0 v0)))"
                 -- could be:  "Pi (Nat tt) \\v0 -> Fin (add (Suc v0) v0)"
  testQuote' = Refl

  --------------------------------------

  SigmaDesc = named "Sigma" (RD
       (Sigma U (lam "SigL" \a -> a => U))
       (lam' "SigL2" \t -> elimSigma t \a b _ -> RHS (Sigma a (lam "SigL3" \x -> b ∙ x)))
    )

  Sigma'' : Tm (Pi U (lam "SL" \a -> (a => U) => U))
  Sigma'' = def "Sigma" (DLam \a -> Lam' \b -> RHS (RTC SigmaDesc (a ,, b)))

  Pair' : Tm (pi U \a -> pi (a => U) \b -> pi (a) \x -> b ∙ x => (Sigma'' ∙∙ a ∙ b))
  Pair' = def "Pair" (DLam \a -> DLam' \b -> DLam' \x -> Lam' \y -> RHS (RDC (x ,, y)))

  Fst' : Tm (pi U \a -> pi (a => U) \b -> (Sigma'' ∙∙ a ∙ b) => a)
  Fst' = def "fst" (DLam \a -> DLam' \b -> Lam' \p -> elimRDC p \p _ -> elimSigma p \a _ _ -> RHS a)

  Snd' : Tm (pi U \a -> pi (a => U) \b -> pi ((Sigma'' ∙∙ a ∙ b)) \t -> (b ∙ (Fst' ∙∙ a ∙∙ b ∙ t)))
  Snd' = def "snd" (DLam \A -> DLam' \B -> DLam' \p -> elimRDC p \{p Refl -> elimSigma p \{_ b Refl -> RHS b}})

  betaFst : ∀ {a b} {x : Tm (a)} {y : Tm (b ∙ x)} -> Fst' ∙∙ a ∙∙ b ∙ (Pair' ∙∙ a ∙∙ b ∙∙ x ∙ y) ≈ x
  betaFst = Refl

  betaSnd : ∀ {a b} {x : Tm (a)} {y : Tm (b ∙ x)} -> Snd' ∙∙ a ∙∙ b ∙∙ (Pair' ∙∙ a ∙∙ b ∙∙ x ∙ y) ≈ y
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
     Id t (Pair' ∙∙ a ∙∙ b ∙∙ (Fst' ∙∙ a ∙∙ b ∙ t) ∙ (Snd' ∙∙ a ∙∙ b ∙∙ t)))
  etaSigma = def "etaSigma" (DLam \a -> DLam' \b -> DLam' \t ->
    elimRDC t \{t' Refl -> elimSigma t' \{x y Refl -> RHS Refl}}
    )



