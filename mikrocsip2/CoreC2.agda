{-
Same as CoreB.agda but neutral terms are added.
Printing is now possible.
Lam and ifTag is not a netural term; to achieve this LHS terms are separated from terms.
-}


{-# OPTIONS --type-in-type --rewriting --prop --guardedness #-}

open import Agda.Builtin.Bool using (Bool) renaming (true to True; false to False)
open import Agda.Builtin.Char using (Char; primIsLower; primIsDigit; primIsAlpha; primIsSpace; primCharEquality)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe) renaming (just to Just; nothing to Nothing)
open import Agda.Builtin.String using (String; primStringAppend; primStringToList; primStringFromList; primStringEquality)
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
  constructor _,,_
  field
    fst : A
    snd : B fst

open _**_

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

coh : {a : A} {e : A ~ B} -> coe~ e a ~ a
coh {e = Refl} = Refl

-----------------------

homog : {a a' : A} -> a ~ a' -> a ≈ a'
homog Refl = Refl

inhomog : {a a' : A} -> a ≈ a' -> a ~ a'
inhomog Refl = Refl

coe≈ : A ≈ B → A → B
coe≈ e = coe~ (inhomog e)

cong≈~ : {B : A -> Set} {a a' : A} -> (f : (a : A) -> B a) -> a ≈ a' -> f a ~ f a'
cong≈~ _ Refl = Refl

cong≈ : {a a' : A} -> (f : A -> B) -> a ≈ a' -> f a ≈ f a'
cong≈ _ Refl = Refl

cong2≈ : {a a' : A} {b b' : B} -> (f : A -> B -> C) -> a ≈ a' -> b ≈ b' -> f a b ≈ f a' b'
cong2≈ _ Refl Refl = Refl

------------------

data _≡_ {A : Set} (a : A) : A -> Set where
  Refl : a ≡ a

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
  coinductive
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

_=>U : Ty -> Set

-- record description
record UnnamedRDesc : Set where
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

data TmNU : TyNU -> Set


Tm U      = Ty       -- definitional equality between (Tm U) and Ty; proposed by Bálint Török
Tm (NU a) = TmNU a

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

proj : ∀ {ps} -> Tm (RTC rc ps => rFields rc ∙ ps)
proj {rc = rc} = ("proj" +++ name rc) := Lam' \t -> elimR t \t _ -> RHS t
{-
proj' : Tm (Pi (rParams rc) (lam "projLam" \ps -> RTC rc ps => rFields rc ∙ ps))
proj' {rc = rc} = def ("proj" +++ name rc)  (DLam' \_ -> Lam' \t -> elimR t \t _ -> RHS t)
-}

-------------------- nonstandard model

record Wrap (⟦_⟧ : Ty -> Set) (rc : RDesc) (ps : Tm (rParams rc)) : Set where
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



--------------------

{-
data Dec' (A : Set) : Set where
  Yes : A -> Dec' A
  No  :      Dec' A

-- convertible types
data Ty~ : Ty -> Ty -> Set where
  Refl :
  U : Ty~ U U
  _=>_ : Ty~ a a' -> Ty~ b b' -> Ty~ (a => b) (a' => b')
  Pi : {b : a =>U} {b' : a' =>U} -> Ty~ a a' -> Tm~ b b' -> Ty~ (Pi a b) (Pi a' b')
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
Tm~ {a = NeU l x} t t' = Tm~' t t'

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
convTy i (NeU l g) (NeU l' g') = {!!}
convTy i _ _ = {!!}

convTmNU {a = Top'} i _ _ = Yes EtaTT
convTmNU {a = a =>' a'} i t t' = {!!}
convTmNU {a = a ×' a'} i t t' = {!!} -- with convTm i (fst× t) (fst× t') | convTm i (snd× t) (snd× t')
-- ... | Yes e | Yes e' = {!!}
convTmNU {a = Pi' a b} i t t' = {!!}
convTmNU {a = Sigma' a b} i t t' = {!!}
convTmNU {a = RTC' rc x} i t t' = {!!}
convTmNU {a = TC' tc x} i t t' = {!!}
convTmNU {a = NeU l g} i t t' = {!!}

convTm {a = U} i t t' = convTy i t t'
convTm {a = Top} i t t' = convTmNU i t t'
convTm {a = a => a'} i t t' = convTmNU i t t'
convTm {a = a × a'} i t t' = convTmNU i t t'
convTm {a = Pi a b} i t t' = convTmNU i t t'
convTm {a = Sigma a b} i t t' = convTmNU i t t'
convTm {a = RTC rc x} i t t' = convTmNU i t t'
convTm {a = TC tc x} i t t' = convTmNU i t t'
convTm {a = NeU l g} i t t' = convTmNU i t t'
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


-------------------------------------

printTm    : Tm a -> Doc
printSpine : Spine a -> Doc

printSpine (Head x) = DVar (name x)
printSpine (s $  x) = printSpine s $ printTm x
printSpine (s $$ x) = printSpine s $ printTm x

-- {-# TERMINATING #-}
printTm {a = U} U           = DVar "U"
printTm {a = U} Top         = DVar "Top"
printTm {a = U} Bot         = DVar "Bot"
printTm {a = U} (t => x)    = DVar "_=>_"    $ printTm t $ printTm x
printTm {a = U} (a × a')    = DVar "_×_"     $ printTm a $ printTm a'
printTm {a = U} (a ⊎ a')    = DVar "_⊎_"     $ printTm a $ printTm a'
printTm {a = U} (Pi t x)    = DVar "Pi"      $ printTm t $ printTm x
printTm {a = U} (Sigma a b) = DVar "_,_"     $ printTm a $ printTm b
printTm {a = U} (Id x y)    = DVar "Id"      $ printTm x $ printTm y
printTm {a = U} (RTC rc x)  = DVar (name rc) $ printTm x
printTm {a = U} (NU (NeU' {s = s} _)) = printSpine s
--printTm {a = NU (a =>' a')} f = DLam "v" (printTm (f ∙ var "v"))
printTm {a = NU _} TT = DVar "tt"
printTm {a = NU _} (x ,  y)  = DVar "_,_"   $ printTm x $ printTm y
printTm {a = NU _} (x ,, y)  = DVar "_,,_"  $ printTm x $ printTm y
printTm {a = NU _} (Left  x) = DVar "Left"  $ printTm x
printTm {a = NU _} (Right x) = DVar "Right" $ printTm x
printTm {a = NU _} Refl      = DVar "Refl"
printTm {a = NU _} (RDC {rc = rc} args) = DVar ("Mk" +++ name rc) $ printTm args
printTm {a = NU _} (NeNU {s = s} _) = printSpine s


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

var : String -> Tm a
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

  testQuote2 : showTm {a = Nat'} (add ∙ (Suc ∙ var {a = Nat'} "n") ∙ var {a = Nat'} "m")   ≈ "MkNat (Right (add n m))"
  testQuote2 = Refl


  {-# TERMINATING #-}
  Fin' : Nat' =>U

  FinDesc = named "Fin" (RD Nat' (lam "FinLam" \p ->
       Sigma Nat' (lam "Fin2" \n -> Id p (Suc ∙ n))
     ⊎ Sigma Nat' (lam "Fin3" \n -> Id p (Suc ∙ n) × Fin' ∙ n)
    ))

  Fin' = "Fin" := Lam' \n -> RHS (RTC FinDesc n)

  testQuote' : showTm (Pi Nat' (lam "f" \n -> Fin' ∙ (add ∙ (Suc ∙ n) ∙ n)))
                 ≈ "Pi (Nat tt) f" 
--                 ≈ "Pi (Nat tt) λv -> Fin (MkNat (Right (add v v)))"
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


