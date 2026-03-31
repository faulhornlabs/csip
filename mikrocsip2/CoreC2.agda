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
infixr 7 _×_     -- non-dependent pair type
infixr 6 _=>_    -- non-dependent function type
infix  3 _~_     -- inhomogenous Prop equality
infix  3 _≈_     -- homogenous Prop equality
infix  3 _≡_     -- homogenous Set equality
infixr 2 _+++_   -- string concatenation
infixr 2 _**_    -- dependent pair type (infix Σ)
infixr 0 _,_     -- non-dependent pair constructor
infixr 0 _,,_    -- dependent pair constructor

_+++_ : String -> String -> String
a +++ b = primStringAppend a b

-------------------

record _**_ (A : Set) (B : A -> Set) : Set where
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

printTy U           = DVar "U"
printTy Top         = DVar "Top"
printTy (t => x)    = DVar "_=>_"    $ printTy t $ printTy x
printTy (a × a')    = DVar "_×_"     $ printTy a $ printTy a'
printTy (a ⊎ a')    = DVar "_⊎_"     $ printTy a $ printTy a'
printTy (Pi t x)    = DVar "Pi"      $ printTy t $ printTm x
printTy (Sigma a b) = DVar "_,_"     $ printTy a $ printTm b
printTy (Id x y)    = DVar "Id"      $ printTm x $ printTm y
printTy (RTC rc x)  = DVar (name rc) $ printTm x
printTy (NU (TLHS {s = s} _)) = printSpine s

printTm {a = U}    t  = printTy   t
printTm {a = NU _} TT = DVar "tt"
printTm {a = NU _} (x ,  y)  = DVar "_,_"   $ printTm x $ printTm y
printTm {a = NU _} (x ,, y)  = DVar "_,,_"  $ printTm x $ printTm y
printTm {a = NU _} (Left  x) = DVar "Left"  $ printTm x
printTm {a = NU _} (Right x) = DVar "Right" $ printTm x
printTm {a = NU _} Refl      = DVar "Refl"
printTm {a = NU _} (RDC {rc = rc} args) = DVar ("Mk" +++ name rc) $ printTm args
printTm {a = NU _} (LHS {s = s} _) = printSpine s


showTm : Tm a -> String
showTm t = showDoc (printTm t)


----------------

var : String -> Tm a
var n = gLHS (CHead (named n Stuck))

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



