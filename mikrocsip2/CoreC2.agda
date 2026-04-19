{-

Compile with C-c C-x C-c    Backend: GHC

Try as

    ./CoreC2 <test.txt

-}


{-# OPTIONS --type-in-type --rewriting --prop --erasure --with-K --injective-type-constructors #-}

open import Agda.Builtin.Unit     using (tt) renaming (⊤ to T)
open import Agda.Builtin.Bool     using (Bool) renaming (true to True; false to False)
open import Agda.Builtin.Maybe    using (Maybe) renaming (just to Just; nothing to Nothing)
open import Agda.Builtin.List     using (List; []) renaming (_∷_ to Cons)
open import Agda.Builtin.Nat      using (Nat) renaming (suc to Suc; zero to Zero; _<_ to lessNat; _==_ to eqNat)
open import Agda.Builtin.Equality using () renaming (_≡_ to Eq; refl to Refl)
open import Agda.Builtin.Char     using (Char) renaming (primCharToNat to charToNat)
open import Agda.Builtin.String   using (String; primStringAppend)
  renaming (primStringToList to stringToList; primStringFromList to stringFromList; primStringEquality to eqString; primShowNat to showNat)
open import Agda.Builtin.IO       using (IO)
open import Agda.Builtin.TrustMe  using (primTrustMe)
--open import Agda.Builtin.Coinduction

-------------------

infixr 5 _&&_
infixr 4 _||_
infix  3 _≈_     -- Prop equality
infix  3 _≡_     -- Set equality
infix  3 _==_    -- Nat equality (to Bool)
infix  3 _<_
infixr 3 _∘_     -- transitivity for _≈_
infixr 2 _++_    -- string concatenation
infixr 2 _::_
infixr 2 _**_    -- dependent pair type (infix Σ)

_++_ : String -> String -> String
a ++ b = primStringAppend a b

_==_ : Nat -> Nat -> Bool
n == m = eqNat n m

_<_ : Nat -> Nat -> Bool
n < m = lessNat n m

pattern _::_ a as = Cons a as

postulate
  interact : (String -> String) → IO T

{-# FOREIGN GHC import qualified Data.Text.IO as TIO #-}
{-# COMPILE GHC interact = TIO.interact #-}

postulate
  fix : {A : Set} -> (A -> A) -> A
{-# COMPILE GHC fix = \_ f -> let x = f x in x #-}

---------------------

private variable
  A A' B C : Set
  P Q : Prop

---------------------

data _≈_ {A : Set} (a : A) : A -> Prop where
  Refl : a ≈ a

postulate
  coe     : A ≈ B → A → B
  coeRefl : {a : A} → coe Refl a ≈ a

{-# BUILTIN REWRITE _≈_ #-}
{-# REWRITE coeRefl #-}
{-# FOREIGN GHC data IEq a b c = IRefl #-}
{-# COMPILE GHC _≈_ = data IEq (IRefl) #-}
{-# COMPILE GHC coe = \_ _ _ -> coe #-}

sym : {a a' : A} -> a ≈ a' -> a' ≈ a
sym Refl = Refl

_∘_ : {a a' a'' : A} -> a ≈ a' -> a' ≈ a'' -> a ≈ a''
Refl ∘ e = e

cong : {a a' : A} -> (f : A -> B) -> a ≈ a' -> f a ≈ f a'
cong _ Refl = Refl

cong2 : {a a' : A} {b b' : B} -> (f : A -> B -> C) -> a ≈ a' -> b ≈ b' -> f a b ≈ f a' b'
cong2 _ Refl Refl = Refl

subst : {a a' : A} (f : A -> Set) -> a ≈ a' -> f a -> f a'
subst f e = coe (cong f e)

------------------

_≡_ : {A : Set} (a : A) -> A -> Set
_≡_ = Eq

propEq : {a a' : A} -> a ≡ a' -> a ≈ a'
propEq Refl = Refl

setEq : {a a' : A} -> a ≈ a' -> a ≡ a'
setEq {a = a} e = subst (_≡_ a) e Refl

-------------------

data Either (A B : Set) : Set where
  Left  : A -> Either A B
  Right : B -> Either A B

record Pair (A B : Set) : Set where
  pattern
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

cong~ : {a a' : A} {B : A -> Set} -> (f : (x : A) -> B x) -> a ≈ a' -> _≈_ {A ** B} (_ ,, f a) (_ ,, f a')
cong~ _ Refl = Refl

-------------------------------------

_||_ : Bool -> Bool -> Bool
True  || _ = True
False || b = b

_&&_ : Bool -> Bool -> Bool
False && _ = False
True  && b = b

not : Bool -> Bool
not True = False
not False = True

if_then_else_ : Bool -> A -> A -> A
if False then t else f = f
if True then t else f = t


foldr : (A -> B -> B) -> B -> List A -> B
foldr c n [] = n
foldr c n (x :: as) = c x (foldr c n as)

map : (A -> B) -> List A -> List B
map f []        = []
map f (a :: as) = f a :: map f as 

all : (A -> Bool) -> List A -> Bool
all p as = foldr _&&_ True (map p as)

any : (A -> Bool) -> List A -> Bool
any p as = foldr _||_ False (map p as)


-----------

data Dec (A : Set) : Set where
  Yes : A -> Dec A
  No  :      Dec A

-----------

record Name : Set where
  constructor MkName
  field
    nameStr : String  -- only for pretty printing
    nameId  : Nat     -- globally unique

open Name

eqName : Name -> Name -> Bool
eqName n m = nameId n == nameId m

decName : (n n' : Name) -> Dec (n ≡ n')
decName n n' = if eqName n n' then Yes primTrustMe else No


----------------------------------

NameMap : Set -> Set

emptySM     : NameMap A
insertSM    : Name -> A -> NameMap A -> NameMap A
lookupSMStr : String -> NameMap A -> Maybe (Pair Name A)

NameMap A = List (Pair Name A)

emptySM = []

insertSM s a m = (s , a) :: m

lookupSMStr s [] = Nothing
lookupSMStr s ((n , x) :: sm) with eqString (nameStr n) s
... | True  = Just (n , x)
... | False = lookupSMStr s sm

------------------------------------------------------------------ end of Lib

infixl 9 _∙_     -- non-dependent application
infixl 9 _∙∙_    -- dependent application
infixl 9 _$_     -- non-dependent application
infixl 9 _$$_    -- dependent application
infixr 8 _[_]_   -- operator syntax for Doc
infixr 7 _×_     -- non-dependent pair type
infixr 6 _⊎_     -- non-dependent function type
infixr 5 _=>_    -- non-dependent function type
infixr 0 _,_     -- non-dependent pair constructor
infixr 0 _,,_    -- dependent pair constructor
infix -1 _:=_

--------------------------------------------

record Named (A : Set) : Set where
  pattern
  constructor named
  field
    name    : Name
    unnamed : A

open Named

decNamed : (a : Named A) (b : Named B) -> Dec (_≡_ {A = Set ** Named} (_ ,, a) (_ ,, b))
decNamed a b with decName (name a) (name b)
... | Yes _ = Yes primTrustMe
... | No    = No

----------------------

data TyNU : Set
data TmNU : TyNU -> Set

data Ty : Set where
  U   :         Ty
  NU  : TyNU -> Ty

Tm : Ty -> Set
Tm U      = Ty       -- definitional equality between (Tm U) and Ty; proposed by Bálint Török
Tm (NU a) = TmNU a

_=>U : Ty -> Set    --   Tm (a => U)

-- record description
record UnnamedRDesc : Set where
  inductive
  pattern
  constructor Record
  field
    rParams : Ty
    rFields : rParams =>U

RDesc = Named UnnamedRDesc

rParams : RDesc -> Ty
rParams rc = UnnamedRDesc.rParams (unnamed rc)

rFields : (rc : RDesc) -> rParams rc =>U
rFields rc = UnnamedRDesc.rFields (unnamed rc)

private variable
  a a' a'' : Ty
  b        : a =>U
  rc       : RDesc

data Spine  : Ty -> Set  -- first  order representation    f e1 e2 ... eN
data Lambda : Ty -> Set  -- second order representation    \v1 -> \v2 ->  ... <<LHS part>> ...  (ret <<RHS part>>)
data Glued  : Spine a -> Lambda a -> Prop

data TyNU where
  Top' Bot'  :                                     TyNU
  _=>'_ _×'_ _⊎'_ : Ty -> Ty ->                    TyNU
  Pi' Sigma' : (a : Ty) -> a =>U ->                TyNU
  Id'        : Tm a -> Tm a ->                     TyNU
  Rec'       : ∀ rc -> Tm (rParams rc) ->          TyNU
  NeU'       : ∀ {s : Spine U} {l} -> Glued s l -> TyNU

pattern Top       = NU Top'
pattern Bot       = NU Bot'
pattern _=>_ a a' = NU (a =>' a')
pattern _×_  a a' = NU (a ×'  a')
pattern _⊎_  a a' = NU (a ⊎'  a')
pattern Pi    a b = NU (Pi'    a b)
pattern Sigma a b = NU (Sigma' a b)
pattern Id x y    = NU (Id' x y)
pattern Rec rc ps = NU (Rec' rc ps)
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
  Wrap  : ∀ {ps} (args : Tm (rFields rc ∙ ps)) ->      Tm (Rec rc ps)
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
--_$$_ : ∀ {bx} -> Spine (Pi a b) -> (x : Tm a) ->               Spine (b ∙ x)
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

VarName = Name

---------------------

spineToTm : Spine a -> Tm a
spineToTm (Head f) = Ne (CHead f)
spineToTm (f $  x) = spineToTm f ∙  x
spineToTm (f $$ x) = spineToTm f ∙∙ x

glued : {s : Spine a} {l : Lambda a} (g : Glued s l) -> spineToTm s ≈ Ne g
glued {s = Head _} (CHead _) = Refl
glued {s = s $ x} (C$ c) = cong (\k -> k ∙ x) (glued c)
glued {s = s $ x} {l = l} (CLam {f = f} c e) = helper e (cong (\k -> k ∙ x) (glued c))  where
  helper : {fx : _} {ee : f x ≈ fx} -> fx ≈ NoRHS l -> spineToTm s ∙ x ≈ lhs∙ c fx ee -> spineToTm s ∙ x ≈ Ne (CLam c e)
  helper Refl cc = cc
glued {s = s $$ x} (C$$ c) = cong (\k -> k ∙∙ x) (glued c)
glued {s = s $$ x} {l = l} (CDLam {f = f} c e) = helper e (cong (\k -> k ∙∙ x) (glued c))  where
  helper : {fx : _} {ee : f x ≈ fx} -> fx ≈ NoRHS l -> spineToTm s ∙∙ x ≈ lhs∙∙ c fx ee -> spineToTm s ∙∙ x ≈ Ne (CDLam c e)
  helper Refl cc = cc

--------------------

record TName (a : Ty) : Set where
  constructor MkTName
  field
    tName : Name

open TName

---------------

_:=_ : TName a -> LHS a -> Tm a
n := RHS   t = t
n := NoRHS t = Ne (CHead (named (tName n) t))

pattern Lam'  f = NoRHS (Lam  f)
pattern DLam' f = NoRHS (DLam f)

var : TName a -> Tm a
var n = n := NoRHS (Stuck (tName n))

-----------------------

objEq : {x y : Tm a} -> x ≡ y -> Tm (Id x y)
objEq Refl = Refl


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

elimR : ∀ {rc ps a} ->
  (tm : Tm (Rec rc ps)) ->
  ((args : Tm (rFields rc ∙ ps)) -> Wrap args ≡ tm -> LHS a) ->
    LHS a
elimR (Wrap args) f = f args Refl
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
  (_≡_ {A = Tm a ** \y -> Tm (Id x y)} (x ,, Refl) (y ,, tm) -> LHS a') ->
    LHS a'
elimId Refl f = f Refl
elimId (NeNU {l = Stuck n} _) f = NoRHS (Stuck n)

jRule : ∀ {x y}
  (tm : Tm (Id x y)) ->
  (P : (y : Tm a) -> Tm (Id x y) -> Ty) ->
  LHS (P x Refl) ->
    LHS (P y tm)
jRule tm P l = elimId tm \{Refl -> l}

kRule : ∀ {x : Tm a}
  (tm : Tm (Id x x)) ->
  (P : Tm (Id x x) -> Ty) ->
  LHS (P Refl) ->
    LHS (P tm)
kRule tm P l = elimId tm \{Refl -> l}

-------------------------------------------------------

data Tys : Set          --  [] (A : U) (x : A) (y : A) (e : x ≡ y)

Tms : Tys -> Set        --  (((tt, Bool), True), True), Refl

-- type depending on context
CTy : Tys -> Set
CTy ts = Tms ts -> Ty

-- term depending on context
CTm : (ts : Tys) -> CTy ts -> Set
CTm ts t = (xs : Tms ts) -> Tm (t xs)

infixl 3 _>>_::_
infixl 3 _>>>_

data Tys where
  []      :                                 Tys
  _>>_::_ : (ts : Tys) -> Name -> CTy ts -> Tys

Tms []             = T
Tms (ts >> n :: t) = Tms ts ** \xs -> Tm (t xs)

private variable
  ts : Tys

---------------

{-# TERMINATING #-}
⟦_⟧ᵤ : Ty -> CTy ts

⟦_⟧  : Tm a    -> CTm ts ⟦ a ⟧ᵤ
⟦_⟧ₛ : Spine a -> CTm ts ⟦ a ⟧ᵤ

postulate
  rParamsClosed : ∀ rc {xs : Tms ts} -> ⟦ rParams rc ⟧ᵤ xs ≈ rParams rc
  rFieldsClosed : ∀ rc {ps : Tm (rParams rc)} {xs : Tms ts} ->
    ⟦ rFields rc ∙ ps ⟧ᵤ xs  ≈  rFields rc ∙ subst Tm (rParamsClosed rc) (⟦ ps ⟧ xs)

⟦ U         ⟧ᵤ = \_ -> U
⟦ Top       ⟧ᵤ = \_ -> Top
⟦ Bot       ⟧ᵤ = \_ -> Bot
⟦ a => a'   ⟧ᵤ = \xs -> ae xs => ae' xs  where
  ae  = ⟦ a  ⟧ᵤ
  ae' = ⟦ a' ⟧ᵤ
⟦ a × a'    ⟧ᵤ = \xs -> ae xs ×  ae' xs  where
  ae  = ⟦ a  ⟧ᵤ
  ae' = ⟦ a' ⟧ᵤ
⟦ a ⊎ a'    ⟧ᵤ = \xs -> ae xs ⊎  ae' xs  where
  ae  = ⟦ a  ⟧ᵤ
  ae' = ⟦ a' ⟧ᵤ
⟦ Pi a b    ⟧ᵤ = \xs -> Pi    (ae xs) (be xs) where
  ae = ⟦ a ⟧ᵤ
  be = ⟦ b ⟧
⟦ Sigma a b ⟧ᵤ = \xs -> Sigma (ae xs) (be xs) where
  ae = ⟦ a ⟧ᵤ
  be = ⟦ b ⟧
⟦ Id x y    ⟧ᵤ = \xs -> Id (xe xs) (ye xs) where
  xe = ⟦ x ⟧
  ye = ⟦ y ⟧
⟦ Rec rc ps ⟧ᵤ = \xs -> Rec rc (subst Tm (rParamsClosed rc) (ps' xs)) where
  ps' = ⟦ ps ⟧
⟦ NU (NeU' {s = s} _) ⟧ᵤ = ⟦ s ⟧ₛ

postulate
  TODO : P

⟦⟧ᵤ∙ : ∀ {a} (b : a =>U) {x : Tm a} (xs : Tms ts) -> ⟦ b ∙ x ⟧ᵤ xs ≈ ⟦ b ⟧ xs ∙ ⟦ x ⟧ xs
⟦⟧ᵤ∙ = TODO

⟦⟧ᵤ[] : ⟦_⟧ᵤ {ts = []} a _ ≈ a
⟦⟧ᵤ[] {a = U        } = Refl
⟦⟧ᵤ[] {a = Top      } = Refl
⟦⟧ᵤ[] {a = Bot      } = Refl
⟦⟧ᵤ[] {a = a => a'  } = cong2 _=>_ ⟦⟧ᵤ[] ⟦⟧ᵤ[]
⟦⟧ᵤ[] {a = a ×  a'  } = cong2 _×_  ⟦⟧ᵤ[] ⟦⟧ᵤ[]
⟦⟧ᵤ[] {a = a ⊎  a'  } = cong2 _⊎_  ⟦⟧ᵤ[] ⟦⟧ᵤ[]
⟦⟧ᵤ[] {a = Pi    a b} = TODO
⟦⟧ᵤ[] {a = Sigma a b} = TODO
⟦⟧ᵤ[] {a = Id x y   } = TODO
⟦⟧ᵤ[] {a = Rec rc x } = TODO
⟦⟧ᵤ[] {a = NeU g    } = TODO

⟦_⟧ {a = U}    t          = ⟦ t ⟧ᵤ
⟦_⟧ {a = NU _} TT         = \xs -> TT
⟦_⟧ {a = NU _} (x ,  y)   = \xs -> xe xs , ye xs where
  xe = ⟦ x ⟧
  ye = ⟦ y ⟧
⟦_⟧ {a = NU _} (_,,_ {b = b} x y) = \xs -> xe xs ,, subst Tm (⟦⟧ᵤ∙ b xs) (ye xs) where
  xe = ⟦ x ⟧
  ye = ⟦ y ⟧
⟦_⟧ {a = NU _} (Left  x)  = \xs -> Left  (xe xs) where
  xe = ⟦ x ⟧
⟦_⟧ {a = NU _} (Right x)  = \xs -> Right (xe xs) where
  xe = ⟦ x ⟧
⟦_⟧ {a = NU _} Refl       = \xs -> Refl
⟦_⟧ {a = NU _} (Wrap {rc = rc} args) = \xs -> Wrap (subst Tm (rFieldsClosed rc) (args' xs)) where
  args' = ⟦ args ⟧
⟦_⟧ {a = NU _} (NeNU {s = s} _) = ⟦ s ⟧ₛ

postulate
  nameIsDefined : String -> Tm a
  weaken     : ∀ {ts} {t : CTy ts} {xs : Tms ts} {x : Tm (t xs)} a -> ⟦ a ⟧ᵤ xs ≈ ⟦_⟧ᵤ {ts = ts >> n :: t} a (xs ,, x)
  strengthen : ∀ {ts} {t : CTy ts} {xs : Tms ts} {x : Tm (t xs)} a -> ⟦_⟧ᵤ {ts = ts >> n :: t} a (xs ,, x) ≈ ⟦ a ⟧ᵤ xs
  thisIsIt : {t : CTy ts} {xs : Tms ts} {x : Tm (t xs)} -> Tm (t xs) ≈ Tm (⟦_⟧ᵤ {ts = ts >> n :: t} a (xs ,, x))
  b∙var⟦⟧ᵤ : ∀ {n} (b : a =>U) {xs : Tms ts} {x : Tm (⟦ a ⟧ᵤ xs)} -> ⟦_⟧ᵤ {ts = ts >> tName n :: ⟦ a ⟧ᵤ} (b ∙ var n) (xs ,, x) ≈ ⟦ b ⟧ xs ∙ x

indexTms : ∀ {a ts} -> Name -> CTm ts ⟦ a ⟧ᵤ
indexTms {ts = []} n = \xs -> nameIsDefined (nameStr n)
indexTms {a = a} {ts = ts >> n' :: t} n with eqName n' n
... | True  = \(xs ,, x) -> coe (thisIsIt {a = a}) x
... | False = \(xs ,, x) -> subst Tm (weaken a) (f xs)
 where
  f = indexTms {a = a} {ts = ts} n

postulate
  NamedLambdaClosed : {xs : Tms ts} -> NamedLambda (⟦ a ⟧ᵤ xs) ≈ NamedLambda a
  closed : {xs : Tms ts} -> ⟦ a ⟧ᵤ xs ≈ a

const : A -> B -> A
const x _ = x

⟦ Head {a = a} (named n (Stuck x)) ⟧ₛ = indexTms {a = a} n
⟦ Head h@(named _ (Lam  _))   ⟧ₛ = \xs -> subst Tm (sym closed) f where
  f = spineToTm (Head h)
⟦ Head h@(named _ (DLam _))   ⟧ₛ = \xs -> subst Tm (sym closed) f where
  f = spineToTm (Head h)
⟦ s $  x                      ⟧ₛ = \xs -> se xs ∙ xe xs where
  se = ⟦ s ⟧ₛ
  xe = ⟦ x ⟧
⟦ DApp {b = b} s x Refl       ⟧ₛ = \xs -> subst Tm (sym (⟦⟧ᵤ∙ b xs)) (se xs ∙∙ xe xs) where
  se = ⟦ s ⟧ₛ
  xe = ⟦ x ⟧


----------------------------------

Error : Set
Error = String

TyTm : Set
TyTm = Ty ** \a -> Tm a

Ctx : Set
Ctx = NameMap TyTm

LCtx = NameMap Ty

record TCState : Set where
  constructor MkTCState
  field
    counter : Nat

record TCEnv : Set where
  constructor MkTCEnv
  field
    globalEnv : Ctx
    localEnv  : LCtx

open TCEnv

-- type checking monad
record TC (A : Set) : Set where
  coinductive
  field
    getTC : TCEnv -> TCState -> Either Error (Pair TCState A)

open TC

throwError : Error -> TC A
getTC (throwError e) _ _ = Left e

runTC : TC A -> Either Error A
runTC tc with getTC tc (MkTCEnv emptySM emptySM) (MkTCState 10)
... | Left  e       = Left e
... | Right (_ , r) = Right r

_>>=_ : TC A -> (A -> TC B) -> TC B
getTC (m >>= f) ctx c with getTC m ctx c
... | Left  e = Left e
... | Right (c , x) = getTC (f x) ctx c

pure : A -> TC A
getTC (pure x) _ c = Right (c , x)

addGlobal : Name -> TyTm -> TC A -> TC A
getTC (addGlobal s d m) (MkTCEnv g l) = getTC m (MkTCEnv (insertSM s d g) l)

addLocal : Name -> Ty -> TC A -> TC A
getTC (addLocal s d m) (MkTCEnv g l) = getTC m (MkTCEnv g (insertSM s d l))

locals : TC LCtx
getTC locals env c = Right (c , localEnv env)

lookupTm : String -> TC TyTm
getTC (lookupTm s) env c with lookupSMStr s (localEnv env)
... | Just (n , x)  = Right (c , (x ,, var (MkTName n)))
... | Nothing with lookupSMStr s (globalEnv env)
...   | Just (n , x)  = Right (c , x)
...   | Nothing = Left ("Not defined: " ++ s)

newName : String -> TC Name
getTC (newName s) ctx (MkTCState c) = Right (MkTCState (Suc c) , MkName s c)

newNameT : String -> TC (TName a)
newNameT s = do
  n <- newName s
  pure (MkTName n)

-------------------------------------------------

data CharClass : Set where
  Alpha Graphic Punctuation InvalidChar : CharClass

charClass : Char -> CharClass
charClass '(' = Punctuation
charClass ')' = Punctuation
charClass ';' = Punctuation
charClass ',' = Punctuation
charClass '*' = Graphic
charClass '+' = Graphic
charClass '-' = Graphic
charClass '^' = Graphic
charClass '=' = Graphic
charClass '@' = Graphic
charClass '%' = Graphic
charClass '$' = Graphic
charClass '&' = Graphic
charClass '~' = Graphic
charClass '.' = Graphic
charClass '!' = Graphic
charClass '?' = Graphic
charClass ':' = Graphic
charClass '<' = Graphic
charClass '>' = Graphic
charClass '/' = Graphic
charClass '\\'= Graphic
charClass '|' = Graphic
charClass '#' = Graphic
charClass '_'  = Alpha
charClass '\'' = Alpha
charClass c    = if between 'A' 'Z' c || between 'a' 'z' c || between '0' '9' c then Alpha else InvalidChar  where
  between : Char -> Char -> Char -> Bool
  between a z c = (charToNat a < Suc (charToNat c)) && (charToNat c < Suc (charToNat z))

joinChars : CharClass -> CharClass -> Bool
joinChars Alpha   Alpha   = True
joinChars Graphic Graphic = True
joinChars _       _       = False

{-# TERMINATING #-}
tokens : Bool -> List Char -> TC (List String)
tokens _ [] = pure []
tokens True ('\n' :: c :: s) with charClass c
... | Alpha = do
  ts <- tokens False (c :: s)
  pure (";" :: ts)
... | _     = tokens True (c :: s)
tokens b ('\n' :: s) = tokens b s
tokens b (' '  :: s) = tokens b s
tokens b ('-' :: '-' :: s) = skip s where
  skip : List Char -> TC (List String)
  skip ('\n' :: s) = tokens b ('\n' :: s)
  skip (_    :: s) = skip s
  skip []          = pure []
tokens b (c :: s) with charClass c
... | InvalidChar = throwError ("invalid character: " ++ stringFromList (c :: []))
... | cc          = go cc s \r rs -> do
  ts <- tokens True rs
  pure (stringFromList (c :: r) :: ts)
 where
  go : CharClass -> List Char -> (List Char -> List Char -> A) -> A
  go cc (d :: cs) cont with joinChars cc (charClass d)
  ... | True  = go cc cs \r rs -> cont (d :: r) rs
  ... | False = cont [] (d :: cs)
  go cc [] cont = cont [] []

tokens' : String -> TC (List String)
tokens' s = tokens False (stringToList s)

testTokens : runTC (tokens' "(a ++ bc)") ≡ Right ("(" :: "a" :: "++" :: "bc" :: ")" :: [])
testTokens = Refl

showTokens : List String -> String
showTokens [] = ""
showTokens (t :: ts) = t ++ " " ++ showTokens ts

----------------------------------
  -- True for closed terms
--  noVars : VarName -> ⊥

postulate
  TODOP : P

--------------------

data Dec' (A : Set) : Set where
  Yes : A -> Dec' A
  No  :      Dec' A

data Emb (T : Prop) : Set where
  emb : T -> Emb T

data ⊥ : Prop where

data Ty~ : Ty -> Ty -> Prop
data TmNU~ : {a : TyNU} -> TmNU a -> {b : TyNU} -> TmNU b -> Prop
Tm~  : {a : Ty} -> Tm a -> {b : Ty} -> Tm b -> Prop
Tm~ {a = U} t {b = U} t' = Ty~ t t'
Tm~ {a = NU _} t {b = NU _} t' = TmNU~ t t'
Tm~ {a = U} _ {b = NU _} _ = ⊥
Tm~ {a = NU _} _ {b = U} _ = ⊥

data Spine~ : {a : Ty} -> Spine a -> {a' : Ty} -> Spine a' -> Prop
-- convertible types
data Ty~ where
  U : Ty~ U U
  Bot' : Ty~ Bot Bot
  Top' : Ty~ Top Top
  Arr : {a a' : _}{b b' : _} -> Tm~ a a' -> Tm~ b b' -> Ty~ (a => b) (a' => b')
  Tuple : {a a' : _}{b b' : _} -> Tm~ a a' -> Tm~ b b' -> Ty~ (a × b) (a' × b')
  Either' : {a a' : _}{b b' : _} -> Tm~ a a' -> Tm~ b b' -> Ty~ (a ⊎ b) (a' ⊎ b')
  Pi' : {a a' : _}{b : _}{b' : _} -> Tm~ a a' -> Tm~ b b' -> Ty~ (Pi a b) (Pi a' b')
  Sigma' : {a a' : _}{b : _}{b' : _} -> Tm~ a a' -> Tm~ b b' -> Ty~ (Sigma a b) (Sigma a' b')
  Id' : {t : Ty}{a b a' b' : Tm t} -> Tm~ a a' -> Tm~ b b' -> Ty~ (Id a b) (Id a' b')
  RTC' : {desc desc' : _} -> (eq : desc' ≈ desc) -> {p : Tm (rParams desc)}{p' : Tm (rParams desc')} -> Tm~ p p' -> Ty~ (Rec desc p) (Rec desc' p')
  NeU' : {s s' : _}{l : _}{g : Glued s l}{g' : Glued s' l} -> Spine~ s s' -> Ty~ (NeU g) (NeU g')

postulate symTm~ : {a' b' : Ty} {a : Tm a'}{b : Tm b'} -> Tm~ a b -> Tm~ b a
postulate coeTm : Tm~ a a' -> Tm a -> Tm a'
postulate substTm : (P : Tm a -> Set) -> {x y : Tm a} -> Tm~ x y -> P x -> P y

fst× : Tm (a × a' => a)
fst× = MkTName (MkName "fst×" 0) := Lam' \p -> elim× p \x y _ -> RHS x

snd× : Tm (a × a' => a')
snd× = MkTName (MkName "snd×" 1) := Lam' \p -> elim× p \x y _ -> RHS y

fstΣ : Tm (Sigma a b => a)
fstΣ = MkTName (MkName "fstΣ" 2) := Lam' \p -> elimSigma p \x y _ -> RHS x

sndLam : Sigma a b =>U
sndLam {b = b} = MkTName (MkName "sndΣLam" 3) := Lam' \t -> RHS (b ∙ (fstΣ ∙ t))

sndΣ : Tm (Pi (Sigma a b) sndLam)
sndΣ = MkTName (MkName "sndΣ" 4) := DLam' \p -> elimSigma p \{x y Refl -> RHS y}

proj : ∀ {ps} -> Tm (Rec rc ps => rFields rc ∙ ps)
proj = MkTName (MkName "unwrap" 5) := Lam' \t -> elimR t \t _ -> RHS t


either' : {a b c : _} -> Tm ((a => c) => (b => c) => a ⊎ b => c)
either' = MkTName (MkName "either" 6) := Lam' (λ f → Lam' (λ g → Lam' (λ e → elim⊎ e (λ t x → RHS (f ∙ t)) λ t x → RHS (g ∙ t))))

data TmNU~ where
  EtaTT : ∀ {t t'} -> TmNU~ {a = Top'} t {b = Top'} t'
  EtaBot : ∀ {t t'} -> TmNU~ {a = Bot'} t {b = Bot'} t'
  Eta× : {a : _}{a' : _} -> {t t' : Tm (a × a')} -> Tm~ (fst× ∙ t) (fst× ∙ t') -> Tm~ (snd× ∙ t) (snd× ∙ t') -> TmNU~ t t'
  Eta⊎ : {a b : _}{t t' : Tm (a ⊎ b)} -> ({c : _}(f : Tm (a => c))(g : Tm (b => c)) -> Tm~ (either' ∙ f ∙ g ∙ t ) (either' ∙ f ∙ g ∙ t')) -> TmNU~ t t'
  EtaRDC : {h : RDesc}{g : Tm (rParams h)} -> {m m' : Tm (Rec h g)} -> Tm~ (proj {h} {g} ∙ m) (proj {h} {g} ∙ m') -> TmNU~ m m'
  EtaArr : {a : _}{b : _} -> {arr arr' : TmNU (a =>' b)} -> ((x : _) -> Tm~ (arr ∙ x) (arr' ∙ x)) -> TmNU~ arr arr'
  EtaSigma : {a : _}{b : _}{b' : _}{sig : Tm (Sigma a b)}{sig' : Tm (Sigma a b')} -> (e : Tm~ (fstΣ ∙ sig) (fstΣ ∙ sig')) -> (eq : Ty~ (b ∙ (fstΣ ∙ sig)) (b' ∙ (fstΣ ∙ sig'))) -> Tm~ (sndΣ ∙∙ sig) (sndΣ ∙∙ sig') -> TmNU~ sig sig'
  EtaPi : {a : _}{b : _}{b' : _}{pi : Tm (Pi a b)}{pi' : Tm (Pi a b')} -> (Tm~ b b') -> {n : _} -> (Tm~ (pi ∙∙ var n) (pi' ∙∙ var n)) -> TmNU~ pi pi'
  EtaId : {t : _}{a b : Tm t}{id id' : Tm (Id a b)} -> TmNU~ id id' -- Use J instead?
  EtaVar : {t : TyNU}{s : _}{s' : _}{l : _} -> Spine~ s s' -> {g : Glued s l}{g' : Glued s' l} -> TmNU~ {a = t} (NeNU g) (NeNU g')
  -- ...

postulate
  coeSpine : {b b' : _} -> Ty~ b b' -> Spine (b => a) -> Spine (b' => a)

data Spine~ where
  Head : {a : Ty}{l l' : NamedLambda a} -> name l ≡ name l' -> Spine~ (Head l) (Head l')
  App : {a b b' : Ty}{s : Spine (b => a)}{s' : Spine (b' => a)}(proof : Ty~ b' b) -> Spine~ s s' -> {x : Tm b}{x' : Tm b'} -> Tm~ x x' -> Spine~ (s $ x) (s' $ x')
  DApp' : {a c : Ty}{b : Tm (c => U)}{s s' : Spine (Pi c b)} -> Spine~ s s' -> {x x' : Tm c}(eq : Tm~ x x')(proof : b ∙ x ≡ a) -> Spine~ {a = a} (DApp {a = c} {bx = a} s x proof) {a' = a} (DApp s' x' primTrustMe)

{-# TERMINATING #-}
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
reflTm~ {U} (Rec rc x) = RTC' Refl (reflTm~ x)
reflTm~ {U} (NU (NeU' {s = Head x₁} x)) = NeU' (Head Refl)
reflTm~ {U} (NU (NeU' {s = s $ x₁} x)) = NeU' (App (reflTm~ _) TODO (reflTm~ _))
reflTm~ {U} (NU (NeU' {s = DApp s x₁ x₂} x)) = NeU' TODO
reflTm~ {Top} a' = EtaTT
reflTm~ {Bot} a' = EtaBot
reflTm~ {x => x₁} a' = EtaArr (λ x₂ → reflTm~ (a' ∙ x₂))
reflTm~ {x × x₁} a' = Eta× (reflTm~ (fst× ∙ a')) (reflTm~ (snd× ∙ a'))
reflTm~ {x ⊎ x₁} a' = Eta⊎ (λ f g → reflTm~ (either' ∙ f ∙ g ∙ a'))
reflTm~ {Pi a x} a' = EtaPi (reflTm~ x) {n = MkTName (MkName "var" 1000)} (reflTm~ _) -- TODO: Less cheating
reflTm~ {Sigma a x} a' = EtaSigma (reflTm~ (fstΣ ∙ a')) (reflTm~ (x ∙ (fstΣ ∙ a'))) (reflTm~ (sndΣ ∙∙ a'))
reflTm~ {Id x x₁} a' = EtaId
reflTm~ {Rec rc x} r = EtaRDC (reflTm~ (proj ∙ r))
reflTm~ {NeU x} (NeNU {s = s} {l = Stuck x₂} x₁) = TODO

subst≡ : {A : Set}(@0 P : (a : A) -> Set){a a' : A} -> (@0 eq : a ≡ a') -> P a -> P a'
subst≡ _ Refl x = x

{-
injTm : {t t' : Ty} -> Tm t ≈ Tm t' -> t ≈ t'
injTm x = {!  !}
-}

postulate
  funExt : {A : Set}{B : A -> Set}{f g : (a : A) -> B a} -> ((x : A) -> f x ≡ g x) -> f ≡ g
  inj∙ : {a b : _}(b b' : Tm (a => b)) -> _∙_ b ≡ _∙_ b' -> b ≡ b'

  Ty~Toeq : {t t' : Ty} -> Ty~ t t' -> t ≡ t'
{-
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
Ty~Toeq (Id' x x₁) = {!  !}
Ty~Toeq (RTC' eq {p} {p'} x) with setEq eq
... | Refl = {!  !}
Ty~Toeq (Either' x x₁) with Ty~Toeq x | Ty~Toeq x₁
... | Refl | Refl = Refl
Ty~Toeq Bot' = Refl
Ty~Toeq (NeU' k) = {!  !}
-}
{-
symTm~ {U} {U} {U} {U} x = x
symTm~ {U} {U} {Bot} {Bot} x = x
symTm~ {U} {U} {NeU y} {NeU z} (NeU' k) = NeU' {!  !}
symTm~ {U} {U} {Top} {Top} x = x
symTm~ {U} {U} {x₁ => x₃} {x₂ => x₄} (Arr x x₅) = Arr (symTm~ x) (symTm~ x₅)
symTm~ {U} {U} {x₁ × x₃} {x₂ × x₄} (Tuple x x₅) = Tuple (symTm~ x) (symTm~ x₅)
symTm~ {U} {U} {Pi a x₁} {Pi a₁ x₂} (Pi' x x₃) = Pi' (symTm~ x) (symTm~ x₃)
symTm~ {U} {U} {Sigma a x₁} {Sigma a₁ x₂} (Sigma' x x₃) = Sigma' (symTm~ x) (symTm~ x₃)
symTm~ {U} {U} {Id x₁ x₃} {Id x₂ x₄} (Id' x x₅) = Id' (symTm~ x) (symTm~ x₅)
symTm~ {U} {U} {_ ⊎ _} {_ ⊎ _} (Either' y y₁) = Either' (symTm~ y) (symTm~ y₁)
--symTm~ {U} {U} {RTC rc x₁} {RTC rc₁ x₂} (RTC' eq x) with setEq eq
--... | Refl = RTC' eq (symTm~ x)
symTm~ {Top} {Top} {a} {b} EtaTT = EtaTT
symTm~ {_ => _} {_ => _} {a} {b} (EtaArr x) = EtaArr (λ x₃ → symTm~ (x x₃))
symTm~ {_ × _} {_ × _} {a} {b} (Eta× x x₁) = Eta× (symTm~ x) (symTm~ x₁)
symTm~ {Pi _ _} {Pi _ _} {a} {b} (EtaPi f x) = EtaPi (symTm~ f) (symTm~ x)
symTm~ {Sigma _ _} {Sigma _ _} {a} {b} (EtaSigma e eq x) = EtaSigma (symTm~ e) (symTm~ eq) (symTm~ x)
symTm~ {Id _ _} {Id _ _} {a} {b} EtaId = EtaId
--symTm~ {RTC _ _} {RTC _ _} {a} {b} (EtaRDC x) = EtaRDC (symTm~ x)
symTm~ {Bot} {Bot} {a} {b} EtaBot = EtaBot
symTm~ {x ⊎ x₁} {x₂ ⊎ x₃} (Eta⊎ x₄) = Eta⊎ (λ f g → symTm~ (x₄ f g))
-}
{-
coeTm {U} U x₁ = x₁
coeTm {Top} Top' x₁ = x₁
coeTm {Bot} Bot' y = y
coeTm {x₂ => x₃} (Arr x x₄) l = {!  !} --lam "" λ x₁ → coeTm x₄ (l ∙ (coeTm (symTm~ x) x₁))
coeTm {x₂ × x₃} (Tuple x x₄) y = coeTm x (fst× ∙ y ) , coeTm x₄ (snd× ∙ y)
coeTm {Pi a x₂} (Pi' {b' = b'} x (EtaArr f)) x₁ = NeNU (CHead (named {!  !} (DLam (λ i → RHS (coeM {b = x₂} {b' = b'} {a = i} (EtaArr f) (x₁ ∙∙ i))))))
coeTm {Sigma a x₂} (Sigma' {b' = b'} x (EtaArr f)) x₁ = fstΣ ∙ x₁ ,, coeM {_} {x₂} {b'} {fstΣ ∙ x₁} (EtaArr f) (sndΣ ∙∙ x₁)
coeTm {Id x₂ x₃} (Id' x x₄) r with elimId r (λ {x₁ → RHS {! subst~ ? x₁ (eqt x₁) ?  !}})
... | RHS x₁ = x₁
... | NoRHS (Stuck x₁) = {!  !}
coeTm {a ⊎ b} (Either' y y₁) z = {!  !} --either' ∙ lam "f" (λ x → Left (coeTm y x)) ∙ lam "g" (λ x → Right (coeTm y₁ x)) ∙ z
--coeTm {RTC rc x₂} (RTC' eq x) y with setEq eq
--... | Refl = RDC (coeApp {b = rc .unnamed .UnnamedRDesc.rFields} _ _ x (proj ∙ y))
coeTm {NeU _} (NeU' k) x = {! x !}
-}
postulate decString : (str str' : String) -> Dec' (str ≡ str')

{-# TERMINATING #-}
convTy  : Nat -> (a a' : Ty) -> TC (Emb (Ty~ a a'))
convTmNU : ∀ {a a'} -> Nat -> (t : TmNU a)(t' : TmNU a') -> TC (Emb (TmNU~ t t'))
convTm  : Nat -> (t : Tm  a)(t' : Tm a') -> TC (Emb (Tm~ t t'))
convSpine : Nat -> (s : Spine a)(s' : Spine a) -> TC (Emb (Spine~ s s'))

convTy x U U = pure (emb U)
convTy i Top Top = pure (emb Top')
convTy i (a => b) (a' => b') = do
  (emb j) <- convTy i a a'
  (emb k) <- convTy i b b'
  pure (emb (Arr j k))
convTy i (a × b) (a' × b') = do
  (emb j) <- convTy i a a'
  (emb k) <- convTy i b b'
  pure (emb (Tuple j k))
convTy i (a ⊎ b) (a' ⊎ b') = do
  (emb j) <- convTy i a a'
  (emb k) <- convTy i b b'
  pure (emb (Either' j k))
convTy i (Pi a x) (Pi a' x') = do
  (emb j) <- convTy i a a'
  (emb k) <- convTm i x x'
  pure (emb (Pi' j k))
convTy i (Sigma a x) (Sigma a' x') = do
  (emb j) <- convTy i a a'
  (emb k) <- convTm i x x'
  pure (emb (Sigma' j k))
convTy i (Id x x₁) (Id x₂ x₃) = do
  j <- convTm i x x₂
  k <- convTm i x₁ x₃
  pure (emb TODO)
convTy i (Rec rc x) (Rec rc₁ x₁) = do
  Yes Refl <- pure (decNamed rc rc₁ ) where
    No -> throwError "convTy: Unable to convert record"
  (emb m) <- convTm i x x₁
  pure (emb (RTC' Refl m))
convTy i (NU (NeU' {s = s} x)) (NU (NeU' {s = s'} y)) = do
  m <- convSpine i s s'
  pure (emb TODO)
convTy _ _ _ = throwError "convTy: No conversion rule for type"

convTmNU {a = Top'} {a' = Top'} i t t' = pure (emb EtaTT)
convTmNU {a = Bot'} {a' = Bot'} i t t' = pure (emb EtaBot)
convTmNU {a = x =>' x₁} {a' = x' =>' x₁'} i t t' = pure (emb TODO)
convTmNU {a = x ×' x₁} {a' = x' ×' x₁'} i t t' = throwError "convTmNU2"
convTmNU {a = x ⊎' x₁} {a' = x' ⊎' x₁'} i t t' = throwError "convTmNU3"
convTmNU {a = Pi' a x} {a' = Pi' a' x'} i t t' = throwError "convTmNU4"
convTmNU {a = Sigma' a x} {a' = Sigma' a' x'} i t t' = throwError "convTmNU4"
convTmNU {a = Id' x x₁} {a' = Id' x' x₁'} i t t' = throwError "convTmNU5"
convTmNU {a = Rec' rc x} {a' = Rec' rc' x'} i t t' = throwError "convTmNU6"
convTmNU {a = NeU' {s = s} x} {a' = NeU' {s = s'} x'} i t t' = do
  (emb m) <- convSpine 0 s s'
--  _ <- pure {!  !}
  throwError "convTmNU7"
convTmNU {a = _} {a' = _} _ _ _ = throwError "convTmNU: Unable to convert terms"

{-
convertSpine (s $$ x) (s' $$ x') = do
  Refl <- convertSpine s s'
  Refl <- convert x x'
  pure Refl
-}

-- Is this a lie?
postulate Ty~2eq : Ty~ a a' -> a ≡ a'

convSpine x (Head l) (Head l') = do
  Yes Refl <- pure (decNamed l l') where
    No -> throwError "convSpine1"
  pure (emb (Head Refl))
convSpine i (_$_ {a = a} {a' = a'} s  x) (_$_ {a = b} {a' = b'} s' x') = do
  (emb ty) <- convTm i b a
  Refl <- pure (Ty~2eq ty)
  (emb c) <- convSpine i s s'
  (emb t) <- convTm i x x'
  pure (emb (App ty c t))
convSpine x (DApp {a = a} {b = b} s x₁ Refl) (DApp {a = a'} {b = b'} s' x₃ x₄) = do
  (emb ty) <- convTm x a a'
  Refl <- pure (Ty~2eq ty)
  pure (emb TODO)
convSpine x _ _ = throwError "convSpine"

convTm {a = U} {a' = U} i t t' = convTy i t t'
convTm {a = NU _} {a' = NU _} i t t' = convTmNU i t t'
convTm {a = _} {a' = _} _ _ _ = throwError "convTm : Can not convert inhomogen terms"

-------------------------------------

headCharClass : List Char -> CharClass
headCharClass (c :: _) = charClass c
headCharClass _ = InvalidChar

isAlphaToken : String -> Bool
isAlphaToken s with headCharClass (stringToList s)
... | Alpha = True
... | _     = False

operators : List String
operators = ";" :: "=" :: "." :: ":" :: "," :: "->" :: "==" :: "+" :: "*" :: []

isOperator : String -> Bool
isOperator s = any (eqString s) operators

keywords : List String
keywords
  =  "ret" :: "fix" :: "U" :: "?"
-- type       constructor            eliminator  
---------------------------------------------------
  {- _->_ -}  {- _._ -}              {- _ _ -}
  :: "Pi"     {- _._ -}              {- _ _ -}
  {- _*_  -}  {- _,_ -}              :: "pair"
  :: "Sigma"  {- _,_ -}              :: "sigma"
  {- _+_  -}  :: "Left" :: "Right"   :: "either"
  :: "Top"    :: "TT"                {- --- -}
  :: "Bot"    {- --- -}              :: "absurd"
  {- _==_ -}  :: "Refl"              :: "jRule" :: "kRule"
  :: "record" :: "Wrap"              :: "unwrap"
  :: []

isKeyword : String -> Bool
isKeyword s = any (eqString s) keywords

isVariable : String -> Bool
isVariable s = isAlphaToken s && not (isKeyword s)

data Doc : Set where
  _$_   : Doc -> Doc ->                                          Doc
  KW'   : (s : String) -> {isKeyword s ≡ True} -> List Doc ->    Doc
  DVar' : (s : String) -> {isVariable s ≡ True} ->               Doc
  BinOp : Doc -> (s : String) -> {isOperator s ≡ True} -> Doc -> Doc

pattern KW s = KW' s {Refl} []
pattern _[_]_ a b c = BinOp a b {Refl} c
pattern DVar s = DVar' s {Refl}

-------------------------------------

infixl 9 _$D_

_$D_ : Doc -> Doc -> Doc
KW' s {isKW} ds $D d = KW' s {isKW} (d :: ds)
a $D b = a $ b

{-# TERMINATING #-}
parse : String -> TC Doc
parse s = tokens' s >>= parseOps end  where

  X = List String -> TC Doc

  end : Doc -> X
  end d [] = pure d
  end d ts  = throwError ("End expected instead of  " ++ showTokens ts)

  expect : String -> X -> X
  expect t r (t' :: ts) with eqString t' t
  ... | True  = r ts
  ... | False = throwError (t ++ " expected instead of " ++ showTokens (t' :: ts))
  expect t _ [] = throwError (t ++ " expected instead of end")

  parseOps : (Doc -> X) -> X

  parseAtom : (Doc -> X) -> X -> X
  parseAtom r _ ("(" :: ts) = parseOps (\b -> expect ")" (r b)) ts
  parseAtom r z (t :: ts) with isKeyword t
  ... | True  = r (KW' t {primTrustMe} []) ts
  ... | False with isAlphaToken t
  ...   | True  = r (DVar' t {primTrustMe}) ts
  ...   | False = z (t :: ts)
  parseAtom _ z ts = z ts

  parseApps : (Doc -> X) -> X
  parseApps r = parseAtom (f r) \ts -> throwError ("unknown token at  " ++ showTokens ts)  where

    f : (Doc -> X) -> Doc -> X
    f r a ts = parseAtom (\b -> f r (a $D b)) (r a) ts

  mkPi : Doc -> Doc -> Doc -> Doc
  mkPi (ns $ n) a b = mkPi ns a (KW "Pi" $D a $D (n [ "." ] b))
  mkPi n a b = KW "Pi" $D a $D (n [ "." ] b)

  mkSigma : Doc -> Doc -> Doc -> Doc
  mkSigma (ns $ n) a b = mkPi ns a (KW "Sigma" $D a $D (n [ "." ] b))
  mkSigma n a b = KW "Sigma" $D a $D (n [ "." ] b)

  mkOp : (s : String) -> {isOperator s ≡ True} -> Doc -> Doc -> Doc
  mkOp "->" (bs $ (n [ ":" ] a)) b = mkOp "->" {Refl} bs (mkPi n a b)
  mkOp "->" (n [ ":" ] a) b = mkPi n a b
  mkOp "*" (bs $ (n [ ":" ] a)) b = mkOp "*" {Refl} bs (mkSigma n a b)
  mkOp "*" (n [ ":" ] a) b = mkSigma n a b
  mkOp "." (ns $ n) b = mkOp "." {Refl} ns (n [ "." ] b)
  mkOp t {isOp} a b = BinOp a t {isOp} b

  addOp : (String ** \s -> isOperator s ≡ True) -> ((Doc -> X) -> X) -> (Doc -> X) -> X
  addOp op@(t ,, isOp) g r = g (f r) where

    f : (Doc -> X) -> Doc -> X
    f r a (t' :: ts) with eqString t' t
    ... | True  = addOp op g (\b -> r (mkOp t {isOp} a b)) ts
    ... | False = r a (t' :: ts)
    f r a ts = r a ts

  parseOps = foldr addOp parseApps (map (\s -> s ,, primTrustMe) operators)

testParse : runTC (parse "f (b a * c * e) d")
          ≡ Right (DVar "f" $ (DVar "b" $ DVar "a" [ "*" ] DVar "c" [ "*" ] DVar "e") $ DVar "d")
testParse = Refl

-------------------------------------

{-# TERMINATING #-}
showDoc : Doc -> String
showDoc = go 0  where

  parens : Bool -> String -> String
  parens True  a = "(" ++ a ++ ")"
  parens False a =        a

  addOp : String -> (String -> Nat) -> String -> Nat
  addOp t r s with eqString s t
  ... | True  = 0
  ... | False = Suc (r s)

  prec : String -> Nat
  prec = foldr addOp (\_ -> 0) operators

  go : Nat -> Doc -> String
  go p (KW' n args) = go p (foldr (\a b -> b $ a) (DVar' n {primTrustMe}) args)
  go p (DVar' n)    = n
  go p (a $ b)     = parens (q < p) (go q a ++ " " ++ go (Suc q) b) where
    q = 100
  go p (BinOp a s b) = parens (q < p) (go (Suc q) a ++ " " ++ s ++ " " ++ go q b) where
    q = prec s

testShowDoc : showDoc ((DVar "a" [ "." ] DVar "a" $ DVar "b") $ (DVar "c" $ DVar "e") $ DVar "d" $ (DVar "a" [ "." ] DVar "b" [ "." ] DVar "a"))
        ≈ "(a . a b) (c e) d (a . b . a)"
testShowDoc = Refl

testShowDoc' : showDoc ((DVar "a" [ "*" ] DVar "a" $ DVar "b" [ "*" ] DVar "b") $ DVar "d" [ "*" ] DVar "f" $ (DVar "c" [ "*" ] DVar "e"))
        ≈ "(a * a b * b) d * f (c * e)"
testShowDoc' = Refl

-------------------------------------

newNameD : Doc -> TC Name
newNameD (DVar' n) = newName n
newNameD d = throwError ("variable name expected instead of: " ++ showDoc d)

newTName : Doc -> TC (TName a)
newTName d = do
  n <- newNameD d
  pure (MkTName n)

declareVar : TName a -> TC A -> TC A
declareVar {a = a} n = addLocal (tName n) a

_>>>_ : (ts : Tys) -> TName a -> Tys
_>>>_ {a = a} ts n = ts >> tName n :: ⟦ a ⟧ᵤ

------------------------

empty : List Doc -> TC T
empty [] = pure tt
empty args = throwError "too much arguments"

getArg : List Doc -> TC (Pair Doc (List Doc))
getArg (d :: ds) = pure (d , ds)
getArg [] = throwError "not enough arguments"

firstArg : List Doc -> TC Doc
firstArg ds = do
  d , ds <- getArg ds
  _ <- empty ds
  pure d

------------------------

pattern SLam n d = DVar' "λ" $ DVar' n $ d

printName : Name -> Doc
printName n = DVar' (pr (nameStr n)) {primTrustMe {- TODO -}}  where
  pr : String -> String
  pr "lam" = "lam" ++ showNat (nameId n)
  pr "v"   = "v"   ++ showNat (nameId n)
  pr n     = n

printTm'    : Nat -> Tm a -> Doc
printSpine' : Nat -> Spine a -> Doc

printSpine' _ (Head x) = printName (name x)
printSpine' n (s $  x) = printSpine' n s $ printTm' n x
printSpine' n (s $$ x) = printSpine' n s $ printTm' n x

{-# TERMINATING #-}
printTm' {a = U} n U           = KW "U"
printTm' {a = U} n Top         = KW "Top"
printTm' {a = U} n Bot         = KW "Bot"
printTm' {a = U} n (a => a')   = printTm' n a [ "->" ] printTm' n a'
printTm' {a = U} n (a × a')    = printTm' n a [ "*"  ] printTm' n a'
printTm' {a = U} n (a ⊎ a')    = printTm' n a [ "+"  ] printTm' n a'
printTm' {a = U} n (Pi a b)    = KW "Pi"      $D printTm' n a $D printTm' n b
printTm' {a = U} n (Sigma a b) = KW "Sigma"   $D printTm' n a $D printTm' n b
printTm' {a = U} n (Id x y)    = printTm' n x [ "=="  ] printTm' n y
printTm' {a = U} n (Rec rc x)  = printName (name rc) $ printTm' n x
printTm' {a = U} n (NU (NeU' {s = s} _)) = printSpine' n s
printTm' {a = NU (a =>' a')} n f = let sv = "v" ++ showNat n in DVar' "λ" {primTrustMe} $ DVar' sv {primTrustMe}  $ (printTm' {a = a'} (Suc n) (f ∙ var (MkTName (MkName sv n))))
printTm' {a = NU _} n TT        = KW "TT"
printTm' {a = NU _} n (x ,  y)  = printTm' n x [ ","  ] printTm' n y
printTm' {a = NU _} n (x ,, y)  = printTm' n x [ ","  ] printTm' n y
printTm' {a = NU _} n (Left  x) = KW "Left"  $D printTm' n x
printTm' {a = NU _} n (Right x) = KW "Right" $D printTm' n x
printTm' {a = NU _} n Refl      = KW "Refl"
printTm' {a = NU _} n (Wrap {rc = rc} args) = KW "Wrap" $D printTm' n args
printTm' {a = NU _} n (NeNU {s = s} _) = printSpine' n s

printTm : Tm a -> Doc
printTm a = printTm' Zero a

showTm : Tm a -> String
showTm t = showDoc (printTm t)

--------------------

showLocals : LCtx -> String
showLocals [] = ""
showLocals ((n , a) :: ls) = showLocals ls ++ "\n" ++ showDoc (printName n [ ":" ] printTm a)

----------------

vars : (ts : Tys) -> Tms ts
vars []             = tt
vars (ts >> n :: t) = vars ts ,, var (MkTName n)

postulate
  ⟦⟧vars : ⟦ a ⟧ᵤ (vars ts) ≈ a

-- TODO!
lamm : (Tm a -> Tm U) -> a =>U
lamm f = MkTName (MkName "lamm" 9) := Lam' \x -> RHS (f x)

upTy : (ts : Tys) -> CTy ts -> Ty
upTy []             a = a tt
upTy (ts >> n :: t) a = upTy ts \xs -> Pi (t xs) (lamm \x -> a (xs ,, x))

up : ∀ ts -> {t : CTy ts} -> ((xs : Tms ts) -> LHS (t xs)) -> LHS (upTy ts t)
up [] l = l tt
up (ts >> n :: t) l = up ts \xs -> DLam' \x -> l (xs ,, x)

down : (ts : Tys) -> {t : CTy ts} -> Tm (upTy ts t) -> Tm (t (vars ts))
down []             x = x
down (ts >> n :: f) x = down ts x ∙∙ var (MkTName n)

mkLam : Name -> Tys -> TName a -> Tm a' -> Tm (a => a')
mkLam {a = a} {a' = a'} ln ts n e
  = subst Tm (⟦⟧vars {a = a => a'} {ts = ts}) (
      down ts {t = ⟦ a => a' ⟧ᵤ} (
        MkTName ln := up ts \xs -> Lam' \x -> RHS (subst Tm (strengthen a') (e' (xs ,, x)))
      )
    )
 where
  e' : CTm (ts >>> n) ⟦ a' ⟧ᵤ
  e' = ⟦_⟧ {ts = ts >>> n} e

mkDLam : Name -> Tys -> (n : TName a) -> Tm (b ∙ var n) -> Tm (Pi a b)
mkDLam {a = a} {b = b} ln ts n e
  = subst Tm (⟦⟧vars {a = Pi a b} {ts = ts}) (
      down ts {t = ⟦ Pi a b ⟧ᵤ} (
        MkTName ln := up ts \xs -> DLam' \x -> RHS (subst Tm (b∙var⟦⟧ᵤ b) (e' (xs ,, x)))
      )
    )
 where
  e' : CTm (ts >>> n) ⟦ b ∙ var n ⟧ᵤ
  e' = ⟦ e ⟧

ctxToTys : NameMap Ty -> Tys
ctxToTys [] = []
ctxToTys ((n , a) :: ctx) = ctxToTys ctx >> n :: ⟦ a ⟧ᵤ

printGoal : List Doc -> Ty -> TC A
printGoal ds a = do
  _ <- empty ds
  ls <- locals
  throwError (showLocals ls ++ "\n----------------\n" ++ "? : " ++ showTm a)

fixTm : Tm ((a => a) => a)
fixTm = MkTName (MkName "fix" 15) := NoRHS (Lam (λ f → RHS (fix (λ tm → f ∙ tm))))

infer : Doc -> TC TyTm
{-# TERMINATING #-}
check : Doc -> (a : Ty) -> TC (Tm a)
check (KW' "U" ds) U = do
  _ <- empty ds
  pure U
check (KW' "Bot" ds) U = do
  _ <- empty ds
  pure Bot
check (KW' "Top" ds) U = do
  _ <- empty ds
  pure Top
check (a [ "*" ] a') U = do
  a  <- check a  U
  a' <- check a' U
  pure (a × a')
check (a [ "+" ] a') U = do
  a  <- check a  U
  a' <- check a' U
  pure (a ⊎ a')
check (a [ "->" ] a') U = do
  a  <- check a  U
  a' <- check a' U
  pure (a => a')
check (KW' "Pi" ds) U = do
  b , ds <- getArg ds
  a <- firstArg ds
  a <- check a U
  b <- check b (a => U)
  pure (Pi a b)
check (KW' "Sigma" ds) U = do
  b , ds <- getArg ds
  a <- firstArg ds
  a <- check a U
  b <- check b (a => U)
  pure (Sigma a b)
check (x [ "==" ] y) U = do
  a ,, x <- infer x
  y <- check y a
  pure (Id x y)
check (KW' "TT" ds) Top = do
  _ <- empty ds
  pure TT
check (x [ "," ] x') (a × a') = do
  x  <- check x  a
  x' <- check x' a'
  pure (x , x')
check (KW' "Left" ds) (a ⊎ a') = do
  x <- firstArg ds
  x  <- check x a
  pure (Left x)
check (KW' "Right" ds) (a ⊎ a') = do
  x <- firstArg ds
  x  <- check x a'
  pure (Right x)
check (sn [ "." ] e) (a => a') = do
  n <- newTName {a = a} sn
  e <- declareVar n (check e a')
  ln <- newName "lam"
  ctx <- locals
  pure (mkLam ln (ctxToTys ctx) n e)
check (sn [ "." ] e) (Pi a b)  = do
  n <- newTName sn
  e <- declareVar n (check e (b ∙ var n))
  ln <- newName "lam"
  ctx <- locals
  pure (mkDLam ln (ctxToTys ctx) n e)
check (x [ "," ] y) (Sigma a b) = do
  x <- check x  a
  y <- check y (b ∙ x)
  pure (x ,, y)

check (KW' "Refl" ds) (Id x y) = do
  _ <- empty ds
  (emb e) <- convTm 0 x y
  pure (substTm (λ k → Tm (Id x k)) e Refl)

check (KW' "Wrap" ds) (Rec rc ps) = do
  x <- firstArg ds
  x <- check x (rFields rc ∙ ps)
  pure (Wrap x)
check (KW' "?" ds) a = printGoal ds a
--check d@(KW' _ _) a = throwError (showDoc d ++ " :? " ++ showTm a)
--check d@(BinOp _ _ _) a = throwError (showDoc d ++ " :? " ++ showTm a)
check d a = do
  a' ,, t <- infer d
  (emb k) <- convTm 0 a' a
  Refl <- pure (Ty~2eq k)
  pure t


infer (KW' "fix" ds) = do
  f , ds <- getArg ds
  a <- firstArg ds
  a <- check a U
  f <- check f (a => a)
  pure (a ,, fixTm ∙ f)
infer (f $ x) = infer f >>= matchPi  where
  matchPi : TyTm -> TC TyTm
  matchPi (a => a' ,, f) = do
    x <- check x a
    pure (a' ,, f ∙ x)
  matchPi (Pi a b ,, f) = do
    x <- check x a
    pure (b ∙ x ,, f ∙∙ x)
  matchPi (t ,, _) = throwError ("matchPi: " ++ showTm t)
infer (DVar' n) = lookupTm n
infer d = throwError ("infer: " ++ showDoc d)


--       U  -> U
-- \(A : U) -> A -> A -> U
jPTy2T : Tm (U => U)
jPTy2T = MkTName (MkName "jLam" 10) := Lam' \a -> RHS (a => a => U)

-- Pi U \(A : U) -> A -> A -> U
--  (A : U) ->   A  ->   A  -> U
-- \(A : U) (x : A) (y : A) -> Id x y -> U
jPTy2 : Tm (Pi U jPTy2T)
jPTy2 = MkTName (MkName "jLam" 11) := DLam' \a -> Lam' \x -> Lam' \y -> RHS (Id x y => U)

--       U  -> U
-- \(A : U) -> A -> U
jPTyT : Tm (U => U)
jPTyT = MkTName (MkName "jLam" 12) := Lam' \a -> RHS (a => U)

-- Pi U \(A : U) -> A -> U
--  (A : U) ->   A  -> U
-- \(A : U) (x : A) -> (y : A) -> Id x y -> U
jPTy : Tm (Pi U jPTyT)
jPTy = MkTName (MkName "jLam" 13) := DLam' \a -> Lam' \x -> RHS (Pi a (jPTy2 ∙∙ a ∙ x))

kPTyT = jPTyT

-- Pi U \(A : U) -> A -> U
--  (A : U) ->   A  -> U
-- \(A : U) (x : A) -> Id x x -> Ty
kPTy : Tm (Pi U kPTyT)
kPTy = MkTName (MkName "kLam" 14) := DLam' \a -> Lam' \x -> RHS (Id x x => U)

-- first order representation of LHS
-- TODO: add Ctx index
data FLHS : Ty -> Set where
  RHS         : Tm a ->                                   FLHS a
  Lam         : (n : TName a) -> FLHS a' ->               FLHS (a => a')
  DLam        : (n : TName a) -> FLHS (b ∙ var n) ->      FLHS (Pi a b)
  MatchPair   : (p : Tm (a × a'))    (n : TName a) (m : TName a')          -> TName (Id (var n ,  var m) p) -> FLHS a'' -> FLHS a''
  MatchSigma  : (p : Tm (Sigma a b)) (n : TName a) (m : TName (b ∙ var n)) -> TName (Id (var n ,, var m) p) -> FLHS a'' -> FLHS a''
  MatchEither : (p : Tm (a ⊎ a')) (n  : TName a ) -> TName (Id (Left  (var n )) p) -> FLHS a'' ->
                                  (n' : TName a') -> TName (Id (Right (var n')) p) -> FLHS a'' -> FLHS a''
  MatchRecord : ∀ {ps a} (p : Tm (Rec rc ps)) (n : TName (rFields rc ∙ ps)) -> TName (Id (Wrap (var n)) p) -> FLHS a -> FLHS a
  MatchBot    : Tm Bot -> FLHS a
  MatchJ      : ∀ {x y : Tm a} (tm : Tm (Id x y)) (P : Tm (jPTy ∙∙ a ∙ x)) -> FLHS (P ∙∙ x ∙ Refl) -> FLHS (P ∙∙ y ∙ tm)
  MatchK      : ∀ {x   : Tm a} (tm : Tm (Id x x)) (P : Tm (kPTy ∙∙ a ∙ x)) -> FLHS (P      ∙ Refl) -> FLHS (P      ∙ tm)

newTName' : Doc -> TC (Pair (TName a) Doc)
newTName' (n [ "." ] d) = do
  n <- newTName n
  pure (n , d)
newTName' d = throwError ("lambda expected instead of: " ++ showDoc d)

{-# TERMINATING #-}
checkLHS : Doc -> (a : Ty) -> TC (FLHS a)
checkLHS (KW' "ret" ds) a = do
  d <- firstArg ds
  t <- check d a
  pure (RHS t)
checkLHS (n [ "." ] t) (a => a') = do
  n <- newTName n
  t <- declareVar n (checkLHS t a')
  pure (Lam n t)
checkLHS (n [ "." ] t) (Pi a b) = do
  n <- newTName n
  t <- declareVar n (checkLHS t (b ∙ var n))
  pure (DLam n t)
checkLHS (KW' "pair" ds) a'' = do
  e , ds <- getArg ds
  p <- firstArg ds
  _ × _ ,, p <- infer p where
    r ,, _ -> throwError ("pair: " ++ showTm r)
  n   , e <- newTName' e
  n'  , e <- newTName' e
  n'' , e <- newTName' e
  e <- declareVar n (declareVar n' (declareVar n'' (checkLHS e a'')))
  pure (MatchPair p n n' n'' e)
checkLHS (KW' "sigma" ds) a'' = do
  e , ds <- getArg ds
  p <- firstArg ds
  Sigma _ _ ,, p <- infer p where
    r ,, _ -> throwError ("sigma: " ++ showTm r)
  n   , e <- newTName' e
  n'  , e <- newTName' e
  n'' , e <- newTName' e
  e <- declareVar n (declareVar n' (declareVar n'' (checkLHS e a'')))
  pure (MatchSigma p n n' n'' e)
checkLHS (KW' "either" ds) a'' = do
  e' , ds <- getArg ds
  e , ds <- getArg ds
  p <- firstArg ds
  _ ⊎ _ ,, p <- infer p where
    r ,, _ -> throwError ("either: " ++ showTm r)
  n , e <- newTName' e
  k , e <- newTName' e
  e <- declareVar n (declareVar k (checkLHS e a''))
  n' , e' <- newTName' e'
  k' , e' <- newTName' e'
  e' <- declareVar n' (declareVar k' (checkLHS e' a''))
  pure (MatchEither p n k e n' k' e')
checkLHS (KW' "unwrap" ds) a'' = do
  e , ds <- getArg ds
  p <- firstArg ds
  Rec rc ps ,, p <- infer p where  
    r ,, _ -> throwError ("unwrap: " ++ showTm r)
  n , e <- newTName' e
  k , e <- newTName' e
  e  <- declareVar n (declareVar k (checkLHS e a''))
  pure (MatchRecord p n k e)
checkLHS (KW' "absurd" ds) a'' = do
  p <- firstArg ds
  Bot ,, p <- infer p where
    r ,, _ -> throwError ("absurd: " ++ showTm r)
  pure (MatchBot p)
{-
checkLHS (KW' "jRule" ds) a'' = do
  w , ds <- getArg ds
  P , ds <- getArg ds
  e      <- firstArg ds
  NU (Id' {a = a} x y) ,, e <- infer e  where
    r ,, _ -> throwError ("jRule: " ++ showTm r)
  P <- check P (jPTy ∙∙ a ∙ x)
  Refl <- convert a'' (P ∙∙ y ∙ e)
  w <- checkLHS w (P ∙∙ x ∙ Refl)
  pure (MatchJ e P w)
-}
{-
checkLHS (KW' "kRule" ds) a'' = do
  w , ds <- getArg ds
  P , ds <- getArg ds
  e      <- firstArg ds
  NU (Id' {a = a} x y) ,, e <- infer e  where
    r ,, _ -> throwError ("jRule: " ++ showTm r)
  Refl <- convert x y
  P <- check P (kPTy ∙∙ a ∙ x)
  Refl <- convert a'' (P ∙ e)
  w <- checkLHS w (P ∙ Refl)
  pure (MatchK e P w)
-}
checkLHS (KW' "?" ds) a = printGoal ds a
checkLHS d a = throwError ("checkLHS: " ++ showDoc d)


CLHS : (ts : Tys) -> CTy ts -> Set
CLHS ts t = (xs : Tms ts) -> LHS (t xs)

quoteLHS : {a : Ty} -> FLHS a -> (ts : Tys) -> CLHS ts ⟦ a ⟧ᵤ
quoteLHS (Lam {a' = a'} n t) ts = \xs -> Lam' \x -> subst LHS (strengthen a') (t' (xs ,, x))
 where
  t' = quoteLHS t (ts >>> n)
quoteLHS (DLam {b = b} n t) ts = \xs -> DLam' \x -> subst LHS (b∙var⟦⟧ᵤ b) (t' (xs ,, x))
 where
  t' = quoteLHS t (ts >>> n)
quoteLHS (MatchPair {a = a} {a' = a2} {a'' = a''} p n n' n'' e) ts
  = \xs -> elim× (p' xs) \{x x' ee ->
       subst LHS (strengthen a'' ∘ strengthen a'' ∘ strengthen a'') (t' (((xs ,, x) ,, x') ,, objEq ee))
     }
 where
  p'  = ⟦ p ⟧
  a2' = ⟦ a2 ⟧
  t'  = quoteLHS e (ts >>> n >> tName n' :: (\(xs' ,, _) -> a2' xs') >> tName n'' :: (\((xs' ,, y) ,, y') -> Id (y , y') (p' xs')))

quoteLHS (MatchSigma {a = a} {b = b} {a'' = a''} p n n' n'' e) ts
  = \xs -> elimSigma (p' xs) \{x x' ee ->
       subst LHS (strengthen a'' ∘ strengthen a'' ∘ strengthen a'') (t' (((xs ,, x) ,, x') ,, objEq ee))
     }
 where
  p' = ⟦ p ⟧
  t' = quoteLHS e (ts >>> n >> tName n' :: (\(xs' ,, y) -> ⟦ b ⟧ xs' ∙ y) >> tName n'' :: (\((xs' ,, y) ,, y') -> Id (y ,, y') (p' xs')))
quoteLHS (MatchEither {a = a} {a' = a'} {a'' = a''} p n k e n' k' e') ts
  = \xs -> elim⊎ (p' xs)
     (\x ee -> subst LHS (strengthen a'' ∘ strengthen a'') (t1 ((xs ,, x) ,, objEq ee)))
     (\x ee -> subst LHS (strengthen a'' ∘ strengthen a'') (t2 ((xs ,, x) ,, objEq ee)))
 where
  p' = ⟦ p ⟧
  t1 = quoteLHS e  (ts >>> n  >> tName k  :: (\(xs' ,, y) -> Id (Left  y) (p' xs')))
  t2 = quoteLHS e' (ts >>> n' >> tName k' :: (\(xs' ,, y) -> Id (Right y) (p' xs')))
quoteLHS (MatchRecord {rc = rc} {ps = ps} {a = a} p n k e) ts
  = \xs -> elimR {rc = rc} (p' xs) \x ee ->
       subst LHS (strengthen a ∘ strengthen a) (t' ((xs ,, subst Tm (sym (rFieldsClosed rc)) x) ,, objEq (subst (\k -> Wrap k ≡ p' xs) TODO ee)))
 where
  p' = ⟦ p ⟧
  t' = quoteLHS e (ts >>> n >> tName k :: (\(xs' ,, y) -> Id (Wrap (subst Tm (rFieldsClosed rc) y)) (p' xs')))
quoteLHS (MatchBot p) ts
  = \xs -> elimBot p
quoteLHS (MatchJ tm p lhs) ts
  = \xs -> subst LHS TODO (jRule (tm' xs) (\y e -> p' xs ∙∙ y ∙ e) (subst LHS TODO (lhs' xs)))
 where
  p'   = ⟦ p ⟧
  tm'  = ⟦ tm ⟧
  lhs' = quoteLHS lhs ts
quoteLHS (MatchK tm p lhs) ts
  = \xs -> subst LHS TODO (kRule (tm' xs) (\e -> p' xs ∙ e) (subst LHS TODO (lhs' xs)))
 where
  p'   = ⟦ p ⟧
  tm'  = ⟦ tm ⟧
  lhs' = quoteLHS lhs ts
quoteLHS (RHS t) _ = \xs -> RHS (t' xs)
 where
  t' = ⟦ t ⟧

quoteFLHS : FLHS a -> LHS a
quoteFLHS t = subst LHS ⟦⟧ᵤ[] (quoteLHS t [] tt)

inferTop : Doc -> TC TyTm
inferTop (((n [ ":" ] a) [ "=" ] t) [ ";" ] ds) = do
  a <- check a U
  n <- newNameD n
  t <- checkLHS t a
  addGlobal n (a ,, (MkTName n := quoteFLHS t)) (inferTop ds)
{-
inferTop ((DVar n [ ":" ] a) [ ";" ] (DVar n' [ "=" ] t) [ ";" ] ds) = do
  True <- pure (primStringEquality n' n) where
    _ -> throwError "TODO"
  n <- newName n
  a <- check a U
  t <- addGlobal n (a ,, var n) (checkLHS t a)
  addGlobal n (a ,, (n := quoteFLHS t)) (inferTop ds)
-}
inferTop ((n [ "=" ] KW' "record" ds) [ ";" ] ds') = do
  fs , ds <- getArg ds
  ps <- firstArg ds
  ps <- check ps U
  fs <- check fs (ps => U)
  dn <- newNameD n
  dnl <- newNameT "lam"
  let desc = named dn (Record ps fs)
  addGlobal dn (ps => U ,, (dnl := Lam' \x -> RHS (Rec desc x))) (inferTop ds')
{-
inferTop ((n [ "=" ] KW "fix" $ KW "record" $ ps $ fs) [ ";" ] ds) = do
  dn <- newNameD n
  ps <- check ps U
  fs <- addGlobal dn (ps => U ,, var dn) (check fs (ps => U))
  dnl <- newName "lam"
  let desc = fixDecl dn dnl ps fs
  addGlobal dn (ps => U ,, (dnl := Lam' \x -> RHS (Rec desc x))) (inferTop ds)
-}
inferTop (t [ ":" ] a) = do
  a <- check a U
  t <- check t a
  pure (a ,, t)
inferTop d = throwError ("inferTop: " ++ showDoc d)

tc : String -> TC TyTm
tc s = parse s >>= inferTop

convertSpine : (s : Spine a) (s' : Spine a') -> TC (_≡_ {A = Ty ** Spine} (a ,, s) (a' ,, s'))

{-# TERMINATING #-}
convert : (x : Tm a) (y : Tm a) -> TC (x ≡ y)
convert {a = U} U   U   = pure Refl
convert {a = U} Top Top = pure Refl
convert {a = U} Bot Bot = pure Refl
convert {a = U} (a => b) (a' => b') = do
  Refl <- convert a a'
  Refl <- convert b b'
  pure Refl
convert {a = U} (a ⊎ b) (a' ⊎ b') = do
  Refl <- convert a a'
  Refl <- convert b b'
  pure Refl
convert {a = U} (a × b) (a' × b') = do
  Refl <- convert a a'
  Refl <- convert b b'
  pure Refl
convert {a = U} (Pi a b) (Pi a' b') = do
  Refl <- convert a a'
  Refl <- convert b b'
  pure Refl
convert {a = U} (Sigma a b) (Sigma a' b') = do
  Refl <- convert a a'
  Refl <- convert b b'
  pure Refl
convert {a = U} (NU (Id' {a = a} x y)) (NU (Id' {a = a'} x' y')) = do
  Refl <- convert a a'
  Refl <- convert x x'
  Refl <- convert y y'
  pure Refl
convert {a = U} a@(Rec rc x) b@(Rec rc' x') = do
  Yes Refl <- pure (decNamed rc rc')  where
    No -> throwError (showTm a ++ "  =?=  " ++ showTm b)
  Refl <- convert x x'
  pure Refl
convert {a = U} (NU (NeU' {s = s} g)) (NU (NeU' {s = s'} g')) = do
  Refl <- convertSpine s s'
  pure (setEq (sym (glued g) ∘ glued g'))
convert {a = a ⊎ a'} (Left  x) (Left  y) = do
  Refl <- convert x y
  pure Refl
convert {a = a ⊎ a'} (Right x) (Right y) = do
  Refl <- convert x y
  pure Refl
convert {a = Top} _ _ = pure (setEq TODO)
convert {a = a => a'} x y = do
  n <- newNameT "v"
  e <- convert (x ∙ var n) (y ∙ var n)
  pure (setEq TODO)
convert {a = Pi a b} x y = do
  n <- newNameT "v"
  e <- convert (x ∙∙ var n) (y ∙∙ var n)
  pure (setEq TODO)
convert {a = a × a'} x y = do
  e1 <- convert (fst× ∙ x) (fst× ∙ y)
  e2 <- convert (snd× ∙ x) (snd× ∙ y)
  pure (setEq TODO)
convert {a = Sigma a b} x y = do
  e <- convert (fstΣ ∙ x) (fstΣ ∙ y)
  helper e (sndΣ ∙∙ x) Refl (sndΣ ∙∙ y) Refl
 where
  helper : ∀ {fstx fsty} -> fstx ≡ fsty ->
     (sx : Tm (b ∙ fstx)) -> _≈_ {A = Tm a ** \fst -> Tm (b ∙ fst)} (fstx ,, sx) (fstΣ ∙ x ,, sndΣ ∙∙ x) ->
     (sy : Tm (b ∙ fsty)) -> _≈_ {A = Tm a ** \fst -> Tm (b ∙ fst)} (fsty ,, sy) (fstΣ ∙ y ,, sndΣ ∙∙ y) ->
       TC (x ≡ y)
  helper Refl sx e3 sy e4 = do
    Refl <- convert sx sy
    pure (setEq TODO)
convert {a = Rec rc ps} x y = do
  e <- convert (proj ∙ x) (proj ∙ y)
  pure (setEq TODO)
convert {a = Id x y} _ _ = do
  pure (setEq TODO)
convert {a = NeU _} (NeNU {s = s} g) (NeNU {s = s'} g') = do
  Refl <- convertSpine s s'
  pure (setEq (sym (glued g) ∘ glued g'))
convert x y = throwError (showTm x ++ "  =?=  " ++ showTm y)

convertSpine (Head l) (Head l') = do
  Yes Refl <- pure (decNamed l l') where
    No -> throwError "convertSpine1"
  pure Refl
convertSpine (s $ x) (s' $ x') = do
  Refl <- convertSpine s s'
  Refl <- convert x x'
  pure Refl
convertSpine (s $$ x) (s' $$ x') = do
  Refl <- convertSpine s s'
  Refl <- convert x x'
  pure Refl
convertSpine _ _ = throwError "convertSpine"

----------------------------------

the : (A : Set) -> A -> A
the _ x = x

-------------------------------


main'' : String -> TC String
main'' s = do
  d <- parse s
  a ,, t <- inferTop d
  pure (showTm t ++ "\n : " ++ showTm a)

showEither : Either String String -> String
showEither (Left x) = x
showEither (Right x) = x

main : IO T
main = interact \s -> showEither (runTC (main'' s)) ++ "\n"


{-

TODOs

Parser:
- fix combinator?
- more NameT
- lamm hack?
  - review all MkName
- Raw syntax
- first order Lambda in Core
- env to Tm with vars
- recursion
- "unifiers as equivalences" combinators

- case tree compilation
- data compilation
- dependent pattern matching strategy

backend:
- staging
- code generation

-}

