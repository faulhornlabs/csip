{-

Compile with C-c C-x C-c

Try as

    ./CoreC2 <test.txt

-}


{-# OPTIONS --type-in-type --rewriting --prop #-}

open import Agda.Builtin.Bool using (Bool) renaming (true to True; false to False)
open import Agda.Builtin.Char using (Char; primIsLower; primIsDigit; primIsAlpha; primIsSpace; primCharEquality; primCharToNat)
open import Agda.Builtin.Char.Properties using (primCharToNatInjective)
open import Agda.Builtin.String.Properties using (primStringToListInjective)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe) renaming (just to Just; nothing to Nothing)
open import Agda.Builtin.String using (String; primStringAppend; primStringToList; primStringFromList; primStringEquality; primShowNat)
open import Agda.Builtin.Nat using (Nat; _<_; _==_) renaming (suc to S; zero to Z)
--open import Agda.Builtin.Coinduction
open import Agda.Builtin.Unit renaming (⊤ to Unit)
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.TrustMe using (primTrustMe)
open import Agda.Builtin.Equality renaming (_≡_ to Eq; refl to Refl)

-------------------

infixr 8 _∘~_    -- transitivity for _~_
infixr 8 _∘≈_    -- transitivity for _≈_
infixr 8 _∘≡_    -- transitivity for _≡_
infixr 5 _&&_
infixr 4 _||_
infix  3 _~_     -- inhomogenous Prop equality
infix  3 _≈_     -- homogenous Prop equality
infix  3 _≡_     -- homogenous Set equality
infixr 2 _+++_   -- string concatenation
infixr 2 _::_
infixr 2 _**_    -- dependent pair type (infix Σ)

_+++_ : String -> String -> String
a +++ b = primStringAppend a b

pattern _::_ a as = a ∷ as

postulate
  interact : (String -> String) → IO Unit

{-# FOREIGN GHC import qualified Data.Text.IO as TIO #-}
{-# COMPILE GHC interact = TIO.interact #-}

---------------------

private variable
  A A' B C : Set
  P Q : Prop

-------------------
{-
data Sing {A : Set} : A -> Set where
  sing : (x : A) -> Sing x
-}

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

------------------

record T : Set where
  pattern
  constructor tt

data ⊥ : Set where

exfalsoP : ⊥ -> P
exfalsoP ()

exfalso : ⊥ -> A
exfalso ()


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

{-# FOREIGN GHC data IEq a b c d = IRefl #-}
{-# COMPILE GHC _~_ = data IEq (IRefl) #-}
{-# COMPILE GHC coe~ = \_ _ _ a -> coe a #-}

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


_≡_ : {A : Set} (a : A) -> A -> Set
_≡_ = Eq

propEq : {a a' : A} -> a ≡ a' -> a ≈ a'
propEq Refl = Refl

setEq : {a a' : A} -> a ≈ a' -> a ≡ a'
setEq {a = a} e = coe≈ (cong≈ (\x -> a ≡ x) e) Refl

sym≡ : {a a' : A} -> a ≡ a' -> a' ≡ a
sym≡ Refl = Refl

_∘≡_ : {a a' a'' : A} -> a ≡ a' -> a' ≡ a'' -> a ≡ a''
Refl ∘≡ e = e

cong≡ : {a a' : A} -> (f : A -> B) -> a ≡ a' -> f a ≡ f a'
cong≡ f Refl = Refl

cong2≡ : {a a' : A} {b b' : B} -> (f : A -> B -> C) -> a ≡ a' -> b ≡ b' -> f a b ≡ f a' b'
cong2≡ _ Refl Refl = Refl

coe≡ : A ≡ B → A → B
coe≡ Refl a = a

-------------------

data _≡~_ {A : Set} (a : A) : {B : Set} -> B -> Set where
  Refl : a ≡~ a

setEq' : {a : A} {a' : B} -> a ~ a' -> a ≡~ a'
setEq' {a = a} {a' = a'} e = coe~ (helper e) (_≡~_.Refl {a = a})  where
  helper : a ~ a' -> (a ≡~ a) ~ (a ≡~ a')
  helper Refl = Refl


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


-----------

data Dec (A : Set) : Set where
  Yes : A -> Dec A
  No  :      Dec A

decString : (c c' : String) -> Dec (c ≡ c')
decString c c' = if primStringEquality c c' then Yes (primTrustMe) else No

-----------

record Name : Set where
  constructor MkName
  field
    nameStr : String  -- only for pretty printing
    nameId  : Nat     -- globally unique

open Name

nameEquality : Name -> Name -> Bool
nameEquality n m = nameId n == nameId m

decName : (c c' : Name) -> Dec (c ≡ c')
decName c c' = if nameEquality c c' then Yes (primTrustMe) else No


----------------------------------

NameMap : Set -> Set

emptySM     : NameMap A
insertSM    : Name -> A -> NameMap A -> NameMap A
lookupSMStr : String -> NameMap A -> Maybe A

NameMap A = List (Pair Name A)

emptySM = []

insertSM s a m = (s , a) :: m

lookupSMStr s [] = Nothing
lookupSMStr s ((n , x) :: sm) with primStringEquality (nameStr n) s
... | True  = Just x
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
  constructor named
  field
    name    : Name
    unnamed : A

open Named

postulate
  -- True because 'named' is called only in the TC monad with distinct ids
  uniqueNames : {a a' : Named A} -> name a ≈ name a' -> a ≈ a'

----------------------

data Ty : Set

Tm : Ty -> Set

_=>U : Ty -> Set    --   Tm (a => U)

-- record description
record UnnamedRDesc : Set where
  constructor RD
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
glued {s = s $ x} (C$ c) = cong≈ (\k -> k ∙ x) (glued c)
glued {s = s $ x} {l = l} (CLam {f = f} c e) = helper e (cong≈ (\k -> k ∙ x) (glued c))  where
  helper : {fx : _} {ee : f x ≈ fx} -> fx ≈ NoRHS l -> spineToTm s ∙ x ≈ lhs∙ c fx ee -> spineToTm s ∙ x ≈ Ne (CLam c e)
  helper Refl cc = cc
glued {s = s $$ x} (C$$ c) = cong≈ (\k -> k ∙∙ x) (glued c)
glued {s = s $$ x} {l = l} (CDLam {f = f} c e) = helper e (cong≈ (\k -> k ∙∙ x) (glued c))  where
  helper : {fx : _} {ee : f x ≈ fx} -> fx ≈ NoRHS l -> spineToTm s ∙∙ x ≈ lhs∙∙ c fx ee -> spineToTm s ∙∙ x ≈ Ne (CDLam c e)
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

elimR : ∀ {rc ps a} ->
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

_:=_ : Name -> LHS a -> Tm a
n := RHS   t = t
n := NoRHS t = Ne (CHead (named n t))

pattern Lam'  f = NoRHS (Lam  f)
pattern DLam' f = NoRHS (DLam f)

var : Name -> Tm a
var n = n := NoRHS (Stuck n)


-------------------------------------------------------

data Tys : Set          --  [] (A : U) (x : A) (y : A) (e : x ≡ y)

Tms : Tys -> Set        --  (((tt, Bool), True), True), Refl

-- type depending on context
CTy : Tys -> Set
CTy ts = Tms ts -> Ty

-- term depending on context
CTm : (ts : Tys) -> CTy ts -> Set
CTm ts t = (xs : Tms ts) -> Tm (t xs)


data Tys where
  []      :                                 Tys
  _>>_::_ : (ts : Tys) -> Name -> CTy ts -> Tys

Tms []             = T
Tms (ts >> n :: t) = Tms ts ** \xs -> Tm (t xs)

private variable
  ts : Tys

---------------

infixl 10 _//ᵤ_
infixl 10 _//_
infixl 10 _//ₛ_

{-# TERMINATING #-}
_//ᵤ_  : Ty -> CTy ts

_//_ : Tm a    -> CTm ts (_//ᵤ_ a)
_//ₛ_ : Spine a -> CTm ts (_//ᵤ_ a)


postulate
  rParamsClosed : {xs : Tms ts} -> rParams rc //ᵤ xs ≈ rParams rc

U         //ᵤ xs = U
Top       //ᵤ xs = Top
Bot       //ᵤ xs = Bot
(a => a') //ᵤ xs = a //ᵤ xs => a' //ᵤ xs
(a ×  a') //ᵤ xs = a //ᵤ xs ×  a' //ᵤ xs
(a ⊎  a') //ᵤ xs = a //ᵤ xs ⊎  a' //ᵤ xs
Pi    a b //ᵤ xs = Pi    (a //ᵤ xs) (b // xs)
Sigma a b //ᵤ xs = Sigma (a //ᵤ xs) (b // xs)
Id x y    //ᵤ xs = Id (x // xs) (y // xs)
RTC rc x  //ᵤ xs = RTC rc (coe≈ (cong≈ Tm (rParamsClosed {rc = rc})) (x // xs))
NU (NeU' {s = s} _) //ᵤ xs = s //ₛ xs

postulate
  TODO : P

//ᵤ∙ : ∀ {a} (b : a =>U) {x : Tm a} (xs : Tms ts) -> (b ∙ x) //ᵤ xs ≈ b // xs ∙ x // xs
//ᵤ∙ = TODO

//ᵤ[] : _//ᵤ_ {ts = []} a _ ≈ a
//ᵤ[] {a = U        } = Refl
//ᵤ[] {a = Top      } = Refl
//ᵤ[] {a = Bot      } = Refl
//ᵤ[] {a = a => a'  } = cong2≈ _=>_ //ᵤ[] //ᵤ[]
//ᵤ[] {a = a ×  a'  } = cong2≈ _×_  //ᵤ[] //ᵤ[]
//ᵤ[] {a = a ⊎  a'  } = cong2≈ _⊎_  //ᵤ[] //ᵤ[]
//ᵤ[] {a = Pi    a b} = TODO
//ᵤ[] {a = Sigma a b} = TODO
//ᵤ[] {a = Id x y   } = TODO
//ᵤ[] {a = RTC rc x } = TODO
//ᵤ[] {a = NeU g    } = TODO

postulate
{-
  rFieldsClosed : {ps : Tm (rParams rc)} {xs : Tms ts} ->
      rFields rc // xs ∙                                            ps // xs       ≈
      rFields rc        ∙ coe≈ (cong≈ Tm (rParamsClosed {rc = rc})) (ps // xs)
-}

  rFieldsClosed : {ps : Tm (rParams rc)} {xs : Tms ts} ->
      (rFields rc ∙ ps) //ᵤ xs       ≈
      rFields rc ∙ coe≈ (cong≈ Tm (rParamsClosed {rc = rc})) (ps // xs)

_//_ {a = U}    t          xs = t //ᵤ xs
_//_ {a = NU _} TT         xs = TT
_//_ {a = NU _} (x ,  y)   xs = x // xs ,  y // xs
_//_ {a = NU _} (_,,_ {b = b} x y) xs = x // xs ,, coe≈ (cong≈ Tm (//ᵤ∙ b xs)) (y // xs)
_//_ {a = NU _} (Left  x)  xs = Left  (x // xs)
_//_ {a = NU _} (Right x)  xs = Right (x // xs)
_//_ {a = NU _} Refl       xs = Refl
_//_ {a = NU _} (RDC {rc = rc} args) xs = RDC (coe≈ (cong≈ Tm (rFieldsClosed {rc = rc})) (args // xs))
_//_ {a = NU _} (NeNU {s = s} _) xs = s //ₛ xs

postulate
  nameIsDefined : Name -> Tm a
  freeFrom : ∀ n a {ts} {t : CTy ts} {xs : Tms ts} {x : Tm (t xs)} -> _//ᵤ_ {ts = ts >> n :: t} a (xs ,, x) ≈ a //ᵤ xs
  thisIsIt : {t : CTy ts} {xs : Tms ts} {x : Tm (t xs)} -> Tm (t xs) ≈ Tm (_//ᵤ_ {ts = ts >> n :: t} a (xs ,, x))
  b∙var//ᵤ : (b : a =>U) {xs : Tms ts} {x : Tm (a //ᵤ xs)} -> _//ᵤ_ {ts = ts >> n :: \xs' -> a //ᵤ xs'} (b ∙ var n) (xs ,, x) ≈ b // xs ∙ x

indexTms : ∀ {a ts} -> Name -> CTm ts (_//ᵤ_ a)
indexTms {ts = []} n xs = nameIsDefined n
indexTms {a = a} {ts = ts >> n' :: t} n (xs ,, x) with nameEquality n' n
... | False = coe≈ (cong≈ Tm (sym≈ (freeFrom n' a))) (indexTms {a = a} n xs)
... | True  = coe≈ (thisIsIt {a = a}) x

postulate
  NamedLambdaClosed : {xs : Tms ts} -> NamedLambda (a //ᵤ xs) ≈ NamedLambda a

Head {a = a} (named n (Stuck x)) //ₛ xs = indexTms {a = a} n xs
Head h@(named _ (Lam  _))   //ₛ xs = spineToTm (Head (coe≈ (sym≈ NamedLambdaClosed) h))
Head h@(named _ (DLam _))   //ₛ xs = spineToTm (Head (coe≈ (sym≈ NamedLambdaClosed) h))
(s $  x)                    //ₛ xs = s //ₛ xs ∙ x // xs
DApp {b = b} s x Refl       //ₛ xs = coe≈ (cong≈ Tm (sym≈ (//ᵤ∙ b xs))) (s //ₛ xs ∙∙ x // xs)


-------------------------------------------------

isAlphaNumeric : Char -> Bool
isAlphaNumeric '_'  = True
isAlphaNumeric '\'' = True
isAlphaNumeric a    = primIsAlpha a || primIsDigit a

isGraphic : Char -> Bool
isGraphic '*' = True
isGraphic '+' = True
isGraphic '-' = True
isGraphic '^' = True
isGraphic '=' = True
isGraphic '@' = True
isGraphic '%' = True
isGraphic '$' = True
isGraphic '&' = True
isGraphic '~' = True
isGraphic '.' = True
isGraphic '!' = True
isGraphic '?' = True
isGraphic ':' = True
isGraphic '<' = True
isGraphic '>' = True
isGraphic '/' = True
isGraphic '\\'= True
isGraphic '|' = True
isGraphic '#' = True
isGraphic c   = False

glueChar : Char -> Char -> Bool
glueChar a b
   = isAlphaNumeric a && isAlphaNumeric b
  || isGraphic      a && isGraphic      b

tokens : String -> List String
tokens s = map primStringFromList (filter f (groupBy glueChar (primStringToList s)))  where
  f : List Char -> Bool
  f (c :: _) = not (primIsSpace c)
  f _        = True

isVarToken : String -> Bool
isVarToken s = all isAlphaNumeric (primStringToList s)

testTokens : tokens "(a + bc)" ≡ ("(" :: "a" :: "+" :: "bc" :: ")" :: [])
testTokens = Refl

showTokens : List String -> String
showTokens [] = ""
showTokens (t :: ts) = t +++ " " +++ showTokens ts

----------------------------------

data Doc : Set where
  DVar  : String ->               Doc
  _$_   : Doc -> Doc ->           Doc
  _[_]_ : Doc -> String -> Doc -> Doc    -- operator

-------------------------------------

operators : List String
operators = ";" :: "=" :: "." :: ":" :: "," :: "->" :: "+" :: "*" :: []

showDoc : Doc -> String
showDoc = go 0  where

  parens : Bool -> String -> String
  parens True  a = "(" +++ a +++ ")"
  parens False a =         a

  addOp : String -> (String -> Nat) -> String -> Nat
  addOp t r s with primStringEquality s t
  ... | True  = 0
  ... | False = S (r s)

  prec : String -> Nat
  prec = foldr addOp (\_ -> 0) operators

  go : Nat -> Doc -> String
  go p (DVar n)    = n
  go p (a $ b)     = parens (q < p) (go q a +++ " " +++ go (S q) b) where
    q = 100
  go p (a [ s ] b) = parens (q < p) (go (S q) a +++ " " +++ s +++ " " +++ go q b) where
    q = prec s


testShowDoc : showDoc ((DVar "a" [ "." ] DVar "a" $ DVar "b") $ (DVar "c" $ DVar "e") $ DVar "d" $ (DVar "a" [ "." ] DVar "b" [ "." ] DVar "a"))
        ≈ "(a . a b) (c e) d (a . b . a)"
testShowDoc = Refl

testShowDoc' : showDoc ((DVar "a" [ "*" ] DVar "a" $ DVar "b" [ "*" ] DVar "b") $ DVar "d" [ "*" ] DVar "f" $ (DVar "c" [ "*" ] DVar "e"))
        ≈ "(a * a b * b) d * f (c * e)"
testShowDoc' = Refl

-----------------------------------

-------------------------------------

printName : Name -> Doc
printName n = DVar (pr (nameStr n))  where
  pr : String -> String
  pr "lam" = "lam" +++ primShowNat (nameId n)
  pr n     = n

printTm    : Tm a -> Doc
printSpine : Spine a -> Doc

printSpine (Head x) = printName (name x)
printSpine (s $  x) = printSpine s $ printTm x
printSpine (s $$ x) = printSpine s $ printTm x

-- {-# TERMINATING #-}
printTm {a = U} U           = DVar "U"
printTm {a = U} Top         = DVar "Top"
printTm {a = U} Bot         = DVar "Bot"
printTm {a = U} (a => a')   = printTm a [ "->" ] printTm a'
printTm {a = U} (a × a')    = printTm a [ "*"  ] printTm a'
printTm {a = U} (a ⊎ a')    = printTm a [ "+"  ] printTm a'
printTm {a = U} (Pi a b)    = DVar "Pi"      $ printTm a $ printTm b
printTm {a = U} (Sigma a b) = DVar "Sigma"   $ printTm a $ printTm b
printTm {a = U} (Id x y)    = DVar "Id"      $ printTm x $ printTm y
printTm {a = U} (RTC rc x)  = printName (name rc) $ printTm x
printTm {a = U} (NU (NeU' {s = s} _)) = printSpine s
--printTm {a = NU (a =>' a')} f = DLam "v" (printTm (f ∙ var "v"))
printTm {a = NU _} TT        = DVar "tt"
printTm {a = NU _} (x ,  y)  = printTm x [ ","  ] printTm y
printTm {a = NU _} (x ,, y)  = printTm x [ ",," ] printTm y
printTm {a = NU _} (Left  x) = DVar "Left"  $ printTm x
printTm {a = NU _} (Right x) = DVar "Right" $ printTm x
printTm {a = NU _} Refl      = DVar "Refl"
printTm {a = NU _} (RDC {rc = rc} args) = DVar "wrap" $ printTm args
printTm {a = NU _} (NeNU {s = s} _) = printSpine s


showTm : Tm a -> String
showTm t = showDoc (printTm t)

--------------------------------



----------------------------------

Error : Set
Error = String

TyTm : Set
TyTm = Ty ** \a -> Tm a

Ctx : Set
Ctx = NameMap TyTm

TCState = Nat

-- type checking monad
record TC (A : Set) : Set where
  coinductive
  constructor MkTC
  field
    getTC : Ctx -> TCState -> Either Error (Pair TCState A)

open TC

throwError : Error -> TC A
throwError e = MkTC \_ _ -> Left e

runTC : TC A -> Either Error A
runTC tc with getTC tc emptySM 10
... | Left  e       = Left e
... | Right (_ , r) = Right r

instance
  TCMonad : Monad TC

  getTC (_>>=_ {{TCMonad}} m f) ctx c with getTC m ctx c
  ... | Left  e = Left e
  ... | Right (c , x) = getTC (f x) ctx c

  pure {{TCMonad}} x = MkTC \_ c -> Right (c , x)

declareTm : Name -> TyTm -> TC A -> TC A
getTC (declareTm s d m) ctx = getTC m (insertSM s  d ctx)

lookupTm : String -> TC TyTm
getTC (lookupTm s) ctx c with lookupSMStr s ctx
... | Just x  = Right (c , x)
... | Nothing = Left ("Not defined: " +++ s)

newName : String -> TC Name
getTC (newName s) ctx c = Right (S c , MkName s c)

-------------------------------------

{-# TERMINATING #-}
parse : String -> TC Doc
parse s = h0 end (tokens s)  where

  X = List String -> TC Doc

  end : Doc -> X
  end d [] = pure d
  end d ts  = throwError ("End expected instead of  " +++ showTokens ts)

  expect : String -> X -> X
  expect t r (t' :: ts) with primStringEquality t' t
  ... | True  = r ts
  ... | False = throwError (t +++ " expected instead of " +++ showTokens (t' :: ts))
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
  h8 r = h9 (h8' r) \ts -> throwError ("unknown token at  " +++ showTokens ts)

  addOp : String -> ((Doc -> X) -> X) -> (Doc -> X) -> X
  addOp t g r = g (hn' r) where
    hn' : (Doc -> X) -> Doc -> X
    hn' r a (t' :: ts) with primStringEquality t' t
    ... | True = addOp t g (\b -> r (a [ t ] b)) ts
    ... | False = r a (t' :: ts)
    hn' r a ts = r a ts

  h0 = foldr addOp h8 operators

testParse : parse "f (b a * c * e) d"
          ≡ pure (DVar "f" $ (DVar "b" $ DVar "a" [ "*" ] DVar "c" [ "*" ] DVar "e") $ DVar "d")
testParse = Refl


----------------------------------

{-
postulate
  fstΣ : Tm (Sigma a b => a)
  lamSnd : Tm (Sigma a b => U)
  lam : (Tm a -> Tm U) -> Tm (a => U)
  sndΣ : Tm (Pi (Sigma a b) (lam \s -> b ∙ (fstΣ ∙ s)))
-}
convertSpine : (s : Spine a) (s' : Spine a') -> TC (s ≡~ s')
convertRDesc : (rc rc' : RDesc) -> TC (rc ≡ rc')

-- TODO: eta rules
{-# TERMINATING #-}
convert : (x : Tm a) (y : Tm a) -> TC (x ≡ y)
convert {a = U} U U = pure Refl
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
convert {a = U} (RTC rc x) (RTC rc' x') = do
  Refl <- convertRDesc rc rc'
  Refl <- convert x x'
  pure Refl
convert {a = U} (NU (NeU' {s = s} g)) (NU (NeU' {s = s'} g')) = do
  Refl <- convertSpine s s'
  pure (setEq (sym≈ (glued g) ∘≈ glued g'))
convert {a = Top} TT TT = pure Refl
{- TODO
convert {a = Bot} x y = {!!}
convert {a = a => a'} x y = {!!}
convert {a = a × a'} x y = {!!}
convert {a = a ⊎ a'} x y = {!!}
convert {a = Pi a b} x y = {!!}
convert {a = Sigma a b} x y = do
  e <- convert (fstΣ ∙ x) (fstΣ ∙ y)
  e' <- convert (sndΣ ∙∙ x) (coe≈ {!!} (sndΣ ∙∙ y))     --  Tm (b ∙ (fstΣ ∙ x))
  pure (setEq {!!})
convert {a = Id x y} u v = {!!}
convert {a = RTC rc ps} x y = {!!}
convert {a = NeU _} x y = {!!}
-}
convert x y = throwError (showTm x +++ "  =?=  " +++ showTm y)

-- this is only an optimization (when used instead of convert)
convertTrustMe : (x : Tm a) (y : Tm a) -> TC (x ≡ y)
convertTrustMe _ _ = pure primTrustMe

convertRDesc rc rc' with decName (name rc) (name rc')
... | No = throwError "convertRDesc"
... | Yes e = pure (setEq (uniqueNames (propEq e)))

convertSpine (Head {a = a} x) (Head {a = a'} x') with decName (name x) (name x')
... | No = throwError "convertSpine1"
... | Yes e = do
  Refl <- convertTrustMe a a'
  pure (setEq' (inhomog (cong≈ Head (uniqueNames (propEq e)))))
convertSpine (_$_ {a = a} {a' = b} s x) (_$_ {a = a'} {a' = b'} s' x') = do
  e <- convertSpine s s'
  Refl <- convertTrustMe a a'
  Refl <- convertTrustMe b b'
  Refl <- pure e
  Refl <- convert x x'
  pure Refl
convertSpine (DApp {a = a} {b = b} s x Refl) (DApp {a = a'} {b = b'} s' x' Refl) = do
  e <- convertSpine s s'
  Refl <- convertTrustMe a a'
  Refl <- convertTrustMe b b'
  Refl <- pure e
  Refl <- convert x x'
  pure Refl
convertSpine _ _ = throwError "convertSpine"


----------------------------------

infer : Doc -> TC TyTm

check : Doc -> (a : Ty) -> TC (Tm a)
check (DVar "tt") Top = pure TT
check (x [ "," ] x') (a × a') = do
  x  <- check x  a
  x' <- check x' a'
  pure (x , x')
check (DVar "Left" $ x) (a ⊎ a') = do
  x  <- check x a
  pure (Left x)
check (DVar "Right" $ x) (a ⊎ a') = do
  x  <- check x a'
  pure (Right x)
check (DVar sn [ "." ] e) (a => a') = do
  n <- newName sn
  e <- declareTm n (a ,, var n) (check e a')
  ln <- newName "lam"
  pure (ln := Lam' \x -> RHS (coe≈ (cong≈ Tm (freeFrom n a' ∘≈ //ᵤ[])) (_//_ {ts = [] >> n :: \xs -> a //ᵤ xs} e (tt ,, coe≈ (cong≈ Tm (sym≈ //ᵤ[])) x))))
--  pure (("lam" +++ n) := Lam' \x -> RHS (coe≈ (cong≈ Tm (freeFrom n a' ∘≈ //ᵤ[])) (_//_ {ts = [] >> n :: \xs -> a} e (tt ,, x))))
check (DVar sn [ "." ] e) (Pi a b)  = do
  n <- newName sn
  e <- declareTm n (a ,, var n) (check e (b ∙ var n))
  ln <- newName "lam"
  pure (ln := DLam' \x -> RHS (coe≈ (cong≈ Tm (b∙var//ᵤ b ∘≈ TODO)) (_//_ {ts = [] >> n :: \xs -> a //ᵤ xs} e (tt ,, coe≈ (cong≈ Tm (sym≈ //ᵤ[])) x))))
check (x [ "," ] y) (Sigma a b) = do
  x <- check x  a
  y <- check y (b ∙ x)
  pure (x ,, y)
check (DVar "Refl") (Id x y) = do
  e <- convert x y
  pure (coe≈ (cong≈ (\k -> Tm (Id x k)) (propEq e)) Refl)
check (DVar "wrap" $ x) (RTC rc ps) = do
  x <- check x (rFields rc ∙ ps)
  pure (RDC x)
check d a = do
  a' ,, t <- infer d
  Refl <- convert a' a
  pure t

infer (DVar "U")   = pure (U ,, U)
infer (DVar "Bot") = pure (U ,, Bot)
infer (DVar "Top") = pure (U ,, Top)
infer (a [ "*" ] a') = do
  a  <- check a  U
  a' <- check a' U
  pure (U ,, a × a')
infer (a [ "+" ] a') = do
  a  <- check a  U
  a' <- check a' U
  pure (U ,, a ⊎ a')
infer (a [ "->" ] a') = do
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
infer (f $ x) = infer f >>= matchPi  where
  matchPi : TyTm -> TC TyTm
  matchPi (a => a' ,, f) = do
    x <- check x a
    pure (a' ,, f ∙ x)
  matchPi (Pi a b ,, f) = do
    x <- check x a
    pure (b ∙ x ,, f ∙∙ x)
  matchPi _ = throwError "matchPi"
infer (DVar n) = lookupTm n
infer d = throwError ("infer: " +++ showDoc d)


-------------------------------

-- first order representation of LHS
data LHS' : Ty -> Set where
  RHS         : ∀ {a} -> Tm a ->                                       LHS' a
  Lam         : ∀ {a a'} -> (n : Name) -> LHS' a' ->                   LHS' (a => a')
  DLam        : ∀ {a b}  -> (n : Name) -> LHS' (b ∙ var n) ->          LHS' (Pi a b)
  MatchPair   : Tm (a × a') -> Name -> Name -> LHS' a'' ->             LHS' a''
  MatchEither : Tm (a ⊎ a') -> Name -> LHS' a'' -> Name -> LHS' a'' -> LHS' a''
  MatchRecord : ∀ {ps a''} -> Tm (RTC rc ps) -> Name -> LHS' a'' ->    LHS' a''
  -- MatchSigma : ...
  -- MatchRefl : ...

quoteLHS : {a : Ty} -> LHS' a -> {ts : Tys} -> (xs : Tms ts) -> LHS (a //ᵤ xs)
quoteLHS (Lam {a = a} {a' = a'} n t) {ts = ts} xs
  = NoRHS (Lam {a = a //ᵤ xs} {a' = a' //ᵤ xs} \x -> coe≈ (cong≈ LHS (freeFrom n a')) (quoteLHS t {ts = ts >> n :: \xs' -> a //ᵤ xs'} (xs ,, x)))
quoteLHS (DLam {a = a} {b = b} n t) {ts = ts} xs
  = NoRHS (DLam {a = a //ᵤ xs} {b = b // xs} \x -> coe≈ (cong≈ LHS (b∙var//ᵤ b)) (quoteLHS t {ts = ts >> n :: \xs' -> a //ᵤ xs'} (xs ,, x)))
quoteLHS (MatchPair {a = a} {a' = a'} {a'' = a''} p n n' e) {ts = ts} xs
  = elim× {a = a //ᵤ xs} {a' = a' //ᵤ xs} (p // xs) \x x' ee ->
       coe≈ (cong≈ LHS (freeFrom n' a'' ∘≈ freeFrom n a'')) (
         quoteLHS e {ts = (ts >> n :: \xs' -> a //ᵤ xs') >> n' :: \(xs'' ,, _) -> a' //ᵤ xs''} ((xs ,, x) ,, x')
       )
quoteLHS (MatchEither {a = a} {a' = a'} {a'' = a''} p n e n' e') {ts = ts} xs
  = elim⊎ {a = a //ᵤ xs} {a' = a' //ᵤ xs} (p // xs)
     (\x _ -> coe≈ (cong≈ LHS (freeFrom n  a'')) (quoteLHS e  {ts = ts >> n  :: \xs' -> a  //ᵤ xs'} (xs ,, x)))
     (\x _ -> coe≈ (cong≈ LHS (freeFrom n' a'')) (quoteLHS e' {ts = ts >> n' :: \xs' -> a' //ᵤ xs'} (xs ,, x)))
quoteLHS (MatchRecord {rc = rc} {ps = ps} {a'' = a''} p n e) {ts = ts} xs
  = elimR {rc = rc} {ps = coe≈ (cong≈ Tm (rParamsClosed {rc = rc})) (ps // xs)} {a = a'' //ᵤ xs} (p // xs) \x ee ->
       coe≈ (cong≈ LHS (freeFrom n a'')) (
         quoteLHS e {ts = ts >> n :: \xs' -> (rFields rc ∙ ps) // xs} (xs ,, coe≈ (cong≈ Tm (sym≈ (rFieldsClosed {rc = rc}))) x)
       )
quoteLHS (RHS t) xs = RHS (t // xs)

quoteLHS' : LHS' a -> LHS a
quoteLHS' t = coe≈ (cong≈ LHS //ᵤ[]) (quoteLHS t {ts = []} (tt))

checkLHS : Doc -> (a : Ty) -> TC (LHS' a)
checkLHS (DVar n [ "." ] t) (a => a') = do
  n <- newName n
  t <- declareTm n (a ,, var n) (checkLHS t a')
  pure (Lam n t)
checkLHS (DVar n [ "." ] t) (Pi a b) = do
  n <- newName n
  t <- checkLHS t (b ∙ var n)
  pure (DLam n t)
checkLHS (DVar "ret" $ d) a = do
  t <- check d a
  pure (RHS t)
checkLHS (DVar "pair" $ p $ (DVar n [ "." ] DVar n' [ "." ] e)) a'' = do
  n <- newName n
  n' <- newName n'
  a × a' ,, p <- infer p where
    _ -> throwError "pair"
  e <- declareTm n (a ,, var n) (declareTm n' (a' ,, var n') (checkLHS e a''))
  pure (MatchPair p n n' e)
checkLHS (DVar "either" $ p $ (DVar n [ "." ] e) $ (DVar n' [ "." ] e')) a'' = do
  n <- newName n
  n' <- newName n'
  a ⊎ a' ,, p <- infer p where
    r ,, _ -> throwError ("either: " +++ showTm r)
  e  <- declareTm n  (a  ,, var n ) (checkLHS e  a'')
  e' <- declareTm n' (a' ,, var n') (checkLHS e' a'')
  pure (MatchEither p n e n' e')
checkLHS (DVar "unwrap" $ p $ (DVar n [ "." ] e)) a'' = do
  n <- newName n
  RTC rc ps ,, p <- infer p where  
    r ,, _ -> throwError ("unwrap: " +++ showTm r)
  e  <- declareTm n  (rFields rc ∙ ps ,, var n) (checkLHS e  a'')
  pure (MatchRecord p n e)
checkLHS d a = throwError ("checkLHS: " +++ showDoc d)

inferTop : Doc -> TC TyTm
inferTop (((DVar n [ ":" ] a) [ "=" ] t) [ ";" ] ds) = do
  n <- newName n
  a <- check a U
  t <- checkLHS t a
  declareTm n (a ,, (n := quoteLHS' t)) (inferTop ds)
inferTop ((DVar n [ "=" ] DVar "record" $ ps $ fs) [ ";" ] ds) = do
  dn <- newName n
  ps <- check ps U
  fs <- check fs (ps => U)
  let desc = named dn (RD ps fs)
  dnl <- newName "lam"
  declareTm dn (ps => U ,, (dnl := Lam' \x -> RHS (RTC desc x))) (inferTop ds)
inferTop (t [ ":" ] a) = do
  a <- check a U
  t <- check t a
  pure (a ,, t)
inferTop d = throwError ("inferTop: " +++ showDoc d)

tc : String -> Either Error TyTm
tc s = runTC (parse s >>= inferTop)

--------

testTC : tc "f : Top -> U  = x. ret Top;  U : U"
       ≡ pure (U ,, U)
testTC = Refl

testTC3 : tc "id : U -> U  = x. ret x;  id U : U"
       ≡ pure (U ,, U)
testTC3 = Refl

testTC4 : tc "idFun : U -> U  = A. ret (A -> A);  id : Pi U idFun  = A. x. ret x;  id U U : U"
       ≡ pure (U ,, U)
testTC4 = Refl

main'' : String -> TC String
main'' s = do
  d <- parse s
  a ,, t <- inferTop d
  pure (showTm t +++ "\n : " +++ showTm a)

showEither : Either String String -> String
showEither (Left x) = x
showEither (Right x) = x

{- Agda loops
main2 : String -> String
main2 s with runTC (main'' s)
... | Left x = x
... | Right x = x
-}

main : IO Unit
main = interact \s -> showEither (runTC (main'' s)) +++ "\n"

----------------

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
⟦ Top        ⟧ = T
⟦ Bot        ⟧ = ⊥
⟦ a ⊎  a'    ⟧ = Either ⟦ a ⟧ ⟦ a' ⟧
⟦ a ×  a'    ⟧ = Pair   ⟦ a ⟧ ⟦ a' ⟧
⟦ Sigma a b  ⟧ = ⟦ a ⟧ ** \x -> ⟦ b ∙ quoteTm x ⟧
⟦ Id x y     ⟧ = ⟦ x ⟧ₜ ≡ ⟦ y ⟧ₜ
⟦ RTC rc x   ⟧ = Wrap ⟦_⟧ rc x
⟦ t@(NeU _)  ⟧ = ⊥

postulate
  -- True for closed terms
  noVars : VarName -> ⊥

{-# TERMINATING #-}
⟦_⟧ₜ {a = U   } t  = t
⟦_⟧ₜ {a = NU _} TT = tt
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
⟦ Top       ⟧' = T
⟦ Bot       ⟧' = ⊥
⟦ a ⊎ a'    ⟧' = Either ⟦ a ⟧' ⟦ a' ⟧'
⟦ a × a'    ⟧' = Pair   ⟦ a ⟧' ⟦ a' ⟧'
⟦ a => a'   ⟧' = ⟦ a ⟧ -> ⟦ a' ⟧'
⟦ Sigma a b ⟧' = ⟦ a ⟧ ** \x -> ⟦ b ∙ quoteTm x ⟧'
⟦ Pi a b    ⟧' = (x : ⟦ a ⟧) -> ⟦ b ∙ quoteTm x ⟧'
⟦ Id x y    ⟧' = ⟦ x ⟧ₜ' ≡ ⟦ y ⟧ₜ'
⟦ RTC rc x  ⟧' = Wrap ⟦_⟧' rc x
⟦ t@(NeU _) ⟧' = ⊥

{-# TERMINATING #-}
⟦_⟧ₜ' {a = U}    t  = ⟦ t ⟧
⟦_⟧ₜ' {a = NU _} TT = tt
⟦_⟧ₜ' {a = NU _} (x ,  y) = ⟦ x ⟧ₜ' , ⟦ y ⟧ₜ'
⟦_⟧ₜ' {a = NU _} (_,,_ {b = b} x y) = ⟦ x ⟧ₜ ,, coe≈ (cong≈ (\k -> ⟦ b ∙ k ⟧') evalQuote) ⟦ y ⟧ₜ'
⟦_⟧ₜ' {a = NU _} (Left  x) = Left  ⟦ x ⟧ₜ'
⟦_⟧ₜ' {a = NU _} (Right x) = Right ⟦ x ⟧ₜ'
⟦_⟧ₜ' {a = NU _} Refl = Refl
⟦_⟧ₜ' {a = NU _} (RDC args) = wrap ⟦ args ⟧ₜ'
⟦_⟧ₜ' {a = NU _} f@(NeNU {l = Lam  _} _) x = ⟦ f ∙  quoteTm x ⟧ₜ'
⟦_⟧ₜ' {a = NU _} f@(NeNU {l = DLam _} _) x = ⟦ f ∙∙ quoteTm x ⟧ₜ'
⟦_⟧ₜ' {a = NU _} (NeNU {l = Stuck n} x) = exfalso (noVars n)


{-

TODOs

parser:
- recursion
- multi lambda desugaring
- more powerful lhs eliminators

eta rules for conversion checking

frontend:
- case tree compilation
- data compilation

---------------------------

pattern matching for Refl (dependent pattern matching algorithm)

backend

-}

