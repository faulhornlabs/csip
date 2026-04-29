{-

Compile with C-c C-x C-c    Backend: GHC

Try as

    ./Csip <test/basic.csip
    ./Csip hs <test/power.csip >power.hs && runhaskell power.hs

-}


{-# OPTIONS --type-in-type --rewriting --prop --injective-type-constructors #-}

open import Agda.Builtin.Unit       using (tt) renaming (⊤ to T)
open import Agda.Builtin.Bool       using (Bool) renaming (true to True; false to False)
open import Agda.Builtin.Maybe      using (Maybe) renaming (just to Just; nothing to Nothing)
open import Agda.Builtin.List       using (List; []) renaming (_∷_ to Cons)
open import Agda.Builtin.Nat        using (Nat) renaming (suc to Suc; zero to Zero; _<_ to lessNat; _==_ to eqNat)
open import Agda.Builtin.Equality   using () renaming (_≡_ to Eq; refl to Refl)
open import Agda.Builtin.Char       using (Char) renaming (primCharToNat to charToNat)
open import Agda.Builtin.String     using (String; primStringAppend)
  renaming (primStringToList to stringToList; primStringFromList to stringFromList; primStringEquality to eqString; primShowNat to showNat)
open import Agda.Builtin.FromString using (IsString; fromString)
open import Agda.Builtin.IO         using (IO)
open import Agda.Builtin.TrustMe    using (primTrustMe)

-------------------

infixr 5 _&&_
infixr 4 _||_
infix  3 _≈_     -- Prop equality
infix  3 _≡_     -- Set equality
infix  3 _==_    -- Nat equality (to Bool)
infix  3 _<_
infixr 3 _∘_     -- transitivity for _≈_
infixr 2 _++_    -- string concatenation
infixr 2 _+++_   -- TC String concatenation
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
  getArgs  : IO (List String)
  bindIO   : ∀ {A B} -> IO A -> (A -> IO B) -> IO B

{-# FOREIGN GHC import qualified Data.Text.IO as TIO #-}
{-# COMPILE GHC interact = TIO.interact #-}
{-# FOREIGN GHC import System.Environment (getArgs) #-}
{-# FOREIGN GHC
  getArgsText :: IO [Data.Text.Text]
  getArgsText = do
    args <- getArgs
    pure (map Data.Text.pack args)
#-}
{-# COMPILE GHC getArgs = getArgsText #-}
{-# COMPILE GHC bindIO = \_ _ m f -> m >>= f #-}

instance
  StringString : IsString String
  StringString .IsString.Constraint s = T
  StringString .IsString.fromString s = s
  


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

cong~ : {a a' : A} {B : A -> Set} -> (f : (x : A) -> B x) -> a ≈ a' -> _≈_ {A ** B} (_ ,, f a) (_ ,, f a')
cong~ _ Refl = Refl


---------------------------------------

postulate
  future : (A -> (A -> C -> C) -> B) -> B

{-# FOREIGN GHC import System.IO.Unsafe (unsafePerformIO) #-}
{-# FOREIGN GHC import Data.IORef (IORef, newIORef, readIORef, writeIORef) #-}
{-# FOREIGN GHC
  {-# NOINLINE unsafe #-}
  unsafe :: IO a -> (a -> b) -> b
  unsafe m f = unsafePerformIO (f <$> m)

  future :: (a -> (a -> c -> c) -> b) -> b
  future f = unsafe (do
      r <- newIORef (error "value not yet defined")
      pure (unsafePerformIO (readIORef r), \x f -> unsafe (writeIORef r x) (\() -> f))
    ) (uncurry f)
#-}
{-# COMPILE GHC future = \_ _ _ -> future #-}


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
if True  then t else f = t


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

_++L_ : List A -> List A -> List A
[] ++L xs = xs
(x :: xs) ++L ys = x :: (xs ++L ys)

reverse : List A -> List A
reverse = go [] where
  go : List A -> List A -> List A
  go acc [] = acc
  go acc (a :: as) = go (a :: acc) as

-----------

data Dec (A : Set) : Set where
  Yes : A -> Dec A
  No  :      Dec A

decNat : (n n' : Nat) -> Dec (n ≡ n')
decNat n n' = if n == n' then Yes primTrustMe else No


-----------

record Name : Set where
  constructor MkName
  field
    nameStr : String  -- only for pretty printing
    nameId  : Nat     -- globally unique

open Name

decName : (n n' : Name) -> Dec (n ≡ n')
decName n n' = if nameId n == nameId n' then Yes primTrustMe else No



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


------------------------------------------------------------------ end of Lib

infixl 9 _∙_     -- non-dependent application
infixl 9 _∙∙_    -- dependent application
infixl 9 _$_     -- non-dependent application
infixl 9 _$$_    -- dependent application
infixr 8 _[_]_   -- operator syntax for Doc
infixr 8 _[_]m_  -- operator syntax for Doc
infixr 7 _×_     -- non-dependent pair type
infixr 6 _⊎_     -- non-dependent function type
infixr 5 _=>_    -- non-dependent function type
infixr 0 _,_     -- non-dependent pair constructor
infixr 0 _,,_    -- dependent pair constructor
infix -1 _:=_


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

{-# NO_POSITIVITY_CHECK #-}
data Lambda where
  Lam   : (Tm a -> LHS a') ->            Lambda (a => a')
  DLam  : ((x : Tm a) -> LHS (b ∙ x)) -> Lambda (Pi a b)
  Stuck :                                Lambda a

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
  C$    : ∀ {s : Spine (a => a')} {x} ->     Glued s Stuck ->                     Glued (s $  x) Stuck
  C$$   : ∀ {s : Spine (Pi a b)}  {x} ->     Glued s Stuck ->                     Glued (s $$ x) Stuck

lhs∙ : ∀ {s : Spine (a => a')} {f x} -> Glued s (Lam f) -> (r : _) -> f x ≈ r -> Tm a'
lhs∙ c (RHS   t) e = t
lhs∙ c (NoRHS t) e = Ne (CLam c e)

NeNU {l = Lam f} c ∙ x = lhs∙ c (f x) Refl
NeNU {l = Stuck} c ∙ x = Ne (C$ {x = x} c)

lhs∙∙ : ∀ {s : Spine (Pi a b)} {f x} -> Glued s (DLam f) -> (r : _) -> f x ≈ r -> Tm (b ∙ x)
lhs∙∙ c (RHS   t) e = t
lhs∙∙ c (NoRHS t) e = Ne (CDLam c e)

_∙∙_ : Tm  (Pi a b) -> (x : Tm a) -> Tm (b ∙ x)
NeNU {l = DLam f} c ∙∙ x = lhs∙∙ c (f x) Refl
NeNU {l = Stuck}  c ∙∙ x = Ne (C$$ c)


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

decTName : (n : TName a) (m : TName a') -> Dec (_≡_ {A = Ty ** TName} (_ ,, n) (_ ,, m))
decTName n m with decName (tName n) (tName m)
... | Yes _ = Yes primTrustMe
... | No    = No

---------------

_:=_ : TName a -> LHS a -> Tm a
n := RHS   t = t
n := NoRHS t = Ne (CHead (named (tName n) t))

pattern Lam'  f = NoRHS (Lam  f)
pattern DLam' f = NoRHS (DLam f)

var : TName a -> Tm a
var n = n := NoRHS Stuck


-----------------------

objEq : {x y : Tm a} -> x ≡ y -> Tm (Id x y)
objEq Refl = Refl


elimBot : (tm : Tm Bot) -> LHS a
elimBot (NeNU {l = Stuck} _) = NoRHS Stuck

elim× :
  (tm : Tm (a × a')) -> 
  ((x : Tm a) (y : Tm a') -> (x , y) ≡ tm -> LHS a'') ->
    LHS a''
elim× (x , y) f = f x y Refl
elim× (NeNU {l = Stuck} _) f = NoRHS Stuck

elimSigma :
  (tm : Tm (Sigma a b)) -> 
  ((x : Tm a) (y : Tm (b ∙ x)) -> (x ,, y) ≡ tm -> LHS a') ->
    LHS a'
elimSigma (x ,, y) f = f x y Refl
elimSigma (NeNU {l = Stuck} _) f = NoRHS Stuck

elimR : ∀ {rc ps a} ->
  (tm : Tm (Rec rc ps)) ->
  ((args : Tm (rFields rc ∙ ps)) -> Wrap args ≡ tm -> LHS a) ->
    LHS a
elimR (Wrap args) f = f args Refl
elimR (NeNU {l = Stuck} _) f = NoRHS Stuck

elimLet : ∀ {a a'} ->
  (tm : Tm a') ->
  ((x : Tm a') -> x ≡ tm -> LHS a) ->
    LHS a
elimLet x f = f x Refl

elim⊎ :
  (tm : Tm (a ⊎ a')) ->
  ((t : Tm a)  -> Left  t ≡ tm -> LHS a'') ->
  ((t : Tm a') -> Right t ≡ tm -> LHS a'') ->
    LHS a''
elim⊎ (Left  t) l r = l t Refl
elim⊎ (Right t) l r = r t Refl
elim⊎ (NeNU {l = Stuck} _) _ _ = NoRHS Stuck

elimId : {x y : Tm a} ->
  (tm : Tm (Id x y)) ->
  (_≡_ {A = Tm a ** \y -> Tm (Id x y)} (x ,, Refl) (y ,, tm) -> LHS a') ->
    LHS a'
elimId Refl f = f Refl
elimId (NeNU {l = Stuck} _) f = NoRHS Stuck

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

----------------------------------

lName : Nat -> TName a
lName i = MkTName (MkName "lam" i)

fst× : Tm (a × a') -> Tm a
fst× p = fst' ∙∙ _ ∙∙ _ ∙ p  where

  fstTT : Tm (U => U => U)
  fstTT = lName 0 := Lam' \a -> Lam' \a' -> RHS (a × a' => a)

  fstT : Tm (U => U)
  fstT = lName 1 := Lam' \a -> RHS (Pi U (fstTT ∙ a))

  fst' : Tm (Pi U fstT)
  fst' = MkTName (MkName "fst×" 2) := DLam' \a -> DLam' \a' -> Lam' \p -> elim× p \x y _ -> RHS x

snd× : Tm (a × a') -> Tm a'
snd× p = snd' ∙∙ _ ∙∙ _ ∙ p  where

  sndTT : Tm (U => U => U)
  sndTT = lName 3 := Lam' \a -> Lam' \a' -> RHS (a × a' => a')

  sndT : Tm (U => U)
  sndT = lName 4 := Lam' \a -> RHS (Pi U (sndTT ∙ a))

  snd' : Tm (Pi U sndT)
  snd' = MkTName (MkName "snd×" 5) := DLam' \a -> DLam' \a' -> Lam' \p -> elim× p \x y _ -> RHS y

-- \(a : U) -> (a -> U) -> U
aUU : Tm (U => U)
aUU = lName 6 := Lam' \a -> RHS ((a => U) => U)

fstΣ : Tm (Sigma a b) -> Tm a
fstΣ p = fst' ∙∙ _ ∙∙ _ ∙ p  where

  fstTT : Tm (Pi U aUU)
  fstTT = lName 7 := DLam' \a -> Lam' \b -> RHS (Sigma a b => a)

  fstT : Tm (U => U)
  fstT = lName 8 := Lam' \a -> RHS (Pi (a => U) (fstTT ∙∙ a))

  fst' : Tm (Pi U fstT)
  fst' = MkTName (MkName "fstΣ" 9) := DLam' \a -> DLam' \b -> Lam' \p -> elimSigma p \x y _ -> RHS x

sndLam : Tm (Sigma a b => U)
sndLam {b = b} = sndLam' ∙∙ _ ∙∙ b  where

  sndLamT' : Tm (Pi U aUU)
  sndLamT' = lName 10 := DLam' \a -> Lam' \b -> RHS (Sigma a b => U)

  sndLamT : Tm (U => U)
  sndLamT = lName 11 := Lam' \a -> RHS (Pi (a => U) (sndLamT' ∙∙ a))

  sndLam' : Tm (Pi U sndLamT)
  sndLam' = lName 12 := DLam' \a -> DLam' \b -> Lam' \p -> RHS (b ∙ fstΣ p)

sndΣ : (p : Tm (Sigma a b)) -> Tm (sndLam ∙ p)
sndΣ p = snd' ∙∙ _ ∙∙ _ ∙∙ p where

  sndT' : Tm (Pi U aUU)
  sndT' = lName 13 := DLam' \a -> Lam' \b -> RHS (Pi (Sigma a b) sndLam)

  sndT : Tm (U => U)
  sndT = lName 14 := Lam' \a -> RHS (Pi (a => U) (sndT' ∙∙ a))

  snd' : Tm (Pi U sndT)
  snd' = MkTName (MkName "sndΣ" 15) := DLam' \_ -> DLam' \_ -> DLam' \p -> elimSigma p \{x y Refl -> RHS y}

proj : ∀ {ps} -> Tm (Rec rc ps) -> Tm (rFields rc ∙ ps)
proj {rc = rc} t = proj' ∙∙ _ ∙ t  where

  projT : Tm (rParams rc => U)
  projT = lName 16 := Lam' \ps -> RHS (Rec rc ps => rFields rc ∙ ps)

  proj' : Tm (Pi (rParams rc) projT)
  proj' = MkTName (MkName "unwrap" 17) := DLam' \_ -> Lam' \t -> elimR t \t _ -> RHS t

-------------------------------------------------------

data Tys : Set          --  [] (A : U) (x : A) (y : A) (e : x ≡ y)

Tms : Tys -> Set        --  (((tt, Bool), True), True), Refl

infixl 3 _>>_::_
infixl 3 _>>>_

data Tys where
  []    :                                 Tys
  _>>t_ : (ts : Tys) -> (Tms ts -> Ty) -> Tys

Tms []         = T
Tms (ts >>t t) = Tms ts ** \xs -> Tm (t xs)

---------------

-- type depending on context
CTy : Tys -> Set
CTy ts = Tms ts -> Ty

-- term depending on context
CTm : (ts : Tys) -> CTy ts -> Set
CTm ts t = (xs : Tms ts) -> Tm (t xs)

---------------

data Ns : Tys -> Set where
  []    : Ns []
  _>>n_ : ∀ {ts t} -> (ns : Ns ts) -> (n : Name) -> Ns (ts >>t t)

private variable
  ts : Tys
  ns : Ns ts


TysN : Set
TysN = Tys ** Ns

_>>_::_ : ((ts ,, ns) : TysN) -> Name -> CTy ts -> TysN
_>>_::_ (ts ,, ns) n t = (ts >>t t) ,, (ns >>n n)


---------------

{-# TERMINATING #-}
⟦_,_⟧ᵤ : (ns : Ns ts) -> Ty -> CTy ts

⟦_,_⟧  : (ns : Ns ts) -> Tm a    -> CTm ts ⟦ ns , a ⟧ᵤ
⟦_,_⟧ₛ : (ns : Ns ts) -> Spine a -> CTm ts ⟦ ns , a ⟧ᵤ

postulate
  rParamsClosed : ∀ rc {ns} {xs : Tms ts} -> (⟦ ns , rParams rc ⟧ᵤ) xs ≈ rParams rc
  rFieldsClosed : ∀ rc {ns} {ps : Tm (rParams rc)} {xs : Tms ts} ->
    ⟦ ns , rFields rc ∙ ps ⟧ᵤ xs  ≈  rFields rc ∙ subst Tm (rParamsClosed rc) (⟦ ns , ps ⟧ xs)

⟦ _ , U         ⟧ᵤ = \_ -> U
⟦ _ , Top       ⟧ᵤ = \_ -> Top
⟦ _ , Bot       ⟧ᵤ = \_ -> Bot
⟦ ns , a => a'   ⟧ᵤ = \xs -> ae xs => ae' xs  where
  ae  = ⟦ ns , a  ⟧ᵤ
  ae' = ⟦ ns , a' ⟧ᵤ
⟦ ns , a × a'    ⟧ᵤ = \xs -> ae xs ×  ae' xs  where
  ae  = ⟦ ns , a  ⟧ᵤ
  ae' = ⟦ ns , a' ⟧ᵤ
⟦ ns , a ⊎ a'    ⟧ᵤ = \xs -> ae xs ⊎  ae' xs  where
  ae  = ⟦ ns , a  ⟧ᵤ
  ae' = ⟦ ns , a' ⟧ᵤ
⟦ ns , Pi a b    ⟧ᵤ = \xs -> Pi    (ae xs) (be xs) where
  ae = ⟦ ns , a ⟧ᵤ
  be = ⟦ ns , b ⟧
⟦ ns , Sigma a b ⟧ᵤ = \xs -> Sigma (ae xs) (be xs) where
  ae = ⟦ ns , a ⟧ᵤ
  be = ⟦ ns , b ⟧
⟦ ns , Id x y    ⟧ᵤ = \xs -> Id (xe xs) (ye xs) where
  xe = ⟦ ns , x ⟧
  ye = ⟦ ns , y ⟧
⟦ ns , Rec rc ps ⟧ᵤ = \xs -> Rec rc (subst Tm (rParamsClosed rc) (ps' xs)) where
  ps' = ⟦ ns , ps ⟧
⟦ ns , NU (NeU' {s = s} _) ⟧ᵤ = ⟦ ns , s ⟧ₛ

postulate
  TODO : P

⟦⟧ᵤ∙ : ∀ {a ns} (b : a =>U) {x : Tm a} (xs : Tms ts) -> ⟦ ns , b ∙ x ⟧ᵤ xs ≈ ⟦ ns , b ⟧ xs ∙ ⟦ ns , x ⟧ xs
⟦⟧ᵤ∙ = TODO

⟦⟧ᵤ[] : ⟦_,_⟧ᵤ {ts = []} [] a _ ≈ a
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

⟦_,_⟧ {a = U}    ns t          = ⟦ ns , t ⟧ᵤ
⟦_,_⟧ {a = NU _} ns TT         = \xs -> TT
⟦_,_⟧ {a = NU _} ns (x ,  y)   = \xs -> xe xs , ye xs where
  xe = ⟦ ns , x ⟧
  ye = ⟦ ns , y ⟧
⟦_,_⟧ {a = NU _} ns (_,,_ {b = b} x y) = \xs -> xe xs ,, subst Tm (⟦⟧ᵤ∙ b xs) (ye xs) where
  xe = ⟦ ns , x ⟧
  ye = ⟦ ns , y ⟧
⟦_,_⟧ {a = NU _} ns (Left  x)  = \xs -> Left  (xe xs) where
  xe = ⟦ ns , x ⟧
⟦_,_⟧ {a = NU _} ns (Right x)  = \xs -> Right (xe xs) where
  xe = ⟦ ns , x ⟧
⟦_,_⟧ {a = NU _} ns Refl       = \xs -> Refl
⟦_,_⟧ {a = NU _} ns (Wrap {rc = rc} args) = \xs -> Wrap (subst Tm (rFieldsClosed rc) (args' xs)) where
  args' = ⟦ ns , args ⟧
⟦_,_⟧ {a = NU _} ns (NeNU {s = s} _) = ⟦ ns , s ⟧ₛ

postulate
  nameIsDefined : TName a -> CTm ts ⟦ ns , a ⟧ᵤ
  weaken     : ∀ {n} {t : CTy ts} {xs : Tms ts} {x : Tm (t xs)} a -> ⟦ ns , a ⟧ᵤ xs ≈ ⟦_,_⟧ᵤ {ts = ts >>t t} (ns >>n n) a (xs ,, x)
  strengthen : ∀ {n} {t : CTy ts} {xs : Tms ts} {x : Tm (t xs)} a -> ⟦_,_⟧ᵤ {ts = ts >>t t} (ns >>n n) a (xs ,, x) ≈ ⟦ ns , a ⟧ᵤ xs
  thisIsIt : ∀ {a ts n ns} {t : CTy ts} {xs : Tms ts} {x : Tm (t xs)} -> Tm (t xs) ≈ Tm (⟦_,_⟧ᵤ {ts = ts >>t t} (ns >>n n) a (xs ,, x))
  b∙var⟦⟧ᵤ : ∀ {n} (b : a =>U) {xs : Tms ts} {x : Tm (⟦ ns , a ⟧ᵤ xs)} -> ⟦_,_⟧ᵤ {ts = ts >>t ⟦ ns , a ⟧ᵤ} (ns >>n tName n) (b ∙ var n) (xs ,, x) ≈ ⟦ ns , b ⟧ xs ∙ x

indexTms : ∀ {a ts ns} -> TName a -> CTm ts ⟦ ns , a ⟧ᵤ
indexTms {ts = []} {ns = ns} n = \_ -> var (coe TODO n) --nameIsDefined {ns = ns} n
indexTms {a = a} {ts = ts'@(ts >>t t)} {ns = ns'@(ns >>n n')} n with decName n' (tName n)
... | Yes _  = \(xs ,, x) -> coe TODO x --coe (thisIsIt {a = a} {ts = ts'} {n = tName n} {ns = ns'} {t = {!!}}) x
... | No     = \(xs ,, x) -> subst Tm (TODO {-weaken a-}) (f xs)
 where
  f = indexTms {a = a} {ts = ts} {ns = ns} n

postulate
  NamedLambdaClosed : {xs : Tms ts} -> NamedLambda (⟦ ns , a ⟧ᵤ xs) ≈ NamedLambda a
  closed : {xs : Tms ts} -> ⟦ ns , a ⟧ᵤ xs ≈ a


⟦ ns , Head {a = a} (named n Stuck) ⟧ₛ = indexTms {a = a} (MkTName n)
⟦ ns , Head h@(named _ (Lam  _))   ⟧ₛ = \xs -> subst Tm (sym closed) f where
  f = spineToTm (Head h)
⟦ ns , Head h@(named _ (DLam _))   ⟧ₛ = \xs -> subst Tm (sym closed) f where
  f = spineToTm (Head h)
⟦ ns , s $  x                      ⟧ₛ = \xs -> se xs ∙ xe xs where
  se = ⟦ ns , s ⟧ₛ
  xe = ⟦ ns , x ⟧
⟦ ns , DApp {b = b} s x Refl       ⟧ₛ = \xs -> subst Tm (sym (⟦⟧ᵤ∙ b xs)) (se xs ∙∙ xe xs) where
  se = ⟦ ns , s ⟧ₛ
  xe = ⟦ ns , x ⟧


----------------------------------
-- TODO: make it more efficient

NameMap : (Ty -> Set) -> Set

emptySM     : ∀ {P} -> NameMap P
insertSM    : ∀ {P} -> TName a -> P a -> NameMap P -> NameMap P
deleteSM    : ∀ {P} -> TName a ->        NameMap P -> NameMap P
lookupSM    : ∀ {P} -> TName a -> NameMap P -> Maybe (Ty ** P)
lookupSMStr : ∀ {P} -> String -> NameMap P -> Maybe (Ty ** \a -> Pair (TName a) (P a))

NameMap P = List (Ty ** \a -> Pair (TName a) (P a))

emptySM = []

insertSM s a m = (_ ,, s , a) :: m

deleteSM s [] = []
deleteSM s ((_ ,, n , x) :: sm) with decTName n s
... | Yes _ = deleteSM s sm
... | No    = (_ ,, n , x) :: deleteSM s sm

lookupSM s [] = Nothing
lookupSM s ((_ ,, n , x) :: sm) with decTName n s
... | Yes _ = Just (_ ,, x)
... | No    = lookupSM s sm

lookupSMStr s [] = Nothing
lookupSMStr s ((_ ,, n , x) :: sm) with eqString (nameStr (tName n)) s
... | True  = Just (_ ,, n , x)
... | False = lookupSMStr s sm


---------------------

data IsSigs : Tys -> Ty -> Set

sigsToTms : {ts : Tys} -> IsSigs ts a -> Tm a -> Tms ts

data IsSigs where
  IS[] : IsSigs [] Top
  IS>> : ∀ {t a} -> (is : IsSigs ts a) -> {f : _} -> (∀ {xs} -> f ∙ xs ≈ t (sigsToTms is xs)) -> IsSigs (ts >>t t) (Sigma a f)

sigsToTms IS[]        = \xs -> tt
sigsToTms (IS>> is e) = \xs -> f (fstΣ xs) ,, subst Tm e (sndΣ xs)  where
  f = sigsToTms is

IsSigs' : Tys -> Set
IsSigs' ts = Ty ** \a -> Pair (IsSigs ts a) (Tm a)

LCtx' : Set
LCtx' = Tys ** \ts -> Pair (Ns ts) (IsSigs' ts)

emptyLCtx' : LCtx'
emptyLCtx' = [] ,, [] , Top ,, IS[] , TT

addLCtx' : TName a -> Name -> LCtx' -> LCtx'
addLCtx' {a = a} n ln (ts ,, ns , aa ,, is , vars)
  = ts >>t t ,, ns >>n tName n , Sigma aa (MkTName ln := Lam' \xs -> RHS (t (ff xs))) ,, IS>> is Refl , vars ,, subst Tm TODO (var n)
 where
  t = ⟦ ns , a ⟧ᵤ
  ff = sigsToTms is


----------------------------------

Error : Set
Error = String

TyTm : Set
TyTm = Ty ** \a -> Tm a

Ctx : Set
Ctx = NameMap Tm

LCtx = NameMap \a -> Maybe (Tm a)

data FLHS : Ty -> Set

record TC (A : Set) : Set

Fill : Ty -> Set
Fill a = FLHS a -> TC TyTm -> TC TyTm

Fills = NameMap Fill

data Doc : Set

data Vec (A : Set) : Nat -> Set where
  []    : Vec A Zero
  _::V_ : ∀ {n} -> A -> Vec A n -> Vec A (Suc n)

PatternDef' : Nat -> Set
PatternDef' n = Vec Doc n -> Doc

PatternDef = Nat ** PatternDef'

Patterns = List (Pair String PatternDef)

ShowEnv = NameMap \_ -> Doc

record TCState : Set where
  pattern
  constructor MkTCState
  field
    counter   : Nat
    showEnv   : ShowEnv

open TCState

{-# NO_POSITIVITY_CHECK #-}
record TCEnv : Set where
  pattern
  constructor MkTCEnv
  field
    globalEnv : Ctx
    localEnv  : LCtx
    localEnv' : LCtx'
    fillEnv   : Fills
    patterns  : Patterns

open TCEnv

-- type checking monad
record TC A where
  coinductive
  field
    getTC : TCEnv -> TCState -> Either Error (Pair TCState A)

open TC

runTC : TC A -> Either Error A
runTC tc with getTC tc (MkTCEnv emptySM emptySM emptyLCtx' emptySM []) (MkTCState 100 emptySM)
... | Left  e       = Left e
... | Right (_ , r) = Right r

_>>=_ : TC A -> (A -> TC B) -> TC B
getTC (m >>= f) ctx c with getTC m ctx c
... | Left  e = Left e
... | Right (c , x) = getTC (f x) ctx c

pure : A -> TC A
getTC (pure x) _ c = Right (c , x)

fmap : (A -> B) -> TC A -> TC B
fmap f a = do
  a <- a
  pure (f a)

throwError : Error -> TC A
getTC (throwError e) _ _ = Left e

throwError' : TC Error -> TC A
throwError' s = do
  s <- s
  throwError s

newPPName : String -> TC String
getTC (newPPName s) ctx (MkTCState c se) = Right (MkTCState (Suc c) se , s ++ showNat c)

newPName : String -> TC Name
getTC (newPName s) ctx (MkTCState c se) = Right (MkTCState (Suc c) se , MkName s c)

newNameT : String -> TC (TName a)
newNameT s = do
  n <- newPName s
  pure (MkTName n)

addGlobal : TName a -> LHS a -> TC A -> TC A
getTC (addGlobal s d m) (MkTCEnv g l l' f p) = getTC m (MkTCEnv (insertSM s (s := d) g) l l' f p)

addLocal' : TName a -> Name -> TC A -> TC A
getTC (addLocal' n ln m) (MkTCEnv g l l' f p) = getTC m (MkTCEnv g (insertSM n Nothing l) (addLCtx' n ln l') f p)

addLocal : TName a -> TC A -> TC A
addLocal n m = do
  ln <- newPName "lam"
  addLocal' n ln m

addLocal'' : TName a -> Tm a -> TC A -> TC A
getTC (addLocal'' n t m) (MkTCEnv g l l' f p) = getTC m (MkTCEnv g (insertSM n (Just t) l) l' f p)

addFill : TName a -> Fill a -> TC A -> TC A
getTC (addFill s d m) (MkTCEnv g l l' f p) = getTC m (MkTCEnv g l l' (insertSM s d f) p)

delFill : TName a -> TC A -> TC A
getTC (delFill s m) (MkTCEnv g l l' f p) = getTC m (MkTCEnv g l l' (deleteSM s f) p)

lookupFill : String -> TC (Maybe (Ty ** \a -> Pair (TName a) (Fill a)))
getTC (lookupFill s) env c = Right (c , lookupSMStr s (fillEnv env))

addShow : TName a -> Doc -> TC T
getTC (addShow s d) e (MkTCState c se) = Right ((MkTCState c (insertSM s d se)) , tt)

delShow : TName a -> TC T
getTC (delShow s) e (MkTCState c se) = Right ((MkTCState c (deleteSM s se)) , tt)

lookupShow : TName a -> TC Bool
getTC (lookupShow s) env c with lookupSM s (showEnv c)
... | Just (_ ,, x) = Right (c , True)
... | Nothing       = Right (c , False)

getShows : TC ShowEnv
getTC getShows env c = Right (c , showEnv c)

futureTC : TName a -> (FLHS a -> TC A) -> TC A
futureTC n f = future \get set -> addFill n set (f get)

lookupFill' : String -> (Ty ** Fill -> TC A) -> TC A -> TC A
lookupFill' n cont err = do
  Just (_ ,, n , f) <- lookupFill n  where
    Nothing -> err
  delFill n (cont (_ ,, f))

locals : TC LCtx
getTC locals env c = Right (c , localEnv env)

locals' : TC LCtx'
getTC locals' env c = Right (c , localEnv' env)

lookupTm : String -> TC TyTm
getTC (lookupTm s) env c with lookupSMStr s (localEnv env)
... | Just (_ ,, n , Nothing)  = Right (c , (_ ,, var n))
... | Just (_ ,, n , Just t)   = Right (c , (_ ,, t))
... | Nothing with lookupSMStr s (globalEnv env)
...   | Just (_ ,, n , x)  = Right (c , (_ ,, x))
...   | Nothing = Left ("Not defined: " ++ s)

addPattern : String -> PatternDef -> TC A -> TC A
getTC (addPattern s d m) (MkTCEnv g l l' f p) = getTC m (MkTCEnv g l l' f ((s , d) :: p))

getPatterns : TC Patterns
getTC getPatterns env c = Right (c , patterns env)


instance
  TCString : IsString (TC String)
  TCString .IsString.Constraint s = T
  TCString .IsString.fromString s = pure s



-------------------------------------------------

data CharClass : Set where
  Alpha Graphic Punctuation InvalidChar : CharClass

charClass : Char -> CharClass
charClass '(' = Punctuation
charClass ')' = Punctuation
charClass '[' = Punctuation
charClass ']' = Punctuation
charClass '{' = Punctuation
charClass '}' = Punctuation
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
tokens True ('\n' :: '#' :: s) = skip s \a s -> do
  ts <- tokens True s
  pure (";" :: "FFI" :: stringFromList a :: ts)
 where
  skip : List Char -> (List Char -> List Char -> A) -> A
  skip ('\n' :: s) cont = cont [] ('\n' :: s)
  skip (c    :: s) cont = skip s \a s -> cont (c :: a) s
  skip []          cont = cont [] []
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

testTok = runTC (tokens' "\n\na\n a\n\nb\n# b\nc")

testTokens : runTC (tokens' "(a ++ bc)") ≡ Right ("(" :: "a" :: "++" :: "bc" :: ")" :: [])
testTokens = Refl

showTokens : List String -> String
showTokens [] = ""
showTokens (t :: ts) = t ++ " " ++ showTokens ts

----------------------------------

headCharClass : List Char -> CharClass
headCharClass (c :: _) = charClass c
headCharClass _ = InvalidChar

isAlphaToken : String -> Bool
isAlphaToken s with headCharClass (stringToList s)
... | Alpha = True
... | _     = False

operators : List String
operators = ";" :: "=" :: "|" :: "." :: ":" :: "::" :: "$" :: "=>" :: "@" :: "," :: "->" :: "==" :: "+" :: "*" :: []

isOperator : String -> Bool
isOperator s = any (eqString s) operators

keywords : List String
keywords
  =  "Bracket" :: "Brace" :: "pattern" :: "FFI" :: "U" :: "?"
-- type       constructor            eliminator  
---------------------------------------------------
  {- _->_ -}  {- _._ -}              {- _ _ -}
  :: "Pi"     {- _._ -}              {- _ _ -}
  {- _*_  -}  {- _,_ -}              {- _,_ -}
  :: "Sigma"  {- _,_ -}              {- _,_ -}
  {- _+_  -}  :: "Left" :: "Right"   :: "either"
  :: "Top"    :: "TT"                {- --- -}
  :: "Bot"    {- --- -}              :: "absurd"
  {- _==_ -}  :: "Refl"              :: "jRule" :: "kRule"
  :: "record" :: "Wrap"              {- Wrap -}
  :: []

isKeyword : String -> Bool
isKeyword s = any (eqString s) keywords

isVariable : String -> Bool
isVariable s = isAlphaToken s && not (isKeyword s)

data Doc where
  _$_   : Doc -> Doc ->                                          Doc
  FFI   : String ->                                              Doc
  KW'   : (s : String) -> {isKeyword s ≡ True} -> List Doc ->    Doc
  DVar' : (s : String) -> {isVariable s ≡ True} ->               Doc
  BinOp : Doc -> (s : String) -> {isOperator s ≡ True} -> Doc -> Doc

pattern KW s = KW' s {Refl} []
pattern _[_]_ a b c = BinOp a b {Refl} c
pattern DVar s = DVar' s {Refl}

_[_]m_ : TC Doc -> (s : String) -> {{isOperator s ≡ True}} -> TC Doc -> TC Doc
_[_]m_ a s {{isOp}} b = do
  a <- a
  b <- b
  pure (BinOp a s {isOp} b)

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
  go p (FFI s)      = s
  go p (DVar' "LL" $ DVar' n $ b) = parens (0 < p) ("\\" ++ n ++ " -> " ++ go 0 b)
  go p (KW' n args) = go p (foldr (\a b -> b $ a) (DVar' n {primTrustMe}) args)
  go p (DVar' n)    = n
  go p (a $ b)      = parens (q < p) (go q a ++ " " ++ go (Suc q) b) where
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

infixl 9 _$D_
infixl 9 _$Dm_
infixl 9 _$m_

_$D_ : Doc -> Doc -> Doc
KW' s {isKW} ds $D d = KW' s {isKW} (d :: ds)
a $D b = a $ b

_$Dm_ : TC Doc -> TC Doc -> TC Doc
a $Dm b = do
  a <- a
  b <- b
  pure (a $D b)

_$m_ : TC Doc -> TC Doc -> TC Doc
a $m b = do
  a <- a
  b <- b
  pure (a $ b)

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
  parseAtom r _ ("[" :: ts) = parseOps (\b -> expect "]" (r (KW' "Bracket" {Refl} (b :: [])))) ts
  parseAtom r _ ("{" :: ts) = parseOps (\b -> expect "}" (r (KW' "Brace" {Refl} (b :: [])))) ts
  parseAtom r z ("FFI" :: t :: ts) = r (FFI t) ts
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
{-
  mkLam : Doc -> Doc -> TC (Pair Doc Doc)
  mkLam d b = pure (d , b)
-}
  mkOp : (s : String) -> {isOperator s ≡ True} -> Doc -> Doc -> TC Doc
  mkOp "$" a b = pure (a $D b)
  mkOp "->" (bs $ (n [ ":" ] a)) b = mkOp "->" {Refl} bs (mkPi n a b)
  mkOp "->" (n [ ":" ] a) b = pure (mkPi n a b)
  mkOp "*" (bs $ (n [ ":" ] a)) b = mkOp "*" {Refl} bs (mkSigma n a b)
  mkOp "*" (n [ ":" ] a) b = pure (mkSigma n a b)
{-
  mkOp "." (ns $ n) b = do
    n , b <- mkLam n b
    mkOp "." {Refl} ns (n [ "." ] b)
  mkOp "." n b = do
    n , b <- mkLam n b
    pure (n [ "." ] b)
-}
  mkOp t {isOp} a b = pure (BinOp a t {isOp} b)

  addOp : (String ** \s -> isOperator s ≡ True) -> ((Doc -> X) -> X) -> (Doc -> X) -> X
  addOp op@(t ,, isOp) g r = g (f r) where

    f : (Doc -> X) -> Doc -> X
    f r a (t' :: ts) with eqString t' t
    ... | True  = addOp op g (\b ts -> mkOp t {isOp} a b >>= \o -> r o ts) ts
    ... | False = r a (t' :: ts)
    f r a ts = r a ts

  parseOps = foldr addOp parseApps (map (\s -> s ,, primTrustMe) operators)

testParse : runTC (parse "f (b a * c * e) d")
          ≡ Right (DVar "f" $ (DVar "b" $ DVar "a" [ "*" ] DVar "c" [ "*" ] DVar "e") $ DVar "d")
testParse = Refl

-------------------------------------

KWm : (s : String) -> {{isKeyword s ≡ True}} -> TC Doc
KWm s {{isKey}} = pure (KW' s {isKey} [])

printName' : Name -> Doc
printName' n = DVar' (pr (nameStr n)) {primTrustMe {- TODO -}}  where
  pr : String -> String
  pr "lam" = "lam" ++ showNat (nameId n)
  pr "v"   = "v"   ++ showNat (nameId n)
  pr n     = n

printName : Name -> TC Doc
printName n = pure (printName' n)

-------

data PrintMode : Set where
  NormalMode HsMode : PrintMode

isHsMode : PrintMode -> Bool
isHsMode HsMode = True
isHsMode _      = False

module Print (mode : PrintMode) where
 printTm    : Tm    a -> TC Doc
 printSpine : Spine a -> TC Doc

 printSpine (Head (named n Stuck)) = printName n
 printSpine {a = a} e@(Head (named n l)) = do
  _ <- do
    let n' = MkTName {a = a} n
    False <- lookupShow n'  where
      True -> pure tt
    _ <- addShow n' (DVar "IN_PROGRESS")
    e <- printTm (spineToTm e)
    _ <- delShow n'
    _ <- addShow (MkTName {a = a} n) e
    pure tt
  printName n
 printSpine (s $  x) = printSpine s $m printTm x
 printSpine (DApp {a = NU (NeU' {s = Head (named (MkName "Ty" _) Stuck)} _)} s x e)
   = if isHsMode mode
     then printSpine s
     else printSpine s -- $m printTm x   -- ???
 printSpine (s $$ x) = printSpine s $m printTm x

 {-# TERMINATING #-}
 printTm {a = U} U           = KWm "U"
 printTm {a = U} Top         = KWm "Top"
 printTm {a = U} Bot         = KWm "Bot"
 printTm {a = U} (a => a')   = printTm a [ "->" ]m printTm a'
 printTm {a = U} (a × a')    = printTm a [ "*"  ]m printTm a'
 printTm {a = U} (a ⊎ a')    = printTm a [ "+"  ]m printTm a'
 printTm {a = U} (Pi a b)    = KWm "Pi"      $Dm printTm a $Dm printTm b
 printTm {a = U} (Sigma a b) = KWm "Sigma"   $Dm printTm a $Dm printTm b
 printTm {a = U} (Id x y)    = printTm x [ "=="  ]m printTm y
 printTm {a = U} (Rec rc x)  = printName (name rc) $m printTm x
 printTm {a = U} (NU (NeU' {s = s} _)) = printSpine s
 printTm {a = a => a'} t = do
  n <- newNameT "v"
  printName (tName n) [ "." ]m printTm (t ∙ var n)
 printTm {a = Pi a b} t = do
  n <- newNameT "v"
  printName (tName n) [ "." ]m printTm (t ∙∙ var n)
 printTm {a = NU _} TT        = KWm "TT"
 printTm {a = NU _} (x ,  y)  = printTm x [ ","  ]m printTm y
 printTm {a = NU _} (x ,, y)  = printTm x [ ","  ]m printTm y
 printTm {a = NU _} (Left  x) = KWm "Left"  $Dm printTm x
 printTm {a = NU _} (Right x) = KWm "Right" $Dm printTm x
 printTm {a = NU _} Refl      = KWm "Refl"
 printTm {a = NU _} (Wrap {rc = rc} args) = KWm "Wrap" $Dm printTm args
 printTm {a = NU _} (NeNU {s = s} _) = printSpine s

----

printTm    : Tm    a -> TC Doc
printTm = Print.printTm HsMode  -- TODO

printSpine : Spine a -> TC Doc
printSpine = Print.printSpine HsMode  -- TODO

showTm : Tm a -> TC String
showTm t = do
  t <- printTm t
  pure (showDoc t)

showSpine : Spine a -> TC String
showSpine t = do
  t <- printSpine t
  pure (showDoc t)

_+++_ : TC String -> TC String -> TC String
a +++ b = do
  a <- a
  b <- b
  pure (a ++ b)

--------------------

showLocals : LCtx -> TC String
showLocals [] = ""
showLocals ((a ,, n , _) :: ls) = showLocals ls +++ "\n" +++ fmap showDoc (printName (tName n) [ ":" ]m printTm a)



----------------------------------

-- data Tm≈ : Tm a -> Tm a -> Prop where
--    TopEta : (x y : Tm Top) -> Tm≈ x y
--
-- postulate
--     coeTm : Tm≈ {a = U} a a' -> Tm a -> Tm a'

-- TODO: less cheating
postulate
  topEta   : {x y : Tm Top} -> x ≈ y
  pairEta  : {x y : Tm (a × a')} -> fst× x ≈ fst× y -> snd× x ≈ snd× y -> x ≈ y
  sigmaEta : {x y : Tm (Sigma a b)} -> _≈_ {A = Tm a ** \fst -> Tm (b ∙ fst)} (fstΣ x ,, sndΣ x) (fstΣ y ,, sndΣ y) -> x ≈ y
  recEta   : ∀ {ps} {x y : Tm (Rec rc ps)} -> proj x ≈ proj y -> x ≈ y
  idEta    : {x y : Tm a} {u v : Tm (Id x y)} -> u ≈ v
  arrEta   : ∀ {n} {x y : Tm (a => a')} -> x ∙  var n ≈ y ∙  var n -> x ≈ y    -- if n is fresh
  piEta    : ∀ {n} {x y : Tm (Pi a b)}  -> x ∙∙ var n ≈ y ∙∙ var n -> x ≈ y    -- if n is fresh

--------------------

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
    No -> throwError' (showTm a +++ "  =?=  " +++ showTm b)
  Refl <- convert x x'
  pure Refl
convert {a = U} (NU (NeU' {s = s} g)) (NU (NeU' {s = s'} g')) = do
  Refl <- convertSpine s s'
  pure (setEq (sym (glued g) ∘ glued g'))
convert {a = a => a'} x y = do
  n <- newNameT "v"
  e <- convert (x ∙ var n) (y ∙ var n)
  pure (setEq (arrEta (propEq e)))
convert {a = Pi a b} x y = do
  n <- newNameT "v"
  e <- convert (x ∙∙ var n) (y ∙∙ var n)
  pure (setEq (piEta (propEq e)))
convert {a = NU _} (NeNU {s = s} g) (NeNU {s = s'} g') = do
  Refl <- convertSpine s s'
  pure (setEq (sym (glued g) ∘ glued g'))
convert {a = a ⊎ a'} (Left  x) (Left  y) = do
  Refl <- convert x y
  pure Refl
convert {a = a ⊎ a'} (Right x) (Right y) = do
  Refl <- convert x y
  pure Refl
convert {a = Top} _ _ = pure (setEq topEta)
convert {a = a × a'} x y = do
  e1 <- convert (fst× x) (fst× y)
  e2 <- convert (snd× x) (snd× y)
  pure (setEq (pairEta (propEq e1) (propEq e2)))
convert {a = Sigma a b} x y = do
  e <- convert (fstΣ x) (fstΣ y)
  helper e (sndΣ x) Refl (sndΣ y) Refl
 where
  helper : ∀ {fstx fsty} -> fstx ≡ fsty ->
     (sx : Tm (b ∙ fstx)) -> _≈_ {A = Tm a ** \fst -> Tm (b ∙ fst)} (fstx ,, sx) (fstΣ x ,, sndΣ x) ->
     (sy : Tm (b ∙ fsty)) -> _≈_ {A = Tm a ** \fst -> Tm (b ∙ fst)} (fsty ,, sy) (fstΣ y ,, sndΣ y) ->
       TC (x ≡ y)
  helper Refl sx e3 sy e4 = do
    Refl <- convert sx sy
    pure (setEq (sigmaEta (sym e3 ∘ e4)))
convert {a = Rec rc ps} x y = do
  e <- convert (proj x) (proj y)
  pure (setEq (recEta (propEq e)))
convert {a = Id x y} _ _ = do
  pure (setEq idEta)
convert x y = throwError' (showTm x +++ "  =?=  " +++ showTm y)

convertSpine (Head l) (Head l') = do
  Yes Refl <- pure (decNamed l l') where
    No -> throwError ("convertSpineHead: " ++ showDoc (printName' (name l)) ++ " /= " ++ showDoc (printName' (name l')))
  pure Refl
convertSpine (s $ x) (s' $ x') = do
  Refl <- convertSpine s s'
  Refl <- convert x x'
  pure Refl
convertSpine (s $$ x) (s' $$ x') = do
  Refl <- convertSpine s s'
  Refl <- convert x x'
  pure Refl
convertSpine a b = throwError' ("convertSpine: " +++ showSpine a +++ " /= " +++ showSpine b)


----------------------------------

newTName : Doc -> TC (TName a)
newTName (DVar' n) = newNameT n
newTName d = throwError ("variable name expected instead of: " ++ showDoc d)

_>>>_ : (ts : TysN) -> TName a -> TysN
_>>>_ {a = a} (ts ,, ns) n = (ts >>t ⟦ ns , a ⟧ᵤ) ,, (ns >>n tName n)


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

--------------------

mkLam : TName a -> Tm a' -> TC (Tm (a => a'))
mkLam {a = a} {a' = a'} n e = do
  ts ,, ns , aa ,, is , vars <- locals'
  n1 <- newNameT "lam"
  n2 <- newNameT "lam"

  let e' : CTm (ts >>t ⟦ ns , a ⟧ᵤ) ⟦ ns >>n tName n , a' ⟧ᵤ
      e' = ⟦_,_⟧ {ts = ts >>t ⟦ ns , a ⟧ᵤ} (ns >>n tName n) e

      e'' : (xs : Tms (ts >>t ⟦ ns , a ⟧ᵤ)) -> Tm (⟦ ns , a' ⟧ᵤ (fst xs))
      e'' = coe TODO e'

      ff = sigsToTms is

      t = ⟦ ns , a => a' ⟧ᵤ

      up : Tm (Pi aa (n1 := Lam' \xs -> RHS (t (ff xs))))
      up = n2 := DLam' \xs -> Lam' \x -> RHS (e'' (ff xs ,, x))

  pure (coe TODO (up ∙∙ vars))

mkDLam : (n : TName a) -> Tm (b ∙ var n) -> TC (Tm (Pi a b))
mkDLam {a = a} {b = b} n e = do
  ts ,, ns , aa ,, is , vars <- locals'
  n1 <- newNameT "lam"
  n2 <- newNameT "lam"

  let e' : CTm (ts >>t ⟦ ns , a ⟧ᵤ) ⟦ ns >>n tName n , b ∙ var n ⟧ᵤ
      e' = ⟦_,_⟧ {ts = ts >>t ⟦ ns , a ⟧ᵤ} (ns >>n tName n) e

      e'' : ((xs ,, x) : Tms (ts >>t ⟦ ns , a ⟧ᵤ)) -> Tm (⟦ ns , b ⟧ xs ∙ x)
      e'' = coe TODO e'

      ff = sigsToTms is

      t = ⟦ ns , Pi a b ⟧ᵤ

      up : Tm (Pi aa (n1 := Lam' \xs -> RHS (t (ff xs))))
      up = n2 := DLam' \xs -> DLam' \x -> RHS (e'' (ff xs ,, x))

  pure (coe TODO (up ∙∙ vars))

------------------------


printGoal : List Doc -> Ty -> TC A


{-# TERMINATING #-}
infer : Doc -> TC TyTm

check : Doc -> (a : Ty) -> TC (Tm a)
check (KW' "Left" ds) (a ⊎ a') = do
  x <- firstArg ds
  x <- check x a
  pure (Left x)
check (KW' "Right" ds) (a ⊎ a') = do
  x <- firstArg ds
  x <- check x a'
  pure (Right x)
check (sn [ "." ] e) (a => a') = do
  n <- newTName sn
  e <- addLocal n (check e a')
  mkLam n e
check (sn [ "." ] e) (Pi a b)  = do
  n <- newTName sn
  e <- addLocal n (check e (b ∙ var n))
  mkDLam n e
check (x [ "," ] x') (a × a') = do
  x  <- check x  a
  x' <- check x' a'
  pure (x , x')
check (x [ "," ] y) (Sigma a b) = do
  x <- check x  a
  y <- check y (b ∙ x)
  pure (x ,, y)
check (KW' "Refl" ds) (Id x y) = do
  _ <- empty ds
  e <- convert x y
  pure (subst (\k -> Tm (Id x k)) (propEq e) Refl)
check (KW' "Wrap" ds) (Rec rc ps) = do
  x <- firstArg ds
  x <- check x (rFields rc ∙ ps)
  pure (Wrap x)
check (KW' "?" ds) a = printGoal ds a
check d a = do
  a' ,, t <- infer d
  Refl <- convert a' a
  pure t

infer (KW' "U" ds) = do
  _ <- empty ds
  pure (U ,, U)
infer (KW' "Bot" ds) = do
  _ <- empty ds
  pure (U ,, Bot)
infer (KW' "Top" ds) = do
  _ <- empty ds
  pure (U ,, Top)
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
infer (KW' "Pi" ds) = do
  b , ds <- getArg ds
  a <- firstArg ds
  a <- check a U
  b <- check b (a => U)
  pure (U ,, Pi a b)
infer (KW' "Sigma" ds) = do
  b , ds <- getArg ds
  a <- firstArg ds
  a <- check a U
  b <- check b (a => U)
  pure (U ,, Sigma a b)
infer (x [ "==" ] y) = do
  a ,, x <- infer x
  y <- check y a
  pure (U ,, Id x y)
infer (KW' "TT" ds) = do
  _ <- empty ds
  pure (Top ,, TT)
infer (x [ "," ] x') = do
  a  ,, x  <- infer x
  a' ,, x' <- infer x'
  pure (a × a' ,, (x , x'))
infer (f $ x) = infer f >>= matchPi  where
  matchPi : TyTm -> TC TyTm
  matchPi (a => a' ,, f) = do
    x <- check x a
    pure (a' ,, f ∙ x)
  matchPi (Pi a b ,, f) = do
    x <- check x a
    pure (b ∙ x ,, f ∙∙ x)
  matchPi (t ,, _) = throwError' ("matchPi: " +++ showTm t)
infer (DVar' n) = lookupTm n
infer d = throwError ("infer: " ++ showDoc d)


-------------------------------

-- \(a : U) -> a -> U
aU : Tm (U => U)
aU = lName 20 := Lam' \a -> RHS (a => U)

jPTy : Tm a -> Ty
jPTy x = jPTy' ∙∙ _ ∙ x  where

  jPTy2T : Tm (U => U)
  jPTy2T = lName 21 := Lam' \a -> RHS (a => a => U)

  jPTy2 : Tm (Pi U jPTy2T)
  jPTy2 = lName 22 := DLam' \a -> Lam' \x -> Lam' \y -> RHS (Id x y => U)

  jPTy' : Tm (Pi U aU)
  jPTy' = lName 23 := DLam' \a -> Lam' \x -> RHS (Pi a (jPTy2 ∙∙ a ∙ x))

kPTy : Tm a -> Ty
kPTy x = kPTy' ∙∙ _ ∙ x  where

  kPTy' : Tm (Pi U aU)
  kPTy' = lName 24 := DLam' \a -> Lam' \x -> RHS (Id x x => U)

-- first order representation of LHS
data FLHS where
  RHS         : Tm a ->                                   FLHS a
  Lam         : (n : TName a) -> FLHS a' ->               FLHS (a => a')
  DLam        : (n : TName a) -> FLHS (b ∙ var n) ->      FLHS (Pi a b)
  MatchPair   : (p : Tm (a × a'))    (n : TName a) (m : TName a')          -> TName (Id (var n ,  var m) p) -> FLHS a'' -> FLHS a''
  MatchSigma  : (p : Tm (Sigma a b)) (n : TName a) (m : TName (b ∙ var n)) -> TName (Id (var n ,, var m) p) -> FLHS a'' -> FLHS a''
  MatchEither : (p : Tm (a ⊎ a')) (n  : TName a ) -> TName (Id (Left  (var n )) p) -> FLHS a'' ->
                                  (n' : TName a') -> TName (Id (Right (var n')) p) -> FLHS a'' -> FLHS a''
  MatchRecord : ∀ {ps a} (p : Tm (Rec rc ps)) (n : TName (rFields rc ∙ ps)) -> TName (Id (Wrap (var n)) p) -> FLHS a -> FLHS a
  MatchBot    : Tm Bot -> FLHS a
  MatchJ      : ∀ {x y : Tm a} (tm : Tm (Id x y)) (P : Tm (jPTy x)) -> FLHS (P ∙∙ x ∙ Refl) -> FLHS (P ∙∙ y ∙ tm)
  MatchK      : ∀ {x   : Tm a} (tm : Tm (Id x x)) (P : Tm (kPTy x)) -> FLHS (P      ∙ Refl) -> FLHS (P      ∙ tm)
  MatchLet    : ∀ {a a'} (p : Tm a') (n : TName a') -> TName (Id (var n) p) -> FLHS a -> FLHS a

CLHS : (ts : Tys) -> CTy ts -> Set
CLHS ts t = (xs : Tms ts) -> LHS (t xs)

quoteLHS : {a : Ty} -> FLHS a -> ((ts ,, ns) : TysN) -> CLHS ts ⟦ ns , a ⟧ᵤ
quoteLHS (Lam {a = a} {a' = a'} n t) ts'@(ts ,, ns) = \xs -> Lam' \x -> t' (xs ,, x)
 where
  t' : ((xs ,, x) : Tms (ts >>t ⟦ ns , a ⟧ᵤ)) -> LHS (⟦ ns , a' ⟧ᵤ xs)
  t' = coe TODO (quoteLHS t (ts' >>> n))
quoteLHS (DLam {a = a} {b = b} n t) ts'@(ts ,, ns) = \xs -> DLam' \x -> t' (xs ,, x)
 where
  t' : ((xs ,, x) : Tms (ts >>t ⟦ ns , a ⟧ᵤ)) -> LHS (⟦ ns , b ⟧ xs ∙ x)
  t' = coe TODO (quoteLHS t (ts' >>> n))
quoteLHS (MatchPair {a = a} {a' = a2} {a'' = a''} p n n' n'' e) ts'@(ts ,, ns)
  = \xs -> elim× (p' xs) \{x x' ee ->
       subst LHS (strengthen a'' ∘ strengthen a'' ∘ strengthen a'') (t' (((xs ,, x) ,, x') ,, objEq ee))
     }
 where
  p'  = ⟦ ns , p ⟧
  a2' = ⟦ ns , a2 ⟧
  t'  = quoteLHS e (ts' >>> n >> tName n' :: (\(xs' ,, _) -> a2' xs') >> tName n'' :: (\((xs' ,, y) ,, y') -> Id (y , y') (p' xs')))
quoteLHS (MatchSigma {a = a} {b = b} {a'' = a''} p n n' n'' e) ts'@(ts ,, ns)
  = \xs -> elimSigma (p' xs) \{x x' ee ->
       subst LHS (strengthen a'' ∘ strengthen a'' ∘ strengthen a'') (t' (((xs ,, x) ,, x') ,, objEq ee))
     }
 where
  p' = ⟦ ns , p ⟧
  t' = quoteLHS e (ts' >>> n >> tName n' :: (\(xs' ,, y) -> ⟦ ns , b ⟧ xs' ∙ y) >> tName n'' :: (\((xs' ,, y) ,, y') -> Id (y ,, y') (p' xs')))
quoteLHS (MatchEither {a = a} {a' = a'} {a'' = a''} p n k e n' k' e') ts'@(ts ,, ns)
  = \xs -> elim⊎ (p' xs)
     (\x ee -> subst LHS (strengthen a'' ∘ strengthen a'') (t1 ((xs ,, x) ,, objEq ee)))
     (\x ee -> subst LHS (strengthen a'' ∘ strengthen a'') (t2 ((xs ,, x) ,, objEq ee)))
 where
  p' = ⟦ ns , p ⟧
  t1 = quoteLHS e  (ts' >>> n  >> tName k  :: (\(xs' ,, y) -> Id (Left  y) (p' xs')))
  t2 = quoteLHS e' (ts' >>> n' >> tName k' :: (\(xs' ,, y) -> Id (Right y) (p' xs')))
quoteLHS (MatchRecord {rc = rc} {ps = ps} {a = a} p n k e) ts'@(ts ,, ns)
  = \xs -> elimR {rc = rc} (p' xs) \x ee ->
       subst LHS (strengthen a ∘ strengthen a) (t' ((xs ,, subst Tm (sym (rFieldsClosed rc)) x) ,, objEq (subst (\k -> Wrap k ≡ p' xs) TODO ee)))
 where
  p' = ⟦ ns , p ⟧
  t' = quoteLHS e (ts' >>> n >> tName k :: (\(xs' ,, y) -> Id (Wrap (subst Tm (rFieldsClosed rc) y)) (p' xs')))
quoteLHS (MatchLet {a = a} {a' = a'} p n k e) ts'@(ts ,, ns)
  = \xs -> elimLet (p' xs) \x ee ->
       subst LHS (strengthen a ∘ strengthen a) (t' ((xs ,, x) ,, objEq ee))
 where
  p' = ⟦ ns , p ⟧
  t' = quoteLHS e (ts' >>> n >> tName k :: (\(xs' ,, y) -> Id y (p' xs')))
quoteLHS (MatchBot p) ts
  = \xs -> elimBot p
quoteLHS (MatchJ tm p lhs) ts'@(ts ,, ns)
  = \xs -> subst LHS TODO (jRule (tm' xs) (\y e -> p' xs ∙∙ y ∙ e) (subst LHS TODO (lhs' xs)))
 where
  p'   = ⟦ ns , p ⟧
  tm'  = ⟦ ns , tm ⟧
  lhs' = quoteLHS lhs ts'
quoteLHS (MatchK tm p lhs) ts'@(ts ,, ns)
  = \xs -> subst LHS TODO (kRule (tm' xs) (\e -> p' xs ∙ e) (subst LHS TODO (lhs' xs)))
 where
  p'   = ⟦ ns , p ⟧
  tm'  = ⟦ ns , tm ⟧
  lhs' = quoteLHS lhs ts'
quoteLHS (RHS t) (ts ,, ns) = \xs -> RHS (t' xs)
 where
  t' = ⟦ ns , t ⟧

quoteFLHS : FLHS a -> LHS a
quoteFLHS t = subst LHS ⟦⟧ᵤ[] (quoteLHS t ([] ,, []) tt)

newTName' : Doc -> TC (Pair (TName a) Doc)
newTName' (n [ "." ] d) = do
  n <- newTName n
  pure (n , d)
newTName' d = throwError ("lambda expected instead of: " ++ showDoc d)

getArg' : List Doc -> TC (Pair (TName a) (List Doc))
getArg' (n :: ds) = do
  n <- newTName n
  pure (n , ds)
getArg' [] = throwError "not enough arguments"

optEq : Doc -> Pair Doc Doc
optEq (a [ "@" ] b) = (a , b)
optEq  a            = (a , DVar "_")

----------------------------------------

decTm : (n : Tm a) (m : Tm a') -> Dec (_≡_ {A = Ty ** Tm} (_ ,, n) (_ ,, m))

-- TODO: merge with convertSpine
decSpine : (s : Spine a) (s' : Spine a') -> Dec (_≡_ {A = Ty ** Spine} (a ,, s) (a' ,, s'))
decSpine (Head x) (Head x') with decNamed x x'
... | No = No
... | Yes Refl = Yes Refl
decSpine (s $ x) (s' $ x') with decSpine s s'
... | No = No
... | Yes Refl with decTm x x'
...   | No = No
...   | Yes Refl = Yes Refl
-- decSpine (DApp s x x₁) s' = {!!}  -- TODO
decSpine _ _ = No

-- TODO: merge with convert
decTm {a = U} {a' = U} (NU (NeU' {s = s} _)) (NU (NeU' {s = s'} _)) with decSpine s s'
... | No = No
... | Yes e = Yes (setEq TODO)
decTm {a = NU _} {a' = NU _} (NeNU {s = s} _) (NeNU {s = s'} _) with decSpine s s'
... | No = No
... | Yes e = Yes (setEq TODO)
decTm _ _ = No

---------------------------------------------- pattern match compilation

{-
f =
  { a , b . TT . Left x .  b , a
  }

f =
  \i j k ->
  [ i = "a , b",  j = "TT";  k =  "Left x"        ,  "b , a"
  ]

f =
  \i j k -> matchPair i \u v ->
  [ u = "a" , v = "b",  j = "TT";  k =  "Left x"        ,  "b , a"
  ]

f =
  \i j k -> matchPair i \u v -> let a = u in let b = v in
  [ k =  "Left x"        ,  "b , a"
  ]

f =
  \i j k -> matchPair i \u v -> let a = u in let b = v in
            matchEither k
              (\w -> let x = w in b , a
              )
              (\w -> impossible
              )

g = \i ->
  [ half i = "Left TT , b" , "... b ..."
  , half i = "Right TT , b" , "... b ..."
  ]

g = \i -> matchPair (half i) \u w ->
  [ u = "Left TT" , v = "b" , "... b ..."
  , u = "Right TT" , v = "b" , "... b ..."
  ]

g = \i -> matchPair (half i) \u w -> matchEither u
    (\w -> let b = v in ... b ...)
    (\w -> let b = v in ... b ...)


f (S (S (S (S ... (S n))))) = ....
f n = ... n ...

f = \n -> matchEither n
   (\_ -> ... n ...)
   (\k -> matchEither k
     (\_ -> ... n ...)
     (\k -> matchEither k
       (\_ -> ... n ...)
       (\k -> matchEither k
           ...
   )))

--  half : a -> a'
--  a ~ typeOf i

-}

record PEq : Set where
  pattern
  constructor MkPE
  field
    pKey : TyTm
    pDoc : Doc

PMRow = List PEq

PM = List (Pair PMRow Doc)

addPE : TyTm -> Doc -> PMRow -> PMRow
addPE k (DVar' dn {isVar} [ "@" ] d) e = addPE k (DVar' dn {isVar}) (addPE k d e)
addPE k d e = MkPE k d :: e

---------

RowTr : Ty -> Set
RowTr a = Tm a -> Doc -> Maybe (Maybe PMRow)

mapPMRow : RowTr a -> Tm a -> PMRow -> TC (Maybe PMRow)
mapPMRow f p [] = pure (Just [])
mapPMRow f p (r :: rs) = do
  Just r <- ff f p r where
    _ -> pure Nothing
  Just rs <- mapPMRow f p rs where
    _ -> pure Nothing
  pure (Just (r ++L rs))
 where
  ff : RowTr a -> Tm a -> PEq -> TC (Maybe PMRow)
  ff f a p@(MkPE (_ ,, a') d) with decTm a a'
  ... | No = pure (Just (p :: []))
  ... | Yes Refl with f a d
  ...   | Nothing = pure (Just (p :: []))
  ...   | Just r  = pure r

mapPM : RowTr a -> Tm a -> PM -> TC PM
mapPM f p [] = pure []
mapPM f p ((r , d) :: rs) = do
  Just r <- mapPMRow f p r where
    _ -> mapPM f p rs
  rs <- mapPM f p rs
  pure ((r , d) :: rs)

takeOutRow : PMRow -> Maybe (Pair PEq (PMRow -> PMRow))
takeOutRow (e@(MkPE _ (DVar' d)) :: es) = Just (e , \x -> x ++L es)
takeOutRow (e@(MkPE _ (f [ "->" ] d)) :: es) = Just (e , \x -> x ++L es)
takeOutRow _ = Nothing

takeOut : PM -> Maybe (Pair PEq (PMRow -> PM))
takeOut [] = Nothing
takeOut ((r , d) :: rs) with takeOutRow r
... | Just (e , f) = Just (e , \x -> (f x , d) :: rs)
... | Nothing with takeOut rs
...   | Just (e , f) = Just (e , \x -> (r , d) :: f x)
...   | Nothing       = Nothing

nameHint : String -> Doc -> String
nameHint _ (DVar' n) = n
nameHint _ (DVar' n [ "@" ] _) = n
nameHint n _ = n


{-# TERMINATING #-}
checkLHS : Doc -> (a : Ty) -> TC (FLHS a)

pm' : PM -> (a : Ty) -> TC (FLHS a)

pm : PM -> (a : Ty) -> TC (FLHS a)
pm rs a with takeOut rs
... | Just (MkPE (_ ,, n) (DVar' d) , rs) = do
  d <- newNameT d
  addLocal'' d n (pm (rs []) a)
... | Just (MkPE (a'' ,, n) (f [ "->" ] d) , rs) = do
  a' => _ ,, f <- infer f where
    Pi a' _ ,, f -> do
      Refl <- convert a'' a'
      pm (rs (addPE (_ ,, f ∙∙ n) d [])) a
    _ -> throwError "pm view"
  Refl <- convert a'' a'
  pm (rs (addPE (_ ,, f ∙ n) d [])) a
... | _ = pm' rs a

pmEither : Tm (a' ⊎ a'') -> PM -> Doc -> Doc -> (a : Ty) -> TC (FLHS a)
pmEither p' d di dj aa = do
  n  <- newNameT (nameHint "i" di)
  k  <- newNameT "_"
  d1 <- mapPM (left'' (var n)) p' d
  e  <- addLocal n  (addLocal k  (pm d1 aa))
  n' <- newNameT (nameHint "j" dj)
  k' <- newNameT "_"
  d2 <- mapPM (right'' (var n')) p' d
  e' <- addLocal n' (addLocal k' (pm d2 aa))
  pure (MatchEither p' n k e n' k' e')
 where
  left'' : Tm a -> RowTr (a ⊎ a')
  left'' b _ (KW' "Left" (d2 :: [])) = Just (Just (addPE (_ ,, b) d2 []))
  left'' b _ (KW' "Right" (_ :: []))         = Just Nothing
  left'' b _ d = Nothing

  right'' : Tm a' -> RowTr (a ⊎ a')
  right'' b _ (KW' "Right" (d2 :: [])) = Just (Just (addPE (_ ,, b) d2 []))
  right'' b _ (KW' "Left" (_ :: []))           = Just Nothing
  right'' _ _ d = Nothing

pm' d@((MkPE (Id x y ,, p) (KW' "Refl" []) :: _ , _) :: _) aa =
  throwError "TODO Refl pattern match"

pm' d@((MkPE (Bot ,, p) (KW' "absurd" []) :: _ , _) :: _) aa = do
  pure (MatchBot p)

pm' d@((MkPE (Top ,, p) (KW' "TT" []) :: _ , _) :: _) aa = do
  d <- mapPM tt' p d
  pm d aa
 where
  tt' : RowTr Top
  tt' _ (KW' "TT" []) = Just (Just [])
  tt' _ _ = Nothing
 
pm' d@((MkPE (a × a' ,, p') (u [ "," ] v) :: _ , _) :: _) aa = do
  n   <- newNameT (nameHint "u" u)
  n'  <- newNameT (nameHint "v" v)
  n'' <- newNameT "_"
  d <- mapPM (pair'' (var n) (var n')) p' d
  e <- addLocal n (addLocal n' (addLocal n'' (pm d aa)))
  pure (MatchPair p' n n' n'' e)
 where
  pair'' : Tm a -> Tm a' -> RowTr (a × a')
  pair'' b c _ (d1 [ "," ] d2) = Just (Just (addPE (_ ,, b) d1 (addPE (_ ,, c) d2 [])))
  pair'' _ _ _ _ = Nothing

pm' d@((MkPE (Sigma a b ,, p') (u [ "," ] v) :: _ , _) :: _) aa = do
  n   <- newNameT (nameHint "u" u)
  n'  <- newNameT (nameHint "v" v)
  n'' <- newNameT "_"
  d <- mapPM (pair'' (var n) (var n')) p' d
  e <- addLocal n (addLocal n' (addLocal n'' (pm d aa)))
  pure (MatchSigma p' n n' n'' e)
 where
  pair'' : (x : Tm a) -> Tm (b ∙ x) -> RowTr (Sigma a b)
  pair'' b c _ (d1 [ "," ] d2) = Just (Just (addPE (_ ,, b) d1 (addPE (_ ,, c) d2 [])))
  pair'' _ _ _ _ = Nothing

pm' d@((MkPE p@(a ⊎ a' ,, p') (KW' "Left"  (di :: [])) :: _ , _) :: _) aa = pmEither p' d di (DVar "j") aa
pm' d@((MkPE p@(a ⊎ a' ,, p') (KW' "Right" (dj :: [])) :: _ , _) :: _) aa = pmEither p' d (DVar "i") dj aa

pm' d@((MkPE p@(Rec rc ps ,, p') (KW' "Wrap" (w :: [])) :: _ , _) :: _) aa = do
  n <- newNameT (nameHint "w" w)
  k <- newNameT "_"
  d <- mapPM (wrap'' (var n)) p' d
  e  <- addLocal n (addLocal k (pm d aa))
  pure (MatchRecord p' n k e)
 where
  wrap'' : Tm (rFields rc ∙ ps) -> RowTr (Rec rc ps)
  wrap'' b _ (KW' "Wrap" (d2 :: [])) = Just (Just (addPE (_ ,, b) d2 []))
  wrap'' _ _ d = Nothing

pm' (([] , d) :: _) aa = checkLHS d aa   -- TODO: warning if _ is not []?
pm' ((MkPE (a ,, n) d :: _ , _) :: _) aa = throwError' ("pm': " +++ showTm n +++ " : " +++ showTm a +++ " -- " +++ pure (showDoc d))
pm' _ aa = throwError' ("pm': " +++ showTm aa)

mkPM : Doc -> TC PM
mkPM (a [ ";" ] b) = do
  pm <- mkPM b
  pure (([] , a) :: pm)
mkPM a = pure (([] , a) :: [])

lookup : String -> List (Pair String A) -> Maybe A
lookup s [] = Nothing
lookup s ((s' , p) :: ps) with eqString s s'
... | False = lookup s ps
... | True  = Just p

findPattern : String -> Patterns -> Maybe PatternDef
findPattern = lookup

getApps : Doc -> Maybe (Pair String (Nat ** Vec Doc))
getApps d = getApps' d \s vs -> Just (s , vs) where
  getApps' : Doc -> (String -> Nat ** Vec Doc -> Maybe (Pair String (Nat ** Vec Doc))) -> Maybe (Pair String (Nat ** Vec Doc))
  getApps' (DVar' n) cont = cont n (_ ,, [])
  getApps' (f $ d) cont = getApps' f \h (_ ,, args) -> cont h (_ ,, d ::V args)
  getApps' _ cont = Nothing

getApps' : List Doc -> Maybe (List String)
getApps' [] = Just []
getApps' (DVar' n :: ds) with getApps' ds
... | Nothing = Nothing
... | Just ds = Just (n :: ds)
getApps' _ = Nothing


replace : List (Pair String Doc) -> Doc -> Doc
replace env d@(DVar' n) with lookup n env
... | Nothing = d
... | Just d  = d
replace env (KW' n {isOp} ds) = KW' n {isOp} (map (replace env) ds)
replace env (d $ d') = replace env d $ replace env d'
replace env (FFI x) = FFI x
replace env (BinOp d s {isOp} d') = BinOp (replace env d) s {isOp} (replace env d')

vecToList : ∀ {n} -> Vec A n -> List A
vecToList [] = []
vecToList (x ::V xs) = x :: vecToList xs

listToVec : List A -> Nat ** Vec A
listToVec [] = _ ,, []
listToVec (a :: as) with listToVec as
... | _ ,, as = _ ,, a ::V as

zipWith : ∀ {n} -> (A -> B -> C) -> Vec A n -> Vec B n -> Vec C n
zipWith f [] [] = []
zipWith f (a ::V as) (b ::V bs) = f a b ::V zipWith f as bs

compilePatSym : ∀ {n} -> Vec String n -> Doc -> Vec Doc n -> Doc
compilePatSym ss d ds = replace (vecToList (zipWith _,_ ss ds)) d

mapVec : ∀ {n} -> (A -> TC B) -> Vec A n -> TC (Vec B n)
mapVec f [] = pure []
mapVec f (a ::V as) = do
  b <- f a
  bs <- mapVec f as
  pure (b ::V bs)

mapM : (A -> TC B) -> List A -> TC (List B)
mapM f [] = pure []
mapM f (a :: as) = do
  b <- f a
  bs <- mapM f as
  pure (b :: bs)

unfoldPatterns : Patterns -> Doc -> TC Doc
unfoldPatterns pts (a [ "->" ] b) = do
  b <- unfoldPatterns pts b
  pure (a [ "->" ] b)
unfoldPatterns pts (BinOp a n {isOp} b) = do
  a <- unfoldPatterns pts a
  b <- unfoldPatterns pts b
  pure (BinOp a n {isOp} b)
unfoldPatterns pts (KW' n {isOp} ds) = do
  ds <- mapM (unfoldPatterns pts) ds
  pure (KW' n {isOp} ds)
unfoldPatterns pts d with getApps d
... | Nothing = pure d
... | Just (s , n ,, args) with findPattern s pts
...   | Nothing = pure d --throwError ("can't find " ++ s ++ " " ++ foldr _++_ "" (map (\{(n , _) -> n}) pts))
...   | Just (n' ,, p) with decNat n n'
...     | No = throwError "uff"
...     | Yes Refl = do
  args <- mapVec (unfoldPatterns pts) args
  pure (p args)

lamPM : TyTm -> PM -> TC PM
lamPM _ [] = pure []
lamPM n ((ps , p [ "." ] rhs) :: rs) = do
  rs <- lamPM n rs
  pts <- getPatterns
  p <- unfoldPatterns pts p
  pure (((ps ++L addPE n p []) , rhs) :: rs)
lamPM _ _ = throwError "lamPM"


initPM : PM -> (a : Ty) -> TC (FLHS a)
initPM d@((_ , p [ "." ] _) :: _) (a => a') = do
  n <- newNameT (nameHint "x" p)
  p <- lamPM (_ ,, var n) d
  t <- addLocal n (initPM p a')
  pure (Lam n t)
initPM d@((_ , p [ "." ] _) :: _) (Pi a b) = do
  n <- newNameT (nameHint "x" p)
  p <- lamPM (_ ,, var n) d
  t <- addLocal n (initPM p (b ∙ var n))
  pure (DLam n t)
initPM d a = pm d a

checkLHS (KW' "Brace" (d :: [])) aa = do
  d <- mkPM d
  initPM d aa
checkLHS (n [ "." ] t) (a => a') = do
--  n , t <- mkLam' n t
  n <- newTName n
  t <- addLocal n (checkLHS t a')
  pure (Lam n t)
checkLHS (n [ "." ] t) (Pi a b) = do
--  n , t <- mkLam' n t
  n <- newTName n
  t <- addLocal n (checkLHS t (b ∙ var n))
  pure (DLam n t)
checkLHS ((p [ "=>" ] ds) $ e) a'' = checkMatch (optEq ds) a''
 where
  checkMatch : Pair Doc Doc -> (a : Ty) -> TC (FLHS a)
  checkMatch (KW' "Wrap" ds , k) a'' = do
    n <- firstArg ds
    Rec rc ps ,, p <- infer p where  
      r ,, _ -> throwError' ("unwrap: " +++ showTm r)
    n <- newTName n
    k <- newTName k
    e  <- addLocal n (addLocal k (checkLHS e a''))
    pure (MatchRecord p n k e)
  checkMatch (n [ "," ] n' , n'') a'' = do
    _ × _ ,, p <- infer p where
      Sigma _ _ ,, p -> do
        n   <- newTName n
        n'  <- newTName n'
        n'' <- newTName n''
        e <- addLocal n (addLocal n' (addLocal n'' (checkLHS e a'')))
        pure (MatchSigma p n n' n'' e)
      r ,, _ -> throwError' ("pair: " +++ showTm r)
    n   <- newTName n
    n'  <- newTName n'
    n'' <- newTName n''
    e <- addLocal n (addLocal n' (addLocal n'' (checkLHS e a'')))
    pure (MatchPair p n n' n'' e)
  checkMatch _ _ = throwError "checkMatch"
checkLHS (KW' "either" ds) a'' = do
  e' , ds <- getArg ds
  e  , ds <- getArg ds
  p <- firstArg ds
  _ ⊎ _ ,, p <- infer p where
    r ,, _ -> throwError' ("either: " +++ showTm r)
  n , e <- newTName' e
  k , e <- newTName' e
  e <- addLocal n (addLocal k (checkLHS e a''))
  n' , e' <- newTName' e'
  k' , e' <- newTName' e'
  e' <- addLocal n' (addLocal k' (checkLHS e' a''))
  pure (MatchEither p n k e n' k' e')
checkLHS (KW' "absurd" ds) a'' = do
  p <- firstArg ds
  Bot ,, p <- infer p where
    r ,, _ -> throwError' ("absurd: " +++ showTm r)
  pure (MatchBot p)
checkLHS (KW' "jRule" ds) a'' = do
  w , ds <- getArg ds
  P , ds <- getArg ds
  e      <- firstArg ds
  NU (Id' x y) ,, e <- infer e  where
    r ,, _ -> throwError' ("jRule: " +++ showTm r)
  P <- check P (jPTy x)
  Refl <- convert a'' (P ∙∙ y ∙ e)
  w <- checkLHS w (P ∙∙ x ∙ Refl)
  pure (MatchJ e P w)
checkLHS (KW' "kRule" ds) a'' = do
  w , ds <- getArg ds
  P , ds <- getArg ds
  e      <- firstArg ds
  NU (Id' x y) ,, e <- infer e  where
    r ,, _ -> throwError' ("kRule: " +++ showTm r)
  Refl <- convert x y
  P <- check P (kPTy x)
  Refl <- convert a'' (P ∙ e)
  w <- checkLHS w (P ∙ Refl)
  pure (MatchK e P w)
checkLHS d a = do
  t <- check d a
  pure (RHS t)

addFFI : String -> TC T
addFFI s = addShow (MkTName {a = Top} (MkName "FFI" 0)) (FFI s)

compPatSym : List Doc -> Doc -> TC A -> TC A
compPatSym (DVar' n :: ps) d m with getApps' ps
...   | Nothing = throwError "pattern"
...   | Just ps with listToVec ps
...     | i ,, ps = addPattern n (i ,, compilePatSym ps d) m
compPatSym _ _ _  = throwError "pattern"

inferTop : Doc -> TC TyTm
inferTop ((KW' "pattern" ps [ "=" ] d) [ ";" ] ds) = compPatSym (reverse ps) d (inferTop ds)
inferTop (FFI hs [ ";" ] ds) = do
  _ <- addFFI hs
  inferTop ds
inferTop (((n [ ":" ] a) [ "=" ] t) [ ";" ] ds) = do
  a <- check a U
  n <- newTName n
  t <- checkLHS t a
  addGlobal n (quoteFLHS t) (inferTop ds)
inferTop ((n [ "=" ] KW' "record" ds) [ ";" ] ds') = do
  fs , ds <- getArg ds
  ps <- firstArg ds
  ps <- check ps U
  dn <- newTName n
  fs <- check fs (ps => U)
  let desc = named (tName dn) (Record ps fs)
  addGlobal dn (Lam' \x -> RHS (Rec desc x)) (inferTop ds')
inferTop ((n [ ":" ] a) [ ";" ] ds) = do
  a <- check a U
  n <- newTName {a = a} n
  futureTC n \t' -> addGlobal n (quoteFLHS t') (inferTop ds)
inferTop ((n [ "::" ] a) [ ";" ] ds) = do
  a <- check a U
  n <- newTName {a = a} n
  addGlobal n (NoRHS Stuck) (inferTop ds)
inferTop ((DVar' n [ "=" ] t) [ ";" ] ds) = do
  lookupFill' n (\(a ,, fill) -> do
    t <- checkLHS t a
    fill t (inferTop ds)
   ) (do
    a ,, t <- infer t
    n <- newNameT n
    addGlobal n (RHS t) (inferTop ds)
   )
inferTop (t [ ":" ] a) = do
  a <- check a U
  t <- check t a
  pure (a ,, t)
inferTop t = infer t

tc : String -> Either Error TyTm
tc s = runTC (parse s >>= inferTop)

data IsRight {A B : Set} : Either A B -> Set where
  instance YesR : {r : B} -> IsRight (Right r)

getRight : (s : Either A B) -> {{IsRight s}} -> B
getRight s {{YesR {r = r}}} = r

tc' : (s : String) -> {{IsRight (tc s)}} -> TyTm
tc' s = getRight (tc s)

--------
{-
testTC : tc' "f : Top -> U  = x. Top;  U : U"
       ≡ (U ,, U)
testTC = Refl

testTC3 : tc' "id : U -> U  = x. x;  id U : U"
       ≡ (U ,, U)
testTC3 = Refl

testTC4 : tc' "idFun : U -> U  = A. A -> A;  id : Pi U idFun  = A. x. x;  id U U : U"
       ≡ (U ,, U)
testTC4 = Refl
-}
renderHS : Doc -> Doc
renderHS (FFI s) = FFI s
renderHS (f $ x) = renderHS f $ renderHS x
renderHS d@(KW' s x) = d
renderHS d@(DVar' s) = d
renderHS (a [ "." ] b) = DVar "LL" $ renderHS a $ renderHS b
renderHS (BinOp a s {isOp} b) = BinOp (renderHS a) s {isOp} (renderHS b)

render : ShowEnv -> String
render [] = ""
render ((_ ,, MkTName (MkName "FFI" 0) , FFI def) :: m) = render m ++ "\n" ++ stringFromList (trim (stringToList def)) where
  trim : List Char -> List Char
  trim (' ' :: cs) = trim cs
  trim cs = cs
render ((_ ,, n , def) :: m) = render m ++ "\n" ++ showDoc (printName' (tName n)) ++ " = " ++ showDoc (renderHS def)

render' : ShowEnv -> String
render' [] = ""
render' ((_ ,, MkTName (MkName "FFI" 0) , DVar' def) :: m) = render' m
render' ((_ ,, n , def) :: m) = render' m ++ "\n" ++ showDoc (printName' (tName n)) ++ " = " ++ showDoc def

printGoal ds a = do
  _ <- empty ds
  ls <- locals
  ls <- showLocals ls
  a <- showTm a
  ss <- getShows
  throwError (render' ss ++ "\n----------------\n" ++ ls ++ "\n----------------\n? : " ++ a)

mainTC : List String -> String -> TC String
mainTC ("hs" :: []) s = do
  d <- parse s
  a ,, t <- inferTop d
  t <- printTm t
  ss <- getShows
  pure (render ss ++ "\nmain = " ++ showDoc (renderHS t))
mainTC args s = do
  d <- parse s
  a ,, t <- inferTop d
  a <- printTm a
  t <- printTm t
  ss <- getShows
  pure (render' ss ++ "\n------------------------------------------------\n" ++ showDoc t ++ "\n : " ++ showDoc a)

showEither : Either String String -> String
showEither (Left  x) = x
showEither (Right x) = x

main : IO T
main = bindIO getArgs \args -> interact \s -> showEither (runTC (mainTC args s)) ++ "\n"


{- TODOs

- data desugaring
- eliminators for Id proofs: solveLeft, solveRight, inj, conflict, delete

- refactorings
  - optional main expression
  - env to Tm with vars
  - first order Lambda in Core?
  - NameT instead of Name in Ns?

-}

