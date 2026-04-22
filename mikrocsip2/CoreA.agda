
-------------------

infixl 9 _∙_
infixr 6 _=>_
infixr 6 _,_
infixr 6 _::_
infixr 6 _×_
infix  3 _≡_

-------------------

--open import Agda.Builtin.String  -- for pretty printing
--open import Agda.Builtin.Nat renaming (suc to S; zero to Z)

data Nat : Set where
  Z : Nat
  S : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat -> Nat -> Nat
Z + n = n
S m + n = S (m + n)

postulate String : Set

{-# BUILTIN STRING String #-}

-------------------

record T : Set where
  constructor tt


record Σ (a : Set) (b : a -> Set) : Set where
  constructor _,_
  field
    fst : a
    snd : b fst

open Σ


data _≡_ {a : Set} (x : a) : a -> Set where
  Refl : x ≡ x


data Fin : Nat -> Set where
  FZ : ∀ {n} -> Fin (S n)
  FS : ∀ {n} -> Fin n -> Fin (S n)

pattern 0f = FZ
pattern 1f = FS FZ
pattern 2f = FS (FS FZ)



--------------------------------------------

data Ty : Set
data Tm : Ty -> Set

-- telescope
data Tys : Set where
  []   :                              Tys
  _::_ : (t : Ty) -> (Tm t -> Tys) -> Tys

-- telescope record
Tms : Tys -> Set
Tms []        = T
Tms (t :: ts) = Σ (Tm t) \x -> Tms (ts x)


-- data constructor description
record DCDesc (indices : Tys) : Set where
  constructor DCD
  field
    dcName  : String   -- for pretty printing
    dcArgs  : Tys
    sub     : Tms dcArgs -> Tms indices

-- type constructor description
record TCDesc : Set where
  constructor TCD
  field
    tcName     : String  -- for pretty printing
    tcIndices  : Tys
    numOfCstrs : Nat
    dcDescs    : Fin numOfCstrs -> DCDesc tcIndices

  dcFin : Set
  dcFin = Fin numOfCstrs

  dcArgs : dcFin -> Tys
  dcArgs n = DCDesc.dcArgs (dcDescs n)

  -- rename to conTypeIndex ?
  sub : (c : dcFin) -> Tms (dcArgs c) -> Tms tcIndices
  sub n = DCDesc.sub (dcDescs n)

open TCDesc


data Ty where
  U    :                                           Ty
  Pi   : (a : Ty) -> (Tm a -> Ty) ->               Ty
  TC   : (tc : TCDesc) -> Tms (tcIndices tc) ->    Ty

{-# NO_POSITIVITY_CHECK #-}
data Tm where
  code : Ty ->                                                          Tm U
  Lam  : {a : Ty} {b : Tm a -> Ty} -> ((x : Tm a) -> Tm (b x)) ->       Tm (Pi a b)
  DC   : {tc : TCDesc} (tag : dcFin tc) (args : Tms (dcArgs tc tag)) -> Tm (TC tc (sub tc tag args))

module NoPositivityMayBeBad where

  data ⊥ : Set where

  {-# NO_POSITIVITY_CHECK #-}
  data D : Set where
    C : (D -> ⊥) -> D

  not-inhabited : D -> ⊥
  not-inhabited (C f) = f (C f)

  bad : ⊥
  bad = not-inhabited (C not-inhabited)


El : Tm U -> Ty
El (code t) = t

_∙_  : {a : Ty} {b : Tm a -> Ty} -> Tm (Pi a b) -> (x : Tm a) -> Tm (b x)
Lam f ∙ x = f x

--------------------

_×_ : Ty -> Tys -> Tys
a × as = a :: \_ -> as

_=>_ : Ty -> Ty -> Ty
a => b = Pi a \_ -> b

--------------------

betaU : {a : Ty} -> El (code a) ≡ a
betaU = Refl

etaU : {a : Tm U} -> code (El a) ≡ a
etaU {a = code _} = Refl

betaPi : {a : Ty} {b : Tm a -> Ty} {f : (x : Tm a) -> Tm (b x)} {x : _} -> Lam f ∙ x ≡ f x
betaPi = Refl

etaPi : {a : Ty} {b : Tm a -> Ty} {f : Tm (Pi a b)} {x : Tm a} -> Lam (\x -> f ∙ x) ≡ f
etaPi {f = Lam _} = Refl

------------------

module Examples where

  BoolDesc = TCD "Bool" [] 2
    \{ 0f -> DCD "True"  [] \_ -> tt
     ; 1f -> DCD "False" [] \_ -> tt
     }

  Bool : Ty
  Bool = TC BoolDesc tt
  
  True : Tm Bool
  True = DC {BoolDesc} 0f tt

  False : Tm Bool
  False = DC {_} 1f tt

  indBool : (P : Tm Bool -> Ty) -> Tm (P True) -> Tm (P False) -> (b : Tm Bool) -> Tm (P b)
  indBool P t f (DC 0f _) = t
  indBool P t f (DC 1f _) = f

  betaBool₁ : {P : Tm Bool -> Ty} {t : Tm (P True)} {f : Tm (P False)} -> indBool P t f True ≡ t
  betaBool₁ = Refl

  betaBool₂ : {P : Tm Bool -> Ty} {t : Tm (P True)} {f : Tm (P False)} -> indBool P t f False ≡ f
  betaBool₂ = Refl

  etaBool : (b : Tm Bool) -> indBool (\_ -> Bool) True False b ≡ b
  etaBool (DC 0f _) = Refl
  etaBool (DC 1f _) = Refl

  not' : Tm Bool -> Tm Bool
  not' (DC 0f _) = False
  not' _         = True

  F  : Tm Bool -> Ty
  F (DC 0f _) = Bool
  F (DC 1f _) = Bool => Bool

  f : (b : Tm Bool) -> Tm (F b)
  f (DC 0f tt) = True
  f (DC 1f tt) = Lam not'


  {-# TERMINATING #-}
  Nat' : Ty
  Nat' = TC (TCD "Nat" [] 2
    \{ 0f -> DCD "Zero" []          \_ -> tt
     ; 1f -> DCD "Suc"  (Nat' × []) \_ -> tt
     }) tt

  Zero : Tm Nat'
  Zero = DC 0f _

  Suc : Tm Nat' -> Tm Nat'
  Suc n = DC 1f (n , _)

  {-# TERMINATING #-}
  add : Tm Nat' -> Tm Nat' -> Tm Nat'
  add (DC 0f _)       m = m
  add (DC 1f (k , _)) m = Suc (add k m)

  {-# TERMINATING #-}
  indNat : (P : Tm Nat' -> Ty) -> Tm (P Zero) -> ((n : Tm Nat') -> Tm (P n) -> Tm (P (Suc n))) -> (n : Tm Nat') -> Tm (P n)
  indNat P z s (DC 0f _)       = z
  indNat P z s (DC 1f (k , _)) = s k (indNat P z s k)

  add' : Tm Nat' -> Tm Nat' -> Tm Nat'
  add' n m = indNat (\_ -> Nat') m (\_ -> Suc) n

  one = Suc Zero
  two = Suc one

  the : (a : Set) -> a -> a
  the _ x = x

  testAdd  = the (add  (Suc Zero) (Suc Zero) ≡ two) Refl
  testAdd' = the (add' (Suc Zero) (Suc Zero) ≡ two) Refl


  {-# TERMINATING #-}
  List' : Ty -> Ty
  List' t = TC (TCD "List" (U × []) 2
    \{ 0f -> DCD "Nil"  (U × []) \a -> a
     ; 1f -> DCD "Cons" (U :: \t -> El t × List' (El t) × []) \(a , _) -> a , tt
     }) (code t , tt)

  Nil' : {a : Ty} -> Tm (List' a)
  Nil' = DC 0f _

  Cons : {a : Ty} -> Tm a -> Tm (List' a) -> Tm (List' a)
  Cons x xs = DC 1f (_ , x , xs , tt)


  {-# TERMINATING #-}
  Vec' : Ty -> Tm Nat' -> Ty
  Vec' t n = TC (TCD "Vec" (U × Nat' × []) 2
    \{ 0f -> DCD "VNil"  (U × []) \{(a , tt) -> a , Zero , tt}
     ; 1f -> DCD "VCons" (U :: \t -> Nat' :: \n -> El t × Vec' (El t) n × []) \(a , n , _) -> a , Suc n , tt
     }) (code t , n , tt)

  VNil : {a : Ty} -> Tm (Vec' a Zero)
  VNil = DC 0f _

  VCons : {a : Ty} {n : Tm Nat'} -> Tm a -> Tm (Vec' a n) -> Tm (Vec' a (Suc n))
  VCons a as = DC 1f (_ , _ , a , as , tt)


