
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


data _≡_ {ℓ} {a : Set ℓ} (x : a) : a -> Set where
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
    dcArgs' : Tys
    sub'    : Tms dcArgs' -> Tms indices

open DCDesc

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
  dcArgs n = dcArgs' (dcDescs n)

  sub : (c : dcFin) -> Tms (dcArgs c) -> Tms tcIndices
  sub n = sub' (dcDescs n)

open TCDesc

-- record type and data constructor description
record RCDesc : Set where
  constructor RTCD
  field
    rtcName  : String   -- type constructor name for pretty printing
    rdcName  : String   -- data constructor name for pretty printing
    rIndices : Tys
    rdcArgs  : Tms rIndices -> Tys

open RCDesc

variable a   : Ty
variable as  : Tys
variable b   : Tm a -> Ty
variable tc  : TCDesc
variable rc  : RCDesc

data Ty where
  U    :                             Ty
  Pi   : (a : Ty) -> (Tm a -> Ty) -> Ty
  TC   : Tms (tcIndices tc) ->       Ty
  RTC  : Tms (rIndices rc) ->        Ty

{-# NO_POSITIVITY_CHECK #-}
data Tm where
  code : Ty ->                                            Tm U
  Lam  : ((x : Tm a) -> Tm (b x)) ->                      Tm (Pi a b)
  DC   : (tag : dcFin tc) (args : Tms (dcArgs tc tag)) -> Tm (TC {tc} (sub tc tag args))
  RDC  : {is : _} (args : Tms (rdcArgs rc is)) ->         Tm (RTC {rc} is)

El : Tm U -> Ty
El (code t) = t

_∙_  : Tm (Pi a b) -> (x : Tm a) -> Tm (b x)
Lam f ∙ x = f x

--------------------

_×_ : Ty -> Tys -> Tys
a × as = a :: \_ -> as

_=>_ : Ty -> Ty -> Ty
a => b = Pi a \_ -> b

--------------------

betaU : ∀ {a} -> El (code a) ≡ a
betaU = Refl

etaU : ∀ {a} -> a ≡ code (El a)
etaU {a = code _} = Refl

betaPi : {f : (x : Tm a) -> Tm (b x)} {x : _} -> Lam f ∙ x ≡ f x
betaPi = Refl

etaPi : {f : Tm (Pi a b)} {x : Tm a} -> f ≡ Lam \x -> f ∙ x
etaPi {f = Lam _} = Refl

------------------

module Examples where


  Bool : Ty
  Bool = TC {TCD "Bool" [] 2
    \{ 0f -> DCD "True"  [] \_ -> tt
     ; 1f -> DCD "False" [] \_ -> tt
     }} tt

  True : Tm Bool
  True = DC 0f _

  False : Tm Bool
  False = DC 1f _

  indBool : (P : Tm Bool -> Ty) -> Tm (P True) -> Tm (P False) -> (b : Tm Bool) -> Tm (P b)
  indBool P t f (DC 0f _) = t
  indBool P t f (DC 1f _) = f

  betaBool₁ : {P : Tm Bool -> Ty} {t : Tm (P True)} {f : Tm (P False)} -> indBool P t f True ≡ t
  betaBool₁ = Refl

  betaBool₂ : {P : Tm Bool -> Ty} {t : Tm (P True)} {f : Tm (P False)} -> indBool P t f False ≡ f
  betaBool₂ = Refl

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
  Nat' = TC {TCD "Nat" [] 2
    \{ 0f -> DCD "Zero" []          \_ -> tt
     ; 1f -> DCD "Suc"  (Nat' × []) \_ -> tt
     }} tt

  Zero : Tm Nat'
  Zero = DC 0f _

  Suc : Tm Nat' -> Tm Nat'
  Suc n = DC 1f (n , _)

  {-# TERMINATING #-}
  add : Tm Nat' -> Tm Nat' -> Tm Nat'
  add (DC 0f _) m = m
  add (DC 1f (k , _)) m = Suc (add k m)

  {-# TERMINATING #-}
  indNat : (P : Tm Nat' -> Ty) -> Tm (P Zero) -> ((n : Tm Nat') -> Tm (P n) -> Tm (P (Suc n))) -> (n : Tm Nat') -> Tm (P n)
  indNat P z s (DC 0f _) = z
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
  List' t = TC {TCD "List" (U × []) 2
    \{ 0f -> DCD "Nil"  (U × []) \a -> a
     ; 1f -> DCD "Cons" (U :: \t -> El t × List' (El t) × []) \(a , _) -> a , tt
     }} (code t , tt)

  Nil' : Tm (List' a)
  Nil' = DC 0f _

  Cons : Tm a -> Tm (List' a) -> Tm (List' a)
  Cons x xs = DC 1f (_ , x , xs , tt)


  {-# TERMINATING #-}
  Vec' : Ty -> Tm Nat' -> Ty
  Vec' t n = TC {TCD "Vec" (U × Nat' × []) 2
    \{ 0f -> DCD "VNil"  (U × []) \{(a , tt) -> a , Zero , tt}
     ; 1f -> DCD "VCons" (U :: \t -> Nat' :: \n -> El t × Vec' (El t) n × []) \(a , n , _) -> a , Suc n , tt
     }} (code t , n , tt)

  VNil : Tm (Vec' a Zero)
  VNil = DC 0f _

  VCons : {n : Tm Nat'} -> Tm a -> Tm (Vec' a n) -> Tm (Vec' a (Suc n))
  VCons a as = DC 1f (_ , _ , a , as , tt)


