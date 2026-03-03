{-
Same as CoreB.agda but meta-level pattern matching on (CRefl; code; Lam; _,_) is eliminated.

Work in progress.
-}


{-# OPTIONS --erasure #-}

-------------------

infixl 9 _∙_
infixr 9 _∘_
infixr 9 _∘≡_
infixr 9 _[∘]_
infixr 6 _=>_
infixr 6 _::_
infixr 6 _×_
infixr 6 _:s_
infix  3 _≡_
infix  2 _<=>_
infixr 1 _,_
infixr 1 _,≡_

-------------------


open import Agda.Primitive using (Level)

variable ℓ ℓ' : Level

----------------

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

---------------------

data _≡_ {a : Set ℓ} (x : a) : a -> Set where
  Refl : x ≡ x

sym : {a : Set ℓ} {u v : a} -> u ≡ v -> v ≡ u
sym Refl = Refl

_∘≡_ : {a : Set ℓ} {x y z : a} -> x ≡ y -> y ≡ z -> x ≡ z
Refl ∘≡ Refl = Refl

-- coe
_[_] : {a b : Set ℓ} -> a -> @0 a ≡ b -> b
a [ Refl ] = a

_[∘]_ : {x y z : Set ℓ} (e : x ≡ y) (e' : y ≡ z) {w : x} -> w [ e ] [ e' ] ≡ w [ e ∘≡ e' ]
Refl [∘] Refl = Refl

-- needs K
[Refl] : {x : Set ℓ} {c : x} {e : x ≡ x} -> c [ e ] ≡ c
[Refl] {e = Refl} = Refl

cong : {a : Set ℓ} {b : Set ℓ'} {x y : a} -> (f : a -> b) -> x ≡ y -> f x ≡ f y
cong f Refl = Refl

subst : {a : Set} {u v : a} (P : a -> Set) -> @0 u ≡ v -> P u -> P v
subst P e x = x [ cong P e ]

_,≡_ : {A : Set} {B : A -> Set} {a a' : A} {b : B a} {b' : B a'} ->
  (e : a ≡ a') -> subst B e b ≡ b' -> (a , b) ≡ (a' , b')
Refl ,≡ Refl = Refl


--------------------------


data ⊥ : Set where

not : Set -> Set
not a = a -> ⊥

exfalso : {a : Set} -> ⊥ -> a
exfalso ()


data Dec (a : Set) : Set where
  Yes : a     -> Dec a
  No  : not a -> Dec a

data Fin : Nat -> Set where
  FZ : ∀ {n} -> Fin (S n)
  FS : ∀ {n} -> Fin n -> Fin (S n)

pattern 0f = FZ
pattern 1f = FS FZ
pattern 2f = FS (FS FZ)

decFin : ∀ {n} -> (i j : Fin n) -> Dec (i ≡ j)
decFin FZ     FZ     = Yes Refl
decFin FZ     (FS _) = No \()
decFin (FS _) FZ     = No \()
decFin (FS n) (FS m) with decFin n m
... | Yes Refl = Yes Refl
... | No f = No \{ Refl -> f Refl }

data FinVec : (n : _) -> (P : Fin n -> Set) -> Set₁ where
  []   : ∀ {P} -> FinVec Z P
  _::_ : ∀ {n P} -> P FZ -> FinVec n (\f -> P (FS f)) -> FinVec (S n) P

indexFinVec : ∀ {n P} -> FinVec n P -> (f : Fin n) -> P f
indexFinVec (v :: vs) FZ     = v
indexFinVec (v :: vs) (FS s) = indexFinVec vs s

coveredBy : ∀ {a n} {tag : Fin n} -> FinVec n (\f -> not (tag ≡ f)) -> a
coveredBy vs = exfalso (indexFinVec {P = \f -> not (_ ≡ f)} vs _ Refl)


-----------------------------------------------------------------

record _<=>_ (a b : Set) : Set where
  constructor MkEquiv
  field
    forward   : a -> b
    backward  : b -> a
    @0 isLInv : ∀ x -> backward (forward x) ≡ x
    @0 isRInv : ∀ x -> forward (backward x) ≡ x

open _<=>_


solveBy : {a b : Set}
  (e : a <=> b)  ->
  (x : a)        ->
  (P : a -> Set) ->
  ((y : b) -> P (backward e y)) ->
    P x
solveBy e x P subgoal
  = subst P (isLInv e x) (subgoal (forward e x))


---------------------------

id<=> : ∀ {a} -> a <=> a
id<=> = MkEquiv
  (\a -> a)
  (\a -> a)
  (\a -> Refl)
  (\a -> Refl)

id' : ∀ {a b} -> a ≡ b -> a <=> b
id' Refl = id<=>

sym<=> : ∀ {a b} -> a <=> b -> b <=> a
sym<=> (MkEquiv f g l r) = MkEquiv g f r l

_∘_ : ∀ {a b c} -> a <=> b -> b <=> c -> a <=> c
MkEquiv f g l r ∘ MkEquiv f' g' l' r' = MkEquiv
  (\e -> f' (f e))
  (\e -> g (g' e))
  (chain f f' g g' l' l)
  (chain g' g f' f r r')
 where
  chain : ∀ {a b c : Set}
    (f : a -> b)(f' : b -> c)(g : b -> a)(g' : c -> b) ->
    (∀ x -> g' (f' x) ≡ x) ->
    (∀ x -> g  (f  x) ≡ x) ->
     ∀ x -> g (g' (f' (f x))) ≡ x
  chain f f' g g' e1 e2 x = cong g (e1 (f x)) ∘≡ e2 x

----------------------

delete : ∀ {a : Set} {x : a} ->  x ≡ x  <=>  T
delete = MkEquiv
  (\_     -> tt)
  (\_     -> Refl)
  (\{Refl -> Refl})
  (\_     -> Refl)

solveRight : ∀ {A : Set} {a : A} ->  Σ A (\v -> a ≡ v) <=> T
solveRight = MkEquiv
  (\{(_ , Refl) -> tt})
  (\_           -> _ , Refl)
  (\{(_ , Refl) -> Refl})
  (\_           -> Refl)

solveLeft : ∀ {A : Set} {a : A} ->  Σ A (\v -> v ≡ a) <=> T
solveLeft = MkEquiv
  (\{(_ , Refl) -> tt})
  (\_           -> _ , Refl)
  (\{(_ , Refl) -> Refl})
  (\_           -> Refl)


decompEq : {A : Set} {B : A -> Set} {a a' : A} {b : B a} {b' : B a'} ->
  (a , b) ≡ (a' , b')  <=>  Σ (a ≡ a') \e -> subst B e b ≡ b'
decompEq = MkEquiv
  (\{Refl          -> Refl , Refl})
  (\{(Refl , Refl) -> Refl})
  (\{Refl          -> Refl})
  (\{(Refl , Refl) -> Refl})


botFst : ∀ {b} -> Σ ⊥ b <=> ⊥
botFst = MkEquiv
  (\{(() , _)})
  (\())
  (\{(() , _)})
  (\())

botSnd : ∀ {a} -> Σ a (\_ -> ⊥) <=> ⊥
botSnd = MkEquiv
  (\{(_ , ())})
  (\())
  (\{(_ , ())})
  (\())

---------------------- structural equivalences

unit : ∀ {c} -> Σ T (\_ -> c) <=> c
unit = MkEquiv
  (\(_ , e) -> e)
  (\e       -> tt , e)
  (\(_ , e) -> Refl)
  (\_       -> Refl)

swap : ∀ {a b : Set} {c : a -> b -> Set} ->
      Σ a (\x -> Σ b \y -> c x y)
  <=> Σ b (\y -> Σ a \x -> c x y)
swap = MkEquiv
  (\(a , b , c) -> b , a , c)
  (\(a , b , c) -> b , a , c)
  (\(a , b , c) -> Refl)
  (\(a , b , c) -> Refl)

assoc : {a : Set} {b : a -> Set} {c : (x : a) -> b x -> Set} ->
      Σ a (\x -> Σ (b x) \y -> c x y)
  <=> Σ (Σ a b) (\(x , y) -> c x y)
assoc = MkEquiv
  (\(x , (y , z)) -> (x , y) , z)
  (\((x , y) , z) -> x , (y , z))
  (\(x , (y , z)) -> Refl)
  (\((x , y) , z) -> Refl)

second : ∀ {c} {a b : c -> Set} ->
  ((x : c) -> a x <=> b x) -> Σ c a <=> Σ c b
second f = MkEquiv
  (\(x , y) -> x , forward  (f x) y)
  (\(x , y) -> x , backward (f x) y)
  (\(x , y) -> cong (\y -> x , y) (isLInv (f x) y))
  (\(x , y) -> cong (\y -> x , y) (isRInv (f x) y))

first : {a a' : Set} {b : a -> Set} ->
  (e : a <=> a') -> Σ a b <=> Σ a' \x -> b (backward e x)
first {a} {a'} {b} (MkEquiv f g l r) = MkEquiv
  (\(x , c) -> f x , subst b (sym (l x)) c)
  (\(x , c) -> g x , c)
  (\(x , c) -> l x ,≡ (cong b (sym (l x)) [∘] cong b (l x)) ∘≡ [Refl])
  (\(x , c) -> r x ,≡ (cong b (sym (l (g x))) [∘] cong (\y -> b (g y)) (r x)) ∘≡ [Refl])


sndSwap : ∀ {a b : Set} {aa : a -> Set} {c : a -> b -> Set} ->
   ((e : a) -> aa e <=> Σ b (c e)) ->  Σ a aa <=>  Σ b \y -> Σ a \x -> c x y
sndSwap f = second f ∘ swap

sndAssoc : ∀ {a : Set} {aa b : a -> Set} {c : (x : a) -> b x -> Set} ->
   ((x : a) -> aa x <=> Σ (b x) (c x)) -> Σ a aa <=> Σ (Σ a b) \(x , y) -> c x y
sndAssoc f = second f ∘ assoc

sndBot : ∀ {A} {a : A -> Set} ->
  ((e : A) -> a e <=> ⊥) ->  Σ A a  <=>  ⊥
sndBot f = second f ∘ botSnd


--------------------------------------------

data Ty : Set
data Tm : Ty -> Set

data Tys : Set where
  []   :                              Tys
  _::_ : (t : Ty) -> (Tm t -> Tys) -> Tys

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

  sub : (c : dcFin) -> Tms (dcArgs c) -> Tms tcIndices
  sub n = DCDesc.sub (dcDescs n)

open TCDesc

-- record type and data constructor description
record RCDesc : Set where
  constructor RTCD
  field
    rtcName  : String   -- type constructor name for pretty printing
    rdcName  : String   -- data constructor name for pretty printing
    rParams  : Tys
    rdcArgs  : Tms rParams  -> Tys

open RCDesc

private variable
  a   : Ty
  as  : Tys
  b   : Tm a -> Ty
  tc  : TCDesc
  rc  : RCDesc

data Ty where
  U    :                                   Ty
  Pi   : (a : Ty) -> (Tm a -> Ty) ->       Ty
  TC   : (tc : _) -> Tms (tcIndices tc) -> Ty
  RTC  : (rc : _) -> Tms (rParams rc) ->   Ty

{-# NO_POSITIVITY_CHECK #-}
data Tm where
  code : Ty ->                                            Tm U
  Lam  : ((x : Tm a) -> Tm (b x)) ->                      Tm (Pi a b)
  DC   : (tag : dcFin tc) (args : Tms (dcArgs tc tag)) -> Tm (TC tc (sub tc tag args))
  RDC  : {is : _} (args : Tms (rdcArgs rc is)) ->         Tm (RTC rc is)

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

-----------------------


proj : {params : _} -> Tm (RTC rc params) -> Tms (rdcArgs rc params)
proj (RDC args) = args

etaRecord : {params : _} {t : Tm (RTC rc params)} -> t ≡ RDC (proj t)
etaRecord {t = RDC _} = Refl

--------------------

dcTag : ∀ {indices} -> Tm (TC tc indices) -> dcFin tc
dcTag (DC c _) = c

data _≡≡_ {tc : _} {indices : _} : {indices' : _} ->
  Tm (TC tc indices) ->
  Tm (TC tc indices') ->
    Set
 where
  CRefl : ∀ {z} -> z ≡≡ z

ifTag : {a : Set} {indices : _} ->
  (tag   : dcFin tc) ->                                           -- dcTag
  (tm    : Tm (TC tc indices)) ->                                 -- scrutenee
  (match : (args : Tms (dcArgs tc tag)) -> DC tag args ≡≡ tm -> a) ->
  (fail  : not (dcTag tm ≡ tag) -> a) ->
    a
ifTag tag (DC tag' l) match fail with decFin tag' tag
... | Yes Refl = match l CRefl
... | No  f    = fail f




--------------------------


matchCode : Tm U <=> Ty
matchCode = MkEquiv
  El
  code
  (\{(code _) -> Refl})
  (\_         -> Refl)

injCode : ∀ {a a'} ->  code a ≡ code a'  <=>  a ≡ a'
injCode = MkEquiv
  (\{Refl -> Refl})
  (\{Refl -> Refl})
  (\{Refl -> Refl})
  (\{Refl -> Refl})

matchLam : Tm (Pi a b) <=> ((x : Tm a) -> Tm (b x))
matchLam = MkEquiv
  _∙_
  Lam
  (\{(Lam _) -> Refl})
  (\_        -> Refl)

matchCRefl : ∀ {is is'} {t : Tm (TC tc is)} {t' : Tm (TC tc is')} ->
  t ≡≡ t'  <=>   (is , t) ≡ (is' , t')
matchCRefl = MkEquiv
  (\{CRefl -> Refl})
  (\{Refl  -> CRefl})
  (\{CRefl -> Refl})
  (\{Refl  -> Refl})

conflict :
  {tc : _} {t t' : dcFin tc} {args : Tms (dcArgs tc t)} {args' : Tms (dcArgs tc t')} ->
  not (t ≡ t') ->
    DC {tc} t args ≡≡ DC {tc} t' args' <=> ⊥
conflict ne = MkEquiv
  (\{CRefl -> ne Refl})
  (\())
  (\{CRefl -> CReflUniq})
  (\())
 where
  CReflUniq : ∀ {is : Tms (tcIndices tc)} {t : Tm (TC tc is)} {a : t ≡≡ t} -> a ≡ CRefl
  CReflUniq {a = CRefl} = Refl

Eq<=> : {is : Tms (tcIndices tc)} {t t' : Tm (TC tc is)} ->
   t ≡ t'   <=>  t ≡≡ t'
Eq<=> = MkEquiv
  (\{Refl  -> CRefl})
  (\{CRefl -> Refl})
  (\{Refl  -> Refl})
  (\{CRefl -> Refl})


-----------------------------

_:s_ : (a : Set) -> (a -> Set) -> Set
a :s b = Σ a b


module Examples where

  sec = second

  IdDesc = TCD "Id" (U :: \a -> El a × El a × []) 1 \where
     0f -> DCD "Refl" (U :: \a -> El a × []) \(a , x , tt) -> a , x , x , tt

  Id : {a : Ty} -> Tm a -> Tm a -> Ty
  Id {a} x y = TC IdDesc (code a , x , y , tt)

  refl : {x : Tm a} -> Tm (Id x x)
  refl {a} {x} = DC 0f (code a , x , tt)


  equivTel : (
     Ty                  :s \a ->
     Tm a                :s \b ->
     ((x : Tm a) -> Tm (Id b x) -> Ty) :s \P ->
     Tm (P b refl)       :s \w ->
     Tm a                :s \x ->
     Tm (Id b x)         :s \e ->
     ------------------------------ differs from here
     Σ (Tm U) (\a' -> Σ (Tm (El a')) \_ -> T)  :s \a'x' ->
     DC 0f a'x' ≡≡ e     :s \ee ->
     T
    ) <=> (
     Ty                  :s \a ->
     Tm a                :s \b ->
     ((x : Tm a) -> Tm (Id b x) -> Ty) :s \P ->
     Tm (P b refl)       :s \w ->
     Tm a                :s \x ->
     Tm (Id b x)         :s \e ->
     ------------------------------ differs from here
     Tm U                :s \a' ->
     Tm (El a')          :s \x' ->
     DC 0f (a' , x' , tt) ≡≡ e :s \ee ->
     T
    )
  equivTel
    = sec \_ -> sec \_ -> sec \_ -> sec \_ -> sec \_ -> sec \_ ->
  -- (a, (b, tt)), d  --> a, (b, tt), d -->  a, b, tt, d  --> a, b, d
         sym<=> assoc
       ∘ sec \_ -> sym<=> assoc
                 ∘ sec \_ -> unit

  equivCode : (
     Ty                  :s \a ->
     Tm a                :s \b ->
     ((x : Tm a) -> Tm (Id b x) -> Ty) :s \P ->
     Tm (P b refl)       :s \w ->
     Tm a                :s \x ->
     Tm (Id b x)         :s \e ->
     --------------------------------- diff from here
     Tm U                :s \a' ->
     Tm (El a')          :s \x' ->
     DC 0f (a' , x' , tt) ≡≡ e :s \ee ->
     T
    ) <=> (
     Ty                  :s \a ->
     Tm a                :s \b ->
     ((x : Tm a) -> Tm (Id b x) -> Ty) :s \P ->
     Tm (P b refl)       :s \w ->
     Tm a                :s \x ->
     Tm (Id b x)         :s \e ->
     --------------------------------- diff from here
     Ty                  :s \a'' ->
     Tm a''              :s \x' ->
     DC 0f (code a'' , x' , tt) ≡≡ e :s \ee ->
     T
    )
  equivCode
    = sec \_ -> sec \_ -> sec \_ -> sec \_ -> sec \_ -> sec \_ -> first matchCode


  equiv12 : (
     Ty             :s \a ->
     Tm a           :s \b ->
     ((x : Tm a) -> Tm (Id b x) -> Ty) :s \P ->
     Tm (P b refl)  :s \w ->
     ----------------------------- diff from here
     Tm a           :s \x -> 
     Tm (Id b x)    :s \e ->
     Ty             :s \a' ->
     (Tm a')        :s \x' ->
     refl {a'} {x'} ≡≡ e :s \_ ->
     T
    ) <=> (
     Ty             :s \a ->
     Tm a           :s \b ->
     ((x : Tm a) -> Tm (Id b x) -> Ty) :s \P ->
     Tm (P b refl)  :s \w ->
     ----------------------------- diff from here
     T
    )
  equiv12
    = sec \_ -> sec \_ -> sec \_ -> sec \_ ->
        (sec \_ -> sec \_ ->
            (sndAssoc \_ -> sndSwap \_ ->
                first (matchCRefl ∘ decompEq) ∘ sym<=> assoc
              ∘ first decompEq ∘ sym<=> assoc
              ∘ first injCode
            )
          ∘ first solveLeft ∘ unit
          ∘ (sndAssoc \_ -> first decompEq ∘ sym<=> assoc)
          ∘ first solveLeft ∘ unit
        )
      ∘ (sndAssoc \_ -> sndSwap \_ -> first decompEq ∘ sym<=> assoc)
      ∘ first solveRight ∘ unit
      ∘ (sndAssoc \_ -> first delete ∘ unit)
      ∘ first solveRight ∘ unit



  ---------------- core source --------------
  -- J' a b P w x (refl (code a'') x') = w

  J' : ∀ {a b} -> (P : (x : Tm a) -> Tm (Id b x) -> Ty) -> Tm (P b refl) -> (x : Tm a) -> (e : Tm (Id b x)) -> Tm (P x e)
  J' {a = a} {b = b} P w x e =
--    ifTag 0f e (\{ (code a' , x' , tt) CRefl -> w }) \f0 ->

    ifTag 0f e (\{ a'x' ee ->
      solveBy equivTel
           (a , b , P , w , x , e , a'x' , ee , tt)
        (\{(a , b , P , w , x , e , a'x' , ee , tt) -> Tm (P x e)})
        (\{(a , b , P , w , x , e , a'' , x' , ee , tt) ->
          solveBy equivCode
               (a , b , P , w , x , e , a'' , x' , ee , tt)
            (\{(a , b , P , w , x , e , a'' , x' , ee , tt) -> Tm (P x e)})
            (\{(a , b , P , w , x , e , a' , x' , ee , tt) ->
              solveBy equiv12 (a , b , P , w , x , e , a' , x' , ee , tt)
                (\{(a , b , P , w , x , e , a' , x' , ee , tt) -> Tm (P x e)})
                (\{(a , b , P , w , tt) -> w })
              })
          })
        }) \f0 ->

    coveredBy (f0 :: [])


  betaJ' : ∀ {a b} {P : (x : Tm a) -> Tm (Id b x) -> Ty} {w : Tm (P b refl)} -> J' P w b refl ≡ w
  betaJ' = Refl

  ------------------------------------------------

  {-# TERMINATING #-}
  Nat' : Ty

  NatDesc = TCD "Nat" [] 2 \where
      0f -> DCD "Zero" []          \_ -> tt
      1f -> DCD "Suc"  (Nat' × []) \_ -> tt

  Nat' = TC NatDesc tt

  Zero : Tm Nat'
  Zero = DC 0f _

  Suc : Tm Nat' -> Tm Nat'
  Suc n = DC 1f (n , _)

  {-# TERMINATING #-}
  Vec' : Ty -> Tm Nat' -> Ty

  VecDesc = TCD "Vec" (U × Nat' × []) 2 \where
      0f -> DCD "VNil"  (U × []) \{(a , tt) -> a , Zero , tt}
      1f -> DCD "VCons" (U :: \t -> Nat' :: \n -> El t × Vec' (El t) n × []) \(a , n , _) -> a , Suc n , tt

  Vec' t n = TC VecDesc (code t , n , tt)

  VNil : Tm (Vec' a Zero)
  VNil = DC 0f _

  VCons : {n : Tm Nat'} -> Tm a -> Tm (Vec' a n) -> Tm (Vec' a (Suc n))
  VCons a as = DC 1f (_ , _ , a , as , tt)

  equivBot : (
      Ty :s  \b ->
      Ty :s  \c ->
      Tm (Vec' b Zero) :s \bs ->
      (Σ (Tm U) \a' -> Σ (Tm Nat') \n' → Σ (Tm (El a')) \_ -> Σ (Tm (Vec' (El a') n')) \_ -> T) :s \args ->
      (DC 1f args ≡≡ bs) :s \e ->
      T
    ) <=> ⊥
  equivBot
    = (sndBot \_ -> sndBot \_ -> sndBot \_ -> sndBot \{(code a' , n' , x , xs , tt) ->
           first (matchCRefl ∘ decompEq) ∘ sym<=> assoc
         ∘ first decompEq ∘ sym<=> assoc
         ∘ sndBot (\{Refl ->
              first decompEq ∘ sym<=> assoc
            ∘ first (Eq<=> ∘ conflict \())
            ∘ botFst})
         })

  zipWith : {a b c : Ty} {n : Tm Nat'} (f : Tm a -> Tm b -> Tm c) ->
    Tm (Vec' a n) -> Tm (Vec' b n) -> Tm (Vec' c n)
  zipWith {a} {b} {c} {n} f as bs =
    ifTag 0f as (\{ (a' , tt) CRefl ->
      ifTag 0f bs (\{ _ CRefl -> VNil }) \f0 ->
      ifTag 1f bs (\{ args e ->
        solveBy equivBot
          ((b , c , bs , args , e , tt))
          ((\(b , c , bs , args , e , _) -> Tm (Vec' c Zero)))
          (\())
                    }) \f1 ->
      coveredBy (f0 :: f1 :: [])
    }) \f0 ->
    ifTag 1f as (\{ (_ , _ , a , as , tt) CRefl ->
      ifTag 0f bs (\{ _ () }) \f0 ->
      ifTag 1f bs (\{ (_ , _ , b , bs , _) CRefl -> VCons (f a b) (zipWith f as bs) }) \f1 ->
      coveredBy (f0 :: f1 :: [])
    }) \f1 ->
    coveredBy (f0 :: f1 :: [])

  ----------------------------------------------------------------

  module MetaLang where

    data Cmp : Nat -> Nat -> Set where
      CmpLT : {x k : Nat} -> Cmp x (x + S k)
      CmpEQ : {x   : Nat} -> Cmp x x
      CmpGT : {x k : Nat} -> Cmp (x + S k) x

{- wannabe syntax
    cmp : (x y : Nat) -> Cmp x y
    cmp Z     Z     = CmpEQ
    cmp Z     (S y) = CmpLT
    cmp (S x) Z     = CmpGT
    cmp (S x) (S y) | CmpLT <- cmp x y  = CmpLT
    cmp (S x) (S y) | CmpEQ <- cmp x y  = CmpEQ
    cmp (S x) (S y) | CmpGT <- cmp x y  = CmpGT
-}

  {-# TERMINATING #-}
  add : Tm Nat' -> Tm Nat' -> Tm Nat'
  add n m =
    ifTag 0f n (\{ _ e -> m }) \f0 ->
    ifTag 1f n (\{ (k , tt) CRefl -> Suc (add k m) }) \f1 ->
    coveredBy (f0 :: f1 :: [])

  CmpDesc = TCD "Cmp" (Nat' × Nat' × []) 3 \where
    0f -> DCD "CmpLT" (Nat' × Nat' × []) \(x , k , tt) -> x , add x (Suc k) , tt
    1f -> DCD "CmpEQ" (Nat' × [])        \(x , tt)     -> x , x , tt
    2f -> DCD "CmpGT" (Nat' × Nat' × []) \(x , k , tt) -> add x (Suc k) , x , tt

  Cmp : Tm Nat' -> Tm Nat' -> Ty
  Cmp n m = TC CmpDesc (n , m , tt)

  CmpLT : {x k : Tm Nat'} -> Tm (Cmp x (add x (Suc k)))
  CmpLT = DC 0f _

  CmpEQ : {x : Tm Nat'} -> Tm (Cmp x x)
  CmpEQ = DC 1f _

  CmpGT : {x k : Tm Nat'} -> Tm (Cmp (add x (Suc k)) x)
  CmpGT = DC 2f _

  {-# TERMINATING #-}
  cmp : (x : Tm Nat') (y : Tm Nat') -> Tm (Cmp x y)

  equiv : (
       Tm Nat' :s \x' ->
       Tm Nat' :s \y' ->
       Tm Nat' :s \u ->
       Tm Nat' :s \v ->
       CmpLT {u} {v} ≡≡ cmp x' y' :s \e ->
       T
     ) <=> (
       Tm Nat' :s \u ->
       Tm Nat' :s \v ->
       (CmpLT {u} {v} ≡ cmp u (add u (Suc v))) :s \_ ->    -- this equality remained but it will not be used
       T       
     )
  equiv =
      sec \_ ->
          (sndSwap \_ ->
            (sndAssoc \_ -> sndSwap \_ ->
              first (matchCRefl ∘ decompEq) ∘ sym<=> assoc
            ∘ first decompEq ∘ sym<=> assoc
            )
          ∘ first solveLeft ∘ unit
          ∘ sec (\v -> first decompEq ∘ sym<=> assoc)
          )
        ∘ sec \_ ->
            assoc ∘ first solveRight ∘ unit
          ∘ first delete ∘ unit

  cmp x y =
    ifTag 0f x (\{ _ CRefl ->
      ifTag 0f y (\{ _ CRefl -> CmpEQ }) \f0 ->
      ifTag 1f y (\{ _ CRefl -> CmpLT }) \f1 ->
      coveredBy (f0 :: f1 :: [])
    }) \f0 ->
    ifTag 1f x (\{ (x' , tt) CRefl ->
      ifTag 0f y (\{ _ CRefl -> CmpGT }) \f0' ->
      ifTag 1f y (\{ (y' , tt) CRefl ->
        let c = cmp x' y' in
--        ifTag 0f c (\{ (u , v , tt) CRefl -> {!CmpLT!} }) \f0 ->
        ifTag 0f c (\{ (u , v , tt) e ->
              solveBy equiv
                (x' , y' , u , v , e , tt)
                (\{(x' , y' , u , v , e , tt) -> Tm (Cmp (Suc x') (Suc y'))})
                \{(u , v , _ , tt) -> CmpLT}
             }) \f0 ->
        ifTag 1f c (\{ _ e -> {!CmpEQ!} }) \f1 ->
        ifTag 2f c (\{ _ e -> {!CmpGT!} }) \f2 ->
        coveredBy (f0 :: f1 :: f2 :: [])
      }) \f1 ->
      coveredBy (f0' :: f1 :: [])
    }) \f1 ->
    coveredBy (f0 :: f1 :: [])

  the : (a : Set) -> a -> a
  the _ x = x

  cmpTest = the (cmp (Suc Zero) (Suc (Suc (Suc Zero))) ≡ CmpLT) Refl

