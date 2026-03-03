{-
Same as CoreA.agda but meta-level pattern matching on DC is eliminated.

Other changes:
- record types are supported
- variables are used in the implementation

-}

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
decFin (FS n) (FS n) | Yes Refl = Yes Refl
decFin (FS n) (FS m) | No  f    = No \{Refl -> f Refl}


data FinVec : (n : Nat) -> (P : Fin n -> Set) -> Set₁ where
  []   : ∀ {P}   -> FinVec Z P
  _::_ : ∀ {n P} -> P FZ -> FinVec n (\f -> P (FS f)) -> FinVec (S n) P

indexFinVec : ∀ {n P} -> FinVec n P -> (f : Fin n) -> P f
indexFinVec (v :: vs) FZ     = v
indexFinVec (v :: vs) (FS s) = indexFinVec vs s

coveredBy : ∀ {a n} {tag : Fin n} -> FinVec n (\f -> not (tag ≡ f)) -> a
coveredBy {a} {n} {tag} vs = exfalso ((indexFinVec {P = \f -> not (_ ≡ f)} vs tag) Refl)



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
    rtcName  : String              -- type constructor name for pretty printing
    rdcName  : String              -- data constructor name for pretty printing
    rParams  : Tys                 -- parameters of the type constructor
    rdcArgs  : Tms rParams -> Tys  -- additional arguments of the data constructor

open RCDesc

private variable
  a   : Ty
  as  : Tys
  b   : Tm a -> Ty
  tc  : TCDesc
  rc  : RCDesc

data Ty where
  U    :                             Ty
  Pi   : (a : Ty) -> (Tm a -> Ty) -> Ty
  TC   : Tms (tcIndices tc) ->       Ty
  RTC  : Tms (rParams rc) ->         Ty

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



--------------------

proj : {params : _} -> Tm (RTC {rc} params) -> Tms (rdcArgs rc params)
proj (RDC args) = args

etaRecord : {params : _} {t : Tm (RTC {rc} params)} -> t ≡ RDC (proj t)
etaRecord {t = RDC _} = Refl

--------------------

dcTag : ∀ {indices} -> Tm (TC {tc} indices) -> dcFin tc
dcTag (DC c _) = c

data _≡≡_ {tc : _} {indices : _} : {indices' : _} ->
  Tm (TC {tc} indices)  ->
  Tm (TC {tc} indices') ->
    Set
 where
  CRefl : {z : Tm (TC {tc} indices)} -> _≡≡_ {tc} {indices} {indices} z z

ifTag : {a : Set} {indices : _} ->
  (tag   : dcFin tc) ->                                             -- dcTag
  (tm    : Tm (TC {tc} indices)) ->                                 -- scrutenee
  (match : (args : Tms (dcArgs tc tag)) -> DC tag args ≡≡ tm -> a) ->
  (fail  : not (dcTag tm ≡ tag) -> a) ->
    a
ifTag tag (DC tag' args) match fail with decFin tag' tag
... | Yes Refl  = match args CRefl
... | No  refut = fail refut


-------------------------------------

module Examples where

------------------

  Bot : Ty
  Bot = TC {TCD "Bot" [] 0 \()} tt

  exfalso' : Tm Bot -> Tm a
  exfalso' t = coveredBy {tag = dcTag t} []


---------------------------------

  module TopAsData where

    -- data Top : Type  where  tt : Top
    Top : Ty
    Top = TC {TCD "Top" [] 1 \{0f -> DCD "tt" [] \_ -> _}} tt

    TT : Tm Top
    TT = DC 0f tt

    -- etaTop : (t : Top) -> t ≡ tt)
    -- etaTop tt = Refl
    etaTop : {t : Tm Top} -> t ≡ TT
    etaTop {t} =
      ifTag 0f t (\{_ CRefl -> Refl}) \r0 ->
      coveredBy (r0 :: [])


  Top : Ty
  Top = RTC {RTCD "Top" "TT" [] \_ -> []} tt

  TT : Tm Top
  TT = RDC _

  etaTop : {t : Tm Top} -> t ≡ TT
  etaTop = etaRecord


---------------------------------

  module Model where

    data Bool : Set where
      True False : Bool
 
    not' : Bool -> Bool
    not' True = False
    not' _    = True

    F : Bool -> Set
    F True = Bool
    F _    = Bool -> Bool

    f : (b : Bool) -> F b
    f True  = True
    f False = not'     -- cannot write:  f _ = not'


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
  indBool P t f b =
    ifTag 0f b (\{ _ CRefl -> t }) \f0 ->
    ifTag 1f b (\{ _ CRefl -> f }) \f1 ->
    coveredBy (f0 :: f1 :: [])

  betaBool₁ : {P : Tm Bool -> Ty} {t : Tm (P True)} {f : Tm (P False)} -> indBool P t f True ≡ t
  betaBool₁ = Refl

  betaBool₂ : {P : Tm Bool -> Ty} {t : Tm (P True)} {f : Tm (P False)} -> indBool P t f False ≡ f
  betaBool₂ = Refl

  not' : Tm Bool -> Tm Bool
  not' b =
    ifTag 0f b (\{ _ e -> False }) \_ ->
    True

  F  : Tm Bool -> Ty
  F b =
    ifTag 0f b (\{ _ e -> Bool }) \_ ->
    Bool => Bool

  f : (b : Tm Bool) -> Tm (F b)
  f b =
    ifTag 0f b (\{ _ CRefl -> True     }) \f0 ->
    ifTag 1f b (\{ _ CRefl -> Lam not' }) \f1 ->
    coveredBy (f0 :: f1 :: [])

---------------------------------

  module Wrong where

    Sigma : (a : Ty) -> (Tm a -> Ty) -> Ty
    Sigma a b = RTC {RTCD      -- non top-level record description!
         "Sigma"               -- this is bad because names will not be unique
         "_,_"
         []
         \_ -> a :: \z -> b z  × []}
      tt


  Sigma : (a : Ty) -> (Tm a -> Ty) -> Ty
  Sigma a b = RTC {RTCD
       "Sigma"
       "_,_"
       (U :: \a -> (El a => U) × [])
       \(a , b , _) -> El a :: \x -> El (b ∙ x) × []}
    (code a , Lam (\x -> code (b x)) , tt)


  Pair : (x : Tm a) -> Tm (b x) -> Tm (Sigma a b)
  Pair x y = RDC (x , y , _)

  Fst : Tm (Sigma a b) -> Tm a
  Fst p = fst (proj p)

  Snd : (t : Tm (Sigma a b)) -> Tm (b (Fst t))
  Snd p = fst (snd (proj p))

  etaSigma : {t : Tm (Sigma a b)} -> t ≡ Pair (Fst t) (Snd t)
  etaSigma = etaRecord


---------------------------------

  -- record U' : Type where
  --   constructor code'
  --   field
  --     El' : Type

  UDesc = RTCD "U" "code" [] \_ -> U × []

  U' : Ty
  U' = RTC {UDesc} _

  code' : Ty -> Tm U'
  code' a = RDC (code a , _)

  El' : Tm U' -> Ty
  El' z = El (fst (proj z))

  betaU' : El' (code' a) ≡ a
  betaU' = Refl

  etaU' : ∀ {t} -> t ≡ code' (El' t)
  etaU' {t = RDC (code _ , _)} = Refl

---------------------------------

  Pi' : (a : Ty) -> (Tm a -> Ty) -> Ty
  Pi' a b = RTC {RTCD
           "Pi"
           "Lam"
           (U :: \a -> (El a => U) × [])
           \(a , b , _) -> Pi (El a) (\x -> El (b ∙ x)) × []
         }
    (code a , Lam (\x -> code (b x)) , tt)

  Lam' : ((x : Tm a) -> Tm (b x)) -> Tm (Pi' a b)
  Lam' f = RDC (Lam f , _)

  App' : Tm (Pi' a b) -> (x : Tm a) -> Tm (b x)
  App' z x = fst (proj z) ∙ x

  betaPi' : {f : (x : Tm a) -> Tm (b x)} -> App' (Lam' f) ≡ f
  betaPi' = Refl

  etaPi' : {t : Tm (Pi' a b)} -> t ≡ Lam' (App' t)
  etaPi' {t = RDC (Lam _ , _)} = Refl


---------------------------------

  module MetaLevel where

    record W (S : Set) (P : (s : S) -> Set) : Set where
      inductive
      constructor sup
      field
        shape  : S
        branch : P shape -> W S P

    data Either (a b : Set) : Set where
      Left  : a -> Either a b
      Right : b -> Either a b

    List : Set -> Set
    List A = W (Either T A) \where
      (Left tt) -> ⊥
      (Right a) -> T

    Nil : ∀ {A} -> List A
    Nil = sup (Left tt) \()

    Cons : ∀ {A} -> A -> List A -> List A
    Cons a as = sup (Right a) \_ -> as

  {-# TERMINATING #-}
  W : (S : Ty) -> (Tm S -> Ty) -> Ty
  W S' P = RTC {RTCD
            "W"
            "sup"
            (U :: \S' -> (El S' => U) × [])
            \(S' , P , _) -> El S' :: \s -> (El (P ∙ s) => W (El S') \s -> El (P ∙ s)) × []
          }
      (code S' , Lam (\s -> code (P s)) , tt)

  sup : {S : Ty} {P : Tm S -> Ty} (s : Tm S) -> (Tm (P s) -> Tm (W S P)) -> Tm (W S P)
  sup s f = RDC (s , Lam f , tt)

  indW : {S : Ty} {P : Tm S -> Ty} (C : Tm (W S P) -> Ty) ->
    ({s : Tm S} {f : Tm (P s) -> Tm (W S P)} -> ((p : Tm (P s)) -> Tm (C (f p))) -> Tm (C (sup s f))) ->
    (w : Tm (W S P)) -> Tm (C w)
  indW C' h (RDC (s , Lam f , _)) = h \p -> indW C' h (f p)

  module NatWithW where

    fNat : Tm Bool -> Ty
    fNat b =
      ifTag 0f b (\{ _ e -> Bot }) \f0 ->
      ifTag 1f b (\{ _ e -> Top }) \f1 ->
      coveredBy (f0 :: f1 :: [])

    Nat' : Ty
    Nat' = W Bool fNat

    Zero : Tm Nat'
    Zero = sup True exfalso'

    Suc : Tm Nat' -> Tm Nat'
    Suc n = sup False \_ -> n


---------------------------------

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
  add n m =
    ifTag 0f n (\{ _ e -> m }) \f0 ->
    ifTag 1f n (\{ (k , tt) CRefl -> Suc (add k m) }) \f1 ->
    coveredBy (f0 :: f1 :: [])

  {-# TERMINATING #-}
  indNat : (P : Tm Nat' -> Ty) -> Tm (P Zero) -> ((n : Tm Nat') -> Tm (P n) -> Tm (P (Suc n))) -> (n : Tm Nat') -> Tm (P n)
  indNat P z s n =
    ifTag 0f n (\{ _ CRefl -> z }) \f0 ->
    ifTag 1f n (\{ (k , _) CRefl -> s k (indNat P z s k) }) \f1 ->
    coveredBy (f0 :: f1 :: [])

  add' : Tm Nat' -> Tm Nat' -> Tm Nat'
  add' n m = indNat (\_ -> Nat') m (\_ -> Suc) n

  one = Suc Zero
  two = Suc one

  the : (a : Set) -> a -> a
  the _ x = x

  testAdd  = the (add  (Suc Zero) (Suc Zero) ≡ two) Refl
  testAdd' = the (add' (Suc Zero) (Suc Zero) ≡ two) Refl

---------------------------------

  {-# TERMINATING #-}
  List' : Ty -> Ty
  List' t = TC {TCD "List" (U × []) 2
    \{ 0f -> DCD "Nil"  (U × []) \a -> a
     ; 1f -> DCD "Cons" (U :: \t -> El t × List' (El t) × []) \(a , _) -> a , tt
     }} (code t , tt)

  Nil : Tm (List' a)
  Nil = DC 0f _

  Cons : Tm a -> Tm (List' a) -> Tm (List' a)
  Cons x xs = DC 1f (_ , x , xs , tt)

  {-# TERMINATING #-}
  append : Tm (List' a) -> Tm (List' a) -> Tm (List' a)
  append {a} as bs =
    ifTag 0f as (\{ _ e -> bs }) \f0 ->
    ifTag 1f as (\{ (code aa , x , xs , tt) CRefl -> Cons {a} x (append {a} xs bs)  }) \f1 ->
    coveredBy (f0 :: f1 :: [])


  testAppend = the (append (Cons Zero Nil) (Cons (Suc Zero) Nil) ≡ Cons Zero (Cons (Suc Zero) Nil)) Refl


---------------------------------

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

  zipWith : {a b c : Ty} (f : Tm a -> Tm b -> Tm c) {n : Tm Nat'} ->
    Tm (Vec' a n) -> Tm (Vec' b n) -> Tm (Vec' c n)
  zipWith f as bs =
    ifTag 0f as (\{ _ CRefl ->
      ifTag 0f bs (\{ _ CRefl -> VNil }) \f0 ->
      ifTag 1f bs (\{ _ () }) \f1 ->
      coveredBy (f0 :: f1 :: [])
    }) \f0 ->
    ifTag 1f as (\{ (_ , _ , a , as , tt) CRefl ->
      ifTag 0f bs (\{ _ () }) \f0 ->
      ifTag 1f bs (\{ (_ , _ , b , bs , _) CRefl -> VCons (f a b) (zipWith f as bs) }) \f1 ->
      coveredBy (f0 :: f1 :: [])
    }) \f1 ->
    coveredBy (f0 :: f1 :: [])

---------------------------------

  {-# TERMINATING #-}
  Fin' : Tm Nat' -> Ty
  Fin' n = TC {TCD "Fin" (Nat' × []) 2
    \{ 0f -> DCD "FZ" (Nat' × []) \(a , tt) -> Suc a , tt
     ; 1f -> DCD "FS" (Nat' :: \n -> Fin' n × Fin' (Suc n) × []) \(n , _ , _ , _) -> n , tt
     }} (n , tt)


---------------------------------

  Id : {a : Ty} -> Tm a -> Tm a -> Ty
  Id {a} x y = TC
    {TCD "Id" (U :: \a -> El a × El a × []) 1
      \{ 0f -> DCD "Refl" (U :: \a -> El a × []) \(a , x , tt) -> a , x , x , tt
    }}
     (code a , x , y , tt)

  Refl' : {x : Tm a} -> Tm (Id x x)
  Refl' = DC 0f _

  J' : ∀ {a b} -> (P : (x : Tm a) -> Tm (Id b x) -> Ty) -> Tm (P b Refl') -> (x : Tm a) -> (e : Tm (Id b x)) -> Tm (P x e)
  J' P w x e =
    ifTag 0f e (\{ _ CRefl -> w }) \f0 ->
    coveredBy (f0 :: [])

  -- valid only if K is valid in the metatheory
  K' : ∀ {a} {x : Tm a} -> (e : Tm (Id x x)) -> Tm (Id e Refl')
  K' e =
    ifTag 0f e (\{ _ CRefl -> Refl' }) \f0 ->
    coveredBy (f0 :: [])

--------------------------------------

  module MetaLevel' where

    data Cmp : Nat -> Nat -> Set where
      CmpLT : {x k : Nat} -> Cmp x (x + S k)
      CmpEQ : {x   : Nat} -> Cmp x x
      CmpGT : {x k : Nat} -> Cmp (x + S k) x

    cmp : (x y : Nat) -> Cmp x y
    cmp Z     Z     = CmpEQ
    cmp Z     (S y) = CmpLT
    cmp (S x) Z     = CmpGT
    cmp (S x) (S y) with cmp x y
    ... | CmpLT = CmpLT
    ... | CmpEQ = CmpEQ
    ... | CmpGT = CmpGT

    cmpHelper : (x y : Nat) -> Cmp x y -> Cmp (S x) (S y)
    cmpHelper x y CmpLT = CmpLT
    cmpHelper x y CmpEQ = CmpEQ
    cmpHelper x y CmpGT = {!CmpGT!}

    cmp' : (x y : Nat) -> Cmp x y
    cmp' Z     Z     = CmpEQ
    cmp' Z     (S y) = CmpLT
    cmp' (S x) Z     = CmpGT
    cmp' (S x) (S y) = cmpHelper x y (cmp x y)

  {-# TERMINATING #-}
  Cmp : Tm Nat' -> Tm Nat' -> Ty
  Cmp n m = TC {TCD "Cmp" (Nat' × Nat' × []) 3
    \{ 0f -> DCD "CmpLT" (Nat' × Nat' × []) \(x , k , tt) -> x , add x (Suc k) , tt
     ; 1f -> DCD "CmpEQ" (Nat' × [])        \(x , tt)     -> x , x , tt
     ; 2f -> DCD "CmpGT" (Nat' × Nat' × []) \(x , k , tt) -> add x (Suc k) , x , tt
     }} (n , m , tt)

  CmpLT : {x k : Tm Nat'} -> Tm (Cmp x (add x (Suc k)))
  CmpLT = DC 0f _

  CmpEQ : {x : Tm Nat'} -> Tm (Cmp x x)
  CmpEQ = DC 1f _

  CmpGT : {x k : Tm Nat'} -> Tm (Cmp (add x (Suc k)) x)
  CmpGT = DC 2f _

  cmpHelper : {x y : _} -> Tm (Cmp x y) -> Tm (Cmp (Suc x) (Suc y))
  cmpHelper c =
    ifTag 0f c (\{ _ CRefl -> CmpLT }) \f0 ->
    ifTag 1f c (\{ _ CRefl -> CmpEQ }) \f1 ->
    ifTag 2f c (\{ _ CRefl -> CmpGT }) \f2 ->
    coveredBy (f0 :: f1 :: f2 :: [])

  cmp : (x : Tm Nat') (y : Tm Nat') -> Tm (Cmp x y)
  cmp x y =
    ifTag 0f x (\{ _ CRefl ->
      ifTag 0f y (\{ _ CRefl -> CmpEQ }) \f0 ->
      ifTag 1f y (\{ _ CRefl -> CmpLT }) \f1 ->
      coveredBy (f0 :: f1 :: [])
    }) \f0 ->
    ifTag 1f x (\{ (x , _) CRefl ->
      ifTag 0f y (\{ _ CRefl -> CmpGT }) \f0 ->
      ifTag 1f y (\{ (y , _)  CRefl -> cmpHelper (cmp x y)
      }) \f1 ->
      coveredBy (f0 :: f1 :: [])
    }) \f1 ->
    coveredBy (f0 :: f1 :: [])

  cmpTest = cmp (Suc Zero) (Suc (Suc (Suc Zero)))


