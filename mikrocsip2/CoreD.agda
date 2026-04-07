{-
Same as CoreB.agda but meta-level pattern matching on (CRefl; code; Lam; _,_) is eliminated.

Work in progress.
-}


{-# OPTIONS --erasure #-}

-------------------

infixl 9 _∙_
infixr 6 _=>_
infixr 6 _::_
infixr 6 _:×_
infix  3 _≡≡_

-------------------


--open import Agda.Builtin.String  -- for pretty printing
--open import Agda.Builtin.Nat renaming (suc to S; zero to Z)
open import Equ

data Nat : Set where
  Z : Nat
  S : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat -> Nat -> Nat
Z + n = n
S m + n = S (m + n)

postulate String : Set

{-# BUILTIN STRING String #-}

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


data Ty : Set
data Tm : Ty -> Set

data Tys : Set where
  []   :                              Tys
  _::_ : (t : Ty) -> (Tm t -> Tys) -> Tys

Tms : Tys -> Set
Tms []        = T
Tms (t :: ts) = Tm t × \x -> Tms (ts x)

-- data constructor description
record DCDesc (indices : Tys) : Set where
  inductive
  constructor DCD
  field
    dcName  : String   -- for pretty printing
    dcArgs  : Tys
    sub     : Tms dcArgs -> Tms indices

-- type constructor description
record TCDesc : Set where
  inductive
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
  inductive
  constructor RTCD
  inductive
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

_:×_ : Ty -> Tys -> Tys
a :× as = a :: \_ -> as

_=>_ : Ty -> Ty -> Ty
a => b = Pi a \_ -> b

-----------------------


proj : {params : _} -> Tm (RTC rc params) -> Tms (rdcArgs rc params)
proj (RDC args) = args

etaRecord : {params : _} {t : Tm (RTC rc params)} -> t ≡ RDC (proj t)
etaRecord {t = RDC _} = Refl

--------------------

dcTag : ∀ {indices} -> Tm (TC tc indices) -> dcFin tc
dcTag (DC c _) = c

Σtc : TCDesc -> Set
Σtc tc = Tms (tcIndices tc) × \is -> Tm (TC tc is)

_≡≡_ : {tc : _} {is : _} {is' : _} -> Tm (TC tc is) -> Tm (TC tc is') -> Set
_≡≡_ {tc} {is} {is'} t t' = _≡_ {a = Σtc tc} (is , t) (is' , t')

ifTag : {a : Set} {indices : _} ->
  (tag   : dcFin tc) ->                                           -- dcTag
  (tm    : Tm (TC tc indices)) ->                                 -- scrutenee
  (match : (args : Tms (dcArgs tc tag)) -> DC tag args ≡≡ tm -> a) ->
  (fail  : not (dcTag tm ≡ tag) -> a) ->
    a
ifTag tag (DC tag' l) match fail with decFin tag' tag
... | Yes Refl = match l Refl
... | No  f    = fail f

--------------------------

matchCode : Tm U <=> Ty
matchCode = MkEquiv
  (\{(code a) -> a})
  (\a         -> code a)
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
  (\{(Lam f) -> f})
  (\f        -> Lam f)
  (\{(Lam _) -> Refl})
  (\_        -> Refl)

conflict :
  {tc : _} {is : _} {t t' : Tm (TC tc is)} ->
  not (dcTag t ≡ dcTag t') ->
    t ≡ t' <=> ⊥
conflict ne = MkEquiv
  (\{Refl -> ne Refl})
  (\())
  (\{Refl -> UIP})
  (\())


-----------------------------

module Examples where

  sec = second

  IdDesc = TCD "Id" (U :: \a -> El a :× El a :× []) 1 \where
     0f -> DCD "Refl" (U :: \a -> El a :× []) \(a , x , tt) -> a , x , x , tt

  Id : {a : Ty} -> Tm a -> Tm a -> Ty
  Id {a} x y = TC IdDesc (code a , x , y , tt)

  refl : {x : Tm a} -> Tm (Id x x)
  refl {a} {x} = DC 0f (code a , x , tt)


  equivTel : (
     Ty                  × \a ->
     Tm a                × \b ->
     ((x : Tm a) -> Tm (Id b x) -> Ty) × \P ->
     Tm (P b refl)       × \w ->
     Tm a                × \x ->
     Tm (Id b x)         × \e ->
     ------------------------------ differs from here
     (Tm U × \a' -> Tm (El a') × \_ -> T)  × \a'x' ->
     DC 0f a'x' ≡≡ e     × \ee ->
     T
    ) <=> (
     Ty                  × \a ->
     Tm a                × \b ->
     ((x : Tm a) -> Tm (Id b x) -> Ty) × \P ->
     Tm (P b refl)       × \w ->
     Tm a                × \x ->
     Tm (Id b x)         × \e ->
     ------------------------------ differs from here
     Tm U                × \a' ->
     Tm (El a')          × \x' ->
     DC 0f (a' , x' , tt) ≡≡ e × \ee ->
     T
    )
  equivTel
    = sec \_ -> sec \_ -> sec \_ -> sec \_ -> sec \_ -> sec \_ ->
         assoc
       ∘ sec \_ -> assoc
                 ∘ sec \_ -> unit

  equivCode : (
     Ty                  × \a ->
     Tm a                × \b ->
     ((x : Tm a) -> Tm (Id b x) -> Ty) × \P ->
     Tm (P b refl)       × \w ->
     Tm a                × \x ->
     Tm (Id b x)         × \e ->
     --------------------------------- diff from here
     Tm U                × \a' ->
     Tm (El a')          × \x' ->
     DC 0f (a' , x' , tt) ≡≡ e × \ee ->
     T
    ) <=> (
     Ty                  × \a ->
     Tm a                × \b ->
     ((x : Tm a) -> Tm (Id b x) -> Ty) × \P ->
     Tm (P b refl)       × \w ->
     Tm a                × \x ->
     Tm (Id b x)         × \e ->
     --------------------------------- diff from here
     Ty                  × \a'' ->
     Tm a''              × \x' ->
     DC 0f (code a'' , x' , tt) ≡≡ e × \ee ->
     T
    )
  equivCode
    = sec \_ -> sec \_ -> sec \_ -> sec \_ -> sec \_ -> sec \_ -> first matchCode


  equiv12 : (
     Ty             × \a ->
     Tm a           × \b ->
     ((x : Tm a) -> Tm (Id b x) -> Ty) × \P ->
     Tm (P b refl)  × \w ->
     ----------------------------- diff from here
     Tm a           × \x -> 
     Tm (Id b x)    × \e ->
     Ty             × \a' ->
     (Tm a')        × \x' ->
     refl {a'} {x'} ≡≡ e × \_ ->
     T
    ) <=> (
     Ty             × \a ->
     Tm a           × \b ->
     ((x : Tm a) -> Tm (Id b x) -> Ty) × \P ->
     Tm (P b refl)  × \w ->
     ----------------------------- diff from here
     T
    )
  equiv12
    = sec \a -> sec \b -> sec \P -> sec \w ->
        (sec \x -> sec \e ->
            (sec \a' -> sndSwap {Tm a'} {a' ≡ a} {λ x' → refl ≡≡ e × (λ _ → T)} {λ z x₁ →
                subst (λ x₂ → Tms (El x₂ :× El x₂ :× [])) (backward injCode x₁)
                  (z , z , tt)
                  ≡ (b , x , tt)
                  ×
                  (λ e' →
                     subst (λ is → Tm (TC IdDesc is)) (backward injCode x₁ ,≡ e') refl ≡
                     e
                     × (λ e'' → T))} \_ ->
                decomp
              ∘ decomp
              ∘ first injCode
            )
          ∘ solveL
          ∘ (sec \_ -> decomp)
          ∘ solveL
        )
      ∘ (sec \_ -> sndSwap \_ -> decomp)
      ∘ solveR
      ∘ (sec \_ -> delete')
      ∘ solveR



  ---------------- core source --------------
  -- J' a b P w x (refl (code a'') x') = w

  J' : ∀ {a b} -> (P : (x : Tm a) -> Tm (Id b x) -> Ty) -> Tm (P b refl) -> (x : Tm a) -> (e : Tm (Id b x)) -> Tm (P x e)
  J' {a = a} {b = b} P w x e =
--    ifTag 0f e (\{ (code a' , x' , tt) CRefl -> w }) \f0 ->

    ifTag 0f e (\{ a'x' ee ->
      solveBy equivTel
           (a , b , P , w , x , e , a'x' , ee , tt)
        (\{(a , b , P , w , x , e , a'x' , ee , tt) -> Tm (P x e)})
        (\k ->
          solveBy equivCode
               k
            (\{(a , b , P , w , x , e , a'' , x' , ee , tt) -> Tm (P x e)})
            (\k ->
              solveBy equiv12 k
                (\{(a , b , P , w , x , e , a' , x' , ee , tt) -> Tm (P x e)})
                (\{(a , b , P , w , tt) -> w })
              )
          )
        }) \f0 ->

    coveredBy (f0 :: [])


  betaJ' : ∀ {a b} {P : (x : Tm a) -> Tm (Id b x) -> Ty} {w : Tm (P b refl)} -> J' P w b refl ≡ w
  betaJ' = Refl

  ------------------------------------------------

  {-# TERMINATING #-}
  Nat' : Ty

  NatDesc = TCD "Nat" [] 2 \where
      0f -> DCD "Zero" []          \_ -> tt
      1f -> DCD "Suc"  (Nat' :× []) \_ -> tt

  Nat' = TC NatDesc tt

  Zero : Tm Nat'
  Zero = DC 0f _

  Suc : Tm Nat' -> Tm Nat'
  Suc n = DC 1f (n , _)

  {-# TERMINATING #-}
  Vec' : Ty -> Tm Nat' -> Ty

  VecDesc = TCD "Vec" (U :× Nat' :× []) 2 \where
      0f -> DCD "VNil"  (U :× []) \{(a , tt) -> a , Zero , tt}
      1f -> DCD "VCons" (U :: \t -> Nat' :: \n -> El t :× Vec' (El t) n :× []) \(a , n , _) -> a , Suc n , tt

  Vec' t n = TC VecDesc (code t , n , tt)

  VNil : Tm (Vec' a Zero)
  VNil = DC 0f _

  VCons : {n : Tm Nat'} -> Tm a -> Tm (Vec' a n) -> Tm (Vec' a (Suc n))
  VCons a as = DC 1f (_ , _ , a , as , tt)

  equivBot : (
      Ty ×  \b ->
      Ty ×  \c ->
      Tm (Vec' b Zero) × \bs ->
      (Tm U × \a' -> Tm Nat' × \n' → Tm (El a') × \_ -> Tm (Vec' (El a') n') × \_ -> T) × \args ->
      DC 1f args ≡≡ bs × \e ->
      T
    ) <=> ⊥
  equivBot
    = sndBot \_ -> sndBot \_ -> sndBot \_ -> sndBot \ args@(a' , n' , _) ->
           decomp
         ∘ decomp
         ∘ sndBot \{Refl -> decomp                                  -- Refl?
                      ∘ first (conflict \())
                      ∘ botFst
                   }

  zipWith : {a b c : Ty} {n : Tm Nat'} (f : Tm a -> Tm b -> Tm c) ->
    Tm (Vec' a n) -> Tm (Vec' b n) -> Tm (Vec' c n)
  zipWith {a} {b} {c} {n} f as bs =
    ifTag 0f as (\{ (a' , tt) Refl ->
      ifTag 0f bs (\{ _ Refl -> VNil }) \f0 ->
      ifTag 1f bs (\{ args e ->
        solveBy equivBot
          ((b , c , bs , args , e , tt))
          ((\(b , c , bs , args , e , _) -> Tm (Vec' c Zero)))
          (\())
                    }) \f1 ->
      coveredBy (f0 :: f1 :: [])
    }) \f0 ->
    ifTag 1f as (\{ (_ , _ , a , as , tt) Refl ->
      ifTag 0f bs (\{ _ () }) \f0 ->
      ifTag 1f bs (\{ (_ , _ , b , bs , _) Refl -> VCons (f a b) (zipWith f as bs) }) \f1 ->
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
    ifTag 1f n (\{ (k , tt) Refl -> Suc (add k m) }) \f1 ->
    coveredBy (f0 :: f1 :: [])

  CmpDesc = TCD "Cmp" (Nat' :× Nat' :× []) 3 \where
    0f -> DCD "CmpLT" (Nat' :× Nat' :× []) \(x , k , tt) -> x , add x (Suc k) , tt
    1f -> DCD "CmpEQ" (Nat' :× [])         \(x , tt)     -> x , x , tt
    2f -> DCD "CmpGT" (Nat' :× Nat' :× []) \(x , k , tt) -> add x (Suc k) , x , tt

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
       Tm Nat' × \x' ->
       Tm Nat' × \y' ->
       Tm Nat' × \u ->
       Tm Nat' × \v ->
       CmpLT {u} {v} ≡≡ cmp x' y' × \e ->
       T
     ) <=> (
       Tm Nat' × \u ->
       Tm Nat' × \v ->
       CmpLT {u} {v} ≡ cmp u (add u (Suc v)) × \_ ->    -- this equality remained but it will not be used
       T       
     )
  equiv =
      sec \_ ->
          (sndSwap \_ ->
            (sec \_ -> sndSwap \_ ->
              decomp
            ∘ decomp
            )
          ∘ solveL
          ∘ sec (\v -> decomp)
          )
        ∘ sec \_ ->
            solveR
          ∘ delete'

  cmp x y =
    ifTag 0f x (\{ _ Refl ->
      ifTag 0f y (\{ _ Refl -> CmpEQ }) \f0 ->
      ifTag 1f y (\{ _ Refl -> CmpLT }) \f1 ->
      coveredBy (f0 :: f1 :: [])
    }) \f0 ->
    ifTag 1f x (\{ (x' , tt) Refl ->
      ifTag 0f y (\{ _ Refl -> CmpGT }) \f0' ->
      ifTag 1f y (\{ (y' , tt) Refl ->
        let c = cmp x' y' in
--        ifTag 0f c (\{ (u , v , tt) Refl -> {!CmpLT!} }) \f0 ->
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

module Examples2 where

------------------

  Bot : Ty
  Bot = TC (TCD "Bot" [] 0 \()) tt

  exfalso' : Tm Bot -> Tm a
  exfalso' t = coveredBy {tag = dcTag t} []


---------------------------------

  module TopAsData where

    -- data Top : Type  where  tt : Top
    Top : Ty
    Top = TC (TCD "Top" [] 1 \{0f -> DCD "tt" [] \_ -> _}) tt

    TT : Tm Top
    TT = DC 0f tt

    

    -- etaTop : (t : Top) -> t ≡ tt)
    -- etaTop tt = Refl
    etaTop : {t : Tm Top} -> t ≡ TT
    etaTop {t} =
      ifTag 0f t (\{tt g → solveBy (decompEq ∘ delete' ) g (λ x → t ≡ TT) sym}) \r0 ->
      coveredBy (r0 :: [])


  Top : Ty
  Top = RTC (RTCD "Top" "TT" [] \_ -> []) tt

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
  Bool = TC (TCD "Bool" [] 2
    \{ 0f -> DCD "True"  [] \_ -> tt
     ; 1f -> DCD "False" [] \_ -> tt
     }) tt

  True : Tm Bool
  True = DC 0f _

  False : Tm Bool
  False = DC 1f _

  indBool : (P : Tm Bool -> Ty) -> Tm (P True) -> Tm (P False) -> (b : Tm Bool) -> Tm (P b)
  indBool P t f b =
    ifTag 0f b (\{ tt g -> solveBy solveTrue (P , t , f , b , g , tt) (λ {(P , _ , _ , b , g , _) → Tm (P b)}) λ {(P , y) → fst y}}) \f0 ->
    ifTag 1f b (\{ tt h → solveBy solveFalse (P , t , f , b , h , tt) (λ {(P , _ , _ , b , g , _) → Tm (P b)}) λ y → fst (snd (snd y)) }) \f1 ->
    coveredBy (f0 :: f1 :: [])
      where
        solveTrue : ((Tm Bool -> Ty) × \P ->
                    (Tm (P True)) × \_ ->
                    (Tm (P False)) × \_ ->
                    (Tm Bool) × \b ->
                    (DC 0f tt ≡≡ b × \_ -> T )) <=> ((Tm Bool -> Ty) × \P ->
                    (Tm (P True)) × (\_ -> (Tm (P False)) × \_ -> T ))
        solveTrue = second (\_ -> second (\_ -> second (λ x₂ → second (λ x₃ → first (decompEq ∘ delete')) ∘ solveR ))) 
        solveFalse : ((Tm Bool -> Ty) × \P ->
                    (Tm (P True)) × \_ ->
                    (Tm (P False)) × \_ ->
                    (Tm Bool) × \b ->
                    (DC 1f tt ≡≡ b × \_ -> T )) <=> ((Tm Bool -> Ty) × \P ->
                    (Tm (P True)) × (\_ -> (Tm (P False)) × \_ -> T ))
        solveFalse = second (\_ -> second (\_ -> second (λ x₂ → second (λ x₃ → first (decompEq ∘ delete')) ∘ solveR ))) 

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
    ifTag 0f b (\{ tt d -> solveBy solveTrue (b , d , tt) (λ x → Tm (F (fst x ))) λ _ → b }) \f0 ->
    ifTag 1f b (\{ _ e -> solveBy solveFalse (b , e , tt) (\x -> Tm (F (fst x ))) λ y → Lam not' }) \f1 ->
    coveredBy (f0 :: f1 :: [])
      where
        solveTrue : ( Tm Bool × \f -> (DC 0f tt ≡≡ f) × \_ -> T)
                      <=> T
        solveTrue = second (λ x → first (decompEq ∘ delete')) ∘ solveR {b = λ v x → T}
        solveFalse : ( Tm Bool × \f -> (DC 1f tt ≡≡ f) × \_ -> T)
                      <=> T
        solveFalse = second (λ x → first (decompEq ∘ delete')) ∘ solveR {b = λ v x → T}


---------------------------------

  module Wrong where

    Sigma : (a : Ty) -> (Tm a -> Ty) -> Ty
    Sigma a b = RTC (RTCD      -- non top-level record description!
         "Sigma"               -- this is bad because names will not be unique
         "_,_"
         []
         \_ -> a :: \z -> b z :× [])
      tt


  Sigma : (a : Ty) -> (Tm a -> Ty) -> Ty
  Sigma a b = RTC (RTCD
       "Sigma"
       "_,_"
       (U :: \a -> (El a => U) :× [])
       \(a , b , _) -> El a :: \x -> El (b ∙ x) :× [])
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

  UDesc = RTCD "U" "code" [] \_ -> U :× []

  U' : Ty
  U' = RTC UDesc _

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
  Pi' a b = RTC (RTCD
           "Pi"
           "Lam"
           (U :: \a -> (El a => U) :× [])
           \(a , b , _) -> Pi (El a) (\x -> El (b ∙ x)) :× []
        )
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
  W S' P = RTC (RTCD
            "W"
            "sup"
            (U :: \S' -> (El S' => U) :× [])
            \(S' , P , _) -> El S' :: \s -> (El (P ∙ s) => W (El S') \s -> El (P ∙ s)) :× []
          )
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
  Nat' = TC (TCD "Nat" [] 2
    \{ 0f -> DCD "Zero" []          \_ -> tt
     ; 1f -> DCD "Suc"  (Nat' :× []) \_ -> tt
     }) tt

  Zero : Tm Nat'
  Zero = DC 0f _

  Suc : Tm Nat' -> Tm Nat'
  Suc n = DC 1f (n , _)

  {-# TERMINATING #-}
  add : Tm Nat' -> Tm Nat' -> Tm Nat'
  add n m =
    ifTag 0f n (\{ _ e -> m }) \f0 ->
    ifTag 1f n (\{ (k , tt) _ -> Suc (add k m) }) \f1 ->
    coveredBy (f0 :: f1 :: [])

  {-# TERMINATING #-}
  indNat : (P : Tm Nat' -> Ty) -> Tm (P Zero) -> ((n : Tm Nat') -> Tm (P n) -> Tm (P (Suc n))) -> (n : Tm Nat') -> Tm (P n)
  indNat P z s n =
    ifTag 0f n (\{ tt g -> solveBy solveZ (P , z , s , n , g , tt) (λ{ (P , _ , _ , n , _ , _) → Tm (P n)}) λ y → fst (snd y) }) \f0 ->
    ifTag 1f n (\{ (k , tt) g -> solveBy solveS (P , z , s , k , n , g , tt) (λ {(P , _ , _ , _ , n , _ , _) → Tm (P n)}) λ {(P , z , s , k , _) → s k (indNat P z s k) }}) \f1 ->
    coveredBy (f0 :: f1 :: [])
      where
        solveZ : (P :: (Tm Nat' -> Ty) ** 
                  z :: (Tm (P Zero)) **
                  s :: ((n : Tm Nat') -> Tm (P n) -> Tm (P (Suc n))) **
                  n :: (Tm Nat') **
                  e :: (DC 0f tt ≡≡ n) **
                  T) <=> (P :: (Tm Nat' -> Ty) ** 
                  z :: (Tm (P Zero)) **
                  s :: ((n : Tm Nat') -> Tm (P n) -> Tm (P (Suc n))) **
                  T)
        solveZ = second (λ _ → second (λ _ → second (λ _ → second (λ _ → (first (decompEq ∘ delete'))) ∘ solveR )))
        solveS : (P :: (Tm Nat' -> Ty) **
                  z :: (Tm (P Zero)) **
                  s :: ((n : Tm Nat') -> Tm (P n) -> Tm (P (Suc n))) **
                  k :: (Tm Nat') **
                  n :: (Tm Nat') **
                  e :: (DC 1f (k , tt) ≡≡ n) **
                  T) <=> (P :: (Tm Nat' -> Ty) **
                  z :: (Tm (P Zero)) **
                  s :: ((n : Tm Nat') -> Tm (P n) -> Tm (P (Suc n))) **
                  k :: (Tm Nat') **
                  T)
        solveS = second (λ _ → second (λ _ → second (λ _ → second λ _ → second (λ _ → first (decompEq ∘ delete' )) ∘ solveR)))

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
  List' t = TC (TCD "List" (U :× []) 2
    \{ 0f -> DCD "Nil"  (U :× []) \a -> a
     ; 1f -> DCD "Cons" (U :: \t -> El t :× List' (El t) :× []) \(a , _) -> a , tt
     }) (code t , tt)

  Nil : Tm (List' a)
  Nil = DC 0f _

  Cons : Tm a -> Tm (List' a) -> Tm (List' a)
  Cons x xs = DC 1f (_ , x , xs , tt)

  {-# TERMINATING #-}
  append : Tm (List' a) -> Tm (List' a) -> Tm (List' a)
  append {a} as bs =
    ifTag 0f as (\{ _ e -> bs }) \f0 ->
    ifTag 1f as (\{ (code aa , x , xs , tt) g -> solveBy solveCons (bs , aa , x , xs , as , g , tt) (λ v → Tm (List' a)) λ y → Cons (fst (snd y)) (append (fst (snd (snd y))) (fst y))   }) \f1 -> -- Cons {a} x (append {a} xs bs)
    coveredBy (f0 :: f1 :: [])
      where
        solveCons : (
                        bs :: (Tm (List' a)) **
                        aa :: Ty **
                        x :: Tm aa **
                        xs :: Tm (List' aa) **
                        as :: (Tm (List' a)) **
                        e :: (DC 1f (code aa , x , xs , tt) ≡≡ as) **
                        T) <=> (bs :: (Tm (List' a)) **
                        x' :: Tm a **
                        as :: (Tm (List' a)) **
                        T)
        solveCons = second (λ _ → second (λ _ → second (λ x₂ → second λ x₃ → second (\ls -> first (decompEq)) ∘ sym<=> assoc  ∘ first swap ∘ assoc ∘ second (λ x₄ → assoc ∘ solveR)
                    ∘ decomp ∘ first injCode)) ∘ sym<=> assoc ∘ sym<=> assoc ∘ first assoc ∘ assoc ∘ second (λ _ → swap) ∘ solveL ∘ second (λ x₁ → delete') ∘ assoc)


  testAppend = the (append (Cons Zero Nil) (Cons (Suc Zero) Nil) ≡ Cons Zero (Cons (Suc Zero) Nil)) Refl


---------------------------------

  {-# TERMINATING #-}
  Vec' : Ty -> Tm Nat' -> Ty
  VecDesc = TCD "Vec" (U :× Nat' :× []) 2
    \{ 0f -> DCD "VNil"  (U :× []) \{(a , tt) -> a , Zero , tt}
     ; 1f -> DCD "VCons" (U :: \t -> Nat' :: \n -> El t :× Vec' (El t) n :× []) \(a , n , _) -> a , Suc n , tt
     }
  Vec' t n = TC VecDesc (code t , n , tt)

  VNil : Tm (Vec' a Zero)
  VNil = DC 0f _

  VCons : {n : Tm Nat'} -> Tm a -> Tm (Vec' a n) -> Tm (Vec' a (Suc n))
  VCons a as = DC 1f (_ , _ , a , as , tt)

  {-# TERMINATING #-}
  zipWith : {a b c : Ty} (f : Tm a -> Tm b -> Tm c) {n : Tm Nat'} ->
    Tm (Vec' a n) -> Tm (Vec' b n) -> Tm (Vec' c n)
  zipWith {a} {b} {c} f {n} as bs =
    ifTag 0f as (\{ (aa , tt) h -> solveBy solveNil1 (f , n , bs , aa , as , h , tt) (λ x → Tm (Vec' c (fst (snd x))))
        λ {(f , bs , tt) → ifTag 0f bs (λ{ (bb , tt) x → solveBy solveCons1 (bb , bs , x , tt) (λ{ x₁ → Tm (Vec' c Zero)}) λ y → VNil}) λ f0 → 
        ifTag 1f bs (λ{( ty , n , elty , vec , tt) x → solveBy (k) (b , aa , n , bs , ty , elty , vec , x , tt) (λ v → Tm (Vec' c Zero)) \() }) λ f1 → coveredBy (f0 :: f1 :: [])}
    {-
      ifTag 0f bs (\{ _ _ -> VNil }) \f0 ->
      ifTag 1f bs (\{ _ () }) \f1 ->
      coveredBy (f0 :: f1 :: [])
    -}
    }) \f0 ->
    ifTag 1f as (\{ (a' , n' , a'' , as' , tt) j ->
      solveBy solveCons2 (n , as , n' , a' , a'' , as' , j , tt) (λ v → Tm (Vec' c n)) λ f1 → 
        ifTag 0f bs (λ{ (ty , tt) x →  {!  8!}}) λ x →
        ifTag 1f bs (λ{ (ty , n' , b' , bs' , tt) eq → solveBy solveCons3 (n , bs , n' , ty , b' , bs' , eq , tt) (λ v → Tm (Vec' c (fst v))) λ y → VCons (f (fst (snd f1)) (fst (snd y))) (zipWith f {! fst (snd (snd f1)) !} (fst (snd (snd y))))}) λ y → coveredBy (x :: y :: [])
    {-
      ifTag 0f bs (\{ _ () }) \f0 ->
      ifTag 1f bs (\{ (_ , _ , b , bs , _) g -> {!   !} }) \f1 -> --VCons (f a b) (zipWith f as bs)
      coveredBy (f0 :: f1 :: [])
    -}
    }) \f1 ->
    coveredBy (f0 :: f1 :: [])
      where
        solveNil1 : (f :: (Tm a -> Tm b -> Tm c) **
          n :: Tm Nat' **
          bs :: (Tm (Vec' b n)) **
          aa :: (Tm U) **
          as :: (Tm (Vec' a n)) **
          e :: (DC 0f (aa , tt) ≡≡ as) **
          T) <=> (f :: (Tm a -> Tm b -> Tm c) **
          bs :: (Tm (Vec' b Zero)) **
          T)
        solveNil1 = sym<=> assoc ∘ second (λ x → second (λ x₁ → second (λ x₂ → second (λ x₃ → first (decompEq ∘ decomp ∘ second (λ x₄ → decomp )) ∘ assoc) ∘ swap) ∘ solveL ∘ second (λ x₂ → assoc) ∘ swap) ∘ swap) 
                    ∘ assoc ∘ second (λ x → solveR ∘ second (λ x₁ → second (λ x₂ → assoc ∘ delete') ∘ solveR))   -- second (λ x → second (λ x₁ → second (λ x₂ → first (decompEq ∘ decomp ∘ second (λ x₃ → decomp))  ∘ assoc)) ∘ swap ∘ second (λ x₁ → solveL) ∘ {!   !}) ∘ {!   !}
        solveCons1 : (bb :: Tm U **
          bs :: (Tm (Vec' b Zero)) **
          e :: (DC 0f (bb , tt) ≡≡ bs) **
          T) <=> T
        solveCons1 = second (λ x → second (λ x₁ → first (decompEq ∘ decomp ∘ second (λ x₂ → decomp)) ∘ assoc) ∘ swap) ∘ solveL ∘ second (λ x → assoc ∘ delete' ∘ assoc ∘ delete') ∘ solveR
        solveCons2 : (
          rn :: Tm Nat' **
          as :: Tm (Vec' a rn) **
          n :: Tm Nat' **
          aa :: (Tm U) **
          el :: Tm (El aa) **
          as' :: (Tm (Vec' (El aa) n)) **
          e :: DC 1f (aa , n , el , as' , tt) ≡≡ as **
          T) <=> (rn :: Tm Nat' ** j :: Tm a ** _ :: Tm (Vec' a rn) ** T)
        solveCons2 = second(\r  -> second (\ q -> second (λ x → second (λ x₁ → second (λ x₂ → second (λ x₃ → first (decompEq ∘ first (decompEq ∘ second (λ x₄ → decompEq ∘ second (λ x₅ → delete) ∘ ignore)) ∘ assoc)
          ∘ assoc ∘ second (λ x₄ → assoc)) ∘ swap) ∘ swap) ∘ solveL ∘ second (λ x₁ → swap) ∘ swap)) ∘ swap) ∘ swap ∘ second (λ x → second (λ x₁ → swap) ∘ solveR) ∘ second (λ x → swap ∘ second (λ x₁ → swap ∘ second (λ x₂ → solveR)))
        solveCons3 : (
          rn :: Tm Nat' **
          bs :: Tm (Vec' b rn) **
          n :: Tm Nat' **
          aa :: (Tm U) **
          el :: Tm (El aa) **
          as' :: (Tm (Vec' (El aa) n)) **
          e :: DC 1f (aa , n , el , as' , tt) ≡≡ bs **
          T) <=> (rn :: Tm Nat' ** j :: Tm b ** _ :: Tm (Vec' b rn) ** T)
        solveCons3 = second (λ x → second (λ x₁ → second (λ x₂ → second (λ x₃ → second (λ x₄ → second (λ x₅ → first (decompEq ∘ first decompEq ∘ assoc ∘ second (λ x₆ → first decompEq ∘ assoc ∘ second (λ x₇ → first delete ∘ unit))) ∘ assoc) ∘ swap) ∘ swap) ∘ solveL)))
            ∘ sym<=> assoc ∘ swap ∘ second (λ x → swap ∘ second λ x₁ → swap ∘ second (λ x₂ → assoc ∘ second (λ x₃ → second (λ x₄ → assoc) ∘ swap) ∘ solveR ∘ solveR))
        k : (b :: Ty **
              aa :: Tm U **
              nn :: Tm Nat' **
              bbs :: Tm (Vec' b Zero ) **
              tty :: Tm U **
              eltty :: Tm (El tty) **
              vecc :: Tm (Vec' (El tty) nn) **
              eq :: _≡≡_ {VecDesc} {tty , (Suc nn , tt)} {code b , Zero , tt} (DC 1f (tty , nn , eltty , vecc , tt)) bbs ** T)
              <=> ⊥
        k = second (λ x₁ → second (λ x₂ → second (λ x₃ → second (λ x₄ → second (λ x₅ → second (λ x₆ → second (λ x₇ →
              first (decompEq ∘ first decompEq ∘ assoc ∘ second (λ x₈ → first (decompEq ∘ second (λ x₉ → delete) ∘ ignore))) ∘ assoc ∘ second (λ x₈ → assoc)) ∘ swap) ∘ swap) ∘ solveL ∘ second (λ x₅ → swap) ∘ swap) ∘ swap ∘ first (conflict (λ())) ∘ botFst) ∘ botSnd) ∘ botSnd)
            ∘ botSnd
---------------------------------

  {-# TERMINATING #-}
  Fin' : Tm Nat' -> Ty
  Fin' n = TC (TCD "Fin" (Nat' :× []) 2
    \{ 0f -> DCD "FZ" (Nat' :× []) \(a , tt) -> Suc a , tt
     ; 1f -> DCD "FS" (Nat' :: \n -> Fin' n :× Fin' (Suc n) :× []) \(n , _ , _ , _) -> n , tt
     }) (n , tt)

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
    cmpHelper x y CmpGT = CmpGT

    cmp' : (x y : Nat) -> Cmp x y
    cmp' Z     Z     = CmpEQ
    cmp' Z     (S y) = CmpLT
    cmp' (S x) Z     = CmpGT
    cmp' (S x) (S y) = cmpHelper x y (cmp x y)

  {-# TERMINATING #-}
  Cmp : Tm Nat' -> Tm Nat' -> Ty
  Cmp n m = TC (TCD "Cmp" (Nat' :× Nat' :× []) 3
    \{ 0f -> DCD "CmpLT" (Nat' :× Nat' :× []) \(x , k , tt) -> x , add x (Suc k) , tt
     ; 1f -> DCD "CmpEQ" (Nat' :× [])        \(x , tt)     -> x , x , tt
     ; 2f -> DCD "CmpGT" (Nat' :× Nat' :× []) \(x , k , tt) -> add x (Suc k) , x , tt
     }) (n , m , tt)

  CmpLT : {x k : Tm Nat'} -> Tm (Cmp x (add x (Suc k)))
  CmpLT = DC 0f _

  CmpEQ : {x : Tm Nat'} -> Tm (Cmp x x)
  CmpEQ = DC 1f _

  CmpGT : {x k : Tm Nat'} -> Tm (Cmp (add x (Suc k)) x)
  CmpGT = DC 2f _

-- Agda gets stuck on this?!
  cmpHelper : {x y : _} -> Tm (Cmp x y) -> Tm (Cmp (Suc x) (Suc y))
  cmpHelper c =
    ifTag 0f c (\{ (k , j , tt) g -> solveBy solveLT (_ , _ , k , j , c , g , tt) (λ{ (x , y , _) → Tm (Cmp (Suc x) (Suc y))}) λ _ → CmpLT }) \f0 ->
    ifTag 1f c (\{ (k , tt) h -> solveBy solveEq (_ , _ , k , c , h , tt) (λ{ (fst₁ , fst₂ , snd₁) → Tm (Cmp (Suc fst₁) (Suc fst₂))}) λ y₁ → CmpEQ }) \f1 ->
    ifTag 2f c (\{ (k , j , tt) m -> solveBy solveGT (_ , _ , k , j , c , m , tt) ((λ{ (x , y , _) → Tm (Cmp (Suc x) (Suc y))})) λ y → CmpGT }) \f2 ->
    coveredBy (f0 :: f1 :: f2 :: [])
      where
        solveLT : (x :: (Tm Nat') **
          y :: (Tm Nat') **
          k :: (Tm Nat') **
          j :: (Tm Nat') **
          c :: (Tm (Cmp x y)) **
          e :: (DC 0f (k , j , tt) ≡≡ c) **
          T) <=> (x :: (Tm Nat') **
          y :: (Tm Nat') **
          T)
        solveLT = second (λ _ → second (λ _ → second (λ _ → second (λ _ → second (λ á → first (decompEq ∘ decomp ∘ second (λ ő → decomp ∘ second (λ é → delete'))
                  ) ∘ assoc ))))) ∘ sym<=> assoc ∘ second (λ x₁ → sym<=> assoc)  ∘ swap  ∘ second (λ _ → second (λ _ → swap) ∘ assoc ∘ swap ∘ second (λ x₂ → solveR) ∘ second (λ _ → second (λ x₄ → assoc) ∘ swap) ∘ solveR ∘ solveR) ∘ assoc

        solveEq : (x :: (Tm Nat') **
          y :: (Tm Nat') **
          k :: (Tm Nat') **
          c :: (Tm (Cmp x y)) **
          e :: (DC 1f (k , tt) ≡≡ c) **
          T) <=> (x :: (Tm Nat') **
          T)
        solveEq = second (λ _ → second (λ _ → second (λ _ → second (λ x₄ → first (decompEq ∘ decomp ∘ second (λ { _ → decomp ∘ second (λ{ _ → delete'})})))))) ∘ sym<=> assoc ∘ second (λ x₁ → second (λ x₂ → second (λ x₃ → assoc) ∘ swap) ∘ solveL ∘ second (λ _ → assoc) ∘ swap) ∘ assoc ∘ second (λ _ → solveR) ∘ second (λ x₁ → solveR)

        solveGT : (x :: (Tm Nat') **
          y :: (Tm Nat') **
          k :: (Tm Nat') **
          j :: (Tm Nat') **
          c :: (Tm (Cmp x y)) **
          e :: (DC 2f (k , j , tt) ≡≡ c) **
          T) <=> (x :: (Tm Nat') **
          y :: (Tm Nat') **
          T)
        solveGT = second (λ _ → second (λ _ → second (λ _ → second (λ _ → second (λ á → first (decompEq ∘ decomp ∘ second (λ ő → decomp ∘ second (λ é → delete'))
                  ) ∘ assoc ))))) ∘ sym<=> assoc ∘ second (λ x₁ → sym<=> assoc)  ∘ swap  ∘ second (λ _ → second (λ _ → swap) ∘ assoc ∘ swap ∘ second (λ x₂ → solveR) ∘ second (λ _ → second (λ x₄ → assoc) ∘ swap) ∘ solveR ∘ solveR) ∘ assoc


  cmp : (x : Tm Nat') (y : Tm Nat') -> Tm (Cmp x y)
  cmp x y =
    ifTag 0f x (\{ _ Refl ->
      ifTag 0f y (\{ _ Refl -> CmpEQ }) \f0 ->
      ifTag 1f y (\{ _ Refl -> CmpLT }) \f1 ->
      coveredBy (f0 :: f1 :: [])
    }) \f0 ->
    ifTag 1f x (\{ (x , _) Refl ->
      ifTag 0f y (\{ _ Refl -> CmpGT }) \f0 ->
      ifTag 1f y (\{ (y , _)  Refl -> cmpHelper (cmp x y)
      }) \f1 ->
      coveredBy (f0 :: f1 :: [])
    }) \f1 ->
    coveredBy (f0 :: f1 :: [])

  cmpTest = cmp (Suc Zero) (Suc (Suc (Suc Zero)))

