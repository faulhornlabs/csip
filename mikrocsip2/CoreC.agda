{-
Same as CoreB.agda but neutral terms are added.
Printing is now possible.
Lam and ifTag is not a netural term; to achieve this LHS terms are separated from terms.
-}


{-# OPTIONS --type-in-type --rewriting #-}

open import Agda.Builtin.String using (String; primStringAppend)
open import Agda.Builtin.Nat using (Nat) renaming (suc to S; zero to Z)

-------------------

infixl 9 _∙_
infixl 9 _$_
infixr 6 _=>_
infixr 6 _::_
infixr 6 _:×_
infix  3 _≡_
infix  3 _≡≡_
infixr 2 _×_
infixr 2 _+++_
infixr 0 _,_

-------------------

record T : Set where
  constructor tt


record _×_ (A : Set) (B : A -> Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

open _×_


data ⊥ : Set where

not : Set -> Set
not A = A -> ⊥

exfalso : {A : Set} -> ⊥ -> A
exfalso ()


Π : (A : Set) (B : A -> Set) -> Set
Π A B = (x : A) -> B x


---------------------

data _≡_ {a : Set} (x : a) : a -> Set where
  Refl : x ≡ x

{-# BUILTIN REWRITE _≡_ #-}

-------------------

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
... | No  f = No \{Refl -> f Refl}

data FinVec : (n : _) -> (P : Fin n -> Set) -> Set₁ where
  []   : ∀ {P} -> FinVec Z P
  _::_ : ∀ {n P} -> P FZ -> FinVec n (\f -> P (FS f)) -> FinVec (S n) P

indexFinVec : ∀ {n P} -> FinVec n P -> (f : Fin n) -> P f
indexFinVec (v :: vs) FZ     = v
indexFinVec (v :: vs) (FS s) = indexFinVec vs s

--------------------------------------------

data Ty  : Set
data Tm  : Ty -> Set

data Tys : Set where
  []   :                              Tys
  _::_ : (t : Ty) -> (Tm t -> Tys) -> Tys

Tms : Tys -> Set
Tms []        = T
Tms (t :: ts) = Tm t × \x -> Tms (ts x)

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

Name = String

data Spine : Ty -> Set

data Ty where
  U    :                                   Ty
  Pi   : (a : Ty) -> (Tm a -> Ty) ->       Ty
  TC   : (tc : _) -> Tms (tcIndices tc) -> Ty
  RTC  : (rc : _) -> Tms (rParams rc) ->   Ty
  TVar : Spine U ->                        Ty

data Spine where
  SNil : Name ->                         Spine a
  SApp : Spine (Pi a b) -> (x : Tm a) -> Spine (b x)

data TmL : Ty -> Set     -- LHS term

data Tm where
  code  : Ty ->                                            Tm U
  DC    : (tag : dcFin tc) (args : Tms (dcArgs tc tag)) -> Tm (TC tc (sub tc tag args))
  RDC   : {is : _} (args : Tms (rdcArgs rc is)) ->         Tm (RTC rc is)
  Def   : Spine a -> TmL a ->                              Tm a

{-# NO_POSITIVITY_CHECK #-}
data TmL where
  Lam   : ((x : Tm a) -> TmL (b x)) -> TmL (Pi a b)
  Ret   : Tm a ->                      TmL a
  Stuck :                              TmL a

def : Name -> TmL a -> Tm a
def n f = Def (SNil n) f

var : Name -> Tm a
var n = Def (SNil n) Stuck

postulate
  defRet : ∀ {a} {s : Spine a} {t : Tm a} -> Def s (Ret t) ≡ t

{-# REWRITE defRet #-}

El : Tm U -> Ty
El (code t)        = t
El (Def _ (Ret t)) = El t
El (Def s Stuck)   = TVar s

_∙L_  : TmL (Pi a b) -> Π (Tm a) \x -> TmL (b x)

_∙_  : Tm (Pi a b) -> Π (Tm a) \x -> Tm (b x)
Def s f ∙ x = Def (SApp s x) (f ∙L x)

Lam f ∙L x = f x
Ret f ∙L x = Ret (f ∙ x)
Stuck ∙L x = Stuck

--------------------

_:×_ : Ty -> Tys -> Tys
a :× as = a :: \_ -> as

_=>_ : Ty -> Ty -> Ty
a => b = Pi a \_ -> b

-----------------------

proj : ∀ {a} {params : _} ->
  (tm    : Tm (RTC rc params)) ->
  (match : (args : Tms (rdcArgs rc params)) -> RDC args ≡ tm -> TmL a)
  -> TmL a
proj (RDC args) match = match args Refl
proj (Def _ (Ret t)) match = proj t match
proj (Def x Stuck) match = Stuck


--------------------

data TagIs {tc : TCDesc} : {indices : Tms (tcIndices tc)} -> Tm (TC tc indices) -> dcFin tc -> Set where
  DCTag : ∀ {t args} -> TagIs (DC t args) t

coveredBy : ∀ {a} {indices : _} {t : Tm (TC tc indices)} -> FinVec (numOfCstrs tc) (\f -> not (TagIs t f)) -> TmL a
coveredBy {t = DC tag args}   vs = exfalso (indexFinVec {P = λ f → not (TagIs _ f)} vs tag DCTag)
coveredBy {t = Def _ (Ret t)} vs = coveredBy {t = t} vs
coveredBy {t = Def x Stuck}   vs = Stuck

_≡≡_ : {tc : _} {is : _} {is' : _} -> Tm (TC tc is) -> Tm (TC tc is') -> Set
_≡≡_ {tc} {is} {is'} t t' = (is , t) ≡ (is' , t')

ifTag : {a : Ty} {indices : _} ->
  (tag   : dcFin tc) ->
  (tm    : Tm (TC tc indices)) ->                                 -- scrutenee
  (match : (args : Tms (dcArgs tc tag)) -> DC tag args ≡≡ tm -> TmL a) ->
  (fail  : not (TagIs tm tag) -> TmL a) ->
    TmL a
ifTag {tc = tc} tag (DC tag' l) match fail with decFin tag' tag
... | Yes Refl    = match l Refl
... | No  f       = fail \{DCTag -> f Refl}
ifTag t (Def _ (Ret a)) m f = ifTag t a m f
ifTag _ (Def _ Stuck)   _ _ = Stuck


-------------------------------------

_+++_ : String -> String -> String
a +++ b = primStringAppend a b

parens : String -> String
parens a = "(" +++ a +++ ")"

data Doc : Set where
  DVar : String -> Doc
  DLam : String -> Doc -> Doc
  _$_  : Doc -> Doc -> Doc

showDoc' : Nat -> Nat -> Doc -> String
showDoc' _ _ (DVar n)   = n
showDoc' p 1 (DLam n d) = parens ("\\" +++ n +++ " -> " +++ showDoc' 0 0 d)
showDoc' p q (DLam n d) =         "\\" +++ n +++ " -> " +++ showDoc' 0 q d
showDoc' 1 q (a $ b)    = parens (showDoc' 0 1 a +++ " " +++ showDoc' 1 0 b)
showDoc' p q (a $ b)    =         showDoc' p 1 a +++ " " +++ showDoc' 1 q b

showDoc = showDoc' Z Z

testDoc = showDoc (DLam "a" (DVar "a" $ DVar "b") $ (DVar "c" $ DVar "e") $ DVar "d" $ DLam "a" (DLam "b" (DVar "a")))

-----------------------------------

printTy    : Ty -> Doc
printTm    : Tm a -> Doc
printTms   : Tms as -> Doc -> Doc
printSpine : Spine a -> Doc

printSpine (SNil x) = DVar x
printSpine (SApp s x) = printSpine s $ printTm x

printTy U = DVar "U"
printTy (Pi t x)   = DVar "Pi" $ printTy t $ DLam "v" (printTy (x (var "v")))
printTy (TC tc x)  = printTms x (DVar (tcName tc))
printTy (RTC rc x) = printTms x (DVar (rtcName rc))
printTy (TVar x)   = printSpine x

printTm (code x) = printTy x
printTm (DC {tc = tc} tag args) = printTms args (DVar (DCDesc.dcName (dcDescs tc tag)))
printTm (RDC {rc = rc} args) = printTms args (DVar (rdcName rc))
printTm (Def x _) = printSpine x

printTms {as = []} tt acc = acc
printTms {as = a :: as} (t , ts) acc = printTms ts (acc $ printTm t)

showTm : Tm a -> String
showTm t = showDoc (printTm t)

----------------

the : (a : Set) -> a -> a
the _ x = x


module _ where


  {-# TERMINATING #-}
  Nat' : Ty

  NatDesc = TCD "Nat" [] 2 \where
      0f -> DCD "Zero" []           \_ -> tt
      1f -> DCD "Suc"  (Nat' :× []) \_ -> tt

  Nat' = TC NatDesc tt

  Zero : Tm Nat'
  Zero = DC 0f _

  Suc : Tm (Nat' => Nat')
  Suc = def "Suc" (Lam \n -> Ret (DC 1f (n , tt)))

  {-# TERMINATING #-}
  add : Tm (Nat' => Nat' => Nat')
  add = def "add" (Lam \n -> Lam \m ->
    ifTag 0f n (\{ _ e -> Ret m }) \f0 ->
    ifTag 1f n (\{ (k , tt) e -> Ret (Suc ∙ (add ∙ k ∙ m)) }) \f1 ->
    coveredBy (f0 :: f1 :: [])
    )

  addTest = the (add ∙ (Suc ∙ Zero) ∙ (Suc ∙ Zero) ≡ Suc ∙ (Suc ∙ Zero)) Refl
  addTest' = the ((\n -> add ∙ (Suc ∙ Zero) ∙ n) ≡ \n -> Suc ∙ n) Refl

  testPrint = showTm (add ∙ (Suc ∙ Zero) ∙ (Suc ∙ Zero))

  {-# TERMINATING #-}
  Fin' : Tm (Nat' => U)

  FinDesc = TCD "Fin" (Nat' :× []) 2 \where
    0f -> DCD "FZ" (Nat' :× []) \(a , tt) -> Suc ∙ a , tt
    1f -> DCD "FS" (Nat' :: \n -> El (Fin' ∙ n) :× El (Fin' ∙ (Suc ∙ n)) :× []) \(n , _ , _ , _) -> n , tt

  Fin' = def "Fin" (Lam \n -> Ret (code (TC FinDesc (n , tt))))

  testPrint' = showTm (code (Pi Nat' \n -> El (Fin' ∙ (add ∙ (Suc ∙ n) ∙ n))))

  --------------------------------------

  Sigma : (a : Ty) -> Tm (a => U) -> Ty

  SigmaDesc = RTCD
       "Sigma"
       "_,_"
       (U :: \a -> (El a => U) :× [])
       \(a , b , _) -> El a :: \x -> El (b ∙ x) :× []

  Sigma a b = RTC SigmaDesc (code a , b , tt)


  Pair : {b : Tm (a => U)} -> (x : Tm a) -> Tm (El (b ∙ x)) -> Tm (Sigma a b)
  Pair x y = RDC (x , y , _)

  Fst : {b : Tm (a => U)} -> Tm (Sigma a b => a)
  Fst = def "fst" (Lam \p -> proj p \{(a , _ , _) Refl -> Ret a})

  Snd : {b : Tm (a => U)} -> Tm (Pi (Sigma a b) \t -> El (b ∙ (Fst ∙ t)))
  Snd = def "snd" (Lam \p -> proj p \{(_ , b , _) Refl -> Ret b})

  betaFst : {b : Tm (a => U)} {x : Tm a} {y : Tm (El (b ∙ x))} -> Fst {b = b} ∙ (Pair x y) ≡ x
  betaFst = Refl

  betaSnd : {b : Tm (a => U)} {x : Tm a} {y : Tm (El (b ∙ x))} -> Snd {b = b} ∙ (Pair x y) ≡ y
  betaSnd = Refl

  etaSigma : {b : Tm (a => U)} {t : Tm (Sigma a b)} -> t ≡ Pair (Fst ∙ t) (Snd ∙ t)
  etaSigma {t = RDC args}      = Refl
  etaSigma {t = Def _ (Ret t)} = etaSigma {t = t}
  etaSigma {t = Def x Stuck}   = {!!}

