
import Data.Vect

--------------------------------- utils

private infixr 3 ==>

(==>) : Type -> Type -> Type
a ==> b = (1 _ : a) -> b

revApp : List a -> List a -> List a
revApp Nil as = as
revApp (x :: as) bs = revApp as (x :: bs)

sub : Nat -> Nat -> Nat
sub (S i) (S j) = sub i j
sub n Z = n
sub Z n = Z

coe : (0 a : Type) -> (0 b : Type) -> a -> b
coe a b c = believe_me c


data LList : Type -> Type where
  LLNil : LList a
  LLCons : a ==> LList a ==> LList a

lmap : (a ==> b) -> LList a ==> LList b
lmap f LLNil = LLNil
lmap f (LLCons a as) = LLCons (f a) $ lmap f as

lappend : LList a ==> LList a ==> LList a
lappend LLNil as = as
lappend (LLCons a as) bs = LLCons a (lappend as bs)


data LVect : Nat -> Type -> Type where
  VNil  : LVect 0 a
  VCons : a ==> LVect n a ==> LVect (S n) a


------------------------------------ object types

data Polarity : Type where
  Value       : Polarity
  Computation : Polarity

data Ty : Polarity -> Type where
  Int'   :                    Ty Value
  Buffer :                    Ty Value
  FunPtr : Ty Computation  -> Ty Value
  Fun    : List (Ty Value) -> Ty Computation

TyC = Ty Computation

Vs = List (Ty Value)


----------------------------------- phases

data LPhase = PM Bool Bool  -- Dup, Here

data LinPhase
  = A           -- LFree, LAlloc
  | L1          -- LAllocs

data Phase
  = I             -- HOAS
  | PD LPhase Vs  -- DeBruijn
  | L LinPhase    -- linear HOAS

PDup   = PD (PM True False)
PMixed = PD (PM True True)

-- rename to Var?
data Extend : LPhase -> Ty Value -> Vs -> Vs -> Type where
                 -- Extend t ts us    ~    t :: ts ~~ us
  There : Extend l u as bs -> Extend l            u (t :: as) (t :: bs)
  Dup   :                     Extend (PM True l)  t (t :: ts) (t :: ts)
  Here  :                     Extend (PM l True)  t ts        (t :: ts)


--------------------------------------------------- ojbect codes

data Code : Phase -> Ty p -> Type

CodeFun ts = Code I (Fun ts)

LCode : LinPhase -> Ty p -> Type
LCode l t = Code (L l) t

data Code where

------------------------------ HOAS

  Lam : (Code I t -> CodeFun ts) -> CodeFun (t :: ts)
--  App : CodeFun (t :: ts) -> (Code I t -> CodeFun ts)
  Add : Code I Int' -> Code I Int' -> (Code I Int' -> CodeFun ts) -> CodeFun ts
  Print : Code I Int' -> CodeFun ts -> CodeFun ts
  End : CodeFun ts
  Var : Nat -> Code I {p = Value} t

------------------------------ DeBruijn

  DLam   : Code (PD l (t :: ts)) (Fun us) -> Code (PD l ts) (Fun (t :: us))
  DAdd   : Extend l Int' bs cs
        -> Extend l Int' as bs
        -> Code (PD l (Int' :: as)) (Fun us)
        -> Code (PD l cs) (Fun us)
  DPrint : Extend l Int' bs cs -> Code (PD l bs) (Fun us) -> Code (PD l cs) (Fun us)
  DEnd   : Code (PD l []) (Fun [])

  DFree : Code (PDup ts) (Fun us) -> Code (PDup (t :: ts)) (Fun us)

  DKLam : Code (PMixed ts) (Fun us) -> Code (PMixed ts) (Fun (t :: us))

------------------------------ Linear HOAS

  LLam  : (LCode l t ==> LCode l (Fun ts)) ==> LCode l (Fun (t :: ts))
  LKLam : LCode l (Fun ts) ==> LCode l (Fun (t :: ts))
--  LApp  : LCode l (Fun (t :: ts)) ==> LCode l t ==> LCode l (Fun ts) 
  LAdd   : LCode l Int' ==> LCode l Int' ==> (LCode l Int' ==> LCode l Int' ==> LCode l (Fun ts)) ==> LCode l (Fun ts)
  LPrint : LCode l Int' ==> (LCode l Int' ==> LCode l (Fun ts)) ==> LCode l (Fun ts)
  LMov   : LCode l Int' ==> LCode l Int' ==> (LCode l Int' ==> LCode l Int' ==> LCode l (Fun ts)) ==> LCode l (Fun ts)
  LEnd   : LList (LCode l Int') ==> LCode l (Fun ts)

  LFree  : LCode A Int' ==> LCode A (Fun ts) ==> LCode A (Fun ts)
  LAlloc : (LCode A Int' ==> LCode A (Fun ts)) ==> LCode A (Fun ts)

  LAllocs : (LCode L1 Int' ==> LCode L1 (Fun ts)) ==> LCode L1 (Fun ts)
  LVar   : LCode {p = Value} L1 t ==> LCode A t


------------------------------------------------- HOAS -> DeBruijn


mkExt' : Nat -> Extend (PM True False) t ts ts
mkExt' {t = t} {ts = ts} (S n) = believe_me (There {u = t} {t = t} (mkExt' {ts = ts} n))
mkExt' {t = t} {ts = ts} Z = believe_me (Dup {l = False} {t = t} {ts = ts})

mkExt : Nat -> Nat -> Extend (PM True False) t ts ts
mkExt a b = mkExt' $ sub a (S b)

mkEnd : Nat -> Code (PDup ts) (Fun us)
mkEnd Z = coe (Code (PDup _) _) _ DEnd
mkEnd {ts} {us} (S i) = coe (Code (PDup (Int' :: ts)) (Fun us)) _ (DFree (mkEnd i))

db : (n : Nat) -> {0 ts : _} {- length ts = n -} -> CodeFun us -> Code (PDup ts) (Fun us)
db i (Add (Var a) (Var b) cont) = DAdd (mkExt i a) (mkExt i b) $ db (1+i) $ cont (Var i)
db i {ts} (Lam {t} f) = DLam (db (1+i) {ts = t :: ts} $ f (Var i))
db i (Print (Var a) c) = DPrint (mkExt i a) $ db i c
db i End = mkEnd i

--------------------------------------------- dup DeBruijn -> mixed DeBruijn

data Usage : Vs -> Vs -> Type where
  Used   : Usage us ts -> Usage (t :: us) (t :: ts)
  Unused : Usage us ts -> Usage       us  (t :: ts)
  UNil   :                Usage       []        []

-- TODO: linear arrows
mkExtend : Usage us ts' -> Extend (PM True False) t ts' ts -> ({0 vs : _} -> Usage vs ts -> Extend (PM True True) t us vs -> r) -> r
mkExtend (Used   u) Dup       c = c (Used u) Dup
mkExtend (Unused u) Dup       c = c (Used u) Here
mkExtend (Used   u) (There e) c = mkExtend u e $ \u, e => c (Used   u) (There e)
mkExtend (Unused u) (There e) c = mkExtend u e $ \u, e => c (Unused u) e

caseExt : Extend (PM True False) t as bs -> (as = bs -> r) -> r
caseExt (There e) cont = caseExt e $ \Refl => cont Refl
caseExt Dup cont = cont Refl

lamUsed : Usage us (t :: ts) -> ({0 vs : _} -> {- (Usage) -> -} Usage vs ts -> r) -> r
lamUsed (Used   u) c = c u
lamUsed (Unused u) c = c u

reduce : Code (PDup ts) (Fun ks) -> ({0 us : _} -> Usage us ts -> Code (PMixed us) (Fun ks) -> r) -> r
reduce (DLam e)     cont = reduce e $ \u, e => case u of
  Unused u => cont u $ DKLam e
  Used u => cont u $ DLam e
reduce DEnd         cont = cont UNil DEnd
reduce (DAdd a b c) cont = reduce c $ \u, c => case u of
  Unused u => caseExt b $ \Refl => caseExt a $ \Refl => cont u c
  Used u => mkExtend u b $ \u, b => mkExtend u a $ \u, a => cont u (DAdd a b c)
reduce (DFree c) cont = reduce c $ \u, c => cont (Unused u) c
reduce (DPrint a c) cont = reduce c $ \u, c => mkExtend u a $ \u, a => cont u (DPrint a c)


--------------------------------- DeBruijn -> linear HOAS


data DU : Ty Value -> Vs -> Vs -> Type where
  RDup : Extend (PM False True) t ts' ts -> ts = us -> DU t ts us
  RLin : Extend (PM False True) t ts us -> DU t ts us

-- dup or lin usage
caseUsage : Extend l t ts us -> DU t ts us
caseUsage Dup = RDup Here Refl
caseUsage Here = RLin Here
caseUsage (There e) = case caseUsage e of
  RDup a Refl => RDup (There a) Refl
  RLin a => RLin (There a)

data LEnv : LinPhase -> Vs -> Type where
  LCons : LCode l t ==> LEnv l ts ==> LEnv l (t :: ts)
  LNil  : LEnv l []

takeOut : Extend (PM False True) u us ts -> LEnv l ts ==> (LCode l u ==> LEnv l us ==> r) ==> r
takeOut (Here {l = False})      (LCons c cs) cont = cont c cs
takeOut (There e) (LCons c cs) cont = takeOut e cs $ \d, e => cont d (LCons c e)

putBack : Extend (PM False True) u us ts -> LCode l u ==> LEnv l us ==> LEnv l ts
putBack Here c cs = LCons c cs
putBack (There e) c (LCons d cs) = LCons d (putBack e c cs)

eval : Code (PMixed ts) (Fun us) -> LEnv A ts ==> LCode A (Fun us)
eval DEnd LNil = LEnd LLNil
eval (DLam c) e = LLam $ \a => eval c (LCons a e)
eval (DKLam c) e = LKLam $ eval c e
eval (DPrint a c) e = case (caseUsage a) of
  RDup k Refl => takeOut k e $ \a, e => LPrint a $ \a => eval c (putBack k a e)
  RLin a => takeOut a e $ \a, e => LPrint a $ \a => LFree a $ eval c e
eval (DAdd a b c) e = case (caseUsage a) of
  RDup ka Refl => takeOut ka e $ \a, e => LAlloc $ \a' => LMov a a' $ \a, a' => let e = putBack ka a' e in case (caseUsage b) of
    RDup kb Refl => takeOut kb e $ \b, e => LAdd a b $ \a, b => eval c (LCons a $ putBack kb b e)
    RLin kb      => takeOut kb e $ \b, e => LAdd a b $ \a, b => LFree b $ eval c (LCons a e)
  RLin ka => takeOut ka e $ \a, e => case (caseUsage b) of
    RDup kb Refl => takeOut kb e $ \b, e => LAdd a b $ \a, b => eval c (LCons a $ putBack kb b e)
    RLin kb      => takeOut kb e $ \b, e => LAdd a b $ \a, b => LFree b $ eval c (LCons a e)

----------------------------------------------- linear HOAS -> linear HOAS

addl : LList (LCode A Int') ==> LList (LCode L1 Int') ==> LList (LCode L1 Int')
addl LLNil as = as
addl (LLCons (LVar a) as) bs = LLCons a $ addl as bs

line : LCode A (Fun ts) ==> LList (LCode A Int') ==> LCode L1 (Fun ts)
line (LFree a c) as = line c (LLCons a as)
line (LAlloc c) (LLCons a as) = line (c a) as
line (LAlloc c) LLNil = LAllocs $ \a => line (c $ LVar a) LLNil
line (LLam f) as = LLam $ \a => line (f $ LVar a) as
line (LKLam f) as = LKLam $ line f as
line (LAdd (LVar a) (LVar b) c) as = LAdd a b $ \a, b => line (c (LVar a) (LVar b)) as
line (LMov (LVar a) (LVar b) c) as = LMov a b $ \a, b => line (c (LVar a) (LVar b)) as
line (LPrint (LVar a) c) as = LPrint a $ \a => line (c $ LVar a) as
line (LEnd bs) as = LEnd (addl bs (addl as LLNil))


--------------------------------------- transformations

closed a = a

tr1 : closed (CodeFun ts) -> Code (PDup   []) (Fun ts)
tr2 : Code (PDup   []) (Fun us) -> Code (PMixed []) (Fun us)
tr3 : Code (PMixed []) (Fun us) -> LCode A (Fun us)
tr4 : LCode A (Fun ts) ==> LCode L1 (Fun ts)

tr1 a = db 0 a
tr2 a = reduce a $ \UNil, a => a
tr3 a = eval a LNil
tr4 a = line a LLNil

t0 : CodeFun ts -> Code I (Fun ts)
t1 : CodeFun ts -> Code (PDup   []) (Fun ts)
t2 : CodeFun ts -> Code (PMixed []) (Fun ts)
t3 : CodeFun ts -> LCode A (Fun ts)
t4 : CodeFun ts -> LCode L1 (Fun ts)

t0 a = a
t1 a = tr1 (t0 a)
t2 a = tr2 (t1 a)
t3 a = tr3 (t2 a)
t4 a = tr4 (t3 a)

--------------------------------------- examples

pl0 : CodeFun [Int']
pl0 = Lam $ \a => Add a a $ \c => Print c End

pl1 : CodeFun [Int', Int']
pl1 = Lam $ \a => Lam $ \b => Add a b $ \c => Add c b $ \d => Print d End


