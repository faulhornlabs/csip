-- agda-quicker --no-main --ghc-dont-call-ghc --compile --compile-dir=circom CircomA.agda
open import Agda.Builtin.String using (String; primStringAppend) renaming (primShowNat to show)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_; _-_; _*_; _<_; suc; zero; div-helper; mod-helper) renaming (_==_ to _=?=_)
open import Agda.Builtin.Equality using (refl) renaming (_≡_ to _===_)
open import Agda.Builtin.TrustMe using (primTrustMe)

--------------------------------------------------------

infixl 9 _∙_ _∙c_ _∙m_ _∙v_
infixr 8 _^_
infixl 7 _c*_ _/m_ _*m_ _/u_ _*u_ _c*m_
infixl 6 _+ml_ _+mu_ _-ml_ _-mu_ _+u_ _-u_ _+l_ _-l_
infix  5 _==m_&&_ [_*_]==m_&&_ _==_ [_*_]==_
infixr 4 _::_
infixr 3 _<>_
infixr 3 _=>_
infixr 0 _$_

--------------------------------------------------------

sym : {a : Set} {x y : a} -> x === y -> y === x
sym refl = refl

trans : {a : Set} {x y z : a} -> x === y -> y === z -> x === z
trans refl refl = refl

cong : {a b : Set} {x y : a} -> (f : a -> b) -> x === y -> f x === f y
cong f refl = refl

subst : {a : Set} {x y : a} -> (P : a -> Set) -> x === y -> P x -> P y
subst f refl x = x

_<>_ : String -> String -> String
_<>_ = primStringAppend

_^_ : Nat -> Nat -> Nat
x ^ zero  = 1
x ^ suc n = x * x ^ n

not : Bool -> Bool
not true  = false
not false = true

data T : Bool -> Set where
  yes : T true

record NonZero (n : Nat) : Set where
  field
    nonZero : T (not (n =?= 0))

instance
  nonZero : ∀ {n} -> NonZero (suc n)
  nonZero = record { nonZero = yes }

_/_ : (dividend divisor : Nat) .{{_ : NonZero divisor}} -> Nat
m / (suc n) = div-helper 0 n m n

_%_ : (dividend divisor : Nat) .{{_ : NonZero divisor}} -> Nat
m % (suc n) = mod-helper 0 n m n


postulate
  impossible : ∀ {a : Set} -> a
  TODO : ∀ {a : Set} -> a

--------------------------------------------------------

+-suc : (n m : Nat) -> n + suc m === suc (n + m)
+-suc zero    m = refl
+-suc (suc n) m = cong suc (+-suc n m)

+-zero : ∀ {n} -> n + 0 === n
+-zero {zero}  = refl
+-zero {suc n} = cong suc +-zero

_`max`_ : Nat -> Nat -> Nat
zero  `max` b     = b
suc a `max` zero  = suc a
suc a `max` suc b = suc (a `max` b)

maxA : ∀ {a b} -> a `max` b === (b - a) + a
maxA {zero}  {zero}  = refl
maxA {zero}  {suc b} = cong suc (sym +-zero)
maxA {suc a} {zero}  = refl
maxA {suc a} {suc b} = trans (cong suc (maxA {a} {b})) (sym (+-suc _ _))

maxB : ∀ {a b} -> a `max` b === (a - b) + b
maxB {zero}  {zero}  = refl
maxB {zero}  {suc b} = refl
maxB {suc a} {zero}  = cong suc (sym +-zero)
maxB {suc a} {suc b} = trans (cong suc (maxB {a} {b})) (sym (+-suc _ _))

---------------------------------------------------------

F = Nat

--base = 61
base = 21888242871839275222246405745257275088548364400416034343698204186575808495617
halfBase = base / 2

addF subF mulF divF : F -> F -> F
addF a b = (a + b) % base
subF a b = ((base + a) - b) % base
mulF a b = (a * b) % base

{-# TERMINATING #-}
recip : F -> F
recip f = go 0 1 base f  where

  go : F -> F -> F -> F -> F
  go t nt r 0          = t
  go t nt r nr@(suc _) = go nt (subF t (((r / nr) * nt) % base)) nr (r % nr)

divF a b = mulF a (recip b)

negF = subF zero

testRecip : F -> F
testRecip f = mulF f (recip f)

bitF : Nat -> F -> F
bitF 0 f = f % 2
bitF (suc n) f = bitF n (f / 2)

--------------------------------------------------------

_$_ : ∀ {a b : Set} -> (a -> b) -> a -> b
f $ a = f a

---------------------

data List (a : Set) : Set where
  Nil  : List a
  Cons : a -> List a -> List a

pattern _::_ a b = Cons a b

map : ∀ {a b} -> (a -> b) -> List a -> List b
map f Nil = Nil
map f (a :: as) = f a :: map f as

_++_ : ∀ {a} -> List a -> List a -> List a
Nil ++ as = as
(a :: as) ++ bs = a :: (as ++ bs)

----------------------

data VVec (a : Set) : Nat -> Set where
  VNil : VVec a 0
  VCons : ∀ {n} -> a -> VVec a n -> VVec a (suc n)

pad : ∀ {a t} -> (b : Nat) -> t -> VVec t a -> VVec t (b + a)
pad zero _ c = c
pad (suc b) x c = VCons x (pad b x c)

singV : ∀ {t} -> t -> VVec t 1
singV a = VCons a VNil

getV : ∀ {t} -> VVec t 1 -> t
getV (VCons a VNil) = a

takeV : ∀ {n a} -> (m : Nat) -> VVec a (m + n) -> VVec a m
takeV zero c = VNil
takeV (suc m) (VCons a as) = VCons a (takeV m as)

dropV : ∀ {n a} -> (m : Nat) -> VVec a (m + n) -> VVec a n
dropV zero c = c
dropV (suc m) (VCons a as) = dropV m as

_++v_ : ∀ {n m a} -> VVec a n -> VVec a m -> VVec a (n + m)
VNil ++v b = b
VCons x a ++v b = VCons x (a ++v b)

headV : ∀ {n a} -> VVec a (suc n) -> a
headV (VCons c _) = c

tailV : ∀ {n a} -> VVec a (suc n) -> VVec a n
tailV = dropV 1


-------------------------------

data Constr (a : Set) : Set where
  CstrEq  : a -> a -> Constr a
  CstrMul : a -> a -> a -> Constr a

pattern     _==_ a b   = CstrEq  a b
pattern [_*_]==_ a b c = CstrMul a b c

mapC : ∀ {a b} -> (a -> b) -> Constr a -> Constr b
mapC f (a == b) = f a == f b
mapC f ([ a * b ]== c) = [ f a * f b ]== f c


------------------------------------------------------------

data TyTag : Set where
  TBits : Nat -> TyTag

data Domain : Set where
  U : Domain  -- CPU value (including lambdas)
  L : Domain  -- linear value + R1CS constraints & witness generation

-- types of high-level code
data MTy : Domain -> Set where
  Felt   : ∀ {d}                   -> MTy d
  T0     : ∀ {d}                   -> MTy d
  Tup    : ∀ {d} -> MTy d -> MTy d -> MTy d
  Eith   : ∀ {d} -> MTy d -> MTy d -> MTy d
  Arr    :          MTy U -> MTy U -> MTy U
  Wrap   : TyTag                   -> MTy L

pattern _=>_ a b = Arr a b

-- types of low-level code
data Ty : Set where
  FLow :          Ty    -- field element
  IO   :          Ty    -- side effects: contraint addition, witness creation, input, ouput
  E    : MTy U -> Ty    -- embedded CPU computation

FL  = Felt {L}
FU  = Felt {U}


Bits = \n -> Wrap (TBits n)
FBool = Bits 1

representation : TyTag -> MTy L
representation (TBits n) = FL

{-# TERMINATING #-}
size : MTy L -> Nat
size Felt         = 1
size T0           = 0
size (Eith a b)   = suc (size a `max` size b)
size (Tup a b)    = size a + size b
size (Wrap w)     = size (representation w)

Name = Nat
BBool = Eith {U} T0 T0

-- CPU builtin operations
data Builtin : MTy U -> Set where

  Bconst  : F         -> Builtin FU
  bt0    :              Builtin T0
  btup   : ∀ {a b}   -> Builtin (a => b => Tup a b)
  bleft  : ∀ {a b}   -> Builtin (a => Eith a b)
  bright : ∀ {a b}   -> Builtin (b => Eith a b)

  Badd Bsub Bmul Bdiv
         :              Builtin (FU => FU => FU)
  bit    : Nat       -> Builtin (FU => FU)
  beq    :              Builtin (FU => FU => BBool)
  bfail  : ∀ {t}     -> Builtin t
  bfst   : ∀ {a b}   -> Builtin (Tup a b => a)
  bsnd   : ∀ {a b}   -> Builtin (Tup a b => b)
  bcase  : ∀ {a b c} -> Builtin ((a => c) => (b => c) => Eith a b => c)

{-# NO_POSITIVITY_CHECK #-}
data Val : MTy U -> Set where
  VLam   : ∀ {a b} -> (Val a -> Val b) -> Val (a => b)
  VF    : F ->                            Val FU
  VT0   :                                 Val T0
  VTup  : ∀ {a b} -> Val a  -> Val b ->   Val (Tup a b)
  VLeft  : ∀ {a b} -> Val a ->            Val (Eith a b)
  VRight : ∀ {a b} -> Val b ->            Val (Eith a b)

-- CPU code
{-# NO_POSITIVITY_CHECK #-}
data CCode : MTy U -> Set where
  CBuiltin : ∀ {t} -> Builtin t -> CCode t
  CLam     : ∀ {a b} -> (CCode a -> CCode b) -> CCode (a => b)
  _∙c_     : ∀ {a b} -> CCode (a => b) -> (CCode a -> CCode b)
  cLet     : ∀ {a b} -> CCode a -> (CCode a -> CCode b) -> CCode b
  CVal     : ∀ {t} -> Val t -> CCode t                           -- internally used for Val interpretation

data Public : Set where
  P : Public   -- public
  S : Public   -- secret

{-# NO_POSITIVITY_CHECK #-}
-- low-level code, used in the backend
data Code : Ty -> Set where

  ------------------- R1CS
  fconst    : F ->                      Code FLow
  _+l_ _-l_ : Code FLow -> Code FLow -> Code FLow
  _c*_      :         F -> Code FLow -> Code FLow

  ------------------- CPU
  lbuiltin  : ∀ {t} -> Builtin t ->                                 Code (E t)
  llam      : ∀ {a b : MTy U} -> (Code (E a) -> Code (E b)) ->      Code (E (a => b))
  _∙_       : ∀ {a b : MTy U} -> Code (E (a => b)) -> Code (E a) -> Code (E b)

  lu'       : Code FLow -> Code (E FU)

  ------------------- I/O
  CLetU     : ∀ {t : MTy U} -> Code (E t) -> (Code (E t) -> Code IO) -> Code IO
  CLetF     :                  Code FLow ->  (Code FLow  -> Code IO) -> Code IO
  Cstr      : Constr (Code FLow) ->                          Code IO -> Code IO
  FLet      : Public ->        Code (E FU) -> (Code FLow -> Code IO) -> Code IO      -- signal definition / signal output
  Input     : Public ->                       (Code FLow -> Code IO) -> Code IO      -- signal input
  End       :                                                           Code IO

  ------------------- interpretations aux
  var       : Name                     -> Code FLow        -- used in circut extraction
  fcode     : CCode FU                 -> Code FLow        -- used in CPU code extraction
  ucode     : ∀ {t : MTy U} -> CCode t -> Code (E t)       -- used in CPU code extraction

{-# NO_POSITIVITY_CHECK #-}
-- object code of staged compilation
data MCode : ∀ {d} -> MTy d -> Set where

  -------------- R1CS only

  Mconst    : F -> MCode FL
  Mscalar   : F -> MCode FL -> MCode FL
  Madd Msub : MCode FL -> MCode FL -> MCode FL

  MMulEq : ∀ {t : MTy L} -> MCode FL -> MCode FL -> MCode FL -> MCode t -> MCode t
  MEq    : ∀ {t : MTy L} -> MCode FL -> MCode FL             -> MCode t -> MCode t

  MunsafeWrap : ∀ {t} -> MCode (representation t) -> MCode (Wrap t)
  Munwrap     : ∀ {t} -> MCode (Wrap t) -> MCode (representation t)

  -------------- CPU only

  Mbuiltin : ∀ {t} -> Builtin t -> MCode t
  App  : {a b : MTy U} -> MCode (a => b) -> MCode a -> MCode b
  Lam  : {a b : MTy U} -> (MCode a -> MCode b) -> MCode (a => b)

  -------------- polymorphic (R1CS, CPU)

  TT    : ∀ {d} -> MCode (T0 {d})
  MkTup : ∀ {d} -> {a b : MTy d} -> MCode a -> MCode b -> MCode (Tup a b)
  Fst   : ∀ {d} -> {a b : MTy d} -> MCode (Tup a b) -> MCode a
  Snd   : ∀ {d} -> {a b : MTy d} -> MCode (Tup a b) -> MCode b

  left  : ∀ {d} -> {a b : MTy d} -> MCode a -> MCode (Eith a b)
  right : ∀ {d} -> {a b : MTy d} -> MCode b -> MCode (Eith a b)
  case  : ∀ {d} {a b c : MTy d} -> (MCode a -> MCode c) -> (MCode b -> MCode c) -> (MCode (Eith a b) -> MCode c)

  MLet  : ∀ {d} {a : MTy d} {b : MTy L} -> MCode a -> (MCode a -> MCode b) -> MCode b

  -------------- R1CS <--> CPU interaction
  MunsafeLet : ∀ {a : MTy L} -> MCode FU -> (MCode FL -> MCode a) -> MCode a
  Mlu        : ∀ {a : MTy L} -> MCode FL -> (MCode FU -> MCode a) -> MCode a

  -------------- aux (for interpretation)
  mpureU : ∀ {t} -> Code (E t)                -> MCode t
  mpureL : ∀ {t} -> VVec (Code FLow) (size t) -> MCode t

pattern _-ml_ a b = Msub a b
pattern _+ml_ a b = Madd a b
pattern _c*m_ a b = Mscalar a b
pattern [_*_]==m_&&_ a b c d = MMulEq a b c d
pattern _==m_&&_ a b c = MEq a b c
pattern _∙m_ {a} {b} c d = App {a} {b} c d

mbit : Nat -> MCode FU -> MCode FU
mbit n a = Mbuiltin (bit n) ∙m a

mlconst : F -> MCode FU
mlconst f = Mbuiltin (Bconst f)

_*u_ _-u_ _+u_ _/u_ : Code (E FU) -> Code (E FU) -> Code (E FU)
a *u b = lbuiltin Bmul ∙ a ∙ b
a /u b = lbuiltin Bdiv ∙ a ∙ b
a +u b = lbuiltin Badd ∙ a ∙ b
a -u b = lbuiltin Bsub ∙ a ∙ b

_*m_ _/m_ _-mu_ _+mu_ : MCode FU -> MCode FU -> MCode FU
a *m  b = Mbuiltin Bmul ∙m a ∙m b
a /m  b = Mbuiltin Bdiv ∙m a ∙m b
a +mu b = Mbuiltin Badd ∙m a ∙m b
a -mu b = Mbuiltin Bsub ∙m a ∙m b


-------------------------------------------------

example =
  Input P \i ->
  FLet S (lbuiltin Bdiv ∙ lbuiltin (Bconst 1) ∙ lu' i) \inv ->
  FLet P (lbuiltin Bsub ∙ lbuiltin (Bconst 1) ∙ (lbuiltin Bmul ∙ lu' i ∙ lu' inv)) \o ->
  Cstr ([ i * inv ]== fconst 1 -l o) $
  Cstr ([ i * o   ]== fconst 0) $
  End


------------------------------------------------- frontend

runU : ∀ {a : MTy U} -> MCode a -> Code (E a)
runU (Mbuiltin x) = lbuiltin x
runU TT           = lbuiltin bt0
runU (MkTup a b)  = lbuiltin btup ∙ runU a ∙ runU b
runU (Fst c)      = lbuiltin bfst ∙ runU c
runU (Snd c)      = lbuiltin bsnd ∙ runU c
runU (left c)     = lbuiltin bleft ∙ runU c
runU (right c)    = lbuiltin bright ∙ runU c
runU (case f g c) = lbuiltin bcase ∙ llam (\x -> runU (f (mpureU x))) ∙ llam (\x -> runU (g (mpureU x))) ∙ runU c
runU (f ∙m a)     = runU f ∙ runU a
runU (Lam x)      = llam (\z -> runU (x (mpureU z)))
runU (mpureU x)   = x

crepr : ∀ {d} -> MTy d -> Set
crepr {U} t = Code (E t)
crepr {L} t = VVec (Code FLow) (size t)

mux1 : Code FLow -> Code FLow -> Code FLow -> (Code FLow -> Code IO) -> Code IO
mux1 c a b cont = CLetF c \c -> -- Mlu a \a' -> Mlu b \b' -> Mlu c \c' ->
  FLet S (lu' c *u (lu' a -u lu' b) +u lu' b) \r ->
  Cstr ([ c * a -l b ]== r -l b) $
  cont r

muxN : ∀ {n} -> Code FLow -> VVec (Code FLow) n -> VVec (Code FLow) n -> (VVec (Code FLow) n -> Code IO) -> Code IO
muxN {zero} a b c cont = cont VNil
muxN {suc n} a b c cont =
  mux1 a (headV b) (headV c) \d ->
  muxN a (tailV b) (tailV c) \ds ->
  cont (VCons d ds)


runMC : ∀ {d} {t : MTy d} -> MCode t -> (crepr t -> Code IO) -> Code IO

runL : ∀ {t : MTy L} -> MCode t -> (crepr t -> Code IO) -> Code IO
runL (Mconst x)         cont = cont (singV (fconst x))
runL (a c*m b)          cont = runL b \b -> cont (singV (a c* getV b)) 
runL (a +ml b)          cont = runL a \a -> runL b \b -> cont (singV (getV a +l getV b)) 
runL (a -ml b)          cont = runL a \a -> runL b \b -> cont (singV (getV a -l getV b)) 
runL ([ a * b ]==m c && d) cont = runL a \a -> runL b \b -> runL c \c -> Cstr ([ getV a * getV b ]== getV c) (runL d cont)
runL (a ==m b && c)     cont = runL a \a -> runL b \b -> Cstr (getV a == getV b) (runL c cont)
runL (MunsafeWrap a)    cont = runL a \a -> cont a
runL (Munwrap a)        cont = runL a \a -> cont a
runL TT                 cont = cont VNil
runL (MkTup a b)        cont = runL a \a -> runL b \b -> cont (a ++v b)
runL (Fst {_} {x} a)    cont = runL a \a -> cont (takeV (size x) a)
runL (Snd {_} {x} a)    cont = runL a \a -> cont (dropV (size x) a)
runL (left  {_} {x} {y} a) cont rewrite maxA {size x} {size y}
                                  = runL a \a -> cont (VCons (fconst 0) (pad _ (fconst 0) a)) --
runL (right {_} {x} {y} a) cont rewrite maxB {size x} {size y}
                                  = runL a \a -> cont (VCons (fconst 1) (pad _ (fconst 0) a))
runL (MLet {U} {t} a f) cont = runMC a \a -> CLetU a \a -> runL (f (mpureU a)) cont
runL (MLet {L} {t} a f) cont = runL a \a -> runL (f (mpureL a)) cont
runL (MunsafeLet a f)   cont = runMC a \a -> FLet S a \a -> runL (f (mpureL (singV a))) cont
runL (Mlu a f)          cont = runL a \a -> runL (f (mpureU (lu' (getV a)))) cont
runL (mpureL x)         cont = cont x
runL (case {_} {x} {y} {z} f g a) cont
  = runL a \a ->
    runL (f (mpureL (dropV {size x} _ (subst (\x -> VVec (Code FLow) x) (maxA {size x} {size y}) (tailV a))))) \f ->
    runL (g (mpureL (dropV {size y} _ (subst (\x -> VVec (Code FLow) x) (maxB {size x} {size y}) (tailV a))))) \g ->
    muxN (headV a) f g cont

runMC {U} c cont = cont (runU c)
runMC {L} c cont = runL c cont


mksBits : Nat -> MCode FU -> MCode FL
mksBits n a = go (Mconst 0) n where
  go : MCode FL -> Nat -> MCode FL
  go ac 0 = ac
  go ac (suc n) = MunsafeLet (mbit n a) \b -> go ([ b * Mconst 1 -ml b ]==m Mconst 0 && 2 c*m ac +ml b) n

safeWrap : ∀ {t} -> MCode (representation t) -> MCode (Wrap t)
safeWrap {TBits 0} a = a ==m Mconst 0 && MunsafeWrap a
safeWrap {TBits 1} a = [ a * Mconst 1 -ml a ]==m Mconst 0 && MunsafeWrap a
safeWrap {TBits n} a = Mlu a \a' -> MunsafeWrap (mksBits n a' ==m a && a)

{-# TERMINATING #-}
mkInput : ∀ {t : MTy L} -> (MCode t -> Code IO) -> Code IO
mkInput {Felt}     cont = Input S \a -> cont (mpureL (singV a))
mkInput {T0}       cont = cont TT
mkInput {Tup a b}  cont = mkInput {a} \a -> mkInput {b} \b -> cont (MkTup a b)
mkInput {Eith a b} cont = Input S \x -> TODO 
mkInput {Wrap w}   cont = mkInput {representation w} \a -> cont (safeWrap a)

mkOutputs : {n : Nat} -> VVec (Code FLow) n -> Code IO
mkOutputs VNil = End
mkOutputs (VCons f fs) = FLet P (lu' f) \f' -> Cstr (f == f') (mkOutputs fs)

-- CircuitRep a b = MCode a -> MCode b
runFun : ∀ {a b : MTy L} -> (MCode a -> MCode b) -> Code IO
runFun {a} f = mkInput \a -> runMC (MLet a f) mkOutputs

data Circ : Set where
  MkCirc : ∀ {a b : MTy L} -> (MCode a -> MCode b) -> Circ

runFun' : Circ -> Code IO
runFun' (MkCirc f) = runFun f

ci : MCode (Tup (Bits 3) FL) -> MCode (Tup FL (Bits 3))
ci a = MkTup (Snd a) (Fst a)

test' : Code IO
test' = runFun ci

ci' : MCode FL -> MCode (Eith FL (Tup FL FL))
ci' a = left a

--------------------------------------------------------------- example application

mul' : MCode FL -> MCode FL -> MCode FL
mul' a b = MLet a \a -> Mlu a \a' -> MLet b \b -> Mlu b \b' -> MunsafeLet (a' *m b') \c -> [ a * b ]==m c && c        --          c <== a * b

notF : MCode FBool -> MCode FBool
notF t = MunsafeWrap (Mconst 1 -ml Munwrap t)

and or : MCode FBool -> MCode FBool -> MCode FBool
and a b = MunsafeWrap (mul' (Munwrap a) (Munwrap b))
or  a b = notF (and (notF a) (notF b))

isZero : MCode FL -> MCode FBool
isZero i =
  MLet i \i -> Mlu i \i' -> 
  MunsafeLet (mlconst 1 /m i') \inv -> Mlu inv \inv' -> 
  MunsafeLet (mlconst 1 -mu i' *m inv') \o ->
  [ i * inv ]==m (Mconst 1 -ml o) &&
  [ i * o   ]==m Mconst 0 &&
  MunsafeWrap o

eq : MCode FL -> MCode FL -> MCode FBool
eq a b = isZero (a -ml b)   -- OK?

unsafeBit : Nat -> MCode FU -> MCode FBool
unsafeBit n a = MunsafeLet (mbit n a) \b -> safeWrap b

Vec : ∀ {d} -> Nat -> MTy d -> MTy d
Vec 0 _ = T0
Vec (suc n) t = Tup t (Vec n t)

unsafeBitsOfNum : ∀ {n : Nat} -> MCode FU -> MCode (Vec n FBool)
unsafeBitsOfNum {n = zero} _ = TT
unsafeBitsOfNum {n = suc m} a = MLet a \a -> MkTup (unsafeBit m a) (unsafeBitsOfNum a)

numOfBits : {n : Nat} -> MCode (Vec n FBool) -> MCode FL
numOfBits = go (Mconst 0)
 where
  go : {n : Nat} -> MCode FL -> MCode (Vec n FBool) -> MCode FL
  go {n = zero} acc _ = acc
  go {n = suc _} acc ab = MLet ab \ab -> go (2 c*m acc +ml Munwrap (Fst ab)) (Snd ab)

toBits : {n : Nat} -> MCode FL -> MCode (Vec n FBool)
toBits a = Mlu a \a' -> MLet (unsafeBitsOfNum a') \bs -> numOfBits bs ==m a && bs

less' : {n : Nat} -> MCode (Bits n) -> MCode (Bits n) -> MCode FBool
less' {n} a b =
  MLet (Munwrap a +ml Mconst (2 ^ n) -ml Munwrap b) \c ->
  notF (Fst (toBits {suc n} c))

ite' : MCode FBool -> MCode FL -> MCode FL -> MCode FL
ite' c a b = MLet (Munwrap c) \c -> Mlu a \a' -> Mlu b \b' -> Mlu c \c' ->
  MunsafeLet (c' *m (a' -mu b') +mu b') \r ->
  [ c * a -ml b ]==m r -ml b &&
  r

min : {n : Nat} -> MCode (Bits n) -> MCode (Bits n) -> MCode (Bits n)
min a b =
  MLet a \a ->
  MLet b \b ->
  MunsafeWrap (ite' (less' a b) (Munwrap a) (Munwrap b))

minimum : {n k : Nat} -> MCode (Vec (suc k) (Bits n)) -> MCode (Bits n)
minimum {k = zero}  a = Fst a
minimum {k = suc _} aas = MLet aas \aas -> min (Fst aas) (minimum (Snd aas))
{-
minimum : Vec (suc _) (Bits n) -> Bits n
minimum (a :: Nil) = a
minimum (a :: as)  =  min a (minimum as)
-}

test0 = MkCirc (minimum {2} {2})

test : Code IO
test = runFun (minimum {2} {2})


------------------------------------------------------------ R1CS backend

-- normal form of linear expressions
data Lin : Set where
  Z : Lin
  LCons : F -> Name -> Lin -> Lin

cons' : F -> Name -> Lin -> Lin
cons' 0 _ as = as
cons' t n as = LCons t n as

mapT : (F -> F) -> Lin -> Lin
mapT f Z = Z
mapT f (LCons t n as) = cons' (f t) n (mapT f as)

-- TODO: rename to sum
{-# TERMINATING #-}
merge : Lin -> Lin -> Lin
merge Z a = a
merge a Z = a
merge as'@(LCons t n as) bs'@(LCons t' n' bs) with n =?= n' | n < n'
... | true | _ = cons' (addF t t') n (merge as bs)
... | _ | true = cons' t n (merge as bs')
... | _ | _    = cons' t' n' (merge as' bs)

lin : Code FLow -> Lin
lin (a +l b)   = merge (lin a) (lin b)
lin (a -l b)   = merge (lin a) (mapT negF (lin b))
lin (fconst t) = cons' t 0 Z
lin (t c* a)   = mapT (mulF t) (lin a)
lin (var n)    = cons' 1 n Z
lin (fcode _)  = impossible

circuit : Nat -> Code IO -> List (Constr Lin)
circuit n (Input _ f)   = circuit (suc n) (f (var n))
circuit n (FLet _ _ f)  = circuit (suc n) (f (var n))
circuit n (CLetU a f) = circuit n (f a)
circuit n (CLetF a f) = circuit n (f a)
circuit n (Cstr cs f) = mapC lin cs :: circuit n f
circuit n End         = Nil

plusSign : Bool -> Bool -> String
plusSign false true  = " + "
plusSign _ true      = ""
plusSign false false = " - "
plusSign _ false     = "-"

showVar : F -> Name -> String
showVar f 0 = show f
showVar 1 n = "v" <> show n
showVar f n = show f <> "v" <> show n

showTerm : Bool -> F -> Name -> String
showTerm b f n with f < halfBase
... | true  = plusSign b true  <> showVar f n
... | _     = plusSign b false <> showVar (negF f) n

showLin : Bool -> Lin -> String
showLin b (LCons x n l) = showTerm b x n <> showLin false l
showLin true Z = "0"
showLin _    Z = ""

parens : Bool -> String -> String
parens true a = "(" <> a <> ")"
parens _    a = a

complex : Lin -> Bool
complex (LCons _ _ (LCons _ _ _)) = true
complex _                     = false

showCstr : Constr Lin -> String
showCstr (a == b) = showLin true a <> " == " <> showLin true b
showCstr ([ a * b ]== c) = parens (complex a) (showLin true a) <> "*" <> parens (complex b) (showLin true b) <> " == " <> showLin true c

unlines : List String -> String
unlines Nil = "\n"
unlines (s :: ss) = s <> "\n" <> unlines ss

t = map showCstr (circuit 1 test)


----------------------------------------------------- CPU backend

getFU : Val FU -> F
getFU (VF v) = v

getFst : ∀ {a b} -> Val (Tup a b) -> Val a
getFst (VTup a b) = a

getSnd : ∀ {a b} -> Val (Tup a b) -> Val b
getSnd (VTup a b) = b

_∙v_ : ∀ {a b} -> Val (a => b) -> Val a -> Val b
VLam x ∙v e = x e

caseVal : ∀ {a b c} -> Val (a => c) -> Val (b => c) -> Val (Eith a b) -> Val c
caseVal f g (VLeft  x) = f ∙v x
caseVal f g (VRight x) = g ∙v x

isZero' : F -> Val BBool
isZero' 0 = VRight VT0
isZero' _ = VLeft  VT0

evalB : ∀ {t} -> Builtin t -> Val t
evalB (bit a) = VLam \b -> VF (bitF a (getFU b))
evalB (Bconst f) = VF f
evalB bfst   = VLam getFst
evalB bsnd   = VLam getSnd
evalB bcase  = VLam \f -> VLam \g -> VLam (caseVal f g)
evalB Badd   = VLam \a -> VLam \b -> VF (addF (getFU a) (getFU b))
evalB Bsub   = VLam \a -> VLam \b -> VF (subF (getFU a) (getFU b))
evalB Bmul   = VLam \a -> VLam \b -> VF (mulF (getFU a) (getFU b))
evalB Bdiv   = VLam \a -> VLam \b -> VF (divF (getFU a) (getFU b))
evalB beq    = VLam \a -> VLam \b -> isZero' (subF (getFU a) (getFU b))
evalB bt0    = VT0
evalB btup   = VLam \a -> VLam \b -> VTup a b
evalB bleft  = VLam VLeft
evalB bright = VLam VRight
evalB bfail  = TODO

evalC : ∀ {t} -> CCode t -> Val t
evalC (CBuiltin a) = evalB a
evalC (CLam a)     = VLam (\v -> evalC (a (CVal v)))
evalC (a ∙c b)     = evalC a ∙v evalC b
evalC (cLet a f)   = evalC (f (CVal (evalC a)))
evalC (CVal v)     = v

extractF : Code FLow -> CCode FU

extractU : ∀ {t : MTy U} -> Code (E t) -> CCode t
extractU (lbuiltin a) = CBuiltin a
extractU (llam f)     = CLam \a -> extractU (f (ucode a))
extractU (a ∙ b)      = extractU a ∙c extractU b
extractU (lu' a)      = extractF a
extractU (ucode c)    = c

extractF (fconst x) = CBuiltin (Bconst x)
extractF (a +l b)   = CBuiltin Badd ∙c extractF a ∙c extractF b
extractF (a -l b)   = CBuiltin Bsub ∙c extractF a ∙c extractF b
extractF (a c* b)   = CBuiltin Bmul ∙c CBuiltin (Bconst a) ∙c extractF b
extractF (fcode c)  = c
extractF (var _)    = impossible

-- TODO: rename to SigElem
data Sig : Set where
  I : Public -> Sig
  O : Public -> Sig

-- this is well-defined but Agda cannot see it
sig : Code IO -> List Sig
sig (Input out f)    = I out :: sig (f {- _ -} (var 0))
sig (FLet out _ f)   = O out :: sig (f {- _ -} (var 0))
sig (Cstr _ f)   = sig f
sig End          = Nil
sig (CLetU a f)  = sig (f a)
sig (CLetF a f)  = sig (f a)

interpretSig : List Sig -> MTy U
interpretSig Nil         = T0
interpretSig (I _ :: ss) = FU => interpretSig ss
interpretSig (O _ :: ss) = Tup FU (interpretSig ss)

liNum loNum : List Sig -> Nat
liNum Nil = 0
liNum (I x :: s) = suc (liNum s)
liNum (O x :: s) = liNum s

loNum Nil = 0
loNum (_ :: s) = suc (loNum s)

sigTrust : (a b : Code IO) -> CCode (interpretSig (sig a)) -> CCode (interpretSig (sig b))
sigTrust a b = subst (\s -> CCode (interpretSig s)) (primTrustMe {_} {_} {sig a} {sig b})

extractCstr : Constr (Code FLow) -> CCode BBool
extractCstr (a == b)        = CBuiltin beq ∙c extractF a ∙c extractF b
extractCstr ([ a * b ]== c) = CBuiltin beq ∙c (CBuiltin Bmul ∙c extractF a ∙c extractF b) ∙c extractF c

extractIO : (c : Code IO) -> CCode (interpretSig (sig c))
extractIO (Input _ f)    = CLam \x -> sigTrust (f (fcode x)) (f (var 0)) (extractIO (f (fcode x)))
extractIO (FLet _ c f)   = cLet (extractU c) (\x -> CBuiltin btup ∙c x ∙c sigTrust (f (fcode x)) (f (var 0)) (extractIO (f (fcode x))))
extractIO (CLetU c@(ucode _) f) = extractIO (f c)
extractIO (CLetU c f)    = cLet (extractU c) \x -> sigTrust (f (ucode x)) (CLetU c f) (extractIO (f (ucode x)))
extractIO (CLetF c@(fcode _) f) = extractIO (f c)
extractIO (CLetF c f)    = cLet (extractF c) \x -> sigTrust (f (fcode x)) (CLetF c f) (extractIO (f (fcode x)))
extractIO (Cstr a b)     = CBuiltin bcase ∙c (CLam \_ -> CBuiltin bfail) ∙c (CLam \_ -> extractIO b) ∙c extractCstr a
extractIO End            = CBuiltin bt0

evalV : ∀ {s} -> Val (interpretSig s) -> VVec F (liNum s) -> VVec F (loNum s)
evalV {Nil} c i = VNil
evalV {I x :: s} c (VCons i is) = VCons i (evalV {s} (c ∙v VF i) is)
evalV {O x :: s} (VTup (VF c) cs) i = VCons c (evalV {s} cs i)

tsig = sig test
ct = extractIO test
vct  = evalV {sig test} (evalC ct) (VCons 2 (VCons 1 (VCons 3 VNil)))
vct' = evalC ct ∙v VF 2 ∙v VF 1 ∙v VF 4

---------------------------------- Haskell exports

#testCirc = test0

#runFun = runFun'
#circuit = circuit
#liS = interpretSig
#sig = sig
#extractIO = extractIO
#evalC = evalC
#evalV = evalV


