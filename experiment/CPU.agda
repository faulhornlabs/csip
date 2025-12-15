{-# OPTIONS --type-in-type #-}
open import Data.String using (String) renaming (_++_ to _<>_)
open import Data.Nat
open import Agda.Builtin.Equality

infixl 9 _∙_
infixr 5 _*t_
infixr 4 _+t_
infixr 3 _=>_ -- _~>_
infixr 2 _::_
infixr 0 _>>_ _>>=_

---------------------------

cong : {a b : Set} {x y : a} -> (f : a -> b) -> x ≡ y -> f x ≡ f y
cong f refl = refl

+-suc : (n m : ℕ) -> n + suc m ≡ suc (n + m)
+-suc zero    m = refl
+-suc (suc n) m = cong suc (+-suc n m)

---------------------------------------------

record Unit : Set where
  constructor tt

data Void : Set where

elimVoid : ∀ {a : Set} -> Void -> a
elimVoid ()

record Pair (a b : Set) : Set where
  constructor MkPair
  field
    Fst : a
    Snd : b

open Pair

data Either (a b : Set) : Set where
  Left  : a -> Either a b
  Right : b -> Either a b

either : ∀ {a b} {c : Set} -> (a -> c) -> (b -> c) -> Either a b -> c
either f g (Left x) = f x
either f g (Right x) = g x

---------------------------------------------

data List (a : Set) : Set where
  []   : List a
  _::_ : a -> List a -> List a

map : ∀ {a b} -> (a -> b) -> List a -> List b
map f []       = []
map f (x :: l) = f x :: map f l

_++_ : ∀ {a} -> List a -> List a -> List a
[]        ++ b = b
(x :: xs) ++ b = x :: (xs ++ b)

foldr : ∀ {a} {b : Set} -> (a -> b -> b) -> b -> List a -> b
foldr f c (a :: as) = f a (foldr f c as)
foldr f c []        = c


---------------------- closure-free types

data Polarity : Set where
  V : Polarity   -- value
  C : Polarity   -- computation

-- closure-free types
data CTy : Polarity -> Set where
  _=>_ : ∀ {p} -> CTy V -> CTy p -> CTy C
  IO   : CTy V -> CTy V   -- -> CTy C ?
  1t   : CTy V
  _*t_ : CTy V -> CTy V -> CTy V
  0t   : CTy V
  _+t_ : CTy V -> CTy V -> CTy V
  Int  : CTy V

Bool = 1t +t 1t
Maybe = \a -> 1t +t a

----------------------  stackless types   (IR)

data TyP : Set where      -- ~ STy p
  Ptr : List TyP -> TyP   -- computation (function pointer)
  I   : TyP               -- value

TyC  = List TyP           -- ~ STy C
TyCs = List TyC


--------------------------------------------- closure-free codes

interp : ∀ {p} -> CTy p -> Set

Carry = Int
HInt = Int

data Builtin : CTy V -> CTy V -> Set where
  BAdd   :      Builtin (Int *t Int) Int
  BAddC  :      Builtin (Carry *t Int *t Int) (Carry *t Int)
  BAdd2  :      Builtin (Int *t HInt *t Int) (HInt *t Int)    --  c + [h,l]
  BAdd2' :      Builtin (Int *t Int) (HInt *t Int)
  BMul2  :      Builtin (Int *t Int) (HInt *t Int)
  BCC    :      Builtin 1t Carry                        -- zero carry
  BLess  :      Builtin (Int *t Int) (1t +t 1t)
  BPut   :      Builtin Int (IO 1t)
  BGet   :      Builtin 1t (IO Int)
  BConst : ℕ -> Builtin 1t Int

{-# NO_POSITIVITY_CHECK #-}
data CCode : ∀ {p} -> CTy p -> Set where
  _∙_    : ∀ {p} {a} {b : CTy p} -> CCode (a => b) -> (CCode a -> CCode b)
  CLam   : ∀ {p} {a} {b : CTy p} -> (CCode a -> CCode b) -> CCode (a => b)
  CLet   : ∀ {p} {q} {a : CTy p} {b : CTy q} -> CCode a -> (CCode a -> CCode b) -> CCode b
  CTT    : CCode 1t
  CTup   : ∀ {a b} -> CCode (a => b => a *t b)
  CFst   : ∀ {a b} -> CCode (a *t b => a)
  CSnd   : ∀ {a b} -> CCode (a *t b => b)
  CLeft  : ∀ {a b} -> CCode (a => a +t b)
  CRight : ∀ {a b} -> CCode (b => a +t b)
  CCase  : ∀ {p} {a b} {c : CTy p} -> CCode (a => c) -> CCode (b => c) -> CCode (a +t b) -> CCode c
  CElimVoid : ∀ {p} {a : CTy p} -> CCode (0t => a)
  CBuiltin : ∀ {a b} -> Builtin a b -> CCode a -> CCode b
  CPure  : ∀ {a} -> CCode (a => IO a)

  CUnsafe : ∀ {a} -> CCode (IO a) -> CCode a
  CVar   : ∀ {p} {a : CTy p} -> interp a -> CCode a

cTup : ∀ {a b} -> CCode a -> CCode b -> CCode (a *t b)
cTup a b = CTup ∙ a ∙ b

lit   = \n     -> CBuiltin (BConst n) CTT
mul2  = \a b   -> CBuiltin BMul2 (cTup a b)
cAdd  = \a b   -> CBuiltin BAdd (cTup a b)
cAddC = \c a b -> CBuiltin BAddC (cTup c (cTup a b))
add2  = \c ab  -> CBuiltin BAdd2 (cTup c ab)
add2' = \c a   -> CBuiltin BAdd2' (cTup c a)
cPut  = \a     -> CBuiltin BPut a
cGet  =           CBuiltin BGet CTT
clearCarry =      CBuiltin BCC CTT

cFst : ∀ {a b} -> CCode (a *t b) -> CCode a
cFst a = CFst ∙ a

cSnd : ∀ {a b} -> CCode (a *t b) -> CCode b
cSnd a = CSnd ∙ a

cLeft : ∀ {a b} -> CCode a -> CCode (a +t b)
cLeft a = CLeft ∙ a

cRight : ∀ {a b} -> CCode b -> CCode (a +t b)
cRight a = CRight ∙ a

cCase  : ∀ {p} {a b} {c : CTy p} -> (CCode a -> CCode c) -> (CCode b -> CCode c) -> CCode (a +t b) -> CCode c
cCase a b c = CCase (CLam a) (CLam b) c

cLess : ∀ {p} {a : CTy p} ->  CCode Int -> CCode Int -> CCode a -> CCode a -> CCode a
cLess a b c d = cCase (\_ -> c) (\_ -> d) (CBuiltin BLess (cTup a b))

_>>=_  : ∀ {a b} -> CCode (IO a) -> (CCode a -> CCode (IO b)) -> CCode (IO b)
x >>= f = CLet (CUnsafe x) f

_>>_  : ∀ {a b} -> CCode (IO a) -> CCode (IO b) -> CCode (IO b)
x >> y = x >>= \_ -> y

cPure : ∀ {a} -> CCode a -> CCode (IO a)
cPure x = CPure ∙ x

-----------------------------------------------

{-# NO_POSITIVITY_CHECK #-}
data SCode : TyP -> Set

PIO = \a -> SCode (Ptr a)

sCode : CTy V -> Set
sCode (IO a)   = sCode a
sCode Int      = SCode I
sCode 1t       = Unit
sCode (a *t b) = Pair (sCode a) (sCode b)
sCode 0t       = Void
sCode (a +t b) = Either (sCode a) (sCode b)

M' : TyC -> Set -> Set
M' a b = b -> PIO a

M : TyC -> Set -> Set
M a b = M' a (M' a b)   --  (b -> PIO a) -> PIO a

N : Set -> Set
N t = {a : TyC} -> M a t   --  ∀ {a} -> (b -> PIO a) -> PIO a

uu : ∀ {p} -> CTy p -> Set
uu {V} t = sCode t
uu {C} (t => s) = sCode t -> N (uu s)

interp t = N (uu t)

data SCode where
  _∙_    : ∀ {a b} -> PIO (a :: b) ->  SCode a -> PIO b
  SLam   : ∀ {a b} -> (SCode a -> PIO b) -> PIO (a :: b)
  SLet   : ∀ {a b} -> PIO a -> (PIO a -> PIO b) -> PIO b
  SHalt  : PIO []
  SBuiltin : ∀ {a b c} -> Builtin a b -> sCode a -> (sCode b -> PIO c) -> PIO c
  SConst : ℕ -> SCode I

--  Self   : ∀ {a} -> SCode a -> SCode a

-------------------

pure : ∀ {a} {b : Set} -> b -> M a b
pure b cont = cont b

lift : ∀ {z} {a} -> M [] a -> M z a
lift {[]} x = x
lift {_ :: zs} x cont = SLam \y -> lift {zs} x \r -> cont r ∙ y

sLet'  : ∀ {p} {a : CTy p} {b} -> M' b (uu a) -> (M' b (uu a) -> PIO b) -> PIO b
sLet' = {!!}

tr : ∀ {p} {t : CTy p} -> CCode t -> interp t
tr (f ∙ a)  cont = {-sLet ?-} tr a \a -> tr f \f -> f a cont
tr (CLam f) cont = cont \x -> tr (f (CVar (pure x)))
tr (CLet x f) cont = tr x \x -> tr (f (CVar (pure x))) cont
tr CTT    cont = cont tt
tr CTup   cx = cx \x cy -> cy \y cont -> cont (MkPair x y)
tr CFst   cx = cx \x cont -> cont (Fst x)
tr CSnd   cx = cx \x cont -> cont (Snd x)
tr CLeft  cx = cx \x cont -> cont (Left x)
tr CRight cx = cx \x cont -> cont (Right x)
tr (CCase {c = c} f g x) cont = sLet' {_} {c} cont \cont -> tr f \f -> tr g \g -> tr x \c -> either f g c cont
tr CElimVoid cont = cont elimVoid
tr (CUnsafe x) = tr x
tr CPure c = c \c -> pure c
tr (CVar v) = v
tr (CBuiltin (BConst n) a) cont = cont (SConst n)
tr (CBuiltin b a) cont = tr a \a -> SBuiltin b a cont


---------------------------------------- examples

double : CCode (Int => Int)
double = CLam \i -> cAdd i i

example0 = tr (cGet >>= \x -> cPut (double ∙ (double ∙ x)))

not : CCode Bool -> CCode Bool
not = cCase (\_ -> CRight ∙ CTT) \_ -> CLeft ∙ CTT

doublePos : CCode (Int => Int)
doublePos = CLam \c -> cLess c (lit 10) (cAdd c c) c

example0b = tr (cGet >>= \x -> cPut (doublePos ∙ x))

exampleSh = tr (cPut (cLess (lit 1) (lit 2) (lit 3) (lit 4)))

CVec : ℕ -> CTy V -> CTy V
CVec 0 _ = 1t
CVec (suc n) t = CVec n t *t t

addC : ∀ {n} -> CCode Carry -> CCode (CVec n Int) -> CCode (CVec n Int) -> CCode (Carry *t CVec n Int)
addC {zero}  c a b = cTup c CTT
addC {suc n} c a b = 
   CLet (cAddC c (cSnd a) (cSnd b)) \d ->
   CLet (addC (cFst d) (cFst a) (cFst b)) \e ->
   cTup (cFst e) (cTup (cSnd e) (cSnd d))

add : ∀ {n} -> CCode (CVec n Int => CVec n Int => CVec n Int)
add = CLam \a -> CLam \b -> cSnd (addC clearCarry a b)

-----------------

data Vec (a : Set) : ℕ -> Set where
  []   : Vec a 0
  _::_ : ∀ {n} -> a -> Vec a n -> Vec a (suc n)

toListV : ∀ {n a} -> Vec a n -> List a
toListV {zero} [] = []
toListV {suc n} (a :: as) = a :: toListV as

mapV : ∀ {n a b} -> (a -> b) -> Vec a n -> Vec b n
mapV {zero} f [] = []
mapV {suc n} f (a :: as) = f a :: mapV f as

zipV : ∀ {n a b c} -> (a -> b -> c) -> Vec a n -> Vec b n -> Vec c n
zipV {zero} f [] [] = []
zipV {suc _} f (a :: as) (b :: bs) = f a b :: zipV f as bs

repV : ∀ {n a} -> a -> Vec a n
repV {zero} a = []
repV {suc _} a = a :: repV a

matV : ∀ {n m a b c} -> (a -> b -> c) -> Vec a n -> Vec b m -> Vec (Vec c m) n
matV {zero} f [] b = []
matV {suc n} f (a :: as) b = mapV (f a) b :: matV f as b

padV : ∀ {n m a} -> a -> Vec a n -> Vec a (m + n)
padV {zero}  x [] = repV x
padV {suc n} {m} x (a :: as) rewrite +-suc m n = a :: padV {n} x as -- 

diags : ∀ {n m a} -> Vec (Vec a m) (suc n) -> Vec (List a) (n + m)
diags {zero} (a :: []) = mapV (\e -> e :: []) a
diags {suc n} (a :: as) = zipV _++_ (padV [] (mapV (\e -> e :: []) a)) ([] :: diags as)

-------------------------

fromCVec : ∀ {n t} -> CCode (CVec n t) -> Vec (CCode t) n
fromCVec {zero} _ = []
fromCVec {suc n} v = cSnd v :: fromCVec (cFst v)

toCVec : ∀ {n t} -> Vec (CCode t) n -> CCode (CVec n t)
toCVec {zero} [] = CTT
toCVec {suc n} (x :: xs) = cTup (toCVec xs) x

letVec : ∀ {n a} {t : CTy V} -> (a -> (a -> CCode t) -> CCode t) -> Vec a n -> (Vec a n -> CCode t) -> CCode t
letVec {zero} le [] cont = cont []
letVec {suc n} le (x :: xs) cont = le x \x -> letVec le xs \xs -> cont (x :: xs)

letList : ∀ {a} {t : CTy V} -> (a -> (a -> CCode t) -> CCode t) -> List a -> (List a -> CCode t) -> CCode t
letList le [] cont = cont []
letList le (x :: xs) cont = le x \x -> letList le xs \xs -> cont (x :: xs)

-------------------------

getVec : ∀ {n} -> CCode (IO (CVec n Int))
getVec {zero} = cPure CTT
getVec {suc n} = getVec >>= \v -> cGet >>= \i -> cPure (cTup v i)

putVec : ∀ {n} -> CCode (CVec n Int => IO 1t)
putVec {zero} = CLam \_ -> cPure CTT
putVec {suc n} = CLam \c -> putVec ∙ (cFst c) >> cPut (cSnd c)

---------------------

addC2s : CCode (Int *t Int) -> List (CCode Int) -> CCode (Int *t Int)
addC2s c [] = c
addC2s c (i :: is) = addC2s (add2 i c) is

addCs : ∀ {n} -> CCode Int -> Vec (List (CCode Int)) n -> CCode (CVec n Int)
addCs {zero} _ [] = CTT
addCs {suc n} c (is :: iss) = CLet (addC2s (cTup (lit 0) c) is) \a -> cTup (addCs (cFst a) iss) (cSnd a)

mul : ∀ {n m} -> CCode (CVec (suc n) Int => CVec m Int => CVec (suc n + m) Int)
mul =
  CLam \a ->
  CLam \b ->
  letVec (letList CLet) (diags (matV mul2 (fromCVec a) (fromCVec b))) \v ->
  addCs (lit 0) (zipV _++_ (padV {_} {1} [] (mapV (map cSnd) v)) ([] :: mapV (map cFst) v))


example = tr do
   a <- getVec {2}
   b <- getVec {2}
--   putVec ∙ (add ∙ a ∙ (add ∙ a ∙ b))
   putVec ∙ (mul ∙ a ∙ b)

