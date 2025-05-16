{-
Object language supporting an operational semantics without stack and heap.

For a similar object language see
https://github.com/AndrasKovacs/staged/blob/main/icfp24paper/supplement/agda-cftt/Object.agda
This object language supports an operational semantics without runtime closures but
stack and heap is needed.
-}
open import Data.Nat hiding (less; _<_)
open import Data.Bool using (Bool)
open import Data.Product


data Polarity : Set where
  Value       : Polarity
  Computation : Polarity

variable p p' : Polarity

data Ty : Polarity -> Set where
  Int   : Ty Value
  Carry : Ty Value
  IO    : Ty Computation
  Arr   : Ty p -> Ty Computation -> Ty Computation

variable c  : Ty p
variable c' : Ty p'
variable io : Ty Computation

{-# NO_POSITIVITY_CHECK #-}
data Code : Ty p -> Set where

  Lam    : (Code c -> Code io) -> Code (Arr c io)
  App    : Code (Arr c io) -> (Code c -> Code io)
  Let    : Code io -> (Code io -> Code IO) -> Code IO
  LetRec : (Code io -> Code io) -> (Code io -> Code IO) -> Code IO

  Lit  : ℕ ->                                                (Code Int -> Code IO) -> Code IO
  Add  :               Code Int -> Code Int ->               (Code Int -> Code IO) -> Code IO
  AddC : Code Carry -> Code Int -> Code Int -> (Code Carry -> Code Int -> Code IO) -> Code IO
  ClearCarry :                                             (Code Carry -> Code IO) -> Code IO

  Eq   : Code Int -> Code Int ->    Code IO -> Code IO -> Code IO
  Less : Code Int -> Code Int ->    Code IO -> Code IO -> Code IO

  Halt :                          Code IO
  Put  :  Code Int -> Code IO  -> Code IO
  Get  : (Code Int -> Code IO) -> Code IO


Ret : Ty Value -> Set
Ret a = (Code a -> Code IO) -> Code IO

Int'  = Ret Int
Bool' = Code IO -> Code IO -> Code IO
IO'   = Code IO

_==_ : Int' -> Int' -> Bool'
_==_ a b t f = a \x -> b \y -> Eq x y t f

_<_ : Int' -> Int' -> Bool'
_<_ a b t f = a \x -> b \y -> Less x y t f

add : Int' -> Int' -> Int'
add a b c = a \x -> b \y -> Add x y c

lit : ℕ -> Int'
lit = Lit

get : (Int' -> IO') -> IO'
get c = Get \x -> c (\d -> d x)

put : Int' -> IO' -> IO'
put a c = a \x -> Put x c

not : Bool' -> Bool'
not c t f = c f t

_&&_ : Bool' -> Bool' -> Bool'
_&&_ p q t f = Let f \f -> p (q t f) f

_||_ : Bool' -> Bool' -> Bool'
_||_ p q t f = Let t \t -> p t (q t f)

iteValue : Bool' -> Ret c -> Ret c -> Ret c
iteValue p t f c = Let (Lam c) \c -> p (t (App c)) (f (App c))

iteIO : Bool' -> IO' -> IO' -> IO'
iteIO p t f = p t f

letValue : (Ret c -> Ret c') -> Ret c -> Ret c'
letValue f x c = x \x -> f (\d -> d x) c

syntax letValue (\x -> e) = lam x => e

letFun : (Ret c -> Ret c') -> ((Ret c -> Ret c') -> Code IO) -> Code IO
letFun f c = Let (Lam \i -> Lam \c -> f (\d -> d i) (App c)) \f -> c \i co -> i \i -> App (App f i) (Lam co)

------------------

double : Int' -> Int'
double = lam x => add x x

example0 : IO'
example0 = get \x -> put (double (double x)) Halt

example1 : IO'
example1 = letFun double \d -> get \x -> put (d (d x)) Halt

doublePos : Int' -> Int'
doublePos = lam x => iteValue (not (x < lit 0)) (double x) x

example2 : IO'
example2 =
  LetRec (\go -> 
    get \x ->
    iteIO ((double x < lit 13) && not (x == lit 10))
      Halt
      (put (doublePos x) go)
  ) \go -> go
