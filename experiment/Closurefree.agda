{-
Object language supporting an operational semantics without runtume closures.
https://github.com/AndrasKovacs/staged/blob/main/icfp24paper/supplement/agda-cftt/Object.agda
-}
open import Data.Nat
open import Data.Product


data Polarity : Set where
  Value       : Polarity
  Computation : Polarity

variable p p' : Polarity

data Ty : Polarity -> Set where
  Unit  : Ty Value
  Pair  : Ty Value -> Ty Value -> Ty Value
  Bool  : Ty Value
  Maybe : Ty Value -> Ty Value
  Int   : Ty Value
  Carry : Ty Value
  IO    : Ty Computation
  Arr   : Ty Value -> Ty p -> Ty Computation

variable c  : Ty p
variable c' : Ty p'
variable v  : Ty Value
variable v' : Ty Value
variable io : Ty Computation

{-# NO_POSITIVITY_CHECK #-}
data Code : Ty p -> Set where

  Lam    : (Code v -> Code c) -> Code (Arr v c)
  App    : Code (Arr v c) -> (Code v -> Code c)
  Let    : Code c -> (Code c -> Code c') -> Code c'
  LetRec : (Code io -> Code io) -> (Code io -> Code c) -> Code c

  TT        : Code Unit

  MkPair    : Code v -> Code v' -> Code (Pair v v')
  casePair  : Code (Pair v v') -> (Code v -> Code v' -> Code c) -> Code c

  True      : Code Bool
  False     : Code Bool
  caseBool  : Code Bool -> Code c -> Code c -> Code c

  Nothing   : Code (Maybe v)
  Just      : Code v -> Code (Maybe v)
  caseMaybe : Code (Maybe v) -> Code c -> (Code v -> Code c) -> Code c

  Lit  : ℕ -> Code Int
  Add  : Code Int -> Code Int -> Code Int
  AddC : Code Carry -> Code Int -> Code Int -> Code (Pair Carry Int)
  ClearCarry : Code Carry
  Eq   : Code Int -> Code Int -> Code Bool
  Less : Code Int -> Code Int -> Code Bool

  Halt :                          Code IO
  Put  :  Code Int -> Code IO  -> Code IO
  Get  : (Code Int -> Code IO) -> Code IO

not : Code Bool -> Code Bool
not c = caseBool c False True

_&&_ : Code Bool -> Code Bool -> Code Bool
_&&_ p q = caseBool p q False

_||_ : Code Bool -> Code Bool -> Code Bool
_||_ p q = caseBool p True q


letValue : (Code c -> Code c') -> Code c -> Code c'
letValue f x = Let x f

syntax letValue (\x -> e) = lam x => e

letFun : (Code v -> Code c) -> ((Code v -> Code c) -> Code io) -> Code io
letFun f c = Let (Lam f) \f -> c (App f)

------------------

double : Code Int -> Code Int
double = lam x => Add x x

example0 : Code IO
example0 = Get \x -> Put (double (double x)) Halt

example1 : Code IO
example1 = letFun double \d -> Get \x -> Put (d (d x)) Halt

doublePos : Code Int -> Code Int
doublePos = lam x => caseBool (not (Less x (Lit 0))) (double x) x

example2 : Code IO
example2 =
  LetRec (\go -> 
    Get \x ->
    caseBool (Less (double x) (Lit 13) && not (Eq x (Lit 10)))
      Halt
      (Put (doublePos x) go)
  ) \go -> go

