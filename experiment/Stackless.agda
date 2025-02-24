{-
Object language supporting an operational semantics without stack and heap.

For a similar object language see
https://github.com/AndrasKovacs/staged/blob/main/icfp24paper/supplement/agda-cftt/Object.agda
This object language supports an operational semantics without runtime closures but
stack and heap is needed.
-}
{-# OPTIONS --type-in-type #-}

infix  4 _<_
infixr 3 _&&_
infixr 2 _||_

open import Data.Nat hiding (less; _<_)
open import Data.Bool using (Bool)
open import Data.Product

------------------------

data Polarity : Set where
  V : Polarity    -- value
  C : Polarity    -- computation

data Ty : Polarity -> Set where
  Int   : Ty V
  Carry : Ty V
  IO    : Ty C
  Arr   : ∀ {p} -> Ty p -> Ty C -> Ty C

{-# NO_POSITIVITY_CHECK #-}
data Code : ∀ {p} -> Ty p -> Set

R : Ty V -> Set
R a = (Code a -> Code IO) -> Code IO

RT : Ty V -> Ty V -> Set
RT a b = (Code a -> Code b -> Code IO) -> Code IO

RBool = Code IO -> Code IO -> Code IO

data Code where

  Lam : ∀ {p} {a : Ty p} {b} -> (Code a -> Code b) -> Code (Arr a b)
  App : ∀ {p} {a : Ty p} {b} -> Code (Arr a b) -> (Code a -> Code b)
  Let : ∀ {a : Ty C} {b : Ty C} -> Code a -> (Code a -> Code b) -> Code b
  LetRec : ∀ {a : Ty C} {b : Ty C} -> (Code a -> Code a) -> (Code a -> Code b) -> Code b

  Lit  : ℕ -> R Int
  Add  : Code Int -> Code Int -> R Int
  AddC : Code Carry -> Code Int -> Code Int -> RT Carry Int
  ClearCarry : R Carry
  Less : Code Int -> Code Int -> RBool

  Halt : Code IO
  Put  :  Code Int -> Code IO  -> Code IO
  Get  : (Code Int -> Code IO) -> Code IO

ret : ∀ {a} -> Code a -> R a
ret x c = c x

_<_ : R Int -> R Int -> RBool
_<_ a b t f = a \x -> b \y -> Less x y t f

add : R Int -> R Int -> R Int
add a b c = a \x -> b \y -> Add x y c

lit : ℕ -> R Int
lit = Lit

get : (R Int -> Code IO) -> Code IO
get c = Get \x -> c (ret x)

put : R Int -> Code IO -> Code IO
put a c = a \x -> Put x c

iteIO : RBool -> Code IO -> Code IO -> Code IO
iteIO p = p

iteBool : RBool -> RBool -> RBool -> RBool
iteBool a b c t f = Let t \t -> Let f \f -> a (b t f) (c t f)

iteV : ∀ {a} -> RBool -> R a -> R a -> R a
iteV p t f c = Let (Lam c) \c -> p (t (App c)) (f (App c))

true : RBool
true t f = t

false : RBool
false t f = f

letV : ∀ {a b} -> R a -> (R a -> R b) -> R b
letV x f c = x \x -> f (ret x) c

letII : ∀ {a b c} -> (R a -> R b) -> ((R a -> R b) -> Code c) -> Code c
letII f c = Let (Lam \i -> Lam \c -> f (ret i) (App c)) \f -> c \i co -> i \i -> App (App f i) (Lam co)

liftLet : ∀ {a : Set} {p} {i : Ty p} {j} -> (a -> (a -> Code j) -> Code j) -> a -> (a -> Code (Arr i j)) -> Code (Arr i j)
liftLet le i f = Lam \x -> le i \i -> App (f i) x

bind : ∀ {a b} -> (R a -> R b) -> R a -> R b
bind f x = letV x f

syntax bind (\x -> e) = lam x => e

------------------

not : RBool -> RBool
not c = iteBool c false true

_&&_ : RBool -> RBool -> RBool
p && q = iteBool p q false

_||_ : RBool -> RBool -> RBool
p || q = iteBool p true q

double : R Int -> R Int
double = lam x => add x x

doublePos : R Int -> R Int
doublePos = lam x => iteV (not (x < lit 0)) (double x) x

example1 : Code IO
example1 = letII double \d -> get \x -> put (d (d x)) Halt
{- normalized output
Let (Lam (\ i -> Lam (\ c -> Add i i (App c))))
(\ f ->
   Get
   (\ x ->
      App (App f x)
      (Lam (\ i -> App (App f i) (Lam (\ x₁ -> Put x₁ Halt))))))
-}

example2 : Code IO
example2 =
  LetRec (\m -> 
    get \x ->
    iteIO (double x < lit 3 && not (x < lit 0))
      Halt
      (put (double (doublePos x)) m)
  ) \m -> m
{- normalized output
LetRec
(\ m ->
   Get
   (\ x ->
      Let Halt
      (\ t ->
         Let
         (Let (Lam (\ x₁ -> Add x₁ x₁ (\ x₂ -> Put x₂ m)))
          (\ c ->
             Let (Add x x (App c))
             (\ t₁ -> Let (App c x) (\ f -> Lit 0 (\ y -> Less x y f t₁)))))
         (\ f ->
            Add x x
            (\ x₁ ->
               Lit 3
               (\ y ->
                  Less x₁ y
                  (Let t (\ t₁ -> Let f (\ f₁ -> Lit 0 (\ y₁ -> Less x y₁ f₁ t₁))))
                  f))))))
(\ m -> m)
-}
