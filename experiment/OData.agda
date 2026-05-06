
open import Agda.Builtin.String
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

--------------

infixl 9 _$_ _$'_
infixr 4 _=>_

data Ty : Set

-- mangled name (structural)
data Name : Set where
  N    : String ->     Name
  _[_] : Name -> Ty -> Name

record Named (A : Set) : Set where
  inductive
  constructor named
  field
    name : Name
    load : A

open Named

postulate
  uniqueNames : {A B : Set} -> (n : Named A) (m : Named B) -> name n ≡ name m -> _≡_ {A = Σ Set Named} (_ , n) (_ , m)

data Ty where
  Top Bot      :             Ty
  _⊎_ _×_ _=>_ : Ty -> Ty -> Ty
  Newtype      : Named Ty -> Ty

variable
  A B C : Ty
  rd : Named Ty

{-# NO_POSITIVITY_CHECK #-}
data LHS : Ty -> Set

data Tm : Ty -> Set where
  TT    :                  Tm Top
  Left  : Tm A ->          Tm (A ⊎ B)
  Right : Tm B ->          Tm (A ⊎ B)
  _,_   : Tm A -> Tm B ->  Tm (A × B)
  Wrap  : Tm (load rd) ->  Tm (Newtype rd)
  Def   : Named (LHS A) -> Tm A             -- top level definition

  _$_   : Tm (A => B) -> Tm A -> Tm B

  -- or use matchWrap
  unwrap : Tm (Newtype rd) -> Tm (load rd)

  -- or use pair
  fst' : Tm (A × B) -> Tm A
  snd' : Tm (A × B) -> Tm B

  Var : ℕ -> Tm A        -- for printing

data LHS where
  Ret    : Tm A ->            LHS A
  Lam    : (Tm A -> LHS B) -> LHS (A => B)
  either : Tm (A ⊎ B) -> (Tm A -> LHS C) -> (Tm B -> LHS C) -> LHS C
  -- pair : Tm (A × B) -> (Tm A -> Tm B -> LHS C) -> LHS C
  -- matchWrap : Tm (Newtype rd) -> (Tm (load rd) -> LHS C) -> LHS C

---------------------------------------------------------

rec : Name -> Ty -> Ty
rec n a = Newtype (named n a)

fun : Name -> LHS A -> Tm A
fun n f = Def (named n f)


{-

Nat = newtype (Top ⊎ Nat)

Zero : Nat = Wrap (Left TT)

Suc : Nat -> Nat
Suc n = Wrap (Right n)

module (A : U) where
  List = newtype (Top ⊎ A × List)

  Nil : List = Wrap (Left TT)

  Cons : A -> List -> List
  Cons a as = Wrap (Right (a , as))

  length : List -> Nat
  length Nil = Zero
  length (Cons _ as) = Suc (length as)

module (A B : U) where
  map : (A -> B) -> List A -> List B
  map f Nil = Nil
  map f (Cons a as) = Cons (f a) (map f as)

-}



{-# TERMINATING #-}
Nat = rec (N "Nat") (Top ⊎ Nat)

Zero : Tm Nat
Zero = fun (N "Zero") (Ret (Wrap (Left TT)))

Suc : Tm (Nat => Nat)
Suc = fun (N "Suc") (Lam \n -> Ret (Wrap (Right n)))

{-# TERMINATING #-}
List : Ty -> Ty
List A = rec (N "List" [ A ]) (Top ⊎ (A × List A))

Nil : Tm (List A)
-- Nil = Wrap (Left TT)
Nil {A = A} = fun (N "Nil" [ A ]) (Ret (Wrap (Left TT)))

Cons : Tm (A => List A => List A)
Cons {A = A} = fun (N "Cons" [ A ]) (Lam \a -> Lam \as -> Ret (Wrap (Right (a , as))))

{-# TERMINATING #-}
length : Tm (List A => Nat)
length {A = A} = fun (N "lenght" [ A ]) (Lam \as ->
    either (unwrap as)
      (\_ -> Ret Zero)
      (\p -> Ret (Suc $ (length $ snd' p)))
  )

{-# TERMINATING #-}
map : Tm ((A => B) => List A => List B)
map {A = A} {B = B} = fun (N "map" [ A ] [ B ]) (Lam \f -> Lam \as ->
      either (unwrap as)
        (\_ -> Ret Nil)
        (\p ->
          Ret (Cons $ (f $ fst' p) $ (map $ f $ snd' p))
        )
  )

test = map $ Suc $ (Cons $ Zero $ Nil)

-----------------------------------------------------------------------------

infixr 3 _++_
infixr 3 _::_

_++_ : String -> String -> String
_++_ = primStringAppend



record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open Pair

data list (A : Set) : Set where
  []   : list A
  _::_ : A -> list A -> list A

foldr : {A B : Set} -> (A -> B -> B) -> B -> list A -> B
foldr c n [] = n
foldr c n (x :: as) = c x (foldr c n as)

data Doc : Set where
  _[_] : Doc -> Doc -> Doc
  Var  : String -> Doc
  _[[_]]_ : Doc -> String -> Doc -> Doc
  _$_  : Doc -> Doc -> Doc

operators : list String
operators = ":" :: "," :: "->" :: "+" :: "*" :: []

showDoc : Doc -> String
showDoc = go 0  where

  parens : Bool -> String -> String
  parens true  a = "(" ++ a ++ ")"
  parens false a =        a

  addOp : String -> (String -> ℕ) -> String -> ℕ
  addOp t r s with primStringEquality s t
  ... | true  = 0
  ... | false = suc (r s)

  prec : String -> ℕ
  prec = foldr addOp (\_ -> 0) operators

  go : ℕ -> Doc -> String
  go p (Var n)    = n
  go p (a $ b)    = parens (q < p) (go q a ++ " " ++ go (suc q) b) where
    q = 100
  go p (a [ b ])  = parens (q < p) (go q a ++ "[" ++ go 0 b ++ "]") where
    q = 200
  go p (a [[ s ]] b) = parens (q < p) (go (suc q) a ++ " " ++ s ++ " " ++ go q b) where
    q = prec s

State : Set
State = list (Pair Name (Pair Doc Doc))

emptyState : State
emptyState = []

_==D_ : Doc -> Doc -> Bool
Var n ==D Var m = primStringEquality n m
(f $ x) ==D (f' $ x') with f ==D f'
... | false = false
... | true = x ==D x'
(n [ a ]) ==D (n' [ a' ]) with n ==D n'
... | false = false
... | true = a ==D a'
_ ==D _ = false

_==N_ : Name -> Name -> Bool

_==T_ : Ty -> Ty -> Bool
Top ==T Top = true
Bot ==T Bot = true
(a ⊎ b) ==T (a' ⊎ b') with a ==T a'
... | false = false
... | true  = b ==T b'
(a × b) ==T (a' × b') with a ==T a'
... | false = false
... | true  = b ==T b'
(a => b) ==T (a' => b') with a ==T a'
... | false = false
... | true  = b ==T b'
Newtype x ==T Newtype x' = name x ==N name x'
_ ==T _ = false

N a ==N N b = primStringEquality a b
(n [ t ]) ==N (n' [ t' ]) with n ==N n'
... | false = false
... | true = t ==T t'
_ ==N _ = false

elem : Name -> State -> Bool
elem n [] = false
elem n ((n' , _) :: s) with n ==N n'
... | false = elem n s
... | true = true

updateState : Name -> Pair Doc Doc -> State -> State
updateState n p [] = []
updateState n p (x@(n' , _) :: s) with n ==N n'
... | false = x :: updateState n p s
... | true = (n , p) :: s

record M (A : Set) : Set where
  coinductive
  field
    getM : State -> Pair State A

open M

pure : {A : Set} -> A -> M A
getM (pure a) s = s , a

_>>=_ : {A B : Set} -> M A -> (A -> M B) -> M B
getM (m >>= f) s with getM m s
... | s , a = getM (f a) s

Doc' = M Doc

Var' : String -> Doc'
Var' s = pure (Var s)

_$'_ : Doc' -> Doc' -> Doc'
a $' b = do
  a <- a
  b <- b
  pure (a $ b)

_[_]' : Doc' -> Doc' -> Doc'
a [ b ]' = do
  a <- a
  b <- b
  pure (a [ b ])

_[[_]]'_ : Doc' -> String -> Doc' -> Doc'
a [[ s ]]' b = do
  a <- a
  b <- b
  pure (a [[ s ]] b)

showState : State -> String -> String
showState [] s = s
showState ((_ , (n , d)) :: ds) s = showDoc n ++ " = " ++ showDoc d ++ "; " ++ showState ds s

showDoc' : Doc' -> String
showDoc' d with getM d emptyState
... | s , d = showState s (showDoc d)

printTy : Ty -> Doc'

printName : Name -> Doc'
printName (N s) = Var' s
printName (n [ x ]) = printName n [ printTy x ]'

record T : Set where

elem' : Name -> M Bool
getM (elem' n) s = s , elem n s

addDoc : Name -> Doc -> Doc -> M T
getM (addDoc k n d) s = ((k , (n , d)) :: s) , _

updateDoc : Name -> Doc -> Doc -> M T
getM (updateDoc k n d) s = updateState k (n , d) s , _

addDef : {A : _} -> (A -> Doc') -> Named A -> M T
addDef print n' = do
  false <- elem' (name n') where true -> pure _
  _ <- addDoc (name n') (Var "?") (Var "?")
  n <- printName (name n')
  d <- print (load n')
  updateDoc (name n') n d

{-# TERMINATING #-}
printTy Top = Var' "Top"
printTy Bot = Var' "Bot"
printTy (a ⊎  b) = printTy a [[ "+" ]]' printTy b
printTy (a ×  b) = printTy a [[ "*" ]]' printTy b
printTy (a => b) = printTy a [[ "->" ]]' printTy b
printTy (Newtype rd) = do
  _ <- addDef printTy rd
  printName (name rd) 

printVar : ℕ -> Doc'
printVar n = Var' ("v" ++ primShowNat n)

printLHS : LHS A -> Doc'

printLHS' : LHS A -> Doc'
printLHS' {A = A} x =  printLHS x [[ ":" ]]' printTy A

{-# TERMINATING #-}
printTm : Tm A -> Doc'
printTm TT = Var' "TT"
printTm (Left x) = Var' "Left" $' printTm x
printTm (Right x) = Var' "Right" $' printTm x
printTm (x , y) = printTm x [[ "," ]]' printTm y
printTm (Wrap x) = Var' "Wrap" $' printTm x
printTm (f $ x) = printTm f $' printTm x
printTm (unwrap x) = Var' "unwrap" $' printTm x
printTm (fst' x) = Var' "fst" $' printTm x
printTm (snd' x) = Var' "snd" $' printTm x
printTm (Var n) = printVar n
printTm (Def x) = do
  _ <- addDef printLHS' x
  printName (name x)

printLHS = go 0  where
  go : ℕ -> LHS A -> Doc'
  go n (Lam f) = Var' "Lam" $' printVar n $' go (suc n) (f (Var n))
  go n (either x l r) = Var' "either" $' printTm x $' printVar n $' go (suc n) (l (Var n)) $' go (suc n) (r (Var n))
  go n (Ret x) = printTm x


-----------------------------------------------

test' : showDoc' (printTy (List (List Nat))) 
  ≡ "Nat = Top + Nat; List[Nat] = Top + Nat * List[Nat]; List[List[Nat]] = Top + List[Nat] * List[List[Nat]]; List[List[Nat]]"
test' = refl

test'' : showDoc' (printTm test)
  ≡ "Zero = Wrap (Left TT) : Nat; Suc = Lam v0 (Wrap (Right v0)) : Nat -> Nat; Cons[Nat] = Lam v0 (Lam v1 (Wrap (Right (v0 , v1)))) : Nat -> List[Nat] -> List[Nat]; List[Nat] = Top + Nat * List[Nat]; Nil[Nat] = Wrap (Left TT) : List[Nat]; Nat = Top + Nat; map[Nat][Nat] = Lam v0 (Lam v1 (either (unwrap v1) v2 Nil[Nat] (Cons[Nat] (v0 (fst v2)) (map[Nat][Nat] v0 (snd v2))))) : (Nat -> Nat) -> List[Nat] -> List[Nat]; map[Nat][Nat] Suc (Cons[Nat] Zero Nil[Nat])"
test'' = refl
