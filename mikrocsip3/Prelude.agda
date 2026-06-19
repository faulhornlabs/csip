{-# OPTIONS --type-in-type --no-positivity-check --no-termination-check --rewriting --prop --injective-type-constructors --hidden-argument-puns #-}
module Prelude where

infix  3 _~_     -- Prop equality
infix  3 _~e_    -- Set equality
infix  3 _<_     -- less on Nat
infix  3 _<=_    -- less or equal on Nat
infixr 3 _*~_    -- transitivity for _~_
infixr 2 _::_    -- List cons
infixr 2 _**_    -- dependent pair type (infix Sigma)
infixr 2 _<>m_   -- liftM2 _<>_
infixl 1 _&_     -- flipped application
infixl 1 _&P_    -- flipped application on Prop
infixl 1 _&in_   -- flipped application with equality
infixl 4 _<$>_
infixl 4 _<*>_
infixr 0 _,_     -- non-dependent pair constructor
infixr 0 _,,_    -- dependent pair constructor
infixl 1 _<&>_


variable A A' B : Set
variable P Q : Prop
variable M : Set -> Set

--------------------

_&_ : A -> (A -> B) -> B
x & f = f x

_&P_ : P -> (P -> Q) -> Q
x &P f = f x


--------------------

record T : Set where
  constructor tt
{-# COMPILE GHC T = data () (()) #-}


data Bool : Set where
  False True : Bool
{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN FALSE False #-}
{-# BUILTIN TRUE  True  #-}

not : Bool -> Bool
not True  = False
not False = True

------------------------

record Semigroup (A : Set) : Set where
  field
    _<>_ : A -> A -> A

  infixr 2 _<>_

open Semigroup {{...}} public


record Monoid (A : Set) : Set where
  field
    empty : A
    {{Semigroup[A]}} : Semigroup A

open Monoid {{...}} hiding (Semigroup[A]) public


record Eq (A : Set) : Set where
  field
    _==_ : A -> A -> Bool

  infix 3 _==_

open Eq {{...}} public

--------------------------------------

data Nat : Set where
  Zero :              Nat
  Suc  : (n : Nat) -> Nat
{-# BUILTIN NATURAL Nat #-}

eqNat : Nat -> Nat -> Bool
eqNat Zero    Zero    = True
eqNat (Suc n) (Suc m) = eqNat n m
eqNat _      _        = False
{-# BUILTIN NATEQUALS eqNat #-}

instance
  Eq[Nat] : Eq Nat
  Eq[Nat] ._==_ = eqNat

_<_ : Nat -> Nat -> Bool
_     < Zero  = False
Zero  < Suc _ = True
Suc n < Suc m = n < m
{-# BUILTIN NATLESS _<_ #-}

_<=_ : Nat -> Nat -> Bool
n <= m = n < Suc m

-------------------

record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open Pair public

instance 
  Eq[Pair] : {{Eq A}} -> {{Eq B}} -> Eq (Pair A B)
  Eq[Pair] ._==_ (a , b) (a' , b') = a == a' & \where
    False -> False
    True  -> b == b'


-------------------------------------------

data Either (A B : Set) : Set where
  Left  : A -> Either A B
  Right : B -> Either A B

data IsRight {A B : Set} : Either A B -> Set where
  instance YesRight : {r : B} -> IsRight (Right r)

fromRight : (s : Either A B) -> {{IsRight s}} -> B
fromRight s {{YesRight {r}}} = r

fromEither : Either A A -> A
fromEither (Left  x) = x
fromEither (Right x) = x


--------------------

data Maybe (A : Set) : Set where
  Just    : A -> Maybe A
  Nothing :      Maybe A
{-# BUILTIN MAYBE Maybe #-}

fromMaybe : A -> Maybe A -> A
fromMaybe a Nothing  = a
fromMaybe _ (Just a) = a

--------------------------

data List (A : Set) : Set where
  []   :                          List A
  _::_ : (x : A) (xs : List A) -> List A
{-# BUILTIN LIST List #-}

foldr : (A -> B -> B) -> B -> List A -> B
foldr c n []        = n
foldr c n (x :: as) = c x (foldr c n as)

foldl : (B -> A -> B) -> B -> List A -> B
foldl c n [] = n
foldl c n (x :: as) = foldl c (c n x) as

map : (A -> B) -> List A -> List B
map f []        = []
map f (a :: as) = f a :: map f as 

any : (A -> Bool) -> List A -> Bool
any p []        = False
any p (a :: as) = p a & \where
  True  -> True
  False -> any p as

instance
  Semigroup[List] : Semigroup (List A)
  Semigroup[List] ._<>_ as bs = foldr _::_ bs as

instance
  Monoid[List] : Monoid (List A)
  Monoid[List] .empty = []

reverse : List A -> List A
reverse as = foldl (\as a -> a :: as) [] as

lookup : {{Eq A}} -> A -> List (Pair A B) -> Maybe B
lookup s []               = Nothing
lookup s ((s' , p) :: ps) = s == s' & \where
  True  -> Just p
  False -> lookup s ps

concat : {{Monoid A}} -> List A -> A
concat [] = empty
concat (x :: xs) = x <> concat xs

-------------------

record _**_ (A : Set) (B : A -> Set) : Set where
  constructor _,,_
  field
    fst : A
    snd : B fst

open _**_ public

Σ = _**_

syntax Σ A (\ x -> B) = x :: A * B

-----------

variable n : Nat

data Vec (A : Set) : Nat -> Set where
  []   : Vec A Zero
  _::_ : A -> Vec A n -> Vec A (Suc n)

concat' : {n : Nat} -> {{Monoid A}} -> Vec A n -> A
concat' [] = empty
concat' (x :: xs) = x <> concat' xs

mapV : (A -> B) -> Vec A n -> Vec B n
mapV f []        = []
mapV f (a :: as) = f a :: mapV f as 

vecToList : Vec A n -> List A
vecToList []        = []
vecToList (x :: xs) = x :: vecToList xs

listToVec : List A -> Nat ** Vec A
listToVec []        = _ ,, []
listToVec (a :: as) = listToVec as & \(_ ,, as) -> _ ,, a :: as

zipWith : {C : Set} -> (A -> B -> C) -> Vec A n -> Vec B n -> Vec C n
zipWith f []        []        = []
zipWith f (a :: as) (b :: bs) = f a b :: zipWith f as bs


------------------------

postulate Char : Set
{-# BUILTIN CHAR Char #-}

primitive primCharToNat : Char -> Nat
charToNat = primCharToNat

postulate String : Set
{-# BUILTIN STRING String #-}

primitive primStringAppend : String -> String -> String
instance
  Semigroup[String] : Semigroup String
  Semigroup[String] ._<>_ = primStringAppend

primitive primStringEquality : String -> String -> Bool
instance
  Eq[String] : Eq String
  Eq[String] ._==_ = primStringEquality

primitive primStringToList : String -> List Char
stringToList = primStringToList

primitive primStringFromList : List Char -> String
stringFromList = primStringFromList

primitive primShowNat : Nat -> String
showNat = primShowNat

record IsString (A : Set) : Set where
  field
    fromString : (s : String) -> A

open IsString {{...}} public
{-# BUILTIN FROMSTRING fromString #-}

instance
  IsString[String] : IsString String
  IsString[String] .fromString s = s

------------

StringBuilder = String -> String

instance
  Semigroup[StringBuilder] : Semigroup StringBuilder
  Semigroup[StringBuilder] ._<>_ f g s = f (g s)

instance
  IsString[StringBuilder] : IsString StringBuilder
  IsString[StringBuilder] .fromString s s' = s <> s'

runStringBuilder : StringBuilder -> String
runStringBuilder f = f ""


---------------------

data _~_ {A : Set} (a : A) : A -> Prop where
  instance Refl : a ~ a
{-# BUILTIN REWRITE _~_ #-}
{-# FOREIGN GHC data IEq a b c = IRefl #-}
{-# COMPILE GHC _~_ = data IEq (IRefl) #-}

_&in_ : (a : A) -> ((a' : A) -> a ~ a' -> A') -> A'
x &in f = f x Refl

sym : {a a' : A} -> a ~ a' -> a' ~ a
sym Refl = Refl

_*~_ : {a a' a'' : A} -> a ~ a' -> a' ~ a'' -> a ~ a''
Refl *~ e = e

cong : {a a' : A} -> (f : A -> B) -> a ~ a' -> f a ~ f a'
cong _ Refl = Refl

cong2 : {C : Set} -> {a a' : A} {b b' : B} -> (f : A -> B -> C) -> a ~ a' -> b ~ b' -> f a b ~ f a' b'
cong2 _ Refl Refl = Refl

coeP : P ~ Q -> P -> Q
coeP Refl p = p

postulate coe : A ~ B -> A -> B
postulate coeRefl : {a : A} -> coe Refl a ~ a
{-# REWRITE coeRefl #-}
{-# COMPILE GHC coe = \_ _ _ -> coe #-}

subst : {a a' : A} (f : A -> Set) -> a ~ a' -> f a -> f a'
subst f e = coe (cong f e)

substP : {a a' : A} (f : A -> Prop) -> a ~ a' -> f a -> f a'
substP f e = coeP (cong f e)

postulate believeMe : P

believeMe~ : {a a' : A} -> a ~ a'
believeMe~ = believeMe

--------------------

record Emb (P : Prop) : Set where
  constructor emb
  field
    getProp : P

open Emb public

_~e_ : A -> A -> Set
a ~e a' = Emb (a ~ a')

------------------

-- used for pattern matching
data _~e'_ (x : A) : A -> Set where
  Refl : x ~e' x

match : {a a' : A} -> a ~ a' -> a ~e' a'
match {a} e = subst (_~e'_ a) e Refl

match' : {a a' : A} -> a ~e a' -> a ~e' a'
match' (emb e) = match e

-----------------------

record Monad (M : Set -> Set) : Set where
  field
    _>>=_ : M A -> (A -> M B) -> M B
    pure  : A -> M A

open Monad {{...}} public

_<$>_ : {{Monad M}} -> (A -> B) -> M A -> M B
f <$> m = m >>= \a -> pure (f a)

_<&>_ : {{Monad M}} -> M A -> (A -> B) -> M B
m <&> f = m >>= \a -> pure (f a)

_<*>_ : {{Monad M}} -> M (A -> B) -> M A -> M B
f <*> m = f >>= \f -> m >>= \a -> pure (f a)

mapM : {{Monad M}} -> (A -> M B) -> List A -> M (List B)
mapM f [] = pure []
mapM f (a :: as) = (| f a :: mapM f as |)

mapMV : {{Monad M}} -> (A -> M B) -> Vec A n -> M (Vec B n)
mapMV f [] = pure []
mapMV f (a :: as) = (| f a :: mapMV f as |)

_<>m_ : {{Monad M}} -> {{Semigroup A}} -> M A -> M A -> M A
x <>m y = (| x <> y |)

instance
  Monad[Maybe] : Monad Maybe
  Monad[Maybe] .pure a = Just a
  Monad[Maybe] ._>>=_ (Just x) f = f x
  Monad[Maybe] ._>>=_ Nothing  f = Nothing

-----------------------

record MonadError (E : Set) (M : Set -> Set) : Set where
  field
    throwError : E -> M A
    {{monad[M]}} : Monad M

open MonadError {{...}} hiding (monad[M]) public

instance
  MonadError[Maybe] : MonadError A Maybe
  MonadError[Maybe] .throwError s = Nothing

throwErrorM : {{MonadError A M}} -> M A -> M A'
throwErrorM s = do
  s <- s
  throwError s

-----------------------

postulate IO : Set -> Set
{-# BUILTIN IO IO #-}
{-# COMPILE GHC IO = type IO #-}

postulate bindIO : IO A -> (A -> IO B) -> IO B
{-# COMPILE GHC bindIO = \_ _ m f -> m >>= f #-}

postulate pureIO : A -> IO A
{-# COMPILE GHC pureIO = \_ x -> pure x #-}

instance
  Monad[IO] : Monad IO
  Monad[IO] ._>>=_ = bindIO
  Monad[IO] .pure  = pureIO

postulate interact : (String -> String) -> IO T
{-# COMPILE GHC interact = TIO.interact #-}

postulate getArgs  : IO (List String)
{-# FOREIGN GHC import qualified Data.Text.IO as TIO #-}
{-# FOREIGN GHC import System.Environment (getArgs) #-}
{-# FOREIGN GHC
  getArgsText :: IO [Data.Text.Text]
  getArgsText = do
    args <- getArgs
    pure (map Data.Text.pack args)
#-}
{-# COMPILE GHC getArgs = getArgsText #-}


---------------------------------------

postulate future' : {C : Set} -> (A -> (A -> C -> C) -> B) -> B   ---  (A, A -> ())
{-# FOREIGN GHC import System.IO.Unsafe (unsafePerformIO) #-}
{-# FOREIGN GHC import Data.IORef (IORef, newIORef, readIORef, writeIORef) #-}
{-# FOREIGN GHC
  {-# NOINLINE unsafe #-}
  unsafe :: IO a -> (a -> b) -> b
  unsafe m f = unsafePerformIO (f <$> m)

  future :: (a -> (forall c. a -> c -> c) -> b) -> b
  future f = unsafe (newIORef (error "value not yet defined"))
    (\r -> f (unsafe (readIORef r) id) (\x y -> unsafe (writeIORef r x) (\() -> y)))
#-}
{-# COMPILE GHC future' = \_ _ _ f -> future (\get set -> f get set) #-}

future : (A -> ((C : Set) -> A -> C -> C) -> B) -> B
future f = future' {C = Bool} \get set -> f get (\C a c -> coe believeMe~ (set a (coe believeMe~ c)))


