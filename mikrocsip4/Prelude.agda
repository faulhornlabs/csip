
{-# OPTIONS --type-in-type --rewriting --prop --hidden-argument-puns --erasure --no-keep-covering-clauses #-}

-----------------------

variable @0 A A' A'' : Set

variable @0 P P' : Prop

infix  3 _~>_
postulate _~>_ : @0 A -> @0 A -> Prop
{-# BUILTIN REWRITE _~>_ #-}

infixl 1 _&_
_&_ : A -> (A -> A') -> A'
x & f = f x

flip : (A -> A' -> A'') -> A' -> A -> A''
flip f x' x = f x x'

-----------------------

data @0 bot : Set where

-----------------------

record top : Set where
  constructor tt
{-# COMPILE GHC top = data () (()) #-}

data bool : Set where
  false : bool
  true  : bool
{-# BUILTIN BOOL  bool  #-}
{-# BUILTIN FALSE false #-}
{-# BUILTIN TRUE  true  #-}

not : bool -> bool
not true  = false
not false = true

compiled : bool
compiled = false
{-# COMPILE GHC compiled = True #-}


------------------------

record Semigroup (@0 A : Set) : Set where
  infixr 2 _<>_
  field
    _<>_ : A -> A -> A

open Semigroup {{...}} public


record Monoid (@0 A : Set) : Set where
  field
    empty : A
    {{Semigroup[a]}} : Semigroup A

open Monoid {{...}} hiding (Semigroup[a]) public


record Eq (@0 A : Set) : Set where
  infix 3 _==_
  field
    _==_ : A -> A -> bool

open Eq {{...}} public

--------------------------------------

data nat : Set where
  zero :              nat
  suc  : (n : nat) -> nat
{-# BUILTIN NATURAL nat #-}

eqNat : nat -> nat -> bool
eqNat zero    zero    = true
eqNat (suc n) (suc m) = eqNat n m
eqNat _      _        = false
{-# BUILTIN NATEQUALS eqNat #-}

instance
  Eq[nat] : Eq nat
  Eq[nat] ._==_ = eqNat

infix  3 _<_
_<_ : nat -> nat -> bool
_     < zero  = false
zero  < suc _ = true
suc n < suc m = n < m
{-# BUILTIN NATLESS _<_ #-}

infix  3 _<=_
_<=_ : nat -> nat -> bool
n <= m = n < suc m

-------------------

infixr 0 _,_
record pair (@0 A A' : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : A'

open pair public

instance 
  Eq[pair] : {{Eq A}} -> {{Eq A'}} -> Eq (pair A A')
  Eq[pair] ._==_ (x , x') (y , y') = x == y & \where
    false -> false
    true  -> x' == y'


-------------------------------------------

data either (@0 A A' : Set) : Set where
  left  : A  -> either A A'
  right : A' -> either A A'

data @0 IsRight {@0 A A' : Set} : @0 either A A' -> Set where
  instance YesRight : {@0 r : A'} -> IsRight (right r)

fromRight : (s : either A A') -> @0 {{IsRight s}} -> A'
fromRight (right r) {{YesRight {_}}} = r

fromEither : either A A -> A
fromEither (left  x) = x
fromEither (right x) = x


--------------------

data maybe (@0 A : Set) : Set where
  just    : A -> maybe A
  nothing :      maybe A
-- {-# BUILTIN MAYBE maybe #-}

fromMaybe : A -> maybe A -> A
fromMaybe x nothing  = x
fromMaybe _ (just x) = x

--------------------------

infixr 2 _::_
data list (A : Set) : Set where
  []   :                          list A
  _::_ : (x : A) (xs : list A) -> list A
{-# BUILTIN LIST list #-}

foldr : (A -> A' -> A') -> A' -> list A -> A'
foldr c n []        = n
foldr c n (x :: as) = c x (foldr c n as)

foldl : (A' -> A -> A') -> A' -> list A -> A'
foldl c n [] = n
foldl c n (x :: as) = foldl c (c n x) as

map : (A -> A') -> list A -> list A'
map f []        = []
map f (A :: as) = f A :: map f as 

any : (A -> bool) -> list A -> bool
any p []        = false
any p (a :: as) = p a & \where
  true  -> true
  false -> any p as

instance
  Semigroup[list] : Semigroup (list A)
  Semigroup[list] ._<>_ as bs = foldr _::_ bs as

instance
  Monoid[list] : Monoid (list A)
  Monoid[list] .empty = []

reverse : list A -> list A
reverse as = foldl (\as a -> a :: as) [] as

lookup : {{Eq A}} -> A -> list (pair A A') -> maybe A'
lookup s []               = nothing
lookup s ((s' , p) :: ps) = s == s' & \where
  true  -> just p
  false -> lookup s ps

concat : {{Monoid A}} -> list A -> A
concat [] = empty
concat (x :: xs) = x <> concat xs


-------------------

infixr 2 _**_
record _**_ (@0 A : Set) (@0 B : @0 A -> Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

open _**_ public

-----------

variable    K* : nat
variable @0 K  : nat

data vec (@0 A : Set) : @0 nat -> Set where
  []   : vec A zero
  _::_ : A -> vec A K -> vec A (suc K)

mapV : (A -> A') -> vec A K -> vec A' K
mapV f []        = []
mapV f (x :: xs) = f x :: mapV f xs

vecToList : vec A K -> list A
vecToList []        = []
vecToList (x :: xs) = x :: vecToList xs

listToVec : list A -> nat ** \K -> vec A K
listToVec []        = _ , []
listToVec (x :: xs) = listToVec xs & \(_ , xs) -> _ , x :: xs

zipWith : (A -> A' -> A'') -> vec A K -> vec A' K -> vec A'' K
zipWith f []        []        = []
zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys


------------------------

postulate char : Set
{-# BUILTIN CHAR char #-}

primitive primCharToNat : char -> nat
charToNat = primCharToNat

postulate string : Set
{-# BUILTIN STRING string #-}

primitive primStringAppend : string -> string -> string
instance
  Semigroup[string] : Semigroup string
  Semigroup[string] ._<>_ = primStringAppend

primitive primStringEquality : string -> string -> bool
instance
  Eq[string] : Eq string
  Eq[string] ._==_ = primStringEquality

primitive primStringToList : string -> list char
stringToList = primStringToList

primitive primStringFromList : list char -> string
stringFromList = primStringFromList

primitive primShowNat : nat -> string

record IsString (@0 A : Set) : Set where
  field
    fromString : (s : string) -> A

open IsString {{...}} public
{-# BUILTIN FROMSTRING fromString #-}

instance
  IsString[string] : IsString string
  IsString[string] .fromString s = s

------------

stringBuilder = string -> string

instance
  Semigroup[stringBuilder] : Semigroup stringBuilder
  Semigroup[stringBuilder] ._<>_ f g s = f (g s)

instance
  IsString[stringBuilder] : IsString stringBuilder
  IsString[stringBuilder] .fromString s s' = s <> s'

runStringBuilder : stringBuilder -> string
runStringBuilder f = f ""


record Show (@0 A : Set) : Set where
  field
    show : A -> stringBuilder

open Show {{...}} public

show' : {{Show A}} -> A -> string
show' d = runStringBuilder (show d)

instance
  Show[string] : Show string
  Show[string] .show s = fromString s

instance
  Show[nat] : Show nat
  Show[nat] .show n = show (primShowNat n)



---------------------

private variable @0 x  y  z  : A
private variable @0 x' y' z' : A'

infix  3 _~_
data @0 _~_ (@0 x : A) : @0 A -> Prop where
  instance refl : x ~ x

infixl 1 _&in_
_&in_ : (x : A) -> ((y : A) -> @0 x ~ y -> A') -> A'
x &in f = f x refl

@0 sym : @0 x ~ y -> y ~ x
sym refl = refl

infixr 3 _*~_
@0 _*~_ : @0 x ~ y -> @0 y ~ z -> x ~ z
refl *~ refl = refl

@0 cong : (@0 f : A -> A') -> @0 x ~ y -> f x ~ f y
cong _ refl = refl

@0 cong2 : (@0 f : A -> A' -> A'') -> @0 x ~ y -> @0 x' ~ y' -> f x x' ~ f y y'
cong2 _ refl refl = refl

postulate coe : @0 A ~ A' -> A -> A'
postulate @0 coeRefl : {@0 x : A} -> coe refl x ~> x
{-# REWRITE coeRefl #-}
{-# COMPILE GHC coe = \_ _ _ -> coe #-}

subst : (@0 f : @0 A -> Set) -> @0 x ~ y -> f x -> f y
subst f e = coe (cong (\x -> f x) e)

infix  3 _~!_
postulate @0 _~!_ : (@0 x y : A) -> x ~ y

postulate primErased : @0 A -> A
postulate @0 primErasedRule : primErased x ~> x
{-# REWRITE primErasedRule #-}

nopCompiled : {@0 B : @0 A -> Set} -> @0 ((x : A) -> B x) -> (x : A) -> B x
nopCompiled f x = compiled & \where
  true  -> coe (_ ~! _) x
  false -> primErased (f x)

--------------------

record Emb (@0 P : Prop) : Set where
  constructor emb
  field
    @0 getProp : P

open Emb public

infix  3 _~e_
@0 _~e_ : @0 A -> @0 A -> Set
x ~e y = Emb (x ~ y)

------------------

-- used for pattern matching
infix  3 _~e'_
data _~e'_ (@0 x : A) : @0 A -> Set where
  refl : x ~e' x

match : @0 x ~ y -> x ~e' y
match {x} e = subst (\y -> x ~e' y) e refl

match' : @0 x ~e y -> x ~e' y
match' (emb e) = match e

infixl 1 _&in'_
_&in'_ : (x : A) -> ((y : A) -> @0 x ~e' y -> A') -> A'
x &in' f = f x refl


-----------------------

variable @0 M : @0 Set -> Set

record Monad (@0 M : @0 Set -> Set) : Set where
  field
    _>>=_ : M A -> (A -> M A') -> M A'
    pure  : A -> M A

open Monad {{...}} public

matchM : {{Monad M}} -> (x : A) -> M (A ** \y -> x ~e' y)
matchM x = pure (x , refl)

infixl 4 _<$>_
_<$>_ : {{Monad M}} -> (A -> A') -> M A -> M A'
f <$> m = m >>= \x -> pure (f x)

infixl 1 _<&>_
_<&>_ : {{Monad M}} -> M A -> (A -> A') -> M A'
m <&> f = m >>= \x -> pure (f x)

infixl 1 _<&>match
_<&>match : {{Monad M}} -> M (x ~e y) -> M (x ~e' y)
m <&>match = m <&> \e -> match' e


infixl 4 _<*>_
_<*>_ : {{Monad M}} -> M (A -> A') -> M A -> M A'
f <*> m = f >>= \f -> m >>= \a -> pure (f a)

mapM : {{Monad M}} -> (A -> M A') -> list A -> M (list A')
mapM f []        = pure []
mapM f (x :: xs) = (| f x :: mapM f xs |)

mapMV : {{Monad M}} -> (A -> M A') -> vec A K -> M (vec A' K)
mapMV f []        = pure []
mapMV f (x :: xs) = (| f x :: mapMV f xs |)

infixr 2 _<>m_
_<>m_ : {{Monad M}} -> {{Semigroup A}} -> M A -> M A -> M A
x <>m y = (| x <> y |)

instance
  Monad[maybe] : Monad maybe
  Monad[maybe] .pure a = just a
  Monad[maybe] ._>>=_ (just x) f = f x
  Monad[maybe] ._>>=_ nothing  f = nothing

record ShowM (@0 A : Set) (@0 M : @0 Set -> Set) : Set where
  field
    showM : A -> M stringBuilder

open ShowM {{...}} public

-----------------------

record MonadError (@0 E : Set) (@0 M : @0 Set -> Set) : Set where
  field
    throwError   : E -> M A
    {{monad[M]}} : Monad M

open MonadError {{...}} hiding (monad[M]) public

instance
  MonadError[maybe] : MonadError A maybe
  MonadError[maybe] .throwError s = nothing

throwErrorM : {{MonadError A M}} -> M A -> M A'
throwErrorM s = do
  s <- s
  throwError s

-- TODO: rename
try : {{MonadError A' M}} -> M A' -> M (maybe A) -> M A
try e m = m >>= \where
  (just x) -> pure x
  nothing  -> throwErrorM e

-----------------------

postulate IO : Set -> Set
{-# BUILTIN IO IO #-}
{-# COMPILE GHC IO = type IO #-}

postulate bindIO : IO A -> (A -> IO A') -> IO A'
{-# COMPILE GHC bindIO = \_ _ m f -> m >>= f #-}

postulate pureIO : A -> IO A
{-# COMPILE GHC pureIO = \_ x -> pure x #-}

instance
  Monad[IO] : Monad (\A -> IO A)
  Monad[IO] ._>>=_ = bindIO
  Monad[IO] .pure  = pureIO

postulate interact : (string -> string) -> IO top
{-# COMPILE GHC interact = TIO.interact #-}

postulate getArgs  : IO (list string)
{-# FOREIGN GHC import qualified Data.Text.IO as TIO #-}
{-# FOREIGN GHC import System.Environment (getArgs) #-}
{-# FOREIGN GHC
  getArgsText :: IO [Data.Text.Text]
  getArgsText = do
    args <- getArgs
    pure (map Data.Text.pack args)
#-}
{-# COMPILE GHC getArgs = getArgsText #-}

postulate writeFile : string -> string -> IO top
{-# FOREIGN GHC
  writeTextFile :: Data.Text.Text -> Data.Text.Text -> IO ()
  writeTextFile f s = TIO.writeFile (Data.Text.unpack f) s
#-}
{-# COMPILE GHC writeFile = writeTextFile #-}

postulate readFile : string -> IO string
{-# FOREIGN GHC
  readTextFile :: Data.Text.Text -> IO Data.Text.Text
  readTextFile f = TIO.readFile (Data.Text.unpack f)
#-}
{-# COMPILE GHC readFile = readTextFile #-}

postulate putStr : string -> IO top
{-# COMPILE GHC putStr = TIO.putStr #-}

postulate hashString : string -> string
{-# FOREIGN GHC
  hashString :: Data.Text.Text -> Data.Text.Text
  hashString = Data.Text.pack . map char . base 22 . hash (5381 :: Integer) . Data.Text.unpack  where

    -- djb2
    hash acc [] = acc
    hash acc (c: s) = hash (mod (fromIntegral (fromEnum c) + 33 * acc) (2^128)) s 

    base 0 _ = []
    base n i = fromIntegral (mod i 64): base (n-1) (div i 64)

    char i = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_" !! i
#-}
{-# COMPILE GHC hashString = hashString #-}


---------------------------------------

postulate future' : (A -> (A -> A'' -> A'') -> A') -> A'
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

future : (A -> ((@0 A'' : Set) -> A -> A'' -> A'') -> A') -> A'
future f = future' {A'' = bool} \get set -> f get (\C a c -> coe (bool ~! C) (set a (coe (C ~! bool) c)))

--------------------------

record MonadSupply (@0 M : @0 Set -> Set) : Set where
  field
    newId        : M nat           -- TODO: dedicated Identifier type instead of nat
    {{monad[m]}} : Monad M

open MonadSupply {{...}} hiding (monad[m]) public

--------------
{-
postulate unsafeNewId : (nat -> A) -> A
{-# FOREIGN GHC import Data.IORef (atomicModifyIORef') #-}
{-# FOREIGN GHC
  {-# NOINLINE idCounter #-}
  idCounter :: IORef Integer
  idCounter = unsafe (newIORef 0) id

  unsafeNewId :: (Integer -> a) -> a
  unsafeNewId = unsafe (atomicModifyIORef' idCounter (\i -> (i+1, i)))
#-}
{-# COMPILE GHC unsafeNewId = \_ -> unsafeNewId #-}

-}
