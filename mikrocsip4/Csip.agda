
{-# OPTIONS --type-in-type --no-positivity-check --no-termination-check --rewriting --prop --injective-type-constructors --hidden-argument-puns --with-K #-}

infixl 4 _<$>_
infixl 4 _<*>_
infix  3 _~_     -- Prop equality
infix  3 _~e_    -- Set equality
infix  3 _<_     -- less on Nat
infix  3 _<=_    -- less or equal on Nat
infixr 3 _*~_    -- transitivity for _~_
infixr 2 _::_    -- List cons
infixr 2 _**_    -- dependent pair type (infix Sigma)
infixr 2 _<>m_   -- liftM2 _<>_
infixl 1 _<&>_
infixl 1 _&_     -- flipped application
infixl 1 _&p_    -- flipped application on Prop
infixl 1 _&in_   -- flipped application with equality
infixr 0 _,_     -- pair constructor

-----------------------

variable a a' a'' : Set
variable b  : a  -> Set
variable b' : a' -> Set
variable p p' : Prop

-----------------------

_&_ : a -> (a -> a') -> a'
x & f = f x

_&p_ : p -> (p -> p') -> p'
x &p f = f x

-----------------------

record top : Set where
  constructor tt
{-# COMPILE GHC top = data () (()) #-}

data bool : Set where
  false true : bool
{-# BUILTIN BOOL  bool  #-}
{-# BUILTIN FALSE false #-}
{-# BUILTIN TRUE  true  #-}

not : bool -> bool
not true  = false
not false = true

------------------------

record Semigroup (a : Set) : Set where
  field
    _<>_ : a -> a -> a

  infixr 2 _<>_

open Semigroup {{...}}


record Monoid (a : Set) : Set where
  field
    empty : a
    {{Semigroup[a]}} : Semigroup a

open Monoid {{...}} hiding (Semigroup[a])


record Eq (a : Set) : Set where
  field
    _==_ : a -> a -> bool

  infix 3 _==_

open Eq {{...}}

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

_<_ : nat -> nat -> bool
_     < zero  = false
zero  < suc _ = true
suc n < suc m = n < m
{-# BUILTIN NATLESS _<_ #-}

_<=_ : nat -> nat -> bool
n <= m = n < suc m

-------------------

-- TODO: remove
record pair (a a' : Set) : Set where
  constructor _,_
  field
    fst : a
    snd : a'

open pair

instance 
  Eq[pair] : {{Eq a}} -> {{Eq a'}} -> Eq (pair a a')
  Eq[pair] ._==_ (x , x') (y , y') = x == y & \where
    false -> false
    true  -> x' == y'


-------------------------------------------

data either (a a' : Set) : Set where
  left  : a  -> either a a'
  right : a' -> either a a'

data IsRight {a a' : Set} : either a a' -> Set where
  instance YesRight : {r : a'} -> IsRight (right r)

fromRight : (s : either a a') -> {{IsRight s}} -> a'
fromRight s {{YesRight {r}}} = r

fromEither : either a a -> a
fromEither (left  x) = x
fromEither (right x) = x


--------------------

data maybe (a : Set) : Set where
  just    : a -> maybe a
  nothing :      maybe a
{-# BUILTIN MAYBE maybe #-}

fromMaybe : a -> maybe a -> a
fromMaybe a nothing  = a
fromMaybe _ (just a) = a

--------------------------

data list (a : Set) : Set where
  []   :                          list a
  _::_ : (x : a) (xs : list a) -> list a
{-# BUILTIN LIST list #-}

foldr : (a -> a' -> a') -> a' -> list a -> a'
foldr c n []        = n
foldr c n (x :: as) = c x (foldr c n as)

foldl : (a' -> a -> a') -> a' -> list a -> a'
foldl c n [] = n
foldl c n (x :: as) = foldl c (c n x) as

map : (a -> a') -> list a -> list a'
map f []        = []
map f (a :: as) = f a :: map f as 

any : (a -> bool) -> list a -> bool
any p []        = false
any p (a :: as) = p a & \where
  true  -> true
  false -> any p as

instance
  Semigroup[list] : Semigroup (list a)
  Semigroup[list] ._<>_ as bs = foldr _::_ bs as

instance
  Monoid[list] : Monoid (list a)
  Monoid[list] .empty = []

reverse : list a -> list a
reverse as = foldl (\as a -> a :: as) [] as

lookup : {{Eq a}} -> a -> list (pair a a') -> maybe a'
lookup s []               = nothing
lookup s ((s' , p) :: ps) = s == s' & \where
  true  -> just p
  false -> lookup s ps

concat : {{Monoid a}} -> list a -> a
concat [] = empty
concat (x :: xs) = x <> concat xs


-------------------

record _**_ (a : Set) (b : a -> Set) : Set where
  constructor _,_
  field
    fst : a
    snd : b fst

open _**_


-----------

variable k : nat

data vec (a : Set) : nat -> Set where
  []   : vec a zero
  _::_ : a -> vec a k -> vec a (suc k)

mapV : (a -> a') -> vec a k -> vec a' k
mapV f []        = []
mapV f (x :: xs) = f x :: mapV f xs

vecToList : vec a k -> list a
vecToList []        = []
vecToList (x :: xs) = x :: vecToList xs

listToVec : list a -> nat ** vec a
listToVec []        = _ , []
listToVec (x :: xs) = listToVec xs & \(_ , xs) -> _ , x :: xs

zipWith : (a -> a' -> a'') -> vec a k -> vec a' k -> vec a'' k
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
showNat = primShowNat

record IsString (a : Set) : Set where
  field
    fromString : (s : string) -> a

open IsString {{...}}
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


---------------------

data _~_ (x : a) : a -> Prop where
  instance refl : x ~ x
{-# BUILTIN REWRITE _~_ #-}
{-# FOREIGN GHC data IEq a b c = IRefl #-}
{-# COMPILE GHC _~_ = data IEq (IRefl) #-}

_&in_ : (x : a) -> ((y : a) -> x ~ y -> a') -> a'
x &in f = f x refl

sym : {x y : a} -> x ~ y -> y ~ x
sym refl = refl

_*~_ : {x y z : a} -> x ~ y -> y ~ z -> x ~ z
refl *~ e = e

cong : {x y : a} -> (f : a -> a') -> x ~ y -> f x ~ f y
cong _ refl = refl

cong2 : {x y : a} {x' y' : a'} -> (f : a -> a' -> a'') -> x ~ y -> x' ~ y' -> f x x' ~ f y y'
cong2 _ refl refl = refl

coeP : p ~ p' -> p -> p'
coeP refl p = p

postulate coe : a ~ a' -> a -> a'
postulate coeRefl : {x : a} -> coe refl x ~ x
{-# REWRITE coeRefl #-}
{-# COMPILE GHC coe = \_ _ _ -> coe #-}

subst : {x y : a} (f : a -> Set) -> x ~ y -> f x -> f y
subst f e = coe (cong f e)

substP : {x y : a} (f : a -> Prop) -> x ~ y -> f x -> f y
substP f e = coeP (cong f e)

postulate believeMe : p

believeMe~ : {x y : a} -> x ~ y
believeMe~ = believeMe

--------------------

record Emb (p : Prop) : Set where
  constructor emb
  field
    getProp : p

open Emb

_~e_ : a -> a -> Set
x ~e y = Emb (x ~ y)

------------------

-- used for pattern matching
data _~e'_ (x : a) : a -> Set where
  refl : x ~e' x

match : {x y : a} -> x ~ y -> x ~e' y
match {x} e = subst (_~e'_ x) e refl

match' : {x y : a} -> x ~e y -> x ~e' y
match' (emb e) = match e

-----------------------

variable m : Set -> Set

record Monad (m : Set -> Set) : Set where
  field
    _>>=_ : m a -> (a -> m a') -> m a'
    pure  : a -> m a

open Monad {{...}}

_<$>_ : {{Monad m}} -> (a -> a') -> m a -> m a'
f <$> m = m >>= \x -> pure (f x)

_<&>_ : {{Monad m}} -> m a -> (a -> a') -> m a'
m <&> f = m >>= \x -> pure (f x)

_<*>_ : {{Monad m}} -> m (a -> a') -> m a -> m a'
f <*> m = f >>= \f -> m >>= \a -> pure (f a)

mapM : {{Monad m}} -> (a -> m a') -> list a -> m (list a')
mapM f [] = pure []
mapM f (x :: xs) = (| f x :: mapM f xs |)

mapMV : {{Monad m}} -> (a -> m a') -> vec a k -> m (vec a' k)
mapMV f [] = pure []
mapMV f (x :: xs) = (| f x :: mapMV f xs |)

_<>m_ : {{Monad m}} -> {{Semigroup a}} -> m a -> m a -> m a
x <>m y = (| x <> y |)

instance
  Monad[maybe] : Monad maybe
  Monad[maybe] .pure a = just a
  Monad[maybe] ._>>=_ (just x) f = f x
  Monad[maybe] ._>>=_ nothing  f = nothing

-----------------------

record MonadError (e : Set) (m : Set -> Set) : Set where
  field
    throwError   : e -> m a
    {{monad[m]}} : Monad m

open MonadError {{...}} hiding (monad[m])

instance
  MonadError[maybe] : MonadError a maybe
  MonadError[maybe] .throwError s = nothing

throwErrorM : {{MonadError a m}} -> m a -> m a'
throwErrorM s = do
  s <- s
  throwError s


-----------------------

postulate IO : Set -> Set
{-# BUILTIN IO IO #-}
{-# COMPILE GHC IO = type IO #-}

postulate bindIO : IO a -> (a -> IO a') -> IO a'
{-# COMPILE GHC bindIO = \_ _ m f -> m >>= f #-}

postulate pureIO : a -> IO a
{-# COMPILE GHC pureIO = \_ x -> pure x #-}

instance
  Monad[IO] : Monad IO
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


---------------------------------------

postulate future' : (a -> (a -> a'' -> a'') -> a') -> a'   ---  (A, A -> ())
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

future : (a -> ((a'' : Set) -> a -> a'' -> a'') -> a') -> a'
future f = future' {a'' = bool} \get set -> f get (\C a c -> coe believeMe~ (set a (coe believeMe~ c)))



-------------------------------------------------

data CharClass : Set where
  Alpha Graphic Punctuation OtherChar : CharClass

charClass : char -> CharClass
charClass '(' = Punctuation
charClass ')' = Punctuation
charClass '[' = Punctuation
charClass ']' = Punctuation
charClass '{' = Punctuation
charClass '}' = Punctuation
charClass ';' = Punctuation
charClass ',' = Punctuation
charClass '*' = Graphic
charClass '+' = Graphic
charClass '-' = Graphic
charClass '^' = Graphic
charClass '=' = Graphic
charClass '@' = Graphic
charClass '%' = Graphic
charClass '$' = Graphic
charClass '&' = Graphic
charClass '~' = Graphic
charClass '.' = Graphic
charClass '!' = Graphic
charClass '?' = Graphic
charClass ':' = Graphic
charClass '<' = Graphic
charClass '>' = Graphic
charClass '/' = Graphic
charClass '\\'= Graphic
charClass '|' = Graphic
charClass '#' = Graphic
charClass '_'  = Alpha
charClass '\'' = Alpha
charClass c = between 'a' 'z' c & \where
  true  -> Alpha
  false -> between 'A' 'Z' c & \where
    true  -> Alpha
    false -> between '0' '9' c & \where
      true  -> Alpha
      false -> OtherChar
 where
  between : char -> char -> char -> bool
  between a z c = charToNat a <= charToNat c & \where
    false -> false
    true  -> charToNat c <= charToNat z

joinChars : CharClass -> CharClass -> bool
joinChars Alpha   Alpha   = true
joinChars Graphic Graphic = true
joinChars _       _       = false

Token = string

tokens : {{MonadError stringBuilder m}} -> bool -> list char -> m (list Token)
tokens _ [] = pure []
tokens true ('\n' :: '#' :: s) = skip s \a s -> do
  ts <- tokens true s
  pure (";" :: "FFI" :: stringFromList a :: ts)
 where
  skip : list char -> (list char -> list char -> a) -> a
  skip ('\n' :: s) cont = cont [] ('\n' :: s)
  skip (c    :: s) cont = skip s \a s -> cont (c :: a) s
  skip []          cont = cont [] []
tokens true ('\n' :: c :: s) = charClass c & \where
  Alpha -> do
    ts <- tokens false (c :: s)
    pure (";" :: ts)
  _ -> tokens true (c :: s)
tokens b ('\n' :: s) = tokens b s
tokens b (' '  :: s) = tokens b s
tokens {m} b ('-' :: '-' :: s) = skip s where
  skip : list char -> m (list string)
  skip ('\n' :: s) = tokens b ('\n' :: s)
  skip (_    :: s) = skip s
  skip []          = pure []
tokens b (c :: s) = charClass c & \where
  OtherChar -> throwError ("invalid character: " <> fromString (stringFromList (c :: [])))
  cc        -> go cc s \r rs -> do
    ts <- tokens true rs
    pure (stringFromList (c :: r) :: ts)
 where
  go : CharClass -> list char -> (list char -> list char -> a) -> a
  go cc [] cont = cont [] []
  go cc (d :: cs) cont = joinChars cc (charClass d) & \where
    true  -> go cc cs \r rs -> cont (d :: r) rs
    false -> cont [] (d :: cs)

tokens' : {{MonadError stringBuilder m}} -> string -> m (list Token)
tokens' s = tokens false (stringToList s)

testTokens : tokens' "(a ++ bc)" ~ just ("(" :: "a" :: "++" :: "bc" :: ")" :: [])
testTokens = refl

showTokens : list Token -> stringBuilder
showTokens [] = ""
showTokens (t :: ts) = fromString t <> " " <> showTokens ts

----------------------------------

isAlphaToken : Token -> bool
isAlphaToken s = stringToList s & \where
  (c :: _) -> charClass c & \where
    Alpha -> true
    _     -> false
  _ -> false

operators : list (either string string)
operators =
  right ";"  :: left ";"  ::
  right "="  :: left "="  ::
  right "|"  :: left "|"  ::
  right "\\" ::
  right "."  :: left "."  ::
  right ":"  :: left ":"  ::
  right "::" :: left "::" ::
  right "$"  :: left "$"  ::
  right "=>" :: left "=>" ::
  right "@"  :: left "@"  ::
  right ","  :: left ","  ::
  right "->" :: left "->" ::
  right "==" :: left "==" ::
  right "+"  :: left "+"  ::
  right "*"  :: left "*"  ::
  left " "   :: right " " ::
  left "\\"  ::
  []

operators' : list string
operators' = ";" :: "=" :: "|" :: "." :: ":" :: "::" :: "$" :: "=>" :: "@" :: "," :: "->" :: "==" :: "+" :: "*" :: []

isOperator : string -> maybe (pair nat nat)
isOperator s = do
  l <- goLeft  0 operators s
  r <- goRight 0 operators s
  pure (l , r)
 where
  goLeft : nat -> list (either string string) -> string -> maybe nat
  goLeft n [] _ = nothing
  goLeft n (right s :: os) s' = goLeft (suc n) os s'
  goLeft n (left s :: os) s' = s' == s & \where
    true  -> just n
    false -> goLeft (suc n) os s'

  goRight : nat -> list (either string string) -> string -> maybe nat
  goRight n [] _ = nothing
  goRight n (left s :: os) s' = goRight (suc n) os s'
  goRight n (right s :: os) s' = s' == s & \where
    true  -> just n
    false -> goRight (suc n) os s'

isKeyword : (s : string) -> maybe nat
isKeyword "Bracket" = just 1
isKeyword "Brace"   = just 1
isKeyword "Paren"   = just 1
isKeyword "pattern" = just 1
isKeyword "FFI"     = just 1
isKeyword "U"       = just 0
isKeyword "?"       = just 0
isKeyword "Pi"      = just 2
isKeyword "Sigma"   = just 2
isKeyword "CSigma"  = just 2
isKeyword "Left"    = just 1
isKeyword "Right"   = just 1
--isKeyword "Bool"    = just 0
--isKeyword "False"   = just 0
--isKeyword "True"    = just 0
isKeyword "Fam"     = just 1
isKeyword "proj"    = just 1
isKeyword "fst"     = just 1
isKeyword "snd"     = just 1
isKeyword "coFst"     = just 1
isKeyword "coSnd"     = just 1
isKeyword "either"  = just 3
isKeyword "Top"     = just 0
isKeyword "TT"      = just 0
isKeyword "Bot"     = just 0
isKeyword "absurd"  = just 1
isKeyword "Refl"    = just 0
isKeyword "jRule"   = just 3
isKeyword "kRule"   = just 3
isKeyword "record"  = just 2
isKeyword "Wrap"    = just 1
isKeyword "fail"    = just 0
isKeyword "matchFalse" = just 2
isKeyword "matchTrue"  = just 2
isKeyword "matchLeft"  = just 2
isKeyword "matchRight" = just 2
isKeyword _         = nothing

isVariable : string -> bool
isVariable s = isAlphaToken s & \where
  false -> false
  true  -> isKeyword s & \where
    nothing -> true
    _       -> false

isVariableTrue : {s : _} -> (isAlphaToken s ~ true) -> (isKeyword s ~ nothing) -> isVariable s ~ true
isVariableTrue _ _ = believeMe~

------------------------------------

infixl 9 _$d_
infixr 8 _[_]_   -- operator syntax for Doc
infixr 8 _[_]m_  -- operator syntax for Doc

data Doc : Set where
  FFI   : string ->                                                                     Doc
  KW    : (s : string) {n : nat} -> {{e : isKeyword s ~ just n}} -> vec Doc n ->        Doc
  Var   : (s : string) -> {{isVariable s ~ true}} ->                                    Doc
  _[_]_ : Doc -> (s : string) {n : pair nat nat} -> {{isOperator s ~ just n}} -> Doc -> Doc

pattern _$d_ d d' = d [ " " ] d'

-------------------------------------

showDoc : Doc -> stringBuilder
showDoc = go 0 0  where

  parens : bool -> stringBuilder -> stringBuilder
  parens true  a = "(" <> a <> ")"
  parens false a =        a

  renderOp : string -> stringBuilder
  renderOp " " = " "
  renderOp s   = " " <> fromString s <> " "

  precOk : nat -> nat -> nat -> nat -> bool
  precOk p q q' p' = _<_ p q & \where
    true  -> _<_ p' q'
    false -> false

  go : nat -> nat -> Doc -> stringBuilder
  go p p' (FFI s)     = fromString s
  go p p' (KW n args) = go p p' (foldl _$d_ (FFI n) (vecToList args))
  go p p' (Var n)     = fromString n
  go p p' (_[_]_ a s {n = (q , q')} b) = precOk p q q' p' & \where
    true  ->              go p q a <> renderOp s <> go q' p' b
    false -> parens true (go 0 q a <> renderOp s <> go q' 0  b)

showDoc' : Doc -> string
showDoc' d = runStringBuilder (showDoc d)

testShowDoc : showDoc' ((Var "a" [ "." ] Var "a" $d Var "b") $d (Var "c" $d Var "e") $d Var "d" $d (Var "a" [ "." ] Var "b" [ "." ] Var "a"))
        ~ "(a . a b) (c e) d (a . b . a)"
testShowDoc = refl

testShowDoc' : showDoc' ((Var "a" [ "*" ] Var "a" $d Var "b" [ "*" ] Var "b") $d Var "d" [ "*" ] Var "f" $d (Var "c" [ "*" ] Var "e"))
        ~ "(a * a b * b) d * f (c * e)"
testShowDoc' = refl

testShowDoc'' : showDoc' (KW "Pi" (Var "A" :: Var "B" :: []))
        ~ "Pi A B"
testShowDoc'' = refl

---------------------

_[_]m_ : {{Monad m}} -> m Doc -> (s : string) {n : pair nat nat} -> {{isOperator s ~ just n}} -> m Doc -> m Doc
_[_]m_ a s b = do
  a <- a
  b <- b
  pure (a [ s ] b)

infixl 9 _$m_

_$m_ : {{Monad m}} -> m Doc -> m Doc -> m Doc
a $m b = (| a $d b |)

KWm : {{Monad m}} -> (s : string) {n : nat} -> {{e : isKeyword s ~ just n}} -> vec (m Doc) n -> m Doc
KWm s ds = do
  ds <- mapMV (\x -> x) ds
  pure (KW s ds)

----------

pattern Paren a = KW "Paren" (a :: [])


parse : {{MonadError stringBuilder m}} -> string -> m Doc
parse {m} s = tokens' s >>= parseOps end  where

  X = list string -> m Doc

  end : Doc -> X
  end d [] = pure d
  end d ts  = throwError ("End expected instead of  " <> showTokens ts)

  expect : string -> X -> X
  expect t r (t' :: ts) = t' == t & \where
    true  -> r ts
    false -> throwError (fromString t <> " expected instead of " <> showTokens (t' :: ts))
  expect t _ [] = throwError (fromString t <> " expected instead of end")

  parseOps : (Doc -> X) -> X

  parseAtom : ((n : nat) -> (vec Doc n -> Doc) -> X) -> X -> X
  parseAtom r _ ("(" :: ts) = parseOps (\b -> expect ")" (r 0 \_ -> KW "Paren"   (b :: []))) ts
  parseAtom r _ ("[" :: ts) = parseOps (\b -> expect "]" (r 0 \_ -> KW "Bracket" (b :: []))) ts
  parseAtom r _ ("{" :: ts) = parseOps (\b -> expect "}" (r 0 \_ -> KW "Brace"   (b :: []))) ts
  parseAtom r z ("FFI" :: t :: ts) = r 0 (\_ -> FFI t) ts
  parseAtom r z (t :: ts) = isKeyword t &in \where
    (just n) e -> r n (KW t {{e}}) ts
    nothing  e -> isAlphaToken t &in \where
      true e' -> r 0 (\_ -> Var t {{isVariableTrue e' e}}) ts
      false _ -> z (t :: ts)
  parseAtom _ z ts = z ts

  parseAtom0 : (Doc -> X) -> X -> X
  parseAtom0 r z = parseAtom f z  where
    f : (n : nat) -> (vec Doc n -> Doc) -> X
    f 0 d = r (d [])
    f _ _ = z

  parseApps : (Doc -> X) -> X
  parseApps r = parseAtom (f r) \ts -> throwError ("unknown token at  " <> showTokens ts)  where

    f : (Doc -> X) -> (n : nat) -> (vec Doc n -> Doc) -> X
    f r 0       a ts = parseAtom0 (\b -> f r 0 \ds -> a [] $d b) (r (a [])) ts
    f r (suc n) a ts = parseAtom0 (\b -> f r n \ds -> a (b :: ds)) (\ts -> throwError ("argument expected at " <> showTokens ts)) ts

  mkPi : Doc -> Doc -> Doc -> Doc
  mkPi (ns [ " " ] n) a b = mkPi ns a (KW "Pi" (a :: (_[_]_ n "." {{refl}} b) :: []))
  mkPi n a b = KW "Pi" (a :: (n [ "." ] b) :: [])

  mkSigma : Doc -> Doc -> Doc -> Doc
  mkSigma (ns $d n) a b = mkSigma ns a (KW "Sigma" (a :: (_[_]_ n "." {{refl}} b) :: []))
  mkSigma n a b = KW "Sigma" (a :: (n [ "." ] b) :: [])

  mkOp : (s : string) {n : pair nat nat} -> {{isOperator s ~ just n}} -> Doc -> Doc -> m Doc
  mkOp "$" a b = pure (a $d b)
  mkOp "->" (bs $d Paren (n [ ":" ] a)) b = mkOp "->" {{refl}} bs (mkPi n a b)
  mkOp "->" (Paren (n [ ":" ] a)) b = pure (mkPi n a b)
  mkOp "*" (bs $d Paren (n [ ":" ] a)) b = mkOp "*" {{refl}} bs (mkSigma n a b)
  mkOp "*" (Paren (n [ ":" ] a)) b = pure (mkSigma n a b)
  mkOp "." (ns $d n) b = mkOp "." {{refl}} ns (_[_]_ n "." {{refl}} b)
  mkOp "." n b = pure (n [ "." ] b)
  mkOp t a b = pure (a [ t ] b)

  addOp : string -> ((Doc -> X) -> X) -> (Doc -> X) -> X
  addOp op g r = isOperator op &in \where
    nothing _ -> g r
    (just _) e -> g (f e r)
   where

    f : {p : _} -> (isOperator op ~ just p) -> (Doc -> X) -> Doc -> X
    f e r a (t' :: ts) = t' == op & \where
      true  -> addOp op g (\b ts -> mkOp op {{e}} a b >>= \o -> r o ts) ts
      false -> r a (t' :: ts)
    f e r a ts = r a ts

  parseOps = foldr addOp parseApps operators'


testParse : parse "f (b a * c * e) d"
          ~ just (Var "f" $d KW "Paren" ((Var "b" $d Var "a" [ "*" ] Var "c" [ "*" ] Var "e") :: []) $d Var "d")
testParse = refl





-------------------------------------------------------

infixl 9 _$_     -- application
infixr 3 _=>_


----------------------

record Name : Set where
  constructor MkName
  field
    nameStr : string  -- for pretty printing
    nameId  : nat     -- globally unique id

open Name

decName : (n n' : Name) -> maybe (n ~e n')
decName n n' = nameId n == nameId n' & \where
  true  -> just (emb believeMe~)
  false -> nothing

variable n n' : Name

record MonadSupply (m : Set -> Set) : Set where
  field
    newName   : string -> m Name
    {{monad[m]}} : Monad m

open MonadSupply {{...}} hiding (monad[m])


------------------------------------------------------

data Con : Set

variable G : Con

data Ty : Con -> Set

variable A A' A'' : Ty G

record TVar (A : Ty G) : Set
record TVar {G} A where
  coinductive
  field
    varName : Name
    -- add a proof that the name is not in the context

open TVar

variable v : TVar _

data Con where
  []   : Con
  _>>_ : (G : Con) -> {A : Ty G} -> TVar A -> Con

infixl 3 _>>_

data TmR : Ty G -> Set    -- RHS

data Ty where
  U  :              Ty G
  El : TmR {G} U -> Ty G



Tm : Ty G -> Set
Tm {G} U  = Ty   G               -- "Bálint Török" style equality
Tm (El A) = TmR (El A)

rToTm : TmR A -> Tm A
rToTm {A = U   } x = El x
rToTm {A = El _} x =    x


liftTy  : Ty [] -> Ty G
liftTmR : TmR A -> TmR {G} (liftTy A)

liftTy U      = U
liftTy (El A) = El (liftTmR A)

lift : Tm A -> Tm {G} (liftTy A)
lift {A = U   } A = liftTy A
lift {A = El _} x = liftTmR x

lift1Ty  : Ty G -> Ty (G >> v)
lift1TmR : TmR A -> TmR {G >> v} (lift1Ty A)

lift1Ty U      = U
lift1Ty (El A) = El (lift1TmR A)

lift1 : Tm A -> Tm {G >> v} (lift1Ty A)
lift1 {A = U   } A = lift1Ty A
lift1 {A = El _} x = lift1TmR x

{-
{-# FOREIGN GHC data IName = IName #-}
{-# COMPILE GHC Name = data IName (IName) #-}

{-# FOREIGN GHC data ITy = ITy1 | ITy2 #-}
{-# COMPILE GHC Ty = data ITy (ITy1 | ITy2) #-}

{-# FOREIGN GHC data ICon = ICon1 | ICon2 #-}
{-# COMPILE GHC Con = data ICon (ICon1 | ICon2) #-}

-- TODO {-# COMPILE GHC liftTy = \_ -> coe #-}
-- TODO {-# COMPILE GHC liftTmR = \_ -> coe #-}
-- TODO {-# COMPILE GHC lift = \_ -> coe #-}
-- TODO {-# COMPILE GHC lift1Ty = \_ -> coe #-}
-- TODO {-# COMPILE GHC lift1TmR = \_ -> coe #-}
-- TODO {-# COMPILE GHC lift1 = \_ -> coe #-}
-}




_=>_  : Ty G -> Ty G -> Tm {G} U

_$u_ : Tm (A => A') -> Tm A -> Tm {G} A'


record RecordDesc : Set
record RecordDesc where
  coinductive
  field
    recordName   : Name
    recordParams : Ty []
    recordFields : Tm (recordParams => U)

open RecordDesc

rParams : RecordDesc -> Ty G
rParams rd = lift (recordParams rd)

variable rd : RecordDesc

Top    :                                             Tm {G} U
Either : Ty G -> Ty G ->                             Tm {G} U
Id     : {A : Ty G} -> Tm A -> Tm A ->               Tm {G} U
Pi     : (A : Ty G) -> Tm (A => U) ->                Tm {G} U
ISigma : (A : Ty G) -> Tm (A => U) ->                Tm {G} U
CSigma : (A : Ty G) -> Tm (A => U) ->                Tm {G} U
Record : (rd : RecordDesc) -> Tm {G} (rParams rd) -> Tm {G} U

variable B : Tm (A => U)

data TmN : Ty G -> Set

data TmR where
  -- inductive type constructors
  Top#    :                                             TmR {G} U
  Either# : Ty G -> Ty G ->                             TmR {G} U
  Id#     : {A : Ty G} -> Tm A -> Tm A ->               TmR {G} U
  -- coinductive type constructors
  _=>#_   : Ty G -> Ty G ->                             TmR {G} U
  Pi#     : (A : Ty G) -> Tm (A => U) ->                TmR {G} U
  ISigma# : (A : Ty G) -> Tm (A => U) ->                TmR {G} U
  CSigma# : (A : Ty G) -> Tm (A => U) ->                TmR {G} U
  Record# : (rd : RecordDesc) -> Tm {G} (rParams rd) -> TmR {G} U
  -- inductive constructors
  TT      :                                             TmR {G} Top
  Left    : Tm A  ->                                    TmR {G} (Either A A')
  Right   : Tm A' ->                                    TmR {G} (Either A A')
  _,_     : (x : Tm A) -> Tm (B $u x) ->                TmR {G} (ISigma A B)
  Refl    : {x : Tm {G} A} ->                           TmR {G} (Id x x)
  --
  Neut    :                                    TmN A -> TmR {G} A


Top          = El Top#
Either A A'  = El (Either# A A')
Id x y       = El (Id# x y)
A => A'      = El (A =># A')
Pi    A B    = El (Pi# A B)
ISigma A B   = El (ISigma# A B)
CSigma A B   = El (CSigma# A B)
Record rd ps = El (Record# rd ps)


data TmNR  : Ty G -> Set    -- second-order LHS continuation  glued with spine

record TopDef : Set
record TopDef where
  coinductive
  field
    topDefName : Name
    topDefTy   : Ty []
    topDefBody : TmNR topDefTy

open TopDef

variable td : TopDef

topTy   : TopDef -> Ty G
topTy td = lift (topDefTy td)


cFst : Tm (CSigma A B) -> Tm {G} A

rFields : (rd : RecordDesc) -> Tm {G} (rParams rd) -> Ty G

data TmS   : Ty G -> Set    -- Spine

sToTm  : TmS A -> Tm {G} A

data TmS where
  -- coinductive eliminators
  AppU    : Tm (A => A') -> Tm A ->                        TmS {G} A'
  App     : Tm (Pi A B) -> (x : Tm A) ->                   TmS {G} (B $u x)
  Fst     :      Tm (CSigma A B) ->                        TmS {G} A
  Snd     : (x : Tm (CSigma A B)) ->                       TmS {G} (B $u cFst x)
  Proj    : {ps : Tm (rParams rd)} -> Tm (Record rd ps) -> TmS {G} (rFields rd ps)
  -- conversions between forms
  Def     :                               (td : TopDef) -> TmS {G} (topTy td)
  SVar    :                               Name          -> TmS {G} A    -- add a proof that the name is in the context
  --
  IFst    :      TmN (ISigma A B)  -> TmS {G}  A
  ISnd    : (x : TmN (ISigma A B)) -> TmS {G} (B $u sToTm (IFst x))


_$_  : Tm (Pi A B) -> (x : Tm A) -> Tm {G} (B $u x)
iFst : Tm (ISigma A B) -> Tm {G} A
iSnd : (x : Tm (ISigma A B)) -> Tm (B $u iFst x)

data TmL   : Ty G -> Set    -- second-order LHS

Glued : TmS A -> TmL A -> Prop


data TmN where
  Glue  : (s : TmS A) (x : TmL A) -> Glued s x -> TmN A

pattern GlueTm s l e = Neut (Glue s l e)


iFst (x , y) = x
iFst (Neut n) = sToTm (IFst n)

iSnd (x , y) = y
iSnd (Neut n) = sToTm (ISnd n)

data TmLR  : Ty G -> Set    -- second-order LHS continuation
data TmLR where
  LHS     :   TmL  A -> TmLR A
  RHS     :   Tm   A -> TmLR A                    -- Ret

data TmNR where
  RHS'    :   Tm A ->          TmNR A                    -- Ret
  GlueLHS :   Tm A -> TmL A -> TmNR A

nrToTm : TmNR A -> Tm A

data TmSL  : Ty G -> Set    -- Strict second-order LHS
data TmSL where
  -- coinductive constructors (second order) 
  LamU    : (     Tm A  -> TmNR A'   ) ->                      TmSL {G} (A => A')
  Lam     : ((x : Tm A) -> TmNR (B $u x)) ->                   TmSL {G} (Pi    A B)
  _,_     : (x : TmNR A) -> TmNR (B $u nrToTm x) ->            TmSL {G} (CSigma A B)
  Wrap    : {ps : Tm (rParams rd)}  -> TmNR (rFields rd ps) -> TmSL {G} (Record rd ps)

data TmL where
  -- inductive eliminators (second order)
  Stuck   :                     TmL A
  -- pattern matching constructors (second order)
  Fail    :                     TmL A
  Or      : TmSL A -> TmLR A -> TmL A
  Strict  :           TmSL A -> TmL A

-----------



liftTmNR : TmNR {[]} A -> TmNR {G} (lift A)

topBody : (td : TopDef) -> TmNR {G} (topTy td)
topBody td = liftTmNR (topDefBody td)

postulate lift[] : {A : Ty []} -> lift A ~ A

VZ : {v : TVar A} -> Tm {G >> v} (lift1 A)
VZ {v} = sToTm (SVar (varName v))

nrToTm (RHS' x)      = x
nrToTm (GlueLHS s l) = s

sToLR : TmS A -> TmLR A

Glued s x = sToLR s ~ LHS x

glue : (s : TmS A) (lr : TmLR A) -> sToLR s ~ lr -> Tm A
glue s (RHS r) e = r
glue s (LHS l) e = rToTm (GlueTm s l e)

sToTm s = glue s (sToLR s) refl

infixl 9 _$u_
infixr 2 _||_

f $u x = sToTm (AppU f x)

f $ x = sToTm (App f x)

liftTmS : TmS {[]} A -> TmS {G} (lift A)

liftTmR Top# = Top#
liftTmR (Either# A A') = Either# (lift A) (lift A') 
liftTmR (Id# x y) = Id# (lift x) (lift y)
liftTmR (A =># A') = lift A =># lift A'
liftTmR (Pi# A B) = Pi# (lift A) (lift B) 
liftTmR (ISigma# A B) = ISigma# (lift A) (lift B)
liftTmR (CSigma# A B) = CSigma# (lift A) (lift B)
liftTmR (Record# rd x) = Record# rd (lift (subst Tm lift[] x))
liftTmR TT = TT
liftTmR (Left  x) = Left  (lift x)
liftTmR (Right x) = Right (lift x)
liftTmR Refl = Refl
liftTmR (x , y) = lift x , coe believeMe~ y  -- TODO
liftTmR (GlueTm s l e) = GlueTm (liftTmS s) (coe believeMe~ l) believeMe~

liftTmS (Fst x) = Fst (lift x)
liftTmS (AppU f x) = AppU (lift f) (lift x)
liftTmS x = coe believeMe~ x   -- TODO

liftTmNR (RHS' x) = RHS' (lift x)
liftTmNR (GlueLHS x l) = GlueLHS (lift x) (coe believeMe~ l)

lift1TmS : TmS {G} A -> TmS {G >> v} (lift1 A)

lift1TmR Top# = Top#
lift1TmR (Either# A A') = Either# (lift1 A) (lift1 A') 
lift1TmR (Id# x y) = Id# (lift1 x) (lift1 y)
lift1TmR (A =># A') = lift1 A =># lift1 A'
lift1TmR (Pi# A B) = Pi# (lift1 A) (lift1 B) 
lift1TmR (ISigma# A B) = ISigma# (lift1 A) (lift1 B)
lift1TmR (CSigma# A B) = CSigma# (lift1 A) (lift1 B)
lift1TmR (Record# rd x) = Record# rd (coe believeMe~ x) --TODO
lift1TmR TT = TT
lift1TmR (Left  x) = Left  (lift1 x)
lift1TmR (Right x) = Right (lift1 x)
lift1TmR Refl = Refl
lift1TmR (x , y) = lift1 x , coe believeMe~ y  -- TODO
lift1TmR (GlueTm s l e) = GlueTm (lift1TmS s) (coe believeMe~ l) believeMe~

lift1TmS (Fst x) = Fst (lift1 x)
lift1TmS (AppU f x) = AppU (lift1 f) (lift1 x)
lift1TmS x = coe believeMe~ x   -- TODO


rFields rd x = liftTmR (recordFields rd) $u x


cFst x = sToTm (Fst x)

cSnd : (x : Tm (CSigma A B)) -> Tm (B $u cFst x)
cSnd x = sToTm (Snd x)

proj : {ps : Tm (rParams rd)} -> Tm (Record rd ps) -> Tm {G} (rFields rd ps)
proj x = sToTm (Proj x)

nrToLR : TmNR A -> TmLR A
nrToLR (GlueLHS _ l) = LHS l
nrToLR (RHS' x)      = RHS x

_||_ : TmLR A -> TmLR A -> TmLR A
RHS x          || _ = RHS x
LHS Fail       || x = x
LHS (Strict l) || x = LHS (Or l x)
LHS (Or a b)   || x = LHS (Or a (b || x))
LHS Stuck      || _ = LHS Stuck
{-
_||n_ : TmNR A -> TmNR A -> TmNR A
RHS' x          ||n _ = RHS' x
GlueLHS _ Fail  ||n x = x
x@(GlueLHS _ Stuck) ||n _ = x
GlueLHS e (Strict l) ||n x = GlueLHS e (Or l ?)
-}
mapLR : (TmSL A -> TmNR A') -> (Tm A -> Tm A') -> TmL A -> TmLR A'
mapLR f g Fail            = LHS Fail
mapLR f g (Strict x)      = nrToLR (f x)
mapLR f g (Or x (RHS x')) = nrToLR (f x) || RHS (g x')
mapLR f g (Or x (LHS x')) = nrToLR (f x) || mapLR f g x'
mapLR f g Stuck           = LHS Stuck

postulate believeMeTm : Tm A ~ Tm A'

mapLR-CSigma : (p : Tm (CSigma A B)) -> TmLR (B $u cFst p)
mapLR-CSigma (GlueTm _ (Strict (x , y))      _) = nrToLR (coe believeMe~ y)  
mapLR-CSigma (GlueTm s (Or (x , y) (LHS x')) _) = nrToLR (coe believeMe~ y) || coe believeMe~ (mapLR-CSigma (GlueTm s x' believeMe))
mapLR-CSigma (GlueTm _ (Or (x , y) (RHS x')) _) = nrToLR (coe believeMe~ y) || RHS (coe believeMeTm (cSnd x'))
mapLR-CSigma (GlueTm _ Fail                  _) = LHS Fail
mapLR-CSigma (GlueTm _ Stuck                 _) = LHS Stuck
{-
mapLR-CSigma' : (p : Tm (CSigma A B)) -> TmNR (B $u cFst p)
mapLR-CSigma' x@(GlueTm s Fail e) = GlueLHS (rToTm (GlueTm (Snd x) Fail believeMe~)) Fail
mapLR-CSigma' x@(GlueTm s Stuck e) = GlueLHS (rToTm (GlueTm (Snd x) Stuck believeMe~)) Stuck
-}


sToLR (AppU (GlueTm _ f _) x) = mapLR (\{(LamU f) -> f x}) (\f -> f $u x) f
sToLR (App  (GlueTm _ f _) x) = mapLR (\{(Lam  f) -> f x}) (\f -> f $  x) f
sToLR (Fst  (GlueTm _ x _)  ) = mapLR (\{(x , _)  -> x  })  cFst          x
sToLR (Proj (GlueTm _ x _)  ) = mapLR (\{(Wrap x) -> x  })  proj          x
sToLR (Snd  x               ) = mapLR-CSigma x
sToLR (Def  td              ) = nrToLR (topBody td)
sToLR (SVar _               ) = LHS Stuck
sToLR (IFst n) = LHS Stuck
sToLR (ISnd n) = LHS Stuck

{-
def : (td : TopDef) -> Tm (topDefTy td)
def td = coe believeMe~ (sToTm (Def td))
-}
infixr 2 _||'_

jRule : {x y : Tm {G} A}
  (tm : Tm (Id x y)) ->
  (P : (y : Tm A) -> Tm (Id x y) -> Ty G) ->
  TmLR (P x Refl) -> TmLR (P y tm)
jRule Refl     P l = l
jRule (GlueTm _ _ _) P l = LHS Stuck

kRule : {x : Tm {G} A}
  (tm : Tm (Id x x)) ->
  (P : Tm (Id x x) -> Ty G) ->
  TmLR (P Refl) -> TmLR (P tm)
kRule Refl     P l = l
kRule (GlueTm _ _ _) P l = LHS Stuck

------------

record TName (A : Ty []) : Set where
  constructor MkTName
  field
    tName : Name

open TName

decTName : (n : TName A) (m : TName A') -> maybe (_~e_ {Ty [] ** TName} (_ , n) (_ , m))
decTName n m = decName (tName n) (tName m) & \where
  (just _) -> just (emb believeMe~)
  nothing  -> nothing

lName : nat -> TName A
lName i = MkTName (MkName "lam" i)

matchLeft : (x : Tm {G} (Either A A')) -> ((y : Tm A) -> Tm (Id (Left y) x) -> TmLR A'') -> TmLR {G} A''
matchLeft (Left  y)      f = f y Refl
matchLeft (Right _)      f = LHS Fail
matchLeft (GlueTm _ _ _) f = LHS Stuck

matchRight : (x : Tm {G} (Either A A')) -> ((y : Tm A') -> Tm (Id (Right y) x) -> TmLR A'') -> TmLR {G} A''
matchRight (Right y)      f = f y Refl
matchRight (Left  _)      f = LHS Fail
matchRight (GlueTm _ _ _) f = LHS Stuck


fail : TmLR A
fail = LHS Fail

lamU : (Tm A -> TmNR A') -> TmLR {G} (A => A')
lamU f = LHS (Strict (LamU f))

lam : ((x : Tm A) -> TmNR (B $u x)) -> TmLR (Pi A B)
lam f = LHS (Strict (Lam f))

pairL : (x : TmNR A) -> TmNR (B $u nrToTm x) -> TmLR (CSigma A B)
pairL x y = LHS (Strict (x , y))

wrap : {ps : Tm (rParams rd)} -> TmNR (rFields rd ps) -> TmLR {G} (Record rd ps)
wrap y = LHS (Strict (Wrap y))

----------------------------------

data Tys : Set    -- second-order context
Tms : Tys -> Set  -- Env

data Tys where
  []   :                                    Tys
  _>>_ : (ts : Tys) -> (Tms ts -> Ty []) -> Tys

Tms []        = top
Tms (ts >> t) = Tms ts ** \xs -> Tm (t xs)

variable ts : Tys

---------------

-- type depending on context (second order representation)
CTy : Tys -> Set
CTy ts = Tms ts -> Ty []

-- term depending on context
CTm : {ts : Tys} -> CTy ts -> Set
CTm {ts} t = (xs : Tms ts) -> Tm (t xs)

---------------------------------- first-order terms

-- first-order to second-order function
⟦_⟧c : Con -> Tys
⟦_⟧u : Ty G -> CTy ⟦ G ⟧c
⟦_⟧  : {A : Ty G} -> Tm  A -> CTm ⟦ A ⟧u
⟦_⟧s : {A : Ty G} -> TmS A -> CTm ⟦ A ⟧u

⟦ U                  ⟧u = \xs -> U
⟦ El Top#            ⟧u = \xs -> Top
--⟦ El Bool#           ⟧u = \xs -> Bool
⟦ El (Either# A A')  ⟧u = \xs -> Either (⟦ A ⟧u xs) (⟦ A' ⟧ xs)
⟦ El (Id# x y)       ⟧u = \xs -> Id (⟦ x ⟧ xs) (⟦ y ⟧ xs)
⟦ El (A =># A')      ⟧u = \xs -> ⟦ A ⟧u xs => ⟦ A' ⟧u xs
⟦ El (Pi#    A B)    ⟧u = \xs -> Pi    (⟦ A ⟧u xs) (⟦ B ⟧ xs)
⟦ El (ISigma# A B)   ⟧u = \xs -> ISigma (⟦ A ⟧u xs) (⟦ B ⟧ xs)
⟦ El (CSigma# A B)   ⟧u = \xs -> CSigma (⟦ A ⟧u xs) (⟦ B ⟧ xs)
⟦ El (Record# rd ps) ⟧u = \xs -> Record rd (coe believeMe~ (⟦ ps ⟧ xs))
⟦ El (GlueTm s _ _)  ⟧u = ⟦ s ⟧s

⟦_⟧ {A = U   } A     = ⟦ A ⟧u
⟦_⟧ {A = El _} TT    = \xs -> TT
--⟦_⟧ {A = El _} True  = \xs -> True
--⟦_⟧ {A = El _} False = \xs -> False
⟦_⟧ {A = El _} (Left x) = \xs -> Left (⟦ x ⟧ xs)
⟦_⟧ {A = El _} (Right x) = \xs -> Right (⟦ x ⟧ xs)
⟦_⟧ {A = El _} (x , y) = \xs -> ⟦ x ⟧ xs , coe believeMe~ (⟦ y ⟧ xs)
⟦_⟧ {A = El _} Refl  = \xs -> Refl
⟦_⟧ {A = El _} (GlueTm s _ _) = ⟦ s ⟧s

⟦ []           ⟧c = []
⟦ _>>_ c {A} _ ⟧c = ⟦ c ⟧c >> ⟦ A ⟧

postulate impossible : a

index : {A : Ty G} -> Name -> CTm ⟦ A ⟧
index {G = []} n = \_ -> impossible
index {G = G >> v} {A} n = decName n (varName v) & \where
  nothing  -> \(xs , x) -> coe believeMe~ (index {G = G} {A = coe believeMe~ A} n xs)
  (just e) -> \(xs , x) -> coe believeMe~ x

⟦ AppU f x   ⟧s = \xs -> ⟦ f ⟧ xs $u ⟦ x ⟧ xs
⟦ App  f x   ⟧s = \xs -> coe believeMe~ (⟦ f ⟧ xs $ ⟦ x ⟧ xs)
⟦ Fst  x     ⟧s = \xs -> cFst (⟦ x ⟧ xs)
⟦ Snd  x     ⟧s = \xs -> coe believeMe~ (cSnd (⟦ x ⟧ xs))
⟦ Proj x     ⟧s = \xs -> coe believeMe~ (proj (⟦ x ⟧ xs))
⟦ Def {G} td ⟧s = \xs -> coe believeMe~ (sToTm {G = G} (Def td))
⟦ IFst (Glue s _ _) ⟧s = \xs -> iFst (⟦ s ⟧s xs)
⟦ ISnd (Glue s _ _) ⟧s = \xs -> coe believeMe~ (iSnd (⟦ s ⟧s xs))
⟦_⟧s {A} (SVar v) = index {A = A} v

---------------------------------

infix 0 _#_

_#_ : Tm A -> TmLR A -> TmNR A
n # LHS l = GlueLHS n l
_ # RHS r = RHS' r

TmTr : Ty G -> Set
TmTr A = Tm A -> TmNR A

def' : TName A -> TmTr A -> Tm {[]} A
def' {A} n lr = x where

  x : Tm {[]} A

  d : TopDef
  topDefName d = tName n
  topDefTy   d = A
  topDefBody d = lr x

  x = subst Tm lift[] (sToTm (Def {G = []} d))


lam' : ((x : Tm A) -> TmTr (B $u x)) -> TmTr (Pi A B)
lam' f n = n # lam \x -> f x (n $ x)

lamU' : (Tm A -> TmTr A') -> TmTr {G} (A => A')
lamU' f n = n # lamU \x -> f x (n $u x)

wrap' : {ps : Tm (rParams rd)} -> TmTr (rFields rd ps) -> TmTr {G} (Record rd ps)
wrap' f r = r # wrap (f (proj r))

fail' : TmTr A
fail' n = n # fail

_||'_ : TmTr A -> TmTr A -> TmTr A
(f ||' g) n = n # (nrToLR (f n) || nrToLR (g n))

pairL' : (n : Tm (CSigma A B)) -> (x : TmTr A) -> TmTr (B $u nrToTm (x (cFst n))) -> TmNR (CSigma A B)
pairL' n x y = n # pairL (x (cFst n)) (y (coe believeMeTm (cSnd n)))

matchLeft' : (x : Tm {G} (Either A A')) -> ((y : Tm A) -> Tm (Id (Left y) x) -> TmTr A'') -> TmTr {G} A''
matchLeft' x f n = n # matchLeft x \y e -> nrToLR (f y e n)

matchRight' : (x : Tm {G} (Either A A')) -> ((y : Tm A') -> Tm (Id (Right y) x) -> TmTr A'') -> TmTr {G} A''
matchRight' x f n = n # matchRight x \y e -> nrToLR (f y e n)

jRule' : {x y : Tm {G} A}
  (tm : Tm (Id x y)) ->
  (P : (y : Tm A) -> Tm (Id x y) -> Ty G) ->
  TmTr (P x Refl) -> TmTr (P y tm)
jRule' tm P f n = n # jRule tm P (nrToLR (f (coe believeMeTm n)))

ret : Tm A -> TmTr A
ret x n = RHS' x
{-
def'' : nat -> string -> TmTr A -> Tm {[]} A
def'' n s t = def' (MkName s n) t

-- TODO: make a dedicated constructor
jPTy : Tm {G} A -> Ty G
jPTy {G} {A} x = coe believeMe~ (lift {G = G} jPTy' $ A) $u x  where

    aU : Tm (U => U)
    aU = def'' 100 "aU" (lamU' \A -> ret (A => U))

    constTy' : Tm (Pi U aU)
    constTy' = def'' 101 "constTy'" (lam' \A -> lamU' \_ -> ret (A => U))

    jPTy2T : Tm (U => U)
    jPTy2T = def'' 102 "jPTy2T" (lamU' \A -> ret (Pi A (constTy' $ A)))

    jPTy2 : Tm (Pi U jPTy2T)
    jPTy2 = def'' 103 "jPTy2" (lam' \A -> lam' \x -> lamU' \y -> ret (Id x y => U))

    jPTy' : Tm (Pi U aU)
    jPTy' = def'' 104 "jPTy'" (lam' \A -> lamU' \x -> ret (Pi A (jPTy2 $ A $ x)))
-}
-------------------------------------


{-
jRule'' : {x y : Tm {G} A}   -- TODO: G
  (tm : Tm (Id x y)) ->
  (P : Tm (jPTy x)) ->
  TmLR (P $ x $u Refl) -> TmLR (P $ y $u tm)
jRule'' Refl     P l = l
jRule'' (GlueTm _ _ _) P l = LHS Stuck
-}
{-
jRule'' : {x y : Tm {[]} A}   -- TODO: G
  (tm : Tm (Id x y)) ->
  (P : Tm (jPTy x)) ->
  TmTr (P $ x $u Refl) -> TmTr (P $ y $u tm)
jRule'' tm P f n = n # jRule tm P (nrToLR (f (coe believeMeTm n)))
-}

data TmFL  : Ty G -> Set    -- First-order  LHS

data TmFL' : Ty G -> Set    -- First-order  LHS  glued with spine
data TmFL' where
  GlueFLHS :  Tm A -> TmFL A -> TmFL' A

flToTm : TmFL' A -> Tm A

data TmFL where
  -- coinductive constructors (first order)
  FLamU   : {v : TVar A} -> TmFL  {G >> v} (lift1 A')        -> TmFL {G} (A => A')
  FLam    : {v : TVar A} -> TmFL' {G >> v} (lift1 B $u VZ) -> TmFL {G} (Pi A B)
  _,_     : (x : TmFL' A) -> TmFL' (B $u flToTm x) -> TmFL {G} (CSigma A B)
  FWrap   : {ps : Tm (rParams rd)} -> TmFL' (rFields rd ps) -> TmFL {G} (Record rd ps)
  -- inductive eliminators (first order)
  MatchLeft  : (x : Tm {G} (Either A A')) {v : TVar A } {v' : TVar {G >> v} (Id (Left  VZ) (lift1 x))} -> TmFL {G >> v >> v'} (lift1 (lift1 A'')) -> TmFL {G} A''
  MatchRight : (x : Tm {G} (Either A A')) {v : TVar A'} {v' : TVar {G >> v} (Id (Right VZ) (lift1 x))} -> TmFL {G >> v >> v'} (lift1 (lift1 A'')) -> TmFL {G} A''
--  MkJRule : {x y : Tm {G} A} (tm : Tm (Id x y)) (P : Tm (jPTy x)) ->  TmFL {G} (P $ x $u rToTm Refl) -> JRule' {G} (P $ y $u tm)
  -- pattern matching constructors (first order)
  FFail   : TmFL {G} A
  FOr     : TmFL A -> TmFL A -> TmFL {G} A
  -- _||_
  -- Fail
  FRHS    :  Tm A -> TmFL {G} A

--------------

CTmTr : {ts : Tys} -> CTy ts -> Set
CTmTr {ts} t = (xs : Tms ts) -> TmTr (t xs)

flToTm (GlueFLHS x _) = x


flToL' : TmFL' {G} A -> CTmTr ⟦ A ⟧

flToL : TmFL {G} A -> CTmTr ⟦ A ⟧
flToL (FLamU f) = \xs -> lamU' \x -> subst TmTr believeMe~ (flToL f (xs , x))
flToL (FLam  f) = \xs -> lam' \x -> subst TmTr believeMe~ (flToL' f (xs , x))
flToL (x , y)      = \xs n -> pairL' n (flToL' x xs) (coe believeMe~ (flToL' y xs))
flToL (FWrap x)    = \xs -> wrap' (coe believeMe~ (flToL' x xs))
flToL {A} (MatchLeft  x f) = \xs -> matchLeft'  (⟦ x ⟧ xs) \y r -> coe believeMe~ (flToL {A = lift1 (lift1 A)} f ((xs , y) , coe believeMe~ r))
flToL {A} (MatchRight x f) = \xs -> matchRight' (⟦ x ⟧ xs) \y r -> coe believeMe~ (flToL {A = lift1 (lift1 A)} f ((xs , y) , coe believeMe~ r))
flToL FFail        = \xs -> fail'
flToL (FOr l r)    = \xs -> flToL l xs ||' flToL r xs
flToL (FRHS x)     = \xs -> ret (⟦ x ⟧ xs)

flToL' (GlueFLHS _ x) = flToL x

flToLTop : TmFL' {[]} A -> TmTr A
flToLTop x = coe believeMe~ (flToL' x tt)


---------------------------

_:=_ : TName A -> TmFL' A -> Tm A
n := x = def' n (flToLTop x)

----------------------------------



NameMap : (Ty [] -> Set) -> Set

variable W : Ty [] -> Set

emptySM     : NameMap W
insertSM    : TName A -> W A -> NameMap W -> NameMap W
deleteSM    : TName A ->        NameMap W -> NameMap W
lookupSM    : TName A ->        NameMap W -> maybe (W A)
lookupSMStr : string ->        NameMap W -> maybe (Ty [] ** \A -> pair (TName A) (W A))

NameMap P = list (Ty [] ** \a -> pair (TName a) (P a))

emptySM = []

insertSM s a m = (_ , s , a) :: m

deleteSM s [] = []
deleteSM s ((_ , n , x) :: sm) = decTName n s & \where
  (just _) -> deleteSM s sm
  nothing  -> (_ , n , x) :: deleteSM s sm

lookupSM s [] = nothing
lookupSM s ((_ , n , x) :: sm) = decTName n s & \where
  (just e) -> match' e & \{refl -> just x}
  nothing  -> lookupSM s sm

lookupSMStr s [] = nothing
lookupSMStr s ((_ , n , x) :: sm) = s == nameStr (tName n) & \where
  true  -> just (_ , n , x)
  false -> lookupSMStr s sm

Ctx : Set
Ctx = NameMap Tm


---------------------


-- reflect Con as a Ty  (as an iterated Σ)
data ReflectCon : Con -> Ty [] -> Set

sigsToTms : ReflectCon G A -> Tm A -> Tms ⟦ G ⟧c

data ReflectCon where
  IS[] : ReflectCon [] Top
  IS>> : {v : TVar A'} -> (is : ReflectCon G A) {B : _} -> ({xs : _} -> B $u xs ~ ⟦ A' ⟧ (sigsToTms is xs)) -> ReflectCon (G >> v) (ISigma A B)

sigsToTms IS[]        = \xs -> tt
sigsToTms (IS>> is e) = \xs -> sigsToTms is (iFst xs) , subst Tm e (iSnd xs)

ECon : Con -> Set
ECon G = Ty [] ** \A -> pair (ReflectCon G A) (Tm {G} (lift A))

emptyECon : ECon []
emptyECon = Top , IS[] , TT

newTName : {{MonadSupply m}} -> string -> m (TName A)
newTName s = do
  n <- newName s
  pure (MkTName n)

mkLam : {{MonadSupply m}} -> (Tm A -> Tm A') -> m (Tm {[]} (A => A'))
mkLam f = do
  n <- newTName "lam"
  pure (def' n (lamU' \x -> ret (f x)))

addECon : {{MonadSupply m}} -> {v : TVar A} -> ECon G -> m (ECon (G >> v))
addECon {G} {A} {v} (aa , is , vars) = do
  l <- mkLam \xs -> ⟦ A ⟧u (sigsToTms is xs)
  pure (ISigma aa l , IS>> is believeMe~ , coe believeMe~ vars , coe believeMe~ (VZ {v = v}))

--------------

Fill : Ty [] -> Set
Fill A = (C : Set) -> Tm A -> C -> C

Fills = NameMap Fill


error : Set
error = stringBuilder


record TCState : Set where
  constructor MkTCState
  field
    counter   : nat
--    showEnv   : ShowEnv
--    atExpEnv  : AtExpEnv

open TCState

record TCEnv : Set where
  constructor MkTCEnv
  field
    globalEnv : Ctx
    fillEnv   : Fills

open TCEnv

-- type checking monad
record TC (a : Set) : Set where
  coinductive
  field
    getTC : TCEnv -> TCState -> pair TCState (either error a)

open TC


--------------------------


runTC : TC a -> either error a
runTC tc = pair.snd (getTC tc (MkTCEnv emptySM {- [] -} {- emptyECon -} emptySM) (MkTCState 1000 {- emptySM [] -}))

instance
  Monad[TC] : Monad TC 
  getTC (Monad[TC] .pure x) _ c = c , right x
  getTC (Monad[TC] ._>>=_ m f) ctx c = getTC m ctx c & \where
    (c , left  e) -> c , left e
    (c , right x) -> getTC (f x) ctx c

instance
  MonadError[TC] : MonadError stringBuilder TC
  getTC (MonadError[TC] .throwError e) _ c = c , left e

catchError : TC a -> (error -> TC a) -> TC a
getTC (catchError m f) ctx c = getTC m ctx c & \where
  (c , left  e) -> getTC (f e) ctx c
  (c , right x) -> c , right x

addGlobal : TName A -> Tm A -> TC a -> TC a
getTC (addGlobal s d m) (MkTCEnv g {- l l' -} f) = getTC m (MkTCEnv (insertSM s d g) {-l l' -} f)

record TyTm (G : Con) : Set where
  constructor tyTm
  field
    {typeOf} : Ty G
    termOf   : Tm typeOf

open TyTm

liftTyTm : TyTm [] -> TyTm G
liftTyTm (tyTm x) = tyTm (lift x)

lift1TyTm : TyTm G -> TyTm (G >> v)
lift1TyTm (tyTm x) = tyTm (lift1 x)

lookupCon : string -> maybe (TyTm G)
lookupCon {G = []} _ = nothing
lookupCon {G = G >> v} s = s == nameStr (varName v) & \where
  true -> just (tyTm (VZ {v = v}))
  false -> lift1TyTm <$> lookupCon s
  
lookupTm : string -> TC (TyTm G)
getTC (lookupTm s) env c = lookupCon s & \where
  (just d)  -> c , right d
  nothing -> {- lookupSMStr s (concat (atExpEnv c)) & \where
    (just (_ ,, n , x))  -> c , right (_ ,, x)
    nothing              -> -} lookupSMStr s (globalEnv env) & \where
      (just (A , n , x))  -> c , right (liftTyTm (tyTm x))
      nothing              -> c , left ("Not defined: " <> fromString s)

futureTC : TName A -> (Tm A -> TC a) -> TC a
futureTC n f = future \get set -> addFill n set (f get)  where

  addFill : TName A -> Fill A -> TC a -> TC a
  getTC (addFill s d m) (MkTCEnv g f) = getTC m (MkTCEnv g (insertSM s d f))

lookupFill : string -> ({A : Ty []} -> TName A -> Fill A -> TC a) -> TC a -> TC a
lookupFill n cont err = do
  just (_ , n , f) <- lookupFill' n  where  nothing -> err
  delFill n (cont n f)
 where
  delFill : TName A -> TC a -> TC a
  getTC (delFill s m) (MkTCEnv g f) = getTC m (MkTCEnv g (deleteSM s f))

  lookupFill' : string -> TC (maybe (Ty [] ** \A -> pair (TName A) (Fill A)))
  getTC (lookupFill' s) env c = c , right (lookupSMStr s (fillEnv env))

instance
  MonadSupply[TC] : MonadSupply TC
  getTC (MonadSupply[TC] .newName s) ctx (MkTCState c {- se ae-}) = MkTCState (suc c) {- se ae -} , right (MkName s c)

newTVar : string -> TC (TVar A)
newTVar s = do
  n <- newName s
  pure (record {varName = n})

reflectCon : (G : Con) -> TC (ECon G)
reflectCon [] = pure emptyECon
reflectCon (G >> _) = do
  r <- reflectCon G
  addECon r



instance
  IsString[TC_String] : IsString (TC string)
  IsString[TC_String] .fromString s = pure s

instance
  IsString[TC_StringBuilder] : IsString (TC stringBuilder)
  IsString[TC_StringBuilder] .fromString s = pure (fromString s)


-------------------------------

printName' : Name -> Doc
printName' n = Var (pr (nameStr n)) {{believeMe~}}  where
  pr : string -> string
  pr "lam" = "lam" <> showNat (nameId n)
  pr "v"   = "v"   <> showNat (nameId n)
  pr n     = n

printName : Name -> TC Doc
printName n = pure (printName' n)

---------------------------------- printing

-- TODO: eta printing
printTmS : TmS A -> TC Doc

printTm : Tm A -> TC Doc
printTm {A = U   } U                    = KWm "U" []
printTm {A = U   } (El Top#)            = KWm "Top" []
printTm {A = U   } (El (Either# A A'))  = printTm A [ "+" ]m printTm A'
printTm {A = U   } (El (A =># A'))      = printTm A [ "->" ]m printTm A'
printTm {A = U   } (El (Pi#    A B))    = KWm "Pi"     (printTm A :: printTm B :: [])
printTm {A = U   } (El (ISigma# A B))   = KWm "Sigma"  (printTm A :: printTm B :: [])
printTm {A = U   } (El (CSigma# A B))   = KWm "CSigma" (printTm A :: printTm B :: [])
printTm {A = U   } (El (Id# x y))       = printTm x [ "==" ]m printTm y
printTm {A = U   } (El (Record# rd ps)) = printName (recordName rd) $m printTm ps
printTm {A = U   } (El (GlueTm x _ _))  = printTmS x
printTm {A = El _} TT               = KWm "TT"    []
printTm {A = El _} (Left  x)        = KWm "Left"  (printTm x :: [])
printTm {A = El _} (Right x)        = KWm "Right" (printTm x :: [])
printTm {A = El _} (x , y)          = printTm x [ "," ]m printTm y
printTm {A = El _} Refl             = KWm "Refl"  []
printTm {A = El _} (GlueTm x _ _)   = printTmS x

printTmS (Def td)                = printName (topDefName td)
printTmS (SVar n)                = printName n
printTmS (Proj (GlueTm x _ _)  ) = KWm "proj"  (printTmS x :: [])
printTmS (Fst  (GlueTm x _ _)  ) = KWm "coFst"   (printTmS x :: [])
printTmS (Snd  (GlueTm x _ _)  ) = KWm "coSnd"   (printTmS x :: [])
printTmS (AppU (GlueTm f _ _) x) = printTmS f  $m printTm x
printTmS (App  (GlueTm f _ _) x) = printTmS f  $m printTm x
printTmS (IFst (Glue f _ _)) = KWm "fst" (printTmS f :: [])
printTmS (ISnd (Glue f _ _)) = KWm "snd" (printTmS f :: [])

showTm : Tm A -> TC stringBuilder
showTm t = do
  t <- printTm t
  pure (showDoc t)

showSpine : TmS A -> TC stringBuilder
showSpine t = do
  t <- printTmS t
  pure (showDoc t)

showTyTm : TyTm G -> TC stringBuilder
showTyTm t = showTm (termOf t) <>m " : " <>m showTm (typeOf t)

---------------------------------

expectVar : (string -> TC a) -> Doc -> TC a
expectVar f (Var n) = f n
expectVar _ d = throwError ("variable name expected instead of: " <> showDoc d)

decRecordDesc : (rd rd' : RecordDesc) -> maybe (Emb (rd ~ rd'))
decRecordDesc rd rd' = decName (recordName rd) (recordName rd') & \where
  (just e) -> just (emb believeMe~)
  nothing -> nothing

data _~[_]~_ : Tm A -> A ~ A' -> Tm A' -> Prop
data _~[_]~_ where
  refl : {x : Tm {G} A} -> x ~[ refl ]~ x

_$u~_  : {x x' : _} -> (B : Tm (A => A')) -> x ~ x' -> B $u x ~ B $u x'
_ $u~ refl = refl

postulate eta=>    : {f f' : Tm {G} (A => A')} -> lift1 {v = v} f $u VZ ~ lift1 f' $u VZ -> f ~ f'
postulate etaPi    : {f f' : Tm {G} (Pi A B)} -> lift1 {v = v} f $ VZ ~ lift1 f' $ VZ -> f ~ f'
postulate etaTop   : {x x' : Tm {G} Top} -> x ~ x'
postulate etaId    : {x y : Tm {G} A} {e e' : Tm (Id x y)} -> e ~ e'
postulate etaSigma : {f f' : Tm {G} (ISigma A B)} -> (e : iFst f ~ iFst f') -> iSnd f ~[ B $u~ e ]~ iSnd f' -> f ~ f'

convertS : {A A' : Ty G} -> (s : TmS A) (s' : TmS A') -> TC (_~e_ {Ty G ** TmS} (_ , s) (_ , s'))

convert' : (e : A ~ A') -> (x : Tm A) (x' : Tm A') -> TC (Emb (x ~[ e ]~ x'))

convert : (x y : Tm {G} A) -> TC (x ~e y)
convert {A = U} U    U     = pure (emb refl)
convert {A = U} (El Top#) (El Top#)  = pure (emb refl)
convert {A = U} (El (Either# A B)) (El (Either# A' B')) = do
  refl <- convert A A' <&> match'
  refl <- convert B B' <&> match'
  pure (emb refl)
convert {A = U} (El (A =># B)) (El (A' =># B')) = do
  refl <- convert A A' <&> match'
  refl <- convert B B' <&> match'
  pure (emb refl)
convert {A = U} (El (Pi# A B)) (El (Pi# A' B')) = do
  refl <- convert A A' <&> match'
  refl <- convert B B' <&> match'
  pure (emb refl)
convert {A = U} (El (ISigma# A B)) (El (ISigma# A' B')) = do
  refl <- convert A A' <&> match'
  refl <- convert B B' <&> match'
  pure (emb refl)
convert {A = U} (El (CSigma# A B)) (El (CSigma# A' B')) = do
  refl <- convert A A' <&> match'
  refl <- convert B B' <&> match'
  pure (emb refl)
convert {A = U} (El (Id# {A} x y)) (El (Id# {A = A'} x' y')) = do
  refl <- convert A A' <&> match'
  refl <- convert x x' <&> match'
  refl <- convert y y' <&> match'
  pure (emb refl)
convert {A = U} A@(El (Record# rd x)) A'@(El (Record# rd' x')) = do
  just refl <- pure (decRecordDesc rd rd' <&> match') where
    nothing -> throwErrorM (showTm A <>m "  =?=  " <>m showTm A')
  refl <- convert x x' <&> match'
  pure (emb refl)
convert {A = U} (El (GlueTm s _ _)) (El (GlueTm s' _ _)) = do
  refl <- convertS s s' <&> match'
  pure (emb believeMe)
convert {G} {A = El (A =># A')} f f' = do
  v <- newTVar "v"
  emb e <- convert {G = G >> v} (lift1 f $u VZ) (lift1 f' $u VZ)
  pure (emb (eta=> e))
convert {G} {A = El (Pi# A B)} f f' = do
  v <- newTVar "v"
  emb e <- convert {G = G >> v} (lift1 f $ VZ) (lift1 f' $ VZ)
  pure (emb (etaPi e))
convert {A = El _} (GlueTm s _ _) (GlueTm s' _ _) = do
  refl <- convertS s s' <&> match'
  pure (emb believeMe)
convert {A = El Top#} _ _ = do
  pure (emb etaTop)
convert {A = El (ISigma# A B)} x x' = do
  emb e <- convert (iFst x) (iFst x')
  emb e' <- convert' (B $u~ e) (iSnd x) (iSnd x')
  pure (emb (etaSigma e e'))
convert {A = El _} (Left x) (Left x') = do
  refl <- convert x x' <&> match'
  pure (emb refl)
convert {A = El _} (Right x) (Right x') = do
  refl <- convert x x' <&> match'
  pure (emb refl)
convert {A = El (Id# _ _)} _ _ = do
  pure (emb etaId)
convert x y = throwErrorM (showTm x <>m "  =?=  " <>m showTm y)

convert' e x x' = do
  refl <- pure (match e)
  refl <- convert x x' <&> match'
  pure (emb refl)

convertS x@(SVar v) y@(SVar v') = decName v v' & \where
  (just _) -> pure (emb believeMe)
  nothing  -> throwErrorM (showSpine x <>m "  =?=  " <>m showSpine y)
convertS x@(Def td) y@(Def td') = decName (topDefName td) (topDefName td') & \where
  (just _) -> pure (emb believeMe)
  nothing  -> throwErrorM (showSpine x <>m "  =?=  " <>m showSpine y)
convertS (AppU (GlueTm f _ _) x) (AppU (GlueTm f' _ _) x') = do
  refl <- convertS f f' <&> match'
  refl <- convert x x' <&> match'
  pure (emb believeMe~)
convertS (App (GlueTm f _ _) x) (App (GlueTm f' _ _) x') = do
  refl <- convertS f f' <&> match'
  refl <- convert x x' <&> match'
  pure (emb believeMe~)
convertS (Fst (GlueTm x _ _)) (Fst (GlueTm x' _ _)) = do
  refl <- convertS x x' <&> match'
  pure (emb believeMe~)
convertS (Snd (GlueTm x _ _)) (Snd (GlueTm x' _ _)) = do
  refl <- convertS x x' <&> match'
  pure (emb believeMe~)
convertS (Proj (GlueTm x _ _)) (Proj (GlueTm x' _ _)) = do
  refl <- convertS x x' <&> match'
  pure (emb believeMe~)
convertS x y = throwErrorM (showSpine x <>m "  =?=  " <>m showSpine y)



mkLam' : {A A' : _} -> Tm {G >> v} (lift1 A') -> TC (Tm {G} (A => A'))
mkLam' {G} {A} {A'} e = do

  AG , r , vars <- reflectCon G
  let
      e'' : ((xs , x) : Tms (⟦ G ⟧c >> ⟦ A ⟧)) -> Tm {[]} (⟦ A' ⟧ xs)
      e'' = coe believeMe~ ⟦ e ⟧

      ff : Tm AG -> Tms ⟦ G ⟧c
      ff = sigsToTms r

  l1 <- mkLam \xs -> ⟦ A => A' ⟧ (ff xs)
  n2 <- newTName "lam"

  let
      up : Tm {[]} (Pi AG l1)
      up = def' n2 (lam' \xs -> coe believeMe~ (lamU' {A = ⟦ A ⟧ (sigsToTms r xs)} \x -> ret (e'' (ff xs , x))))

  pure (coe believeMe~ (lift up $ vars))

mkDLam : {A : _} {B : _} {v : _} -> Tm {G >> v} (lift1 B $u VZ) -> TC (Tm {G} (Pi A B))
mkDLam {G} {A} {B} e = do

  AG , r , vars <- reflectCon G
  let
      e'' : ((xs , x) : Tms (⟦ G ⟧c >> ⟦ A ⟧)) -> Tm {[]} (⟦ B ⟧ xs $u x)
      e'' = coe believeMe~ ⟦ e ⟧

      ff : Tm AG -> Tms ⟦ G ⟧c
      ff = sigsToTms r

  l1 <- mkLam \xs -> ⟦ Pi A B ⟧ (ff xs)
  n2 <- newTName "lam"

  let
      up : Tm {[]} (Pi AG l1)
      up = def' n2 (lam' \xs -> coe believeMe~ (lam' {A = ⟦ A ⟧ (sigsToTms r xs)} {B = ⟦ B ⟧ (sigsToTms r xs)} \x -> ret (e'' (ff xs , x))))

  pure (coe believeMe~ (lift up $ vars))


infer : Doc -> TC (TyTm G)

check : Doc -> (A : Ty G) -> TC (Tm A)
check (KW "Paren" (x :: [])) A = check x A
check (KW "Refl" []) (El (Id# x y)) = do
  refl <- convert x y <&> match'
  pure Refl
check (KW "Left" (x :: [])) (El (Either# A A')) = do
  x <- check x A
  pure (Left x)
check (KW "Right" (x :: [])) (El (Either# A A')) = do
  x <- check x A'
  pure (Right x)
check {G} (sn [ "." ] x) (El (A =># A')) = do
  v <- expectVar (newTVar {A = A}) sn
  x <- check {G = G >> v} x (lift1 A')
  mkLam' x
check {G} (sn [ "." ] x) (El (Pi# A B)) = do
  v <- expectVar newTVar sn
  x <- check {G = G >> v} x (lift1 B $u VZ)
  mkDLam x
check {G} (sn [ "." ] x) A = throwErrorM ("not a Pi: " <>m showTm A)
check (x [ "," ] y) (El (ISigma# A B)) = do
  x <- check x A
  y <- check y (B $u x)
  pure (x , y)
check (KW "?" []) a = do
  throwError "TODO: printGoal"
check d A = do
  t <- infer d
  refl <- convert (typeOf t) A <&> match'
  pure (termOf t)

infer (KW "Paren" (x :: [])) = infer x
-- TODO: AtExp
infer (KW "U" []) = do
  pure (tyTm U)
infer (KW "Top" []) = do
  pure (tyTm Top)
infer (KW "TT" []) = do
  pure (tyTm TT)
infer (KW "proj" (d :: [])) = do
  tyTm {typeOf = El (Record# _ _)} x <- infer d  where
    t -> throwErrorM ("proj: " <>m showTyTm t)
  pure (tyTm (proj x))
infer (KW "fst" (d :: [])) = do
  tyTm {typeOf = El (ISigma# _ _)} x <- infer d  where
    t -> throwErrorM ("fst: " <>m showTyTm t)
  pure (tyTm (iFst x))
infer (KW "snd" (d :: [])) = do
  tyTm {typeOf = El (ISigma# _ _)} x <- infer d  where
    t -> throwErrorM ("fst: " <>m showTyTm t)
  pure (tyTm (iSnd x))
infer (A [ "+" ] A') = do
  A  <- check A  U
  A' <- check A' U
  pure (tyTm (Either A A'))
infer (A [ "->" ] A') = do
  A  <- check A  U
  A' <- check A' U
  pure (tyTm (A => A'))
infer (KW "Pi" (A :: B :: [])) = do
  A <- check A U
  B <- check B (A => U)
  pure (tyTm (Pi A B))
infer (KW "Sigma" (A :: B :: [])) = do
  A <- check A U
  B <- check B (A => U)
  pure (tyTm (ISigma A B))
infer (KW "CSigma" (A :: B :: [])) = do
  A <- check A U
  B <- check B (A => U)
  pure (tyTm (CSigma A B))
infer (x [ "==" ] y) = do
  x <- infer x
  y <- check y (typeOf x)
  pure (tyTm (Id (termOf x) y))
infer (f $d x) = infer f >>= \where
  (tyTm {typeOf = El (A =># A')} f) -> do
    x <- check x A
    pure (tyTm (f $u x))
  (tyTm {typeOf = El (Pi# A B)} f) -> do
    x <- check x A
    pure (tyTm (f $ x))
  t -> throwErrorM ("matchPi: " <>m showTyTm t)
infer (Var n) = lookupTm n
infer d = throwError ("infer: " <> showDoc d)

newTVar' : Doc -> TC (pair (TVar A) Doc)
newTVar' (Paren d) = newTVar' d
newTVar' (n [ "." ] d) = do
  n <- expectVar newTVar n
  pure (n , d)
newTVar' d = throwError ("lambda expected instead of: " <> showDoc d)


checkLHS : Doc -> (A : Ty G) -> Tm A -> TC (TmFL' A)
checkLHS (KW "Paren" (x :: [])) A z = checkLHS x A z
checkLHS {G} (n [ "." ] t) (El (A =># A')) z = do
  v <- expectVar newTVar n
  GlueFLHS _ t <- checkLHS {G = G >> v} t (lift1 A') (lift1 z $u VZ)
  pure (GlueFLHS z (FLamU t))
checkLHS {G} (n [ "." ] t) (El (Pi# A B)) z = do
  v <- expectVar newTVar n
  t <- checkLHS {G = G >> v} t (lift1 B $u VZ) (lift1 z $ VZ)
  pure (GlueFLHS z (FLam t))
checkLHS (KW "Wrap" (x :: [])) (El (Record# rd ps)) z = do
  x <- checkLHS x (rFields rd ps) (proj z)
  pure (GlueFLHS z (FWrap x))
checkLHS (x [ "," ] y) (El (CSigma# A B)) z = do
  x <- checkLHS x A (cFst z)
  y <- checkLHS y (B $u cFst z) (cSnd z)
  pure (GlueFLHS z (x , coe believeMe~ y))
checkLHS (KW "fail" []) A z = do
  pure (GlueFLHS z FFail)
checkLHS (l [ "|" ] r) A z = do
  GlueFLHS _ l <- checkLHS l A z
  GlueFLHS _ r <- checkLHS r A z
  pure (GlueFLHS z (FOr l r))
checkLHS {G} (KW "matchLeft" (x :: f :: [])) A'' z = do
  tyTm {typeOf = El (Either# A A')} x <- infer {G = G} x where
    t -> throwErrorM ("matchLeft: " <>m showTyTm t)
  v  , f <- newTVar' f
  v' , f <- newTVar' f
  GlueFLHS _ t <- checkLHS {G = G >> v >> v'} f (lift1 (lift1 A'')) (lift1 (lift1 z))
  pure (GlueFLHS z (MatchLeft x t))
checkLHS {G} (KW "matchRight" (x :: f :: [])) A'' z = do
  tyTm {typeOf = El (Either# A A')} x <- infer {G = G} x where
    t -> throwErrorM ("matchRight: " <>m showTyTm t)
  v  , f <- newTVar' f
  v' , f <- newTVar' f
  GlueFLHS _ t <- checkLHS {G = G >> v >> v'} f (lift1 (lift1 A'')) (lift1 (lift1 z))
  pure (GlueFLHS z (MatchRight x t))
-- TODO: jRule kRule absurd
checkLHS d a z = do
  t <- check d a
  pure (GlueFLHS z (FRHS t))

checkLHS' : TName A -> Doc -> (Tm A -> TC a) -> TC a
checkLHS' n t cont = do
  future \get set -> do
    t <- checkLHS t _ get
    let d = n := t
    set _ d (cont d)

inferTop : Doc -> TC (TyTm [])
inferTop (KW "Paren" (x :: [])) = inferTop x
inferTop (((n [ ":" ] A) [ "=" ] t) [ ";" ] ds) = do
  A <- check {G = []} A U
  n <- expectVar (newTName {A = A}) n
  checkLHS' n t \d -> addGlobal n d (inferTop ds)
inferTop ((n [ "=" ] KW "record" (ps :: fs :: [])) [ ";" ] ds') = do
  ps <- check ps U
  fs <- check fs (ps => U)
  dn <- expectVar newTName n
  let d = record {recordName = tName dn; recordParams = ps; recordFields = fs}
  l <- mkLam \x -> Record d x
  addGlobal dn l (inferTop ds')
-- TODO: postulates ("::")
-- TODO: FFI declarations
inferTop ((n [ ":" ] A) [ ";" ] ds) = do
  A <- check A U
  n <- expectVar (newTName {A = A}) n
  futureTC n \t' -> addGlobal n t' (inferTop ds)
inferTop ((Var n [ "=" ] t) [ ";" ] ds) = do
  lookupFill n (\n fill -> do
    checkLHS' n t \t -> fill _ t (inferTop ds)
   ) (do
    t <- infer t
    n <- newTName n
    addGlobal n (termOf t) (inferTop ds)
   )
inferTop (t [ ":" ] a) = do
  a <- check a U
  t <- check t a
  pure (tyTm t)
inferTop t = infer t

tc : string -> either error (TyTm [])
tc s = runTC (parse s >>= inferTop)

tc' : (s : string) -> {{IsRight (tc s)}} -> TyTm []
tc' s = fromRight (tc s)


testTC0 : tc' "U"
       ~ tyTm U
testTC0 = refl
{-
testTC1 : tc' "f : Bool -> U  = x. Bool;  U"
       ~ (U , U)
testTC1 = refl

testTC2 : tc' "idU : U -> U  = x. x; idU U"
       ~ (U , U)
testTC2 = refl
-}
--testTC3 : tc' "constTy' : U -> U = z. U; constTy : U -> U = w. Pi U constTy'; const : Pi U constTy = v. U; U"
--       ~ (U , U)
--testTC3 = refl


mainTC : string -> TC stringBuilder
mainTC s = do
  d <- parse s
  t <- inferTop d
  a <- printTm (typeOf t)
  t <- printTm (termOf t)
--  ss <- getShows
  pure (showDoc t <> "\n : " <> showDoc a)

main : IO top
main = do
--  args <- getArgs
  interact \s -> runStringBuilder (fromEither (runTC (mainTC s)) <> "\n")


--------------

show : (x : Tm {[]} A) -> {{IsRight (runTC (printTm x))}} -> string
show x = runStringBuilder (showDoc (fromRight (runTC (printTm x))))



{-

- jRule kRule

** Refl pattern matching   -- new feature

- on demand
  - AtExp
  - printGoal "?"
  - eta printing
  - Bot needed?
  - CSigma needed?
  - pairs next to sigma needed?
  - inductive records needed?
  - efficient lift compilation
  - cached ECon
  - staging
    - postulates ("::")
    - FFI declarations

  refactorings:
  * glue first order and second order representation
  * rethink FL'
  - less believeMe
    - complete lift definitions

-}



