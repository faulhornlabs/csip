
{-# OPTIONS --type-in-type --no-termination-check --rewriting --prop --hidden-argument-puns --erasure #-}

open import Prelude

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

data Loc : Set where
  NoLoc   :               Loc
  LineCol : nat -> nat -> Loc   -- TODO: add a source index

instance
  Show[Loc] : Show Loc
  Show[Loc] .show NoLoc = ""
  Show[Loc] .show (LineCol l c) = show (suc l) <> ";" <> show (suc c)

  ShowM[Loc] : {{_ : Monad M}} -> ShowM Loc M
  ShowM[Loc] .showM l = pure (show l)

record Token : Set where
  constructor MkToken
  field
    tokenLoc : Loc
    tokenStr : string
    -- TODO: add a proof that joinChars is True for the chars of tokenStr
    --       add a proof that the first and last char is not joined to the neighbours?

open Token public

instance
  Show[Token] : Show Token
  Show[Token] .show t = fromString (tokenStr t)

  Eq[Token] : Eq Token
  Eq[Token] ._==_ t t' = tokenStr t == tokenStr t'

  IsString[Token] : IsString Token
  IsString[Token] .fromString s = MkToken NoLoc s

showWithLoc : Token -> stringBuilder
showWithLoc t = show (tokenStr t) <> " at " <> show (tokenLoc t)

chars = list (pair Loc char)

addLocs : list char -> chars
addLocs = go 0 0 where
  go : nat -> nat -> list char -> chars
  go _ _ [] = []
  go line col (c@'\n' :: cs) = (LineCol line col , c) :: go (suc line) 0   cs
  go line col (c      :: cs) = (LineCol line col , c) :: go line (suc col) cs

tokens : {{MonadError stringBuilder M}} -> bool -> chars -> M (list Token)
tokens _ [] = pure []
tokens true ((_ , '\n') :: (l , '#') :: s) = skip s \a s -> do
  ts <- tokens true s
  pure (MkToken l ";" :: MkToken l "FFI" :: MkToken l (stringFromList (map snd a)) :: ts)
 where
  skip : chars -> (chars -> chars -> A) -> A
  skip ((l , '\n') :: s) cont = cont [] ((l , '\n') :: s)
  skip (c    :: s) cont = skip s \a s -> cont (c :: a) s
  skip []          cont = cont [] []
tokens true ((l0 , '\n') :: (l , c) :: s) = charClass c & \where
  Alpha -> do
    ts <- tokens false ((l , c) :: s)
    pure (MkToken l0 ";" :: ts)
  _ -> tokens true ((l , c) :: s)
tokens b ((_ , '\n') :: s) = tokens b s
tokens b ((_ , ' ')  :: s) = tokens b s
tokens {M} b ((_ , '-') :: (_ , '-') :: s) = skip s where
  skip : chars -> M (list Token)
  skip ((l , '\n') :: s) = tokens b ((l , '\n') :: s)
  skip (_    :: s) = skip s
  skip []          = pure []
tokens b ((l , c) :: s) = charClass c & \where
  OtherChar -> throwError ("invalid character: " <> fromString (stringFromList (c :: [])))
  cc -> go cc s \r rs -> do
    ts <- tokens true rs
    pure (MkToken l (stringFromList (c :: map snd r)) :: ts)
 where
  go : CharClass -> chars -> (chars -> chars -> A) -> A
  go cc [] cont = cont [] []
  go cc ((l , d) :: cs) cont = joinChars cc (charClass d) & \where
    true  -> go cc cs \r rs -> cont ((l , d) :: r) rs
    false -> cont [] ((l , d) :: cs)

tokens' : {{MonadError stringBuilder M}} -> string -> M (list Token)
tokens' s = tokens false (addLocs (stringToList (s <> "\nEndOfFile")))

showTokens : list Token -> stringBuilder
showTokens [] = ""
showTokens (t :: ts) = show t <> " " <> showTokens ts

instance
  Show[list_Token] : Show (list Token)
  Show[list_Token] .show = showTokens

----------------------------------

data TokenClass : Set where
  Operator : nat -> nat -> TokenClass     -- left and right precedence
  Keyword  : nat ->        TokenClass     -- arity
  Var      :               TokenClass

operators' : list string
operators' = ";" :: "=" :: "|" :: "." :: ":" :: "::" :: "$" :: "=>" :: "@" :: "<-" :: "&" :: "," :: "->" :: "==" :: "+" :: "*" :: []

tokenClass' : string -> maybe TokenClass
tokenClass' t = isOperator t & \where
  (just (l , r)) -> just (Operator l r)
  nothing -> isKeyword t & \where
    (just arity) -> just (Keyword arity)
    nothing -> isAlphaToken t & \where
      true  -> just Var
      false -> nothing
 where
  isAlphaToken : string -> bool
  isAlphaToken s = stringToList s & \where
    [] -> false
    (c :: _) -> charClass c & \where
      Alpha -> true
      _     -> false

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
    right "<-" :: left "<-" ::
    right "&"  :: left "&"  ::
    right ","  :: left ","  ::
    right "->" :: left "->" ::
    right "==" :: left "==" ::
    right "+"  :: left "+"  ::
    right "*"  :: left "*"  ::
    left " "   :: right " " ::
    left "\\"  ::
    []

  isOperator : string -> maybe (pair nat nat)
  isOperator s = do
    l <- goLeft  0 operators s
    r <- goRight 0 operators s
    pure (l , r)
   where
    goLeft : nat -> list (either string string) -> string -> maybe nat
    goLeft n [] _ = nothing
    goLeft n (right s :: os) s' = goLeft (suc n) os s'
    goLeft n (left  s :: os) s' = s' == s & \where
      true  -> just n
      false -> goLeft (suc n) os s'

    goRight : nat -> list (either string string) -> string -> maybe nat
    goRight n [] _ = nothing
    goRight n (left  s :: os) s' = goRight (suc n) os s'
    goRight n (right s :: os) s' = s' == s & \where
      true  -> just n
      false -> goRight (suc n) os s'

  isKeyword : (s : string) -> maybe nat
  isKeyword "Bracket"    = just 1
  isKeyword "Brace"      = just 1
  isKeyword "Paren"      = just 1
  isKeyword "U"          = just 0
  isKeyword "?"          = just 0
  isKeyword "TODO"       = just 0
  isKeyword "Pi"         = just 2
  isKeyword "Sigma"      = just 2
  isKeyword "CoSigma"    = just 2
  isKeyword "Left"       = just 1
  isKeyword "Right"      = just 1
  isKeyword "proj"       = just 1
  isKeyword "fst"        = just 1
  isKeyword "snd"        = just 1
  isKeyword "Top"        = just 0
  isKeyword "TT"         = just 0
  isKeyword "EndOfFile"  = just 0
  isKeyword "Refl"       = just 0
  isKeyword "corecord"   = just 2
  isKeyword "record"     = just 2
  isKeyword "Wrap"       = just 1
  isKeyword "wrap"       = just 1
  isKeyword "undefined"  = just 0
  isKeyword "matchLeft"  = just 2
  isKeyword "matchRight" = just 2
  isKeyword "matchWrap"  = just 2
  isKeyword "matchPair"  = just 2
  isKeyword "matchRefl"  = just 2
  isKeyword "coerce"     = just 2
  isKeyword "sym"        = just 1
  isKeyword "jRule"      = just 3
  isKeyword _            = nothing

tokenClass : Token -> maybe TokenClass
tokenClass t = tokenClass' (tokenStr t)

keywordArity : TokenClass -> nat
keywordArity Var            = 0
keywordArity (Operator _ _) = 2
keywordArity (Keyword a)    = a

tokenArity' : string -> maybe nat
tokenArity' t = keywordArity <$> tokenClass' t

tokenArity : Token -> maybe nat
tokenArity t = keywordArity <$> tokenClass t


-------------------------------------------------

data OpDoc : Set where
  _<<_>>_ : OpDoc -> (t : Token) -> {l r : nat} -> @0 {{tokenClass t ~ just (Operator l r)}} -> OpDoc -> OpDoc
  Var     : Token ->                                                                                     OpDoc

showOpDoc : OpDoc -> stringBuilder
showOpDoc = go 0 0 where

  parens : bool -> stringBuilder -> stringBuilder
  parens true  a = "(" <> a <> ")"
  parens false a =        a

  renderOp : string -> stringBuilder
  renderOp " " = " "
  renderOp s   = " " <> fromString s <> " "

  precOk : nat -> nat -> nat -> nat -> bool
  precOk p q q' p' = p < q & \where
    true  -> p' < q'
    false -> false

  go : nat -> nat -> OpDoc -> stringBuilder
  go p p' (Var n)     = show n
  go p p' (_<<_>>_ a (MkToken _ s) {l = q} {r = q'} b) = precOk p q q' p' & \where
    true  ->              go p q a <> renderOp s <> go q' p' b
    false -> parens true (go 0 q a <> renderOp s <> go q' 0  b)

instance
  Show[OpDoc] : Show OpDoc
  Show[OpDoc] .show = showOpDoc

------------------------------------------

infixl 9 _$d_
data Doc' : @0 nat -> Set where
  FFI  : Token ->                                         Doc' 0
  Var  : (s : Token) -> @0 {{tokenClass s ~ just Var}} -> Doc' 0
  _$d_ : Doc' (suc K) -> Doc' 0 ->                        Doc' K
  KW   : (s : Token) -> @0 {{tokenArity s ~ just K}} ->   Doc' K

Doc = Doc' 0

toOpDoc : Doc' K -> OpDoc
toOpDoc (FFI t) = Var t
toOpDoc (Var t) = Var t
toOpDoc (KW t)  = Var t
toOpDoc (KW t $d l $d r) = tokenClass t &in \where
  (just (Operator _ _)) e -> _<<_>>_ (toOpDoc l) t {{e}} (toOpDoc r)
  _                     _ -> (Var t << " " >> toOpDoc l) << " " >> toOpDoc r
toOpDoc (l $d r) = toOpDoc l << " " >> toOpDoc r

instance
  Show[Doc] : Show Doc
  Show[Doc] .show d = show (toOpDoc d)


@0 vecFun : @0 Set -> @0 Set -> @0 nat -> Set
vecFun A A' zero = A'
vecFun A A' (suc n) = A -> vecFun A A' n

mkVecFun : {@0 D : @0 nat -> Set} -> ({@0 K : _} -> D (suc K) -> D 0 -> D K) -> D K* -> vecFun (D 0) (D 0) K*
mkVecFun {K* = zero}  ap f = f
mkVecFun {K* = suc n} ap f a = mkVecFun (\{K} -> ap {K}) (ap f a)

kw : (s : Token) -> @0 {{tokenArity s ~ just K*}} -> vecFun Doc Doc K*
kw s = mkVecFun {D = Doc'} (\a b -> a $d b) (KW s)

kwm : {{Monad M}} -> (s : Token) -> @0 {{tokenArity s ~ just K*}} -> vecFun (M Doc) (M Doc) K*
kwm {M} s = mkVecFun {D = \K -> M (Doc' K)} (\a b -> (| a $d b |)) (pure (KW s))

-------------------------------------

@0 <$>just : {f : A -> A'} {x : maybe A} {y : A} -> x ~ just y -> f <$> x ~ just (f y)
<$>just {x = just _} refl = refl

private pattern Paren l a = KW (MkToken l "Paren") $d a

parse : {{MonadError stringBuilder M}} -> string -> M Doc
parse {M} s = tokens' s >>= parseOps end <&> removeParens  where

  @0 X : Set
  X = list Token -> M Doc

  end : Doc -> X
  end d [] = pure d
  end d ts  = throwError ("End expected instead of  " <> show ts)

  expect : Loc -> string -> X -> X
  expect l t r (t' :: ts) = tokenStr t' == t & \where
    true  -> r ts
    false -> throwError (fromString t <> " expected instead of " <> show (t' :: ts) <> " at " <> show l)
  expect l t _ [] = throwError (fromString t <> " expected instead of end" <> " at " <> show l)

  parseOps : (Doc -> X) -> X

  parseAtom : ((n : nat) -> vecFun Doc Doc n -> X) -> X -> X
  parseAtom r _ (MkToken l "(" :: ts) = parseOps (\b -> expect l ")" (r 0 (kw (MkToken l "Paren")   b))) ts
  parseAtom r _ (MkToken l "[" :: ts) = parseOps (\b -> expect l "]" (r 0 (kw (MkToken l "Bracket") b))) ts
  parseAtom r _ (MkToken l "{" :: ts) = parseOps (\b -> expect l "}" (r 0 (kw (MkToken l "Brace")   b))) ts
  parseAtom r z (MkToken l "FFI" :: MkToken _ t :: ts) = r 0 (FFI (MkToken l t)) ts
  parseAtom r z (t :: ts) = tokenClass t &in \where
    (just (Keyword n)) e -> r n (kw t {{<$>just e}}) ts
    (just  Var)        e -> r 0 (Var t {{e}}) ts
    _                  _ -> z (t :: ts)

  parseAtom _ z ts = z ts

  parseAtom0 : (Doc -> X) -> X -> X
  parseAtom0 r z = parseAtom f z  where
    f : (n : nat) -> vecFun Doc Doc n -> X
    f 0 d = r d
    f _ _ = z

  parseApps : (Doc -> X) -> X
  parseApps r = parseAtom (f r) \ts -> throwError ("unknown token at  " <> show ts)  where

    f : (Doc -> X) -> (n : nat) -> vecFun Doc Doc n -> X
    f r 0       a ts = parseAtom0 (\b -> f r 0 (kw " " a b)) (r a) ts
    f r (suc n) a ts = parseAtom0 (\b -> f r n (       a b)) (\ts -> throwError ("argument expected at " <> show ts)) ts

  mkPi : Loc -> Doc -> Doc -> Doc -> Doc
  mkPi l (KW (MkToken l' " ") $d ns $d n) a b = mkPi l ns a (kw (MkToken l "Pi") a (kw (MkToken l' ".") n b))
  mkPi l                               n  a b =              kw (MkToken l "Pi") a (kw (MkToken l  ".") n b)

  mkSigma : Loc -> Doc -> Doc -> Doc -> Doc
  mkSigma l (KW (MkToken l' " ") $d ns $d n) a b = mkSigma l ns a (kw (MkToken l "Sigma") a (kw (MkToken l' ".") n b))
  mkSigma l                               n  a b =                 kw (MkToken l "Sigma") a (kw (MkToken l  ".") n b)

  mkOp : (s : Token) -> @0 {{tokenArity s ~ just 2}} -> Doc -> Doc -> M Doc
  mkOp (MkToken _ "$") a b = pure (kw " " a b)
  mkOp t@(MkToken l "->") (KW (MkToken _ " ") $d bs $d Paren _ (KW (MkToken _ ":") $d n $d a)) b = mkOp t bs (mkPi    l n a b)
  mkOp   (MkToken l "->")                             (Paren _ (KW (MkToken _ ":") $d n $d a)) b = pure      (mkPi    l n a b)
  mkOp t@(MkToken l "*")  (KW (MkToken _ " ") $d bs $d Paren _ (KW (MkToken _ ":") $d n $d a)) b = mkOp t bs (mkSigma l n a b)
  mkOp   (MkToken l "*")                              (Paren _ (KW (MkToken _ ":") $d n $d a)) b = pure      (mkSigma l n a b)
  mkOp t@(MkToken _ ".")  (KW (MkToken _ " ") $d ns $d n) b = mkOp t ns (kw t n b)
  mkOp t@(MkToken _ ".")                               n  b = pure      (kw t n b)
  mkOp t a b = pure (kw t a b)

  addOp : string -> ((Doc -> X) -> X) -> (Doc -> X) -> X
  addOp op g r = tokenArity' op &in \where
    (just 2) e -> g (f e r)
    _        _ -> g r
   where
    f : @0 (tokenArity' op ~ just 2) -> (Doc -> X) -> Doc -> X
    f e r a (t' :: ts) = tokenStr t' == op &in \where
      true  e' -> addOp op g (\b ts -> mkOp t' {{(_ ~! _) *~ e}} a b >>= \o -> r o ts) ts
      false _ -> r a (t' :: ts)
    f e r a ts = r a ts

  parseOps = foldr addOp parseApps operators'

  removeParens : Doc' K -> Doc' K
  removeParens (FFI x) = FFI x
  removeParens (Var s) = Var s
  removeParens (KW (MkToken l "Paren") $d d) = removeParens (coe (_ ~! _) d)   -- TODO
  removeParens (KW t) = KW t
  removeParens (a $d b) = removeParens a $d removeParens b


------------------------------------

record ToDoc (@0 A : Set) : Set where
  field
    toDoc : A -> Doc

open ToDoc {{...}} public

record ToDocM (@0 A : Set) (@0 M : @0 Set -> Set) {{@0 _ : Monad M}} : Set where
  field
    toDocM : A -> M Doc

open ToDocM {{...}} public

-------------------------------------------------------

record NameStr : Set where
  constructor MkNameStr
  field
    nameStrToken             : Token
    @0 {{nameStrTokenValid}} : tokenClass nameStrToken ~ just Var

generatedName : NameStr -> bool
generatedName (MkNameStr t) = tokenLoc t & \where
  NoLoc -> true
  _     -> false

GeneratedVar : (s : string) -> @0 {{tokenClass (MkToken NoLoc s) ~ just Var}} -> NameStr
GeneratedVar s = MkNameStr (MkToken NoLoc s)

record Name : Set where
  field
    nameStr : NameStr  -- for pretty printing
    nameId  : nat      -- globally unique id

open Name public

builtinName : (s : string) -> @0 {{tokenClass (MkToken NoLoc s) ~ just Var}} -> nat -> Name
builtinName s n = record {nameStr = GeneratedVar s; nameId = n}

variable @0 n n' : Name

record HasName (@0 A : Set) : Set where
  field
    nameOf : A -> Name

open HasName {{...}} public

instance
  HasName[Name] : HasName Name
  HasName[Name] .nameOf n = n

nameToDocM : {{HasName A}} -> {{Monad M}} -> A -> M Doc
nameToDocM x = pure (nameOf x & \n -> nameStr n & \where
    ns@(MkNameStr t') -> generatedName ns & \where
      true  -> Var (MkToken NoLoc (tokenStr t' <> show' (nameId n))) {{_ ~! _}}
      false -> Var t'
  )

matchName : {{HasName A}} -> Token -> A -> bool
matchName t x = nameStr (nameOf x) & \where
  ns@(MkNameStr t') -> generatedName ns & \where
    true  -> false
    false -> t' == t

decHasName : {{d : HasName A}} -> {{d' : HasName A'}} -> (x : A) (x' : A') -> maybe (_~e_ {Set ** \A -> A} (_ , x) (_ , x'))
decHasName x x' = nameId (nameOf x) == nameId (nameOf x') & \where
  true  -> just (emb ((_ , x) ~! (_ , x')))
  false -> nothing

newName : {{MonadSupply M}} -> NameStr -> M Name
newName s = do
  i <- newId
  pure (record {nameStr = s; nameId = i})
{-
unsafeNewName : NameStr -> Name
unsafeNewName s = unsafeNewId \i -> record {nameStr = s; nameId = i}
-}


