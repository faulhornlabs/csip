{-# OPTIONS --type-in-type --no-positivity-check --no-termination-check --rewriting --prop --injective-type-constructors --hidden-argument-puns #-}
module Parser where

open import Prelude

infixl 9 _$d_
infixr 8 _[_]_   -- operator syntax for Doc
infixr 8 _[_]m_  -- operator syntax for Doc

data CharClass : Set where
  Alpha Graphic Punctuation OtherChar : CharClass

charClass : Char -> CharClass
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
  True  -> Alpha
  False -> between 'A' 'Z' c & \where
    True  -> Alpha
    False -> between '0' '9' c & \where
      True  -> Alpha
      False -> OtherChar
 where
  between : Char -> Char -> Char -> Bool
  between a z c = charToNat a <= charToNat c & \where
    False -> False
    True  -> charToNat c <= charToNat z

joinChars : CharClass -> CharClass -> Bool
joinChars Alpha   Alpha   = True
joinChars Graphic Graphic = True
joinChars _       _       = False

Token = String

tokens : {{MonadError StringBuilder M}} -> Bool -> List Char -> M (List Token)
tokens _ [] = pure []
tokens True ('\n' :: '#' :: s) = skip s \a s -> do
  ts <- tokens True s
  pure (";" :: "FFI" :: stringFromList a :: ts)
 where
  skip : List Char -> (List Char -> List Char -> A) -> A
  skip ('\n' :: s) cont = cont [] ('\n' :: s)
  skip (c    :: s) cont = skip s \a s -> cont (c :: a) s
  skip []          cont = cont [] []
tokens True ('\n' :: c :: s) = charClass c & \where
  Alpha -> do
    ts <- tokens False (c :: s)
    pure (";" :: ts)
  _ -> tokens True (c :: s)
tokens b ('\n' :: s) = tokens b s
tokens b (' '  :: s) = tokens b s
tokens {M} b ('-' :: '-' :: s) = skip s where
  skip : List Char -> M (List String)
  skip ('\n' :: s) = tokens b ('\n' :: s)
  skip (_    :: s) = skip s
  skip []          = pure []
tokens b (c :: s) = charClass c & \where
  OtherChar -> throwError ("invalid character: " <> fromString (stringFromList (c :: [])))
  cc        -> go cc s \r rs -> do
    ts <- tokens True rs
    pure (stringFromList (c :: r) :: ts)
 where
  go : CharClass -> List Char -> (List Char -> List Char -> A) -> A
  go cc [] cont = cont [] []
  go cc (d :: cs) cont = joinChars cc (charClass d) & \where
    True  -> go cc cs \r rs -> cont (d :: r) rs
    False -> cont [] (d :: cs)

tokens' : {{MonadError StringBuilder M}} -> String -> M (List Token)
tokens' s = tokens False (stringToList s)

testTokens : tokens' "(a ++ bc)" ~ Just ("(" :: "a" :: "++" :: "bc" :: ")" :: [])
testTokens = Refl

showTokens : List Token -> StringBuilder
showTokens [] = ""
showTokens (t :: ts) = fromString t <> " " <> showTokens ts

----------------------------------

isAlphaToken : Token -> Bool
isAlphaToken s = stringToList s & \where
  (c :: _) -> charClass c & \where
    Alpha -> True
    _     -> False
  _ -> False

operators : List (Either String String)
operators =
  Right ";"  :: Left ";"  ::
  Right "="  :: Left "="  ::
  Right "|"  :: Left "|"  ::
  Right "\\" ::
  Right "."  :: Left "."  ::
  Right ":"  :: Left ":"  ::
  Right "::" :: Left "::" ::
  Right "$"  :: Left "$"  ::
  Right "=>" :: Left "=>" ::
  Right "@"  :: Left "@"  ::
  Right ","  :: Left ","  ::
  Right "->" :: Left "->" ::
  Right "==" :: Left "==" ::
  Right "+"  :: Left "+"  ::
  Right "*"  :: Left "*"  ::
  Left " "   :: Right " " ::
  Left "\\"  ::
  []

operators' : List String
operators' = ";" :: "=" :: "|" :: "." :: ":" :: "::" :: "$" :: "=>" :: "@" :: "," :: "->" :: "==" :: "+" :: "*" :: []

isOperator : String -> Maybe (Pair Nat Nat)
isOperator s = do
  l <- goLeft  0 operators s
  r <- goRight 0 operators s
  pure (l , r)
 where
  goLeft : Nat -> List (Either String String) -> String -> Maybe Nat
  goLeft n [] _ = Nothing
  goLeft n (Right s :: os) s' = goLeft (Suc n) os s'
  goLeft n (Left s :: os) s' = s' == s & \where
    True  -> Just n
    False -> goLeft (Suc n) os s'

  goRight : Nat -> List (Either String String) -> String -> Maybe Nat
  goRight n [] _ = Nothing
  goRight n (Left s :: os) s' = goRight (Suc n) os s'
  goRight n (Right s :: os) s' = s' == s & \where
    True  -> Just n
    False -> goRight (Suc n) os s'

isKeyword : (s : String) -> Maybe Nat
isKeyword "Bracket" = Just 1
isKeyword "Brace"   = Just 1
isKeyword "Paren"   = Just 1
isKeyword "pattern" = Just 1
isKeyword "FFI"     = Just 1
isKeyword "U"       = Just 0
isKeyword "?"       = Just 0
isKeyword "Pi"      = Just 2
isKeyword "Sigma"   = Just 2
isKeyword "Left"    = Just 1
isKeyword "Right"   = Just 1
isKeyword "either"  = Just 3
isKeyword "Top"     = Just 0
isKeyword "TT"      = Just 0
isKeyword "Bot"     = Just 0
isKeyword "absurd"  = Just 1
isKeyword "Refl"    = Just 0
isKeyword "jRule"   = Just 3
isKeyword "kRule"   = Just 3
isKeyword "record"  = Just 2
isKeyword "Wrap"    = Just 1
isKeyword _         = Nothing

isVariable : String -> Bool
isVariable s = isAlphaToken s & \where
  False -> False
  True  -> isKeyword s & \where
    Nothing -> True
    _       -> False

isVariableTrue : {s : _} -> (isAlphaToken s ~ True) -> (isKeyword s ~ Nothing) -> isVariable s ~ True
isVariableTrue _ _ = believeMe~

data Doc : Set where
  FFI   : String ->                                                                     Doc
  KW    : (s : String) {n : Nat} -> {{e : isKeyword s ~ Just n}} -> Vec Doc n ->        Doc
  Var   : (s : String) -> {{isVariable s ~ True}} ->                                    Doc
  _[_]_ : Doc -> (s : String) {n : Pair Nat Nat} -> {{isOperator s ~ Just n}} -> Doc -> Doc

pattern _$d_ d d' = d [ " " ] d'

-------------------------------------

showDoc : Doc -> StringBuilder
showDoc = go 0 0  where

  parens : Bool -> StringBuilder -> StringBuilder
  parens True  a = "(" <> a <> ")"
  parens False a =        a

  renderOp : String -> StringBuilder
  renderOp " " = " "
  renderOp s   = " " <> fromString s <> " "

  precOk : Nat -> Nat -> Nat -> Nat -> Bool
  precOk p q q' p' = _<_ p q & \where
    True  -> _<_ p' q'
    False -> False

  go : Nat -> Nat -> Doc -> StringBuilder
  go p p' (FFI s)     = fromString s
  go p p' (KW n args) = go p p' (foldl _$d_ (FFI n) (vecToList args))
  go p p' (Var n)     = fromString n
  go p p' (_[_]_ a s {n = (q , q')} b) = precOk p q q' p' & \where
    True  ->              go p q a <> renderOp s <> go q' p' b
    False -> parens True (go 0 q a <> renderOp s <> go q' 0  b)

showDoc' : Doc -> String
showDoc' d = runStringBuilder (showDoc d)

testShowDoc : showDoc' ((Var "a" [ "." ] Var "a" $d Var "b") $d (Var "c" $d Var "e") $d Var "d" $d (Var "a" [ "." ] Var "b" [ "." ] Var "a"))
        ~ "(a . a b) (c e) d (a . b . a)"
testShowDoc = Refl

testShowDoc' : showDoc' ((Var "a" [ "*" ] Var "a" $d Var "b" [ "*" ] Var "b") $d Var "d" [ "*" ] Var "f" $d (Var "c" [ "*" ] Var "e"))
        ~ "(a * a b * b) d * f (c * e)"
testShowDoc' = Refl

testShowDoc'' : showDoc' (KW "Pi" (Var "A" :: Var "B" :: []))
        ~ "Pi A B"
testShowDoc'' = Refl

---------------------

_[_]m_ : {{Monad M}} -> M Doc -> (s : String) {n : Pair Nat Nat} -> {{isOperator s ~ Just n}} -> M Doc -> M Doc
_[_]m_ a s b = do
  a <- a
  b <- b
  pure (a [ s ] b)

infixl 9 _$m_

_$m_ : {{Monad M}} -> M Doc -> M Doc -> M Doc
a $m b = (| a $d b |)

KWm : {{Monad M}} -> (s : String) {n : Nat} -> {{e : isKeyword s ~ Just n}} -> Vec (M Doc) n -> M Doc
KWm s ds = do
  ds <- mapMV (\x -> x) ds
  pure (KW s ds)

----------

pattern Paren a = KW "Paren" (a :: [])


parse : {{MonadError StringBuilder M}} -> String -> M Doc
parse {M} s = tokens' s >>= parseOps end  where

  X = List String -> M Doc

  end : Doc -> X
  end d [] = pure d
  end d ts  = throwError ("End expected instead of  " <> showTokens ts)

  expect : String -> X -> X
  expect t r (t' :: ts) = t' == t & \where
    True  -> r ts
    False -> throwError (fromString t <> " expected instead of " <> showTokens (t' :: ts))
  expect t _ [] = throwError (fromString t <> " expected instead of end")

  parseOps : (Doc -> X) -> X

  parseAtom : ((n : Nat) -> (Vec Doc n -> Doc) -> X) -> X -> X
  parseAtom r _ ("(" :: ts) = parseOps (\b -> expect ")" (r 0 \_ -> KW "Paren"   (b :: []))) ts
  parseAtom r _ ("[" :: ts) = parseOps (\b -> expect "]" (r 0 \_ -> KW "Bracket" (b :: []))) ts
  parseAtom r _ ("{" :: ts) = parseOps (\b -> expect "}" (r 0 \_ -> KW "Brace"   (b :: []))) ts
  parseAtom r z ("FFI" :: t :: ts) = r 0 (\_ -> FFI t) ts
  parseAtom r z (t :: ts) = isKeyword t &in \where
    (Just n) e -> r n (KW t {{e}}) ts
    Nothing  e -> isAlphaToken t &in \where
      True e' -> r 0 (\_ -> Var t {{isVariableTrue e' e}}) ts
      False _ -> z (t :: ts)
  parseAtom _ z ts = z ts

  parseAtom0 : (Doc -> X) -> X -> X
  parseAtom0 r z = parseAtom f z  where
    f : (n : Nat) -> (Vec Doc n -> Doc) -> X
    f 0 d = r (d [])
    f _ _ = z

  parseApps : (Doc -> X) -> X
  parseApps r = parseAtom (f r) \ts -> throwError ("unknown token at  " <> showTokens ts)  where

    f : (Doc -> X) -> (n : Nat) -> (Vec Doc n -> Doc) -> X
    f r 0       a ts = parseAtom0 (\b -> f r 0 \ds -> a [] $d b) (r (a [])) ts
    f r (Suc n) a ts = parseAtom0 (\b -> f r n \ds -> a (b :: ds)) (\ts -> throwError ("argument expected at " <> showTokens ts)) ts

  mkPi : Doc -> Doc -> Doc -> Doc
  mkPi (ns [ " " ] n) a b = mkPi ns a (KW "Pi" (a :: (_[_]_ n "." {{Refl}} b) :: []))
  mkPi n a b = KW "Pi" (a :: (n [ "." ] b) :: [])

  mkSigma : Doc -> Doc -> Doc -> Doc
  mkSigma (ns $d n) a b = mkSigma ns a (KW "Sigma" (a :: (_[_]_ n "." {{Refl}} b) :: []))
  mkSigma n a b = KW "Sigma" (a :: (n [ "." ] b) :: [])

  mkOp : (s : String) {n : Pair Nat Nat} -> {{isOperator s ~ Just n}} -> Doc -> Doc -> M Doc
  mkOp "$" a b = pure (a $d b)
  mkOp "->" (bs $d Paren (n [ ":" ] a)) b = mkOp "->" {{Refl}} bs (mkPi n a b)
  mkOp "->" (Paren (n [ ":" ] a)) b = pure (mkPi n a b)
  mkOp "*" (bs $d Paren (n [ ":" ] a)) b = mkOp "*" {{Refl}} bs (mkSigma n a b)
  mkOp "*" (Paren (n [ ":" ] a)) b = pure (mkSigma n a b)
  mkOp "." (ns $d n) b = mkOp "." {{Refl}} ns (_[_]_ n "." {{Refl}} b)
  mkOp "." n b = pure (n [ "." ] b)
  mkOp t a b = pure (a [ t ] b)

  addOp : String -> ((Doc -> X) -> X) -> (Doc -> X) -> X
  addOp op g r = isOperator op &in \where
    Nothing _ -> g r
    (Just _) e -> g (f e r)
   where

    f : {p : _} -> (isOperator op ~ Just p) -> (Doc -> X) -> Doc -> X
    f e r a (t' :: ts) = t' == op & \where
      True  -> addOp op g (\b ts -> mkOp op {{e}} a b >>= \o -> r o ts) ts
      False -> r a (t' :: ts)
    f e r a ts = r a ts

  parseOps = foldr addOp parseApps operators'

optEq : Doc -> Doc
optEq (Paren d)     = optEq d
optEq  a            = a

testParse : parse "f (b a * c * e) d"
          ~ Just (Var "f" $d KW "Paren" ((Var "b" $d Var "a" [ "*" ] Var "c" [ "*" ] Var "e") :: []) $d Var "d")
testParse = Refl
