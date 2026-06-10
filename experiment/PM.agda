
{-# OPTIONS --with-K --type-in-type --no-positivity-check --no-termination-check --prop --rewriting --hidden-argument-puns #-}

open import Agda.Builtin.String

variable a a' a'' : Set
variable b  : a  -> Set
variable b' : a' -> Set

data _~_ (x : a) : a -> Prop where
  instance refl : x ~ x
{-# BUILTIN REWRITE _~_ #-}

postulate                      coe : a ~ a' -> a -> a'
postulate coeRefl : {x : a} -> coe refl x ~ x
{-# REWRITE coeRefl #-}

infixr 3 _<>_

_<>_ : String -> String -> String
_<>_ = primStringAppend

Name = String

variable n n' : Name

------------------------------------------------------

infixl 9 _$u_
infixl 9 _$_
infixr 2 _||_

data Form : Set where
   SL   : Form        -- StrictLHS
   L    : Form        -- LHS
   S    : Form        -- Spine
   N    : Form        -- Neutral
   R    : Form        -- RHS 
   _⊎F_ : Form -> Form -> Form

LR = L ⊎F R
NR = N ⊎F R

variable F : Form

data TyNotU : Form -> Set
data TmNotU : Form -> TyNotU R -> Set

data Ty : Form -> Set where
  U    :             Ty R
  NotU : TyNotU F -> Ty F

TyR  = Ty R

variable A A' A'' : TyR

Tm : Form -> TyR -> Set
Tm F  U       = Ty     F      -- "Bálint Török" style equality
Tm F (NotU a) = TmNotU F a

TmR  = Tm R
TmSL = Tm SL

-- General constructions for both TmNotU and TyNotU
data TmG : Form -> TyR -> Set

TmL  = TmG L
TmLR = TmG LR
TmNR = TmG NR
TmS  = TmG S
TmN  = TmG N

data TyNotU where
  Bool#      :                                                      TyNotU R
  _=>U#      : TyR ->                                               TyNotU R
  Pi# Sigma# : (A : TyR) -> TmR (NotU (A =>U#)) ->                  TyNotU R
  Id#        : TmR A -> TmR A ->                                    TyNotU R
  Record#    : Name -> (A : TyR) -> TmR (NotU (A =>U#)) -> TmR A -> TyNotU R
  GU#        :                                           TmG F U -> TyNotU F

pattern Bool           = NotU Bool#
pattern _=>U A         = NotU (A =>U#)
pattern Pi    A B      = NotU (Pi#    A B)
pattern Sigma A B      = NotU (Sigma# A B)
pattern Id    x y      = NotU (Id#    x y)
pattern Record n A B x = NotU (Record# n A B x)
pattern GU A           = NotU (GU# A)

variable B : TmR (A =>U)

_$u_ : TmR (A =>U) -> TmR A -> TmR U

nrToR : TmNR A -> TmR A

data TmNotU where
  True   :                TmR Bool
  False  :                TmR Bool
  Refl   : {x : TmR A} -> TmR (Id x x)
  LamU   : (     TmR A  -> TmNR  U     ) ->       TmSL (A =>U)
  Lam    : ((x : TmR A) -> TmNR (B $u x)) ->      TmSL (Pi    A B)
  _,_    : (x : TmNR A) -> TmNR (B $u nrToR x) -> TmSL (Sigma A B)
  Wrap   : {x : TmR A}  -> TmNR (B $u x) ->       TmSL (Record n A B x)
  GNotU  :             {A : _} -> TmG F (NotU A) -> Tm F (NotU A)

fst : TmR (Sigma A B) -> TmR A

Glued : TmS A -> TmL A -> Prop

data TmG where
  Neut   :          TmN A -> TmG R A
  Stuck  :                     TmL A
  Fail   :                     TmL A
  Or     : TmSL A -> TmLR A -> TmL A
  Strict : TmSL A ->           TmL A
  LHS    :               TmG F A -> TmG (F ⊎F R) A
  RHS    :               TmR   A -> TmG (F ⊎F R) A
  AppU   : TmR (A =>U)  ->      TmR A ->           TmS  U
  App    : TmR (Pi A B) -> (x : TmR A) ->          TmS (B $u x)
  Fst    :      TmR (Sigma A B) ->                 TmS  A
  Snd    : (x : TmR (Sigma A B)) ->                TmS (B $u fst x)
  Proj   : {x : TmR A} -> TmR (Record n A B x) ->  TmS (B $u x)
  Def    :                       Name -> TmNR A -> TmS  A
  Glue   :   (s : TmS A) (x : TmL A) -> Glued s x -> TmN A

sToLR : TmS  A -> TmLR A

Glued s x = sToLR s ~ LHS x

pattern GlueU    s l e = GU    (Neut (Glue s l e))
pattern GlueNotU s l e = GNotU (Neut (Glue s l e))
pattern GlueLHS  s l e = LHS         (Glue s l e)

nrToR              (RHS x)         = x
nrToR {A = U     } (GlueLHS s l e) = GlueU    s l e
nrToR {A = NotU _} (GlueLHS s l e) = GlueNotU s l e

sToR : TmS A -> TmR A
sToR s = glue s (sToLR s) refl  where

  glue : (s : TmS A) (lr : TmLR A) -> sToLR s ~ lr -> TmR A
  glue              s (RHS r) e = r
  glue {A = U}      s (LHS l) e = GlueU    s l e
  glue {A = NotU _} s (LHS l) e = GlueNotU s l e

f $u x = sToR (AppU f x)

_$_ : TmR (Pi A B) -> (x : TmR A) -> TmR (B $u x)
f $ x = sToR (App f x)

proj : {x : TmR A} -> TmR (Record n A B x) -> TmR (B $u x)
proj x = sToR (Proj x)

fst x = sToR (Fst x)

snd : (x : TmR (Sigma A B)) -> TmR (B $u fst x)
snd x = sToR (Snd x)

def : Name -> TmNR A -> TmR A
def n lr = sToR (Def n lr)

nrToLR : TmNR A -> TmLR A
nrToLR (GlueLHS _ l _) = LHS l
nrToLR (RHS x)         = RHS x

_||_ : TmLR A -> TmLR A -> TmLR A
RHS x          || _ = RHS x
LHS Stuck      || _ = LHS Stuck
LHS Fail       || x = x
LHS (Strict l) || x = LHS (Or l x)
LHS (Or a b)   || x = LHS (Or a (b || x))

mapLR : (TmSL A -> TmNR A') -> (TmR A -> TmR A') -> TmL A -> TmLR A'
mapLR f g Stuck           = LHS Stuck
mapLR f g Fail            = LHS Fail
mapLR f g (Strict x)      = nrToLR (f x)
mapLR f g (Or x (RHS x')) = nrToLR (f x) || RHS (g x')
mapLR f g (Or x (LHS x')) = nrToLR (f x) || mapLR f g x'

postulate believeMeTm : Tm F A ~ Tm F A'
postulate believeMeTmG : TmG F A ~ TmG F A'
postulate believeMe : {a : Set} {x y : a} -> x ~ y

mapLR-Sigma : (p : TmR (Sigma A B)) -> TmLR (B $u fst p)
mapLR-Sigma (GlueNotU _ Stuck _)                 = LHS Stuck
mapLR-Sigma (GlueNotU _ Fail  _)                 = LHS Fail
mapLR-Sigma (GlueNotU _ (Strict (x , y))      _) = nrToLR (coe believeMeTmG y)  
mapLR-Sigma (GlueNotU s (Or (x , y) (LHS x')) _) = nrToLR (coe believeMeTmG y) || coe believeMeTmG (mapLR-Sigma (GlueNotU s x' believeMe))
mapLR-Sigma (GlueNotU _ (Or (x , y) (RHS x')) _) = nrToLR (coe believeMeTmG y) || RHS (coe believeMeTm (snd x'))

sToLR (AppU (GlueNotU _ f _) x) = mapLR (\{(LamU f) -> f x}) (\f -> f $u x) f
sToLR (App  (GlueNotU _ f _) x) = mapLR (\{(Lam  f) -> f x}) (\f -> f $  x) f
sToLR (Fst  (GlueNotU _ x _)  ) = mapLR (\{(x , _)  -> x  })  fst           x
sToLR (Proj (GlueNotU _ x _)  ) = mapLR (\{(Wrap x) -> x  })  proj          x
sToLR (Snd  x                 ) = mapLR-Sigma x
sToLR (Def _ x                ) = nrToLR x

jRule : {x y : TmR A}
  (tm : TmR (Id x y)) ->
  (P : (y : TmR A) -> TmR (Id x y) -> TyR) ->
  TmLR (P x Refl) -> TmLR (P y tm)
jRule Refl      P l = l
jRule (GNotU x) P l = LHS Stuck

kRule : {x : TmR A}
  (tm : TmR (Id x x)) ->
  (P : TmR (Id x x) -> TyR) ->
  TmLR (P Refl) -> TmLR (P tm)
kRule Refl      P l = l
kRule (GNotU x) P l = LHS Stuck

matchFalse : (x : TmR Bool) -> (TmR (Id False x) -> TmLR A) -> TmLR A
matchFalse False            f = f Refl
matchFalse True             f = LHS Fail
matchFalse (GlueNotU _ _ _) f = LHS Stuck

matchTrue : (x : TmR Bool) -> (TmR (Id True x) -> TmLR A) -> TmLR A
matchTrue True             f = f Refl
matchTrue False            f = LHS Fail
matchTrue (GlueNotU _ _ _) f = LHS Stuck

fail : TmLR A
fail = LHS Fail

wrap : {x : TmR A} -> TmNR (B $u x) -> TmLR (Record n A B x)
wrap y = LHS (Strict (Wrap y))

lamU : (TmR A -> TmNR U) -> TmLR (A =>U)
lamU f = LHS (Strict (LamU f))

lam : ((x : TmR A) -> TmNR (B $u x)) -> TmLR (Pi A B)
lam f = LHS (Strict (Lam f))

pairL : (x : TmNR A) -> TmNR (B $u nrToR x) -> TmLR (Sigma A B)
pairL x y = LHS (Strict (x , y))

---------------------------------- printing

infixl 9 _$d_

data Doc : Set where
  Var  : Name ->       Doc
  _$d_ : Doc -> Doc -> Doc

render : Doc -> String
render (Var n) = n
render (f $d x) = render f <> " " <> renderArg x  where

  renderArg : Doc -> String
  renderArg (Var n) = n
  renderArg (f $d x) = "(" <> render f <> " " <> renderArg x <> ")"

-- TODO: eta printing in the name generating monad
printTmS : TmS A -> Doc

printTmR : TmR A -> Doc
printTmR {A = U} U                = Var "U"
printTmR {A = U} Bool             = Var "Bool"
printTmR {A = U} (A =>U)          = Var "Fam"    $d printTmR A
printTmR {A = U} (Pi    A B)      = Var "Pi"     $d printTmR A $d printTmR B
printTmR {A = U} (Sigma A B)      = Var "Sigma"  $d printTmR A $d printTmR B
printTmR {A = U} (Id x y)         = Var "Id"     $d printTmR x $d printTmR y
printTmR {A = U} (Record n A B x) = Var  n       $d printTmR x
printTmR {A = U} (GlueU x _ _)    = printTmS x
printTmR {A = NotU _} False             = Var "False"
printTmR {A = NotU _} True              = Var "True"
printTmR {A = NotU _} Refl              = Var "Refl"
printTmR {A = NotU _} (GlueNotU x _ _)  = printTmS x

printTmS (Def n _)                 = Var n
printTmS (Proj (GlueNotU x _ _)  ) = Var "Proj"  $d printTmS x
printTmS (Fst  (GlueNotU x _ _)  ) = Var "Fst"   $d printTmS x
printTmS (Snd  (GlueNotU x _ _)  ) = Var "Snd"   $d printTmS x
printTmS (AppU (GlueNotU f _ _) x) = printTmS f  $d printTmR x
printTmS (App  (GlueNotU f _ _) x) = printTmS f  $d printTmR x

show : TmR A -> String
show t = render (printTmR t)

---------------------------------

postulate impossible : {a : Set} -> a

getNeut : TmR A -> TmS A
getNeut {A = U     } (GlueU    s _ _) = s
getNeut {A = NotU _} (GlueNotU s _ _) = s
getNeut _ = impossible

infix 0 _#_

_#_ : TmR A -> TmLR A -> TmNR A
n # LHS l = (GlueLHS (getNeut n) l believeMe)
_ # RHS r = RHS r


module Examples where  

  const : {A : TyR} -> TyR -> TmR (A =>U)
  const A' = const' $ _ $ A'  where

    constTy'' : TmR (U =>U)
    constTy'' = def "constTy''" (constTy'' # lamU \_ -> RHS (U =>U))

    constTy' : TmR (Pi U constTy'')
    constTy' = def "constTy'" (constTy' # lam \A -> constTy' $ A # lamU \_ -> RHS (A =>U))

    constTy : TmR (U =>U)
    constTy = def "constTy" (constTy # lamU \A -> RHS (Pi U (constTy' $ A)))

    const' : TmR (Pi U constTy)
    const' = def "const" (const' # lam \A -> const' $ A # lam \A' -> const' $ A $ A' # lamU \_ -> RHS A')

  infixr 3 _=>_

  _=>_ : TyR -> TyR -> TyR
  A => A' = Pi A (const A')

  arrU : TmR (A => U) -> TmR (A =>U)
  arrU B = arrU' $ _ $ B   where

    arrUTy : TmR (U =>U)
    arrUTy = def "arrUTy" (arrUTy # lamU \A -> RHS ((A => U) => (A =>U)))

    arrU' : TmR (Pi U arrUTy)
    arrU' = def "arrU" (arrU' # lam \A -> arrU' $ A # lam \f -> arrU' $ A $ f # lamU \x -> RHS (f $ x))

  Pi' : (A : TyR) (B : TmR (A => U)) -> Ty R
  Pi' A B = Pi A (arrU B)

  Sigma' : (A : TyR) (B : TmR (A => U)) -> Ty R
  Sigma' A B = Sigma A (arrU B)

  Record' : (n : Name) (A : TyR) (B : TmR (A => U)) (x : TmR A) -> Ty R
  Record' n A B x = Record n A (arrU B) x

  _×_ : TyR -> TyR -> TyR
  A × A' = Sigma A (const A')

  topTy : TmR (U =>U)
  topTy = def "topTy" (topTy # lamU \A -> RHS (A => A))

  Top : TyR
  Top = Pi U topTy

  tt : TmR Top
  tt = def "TT" (tt # lam \A -> tt $ A # lam \a -> RHS a)


  pairTy'' : TmR (U =>U)
  pairTy'' = def "pairTy''" (pairTy'' # lamU \A -> RHS ((A =>U) =>U))

  pairTy'LamTy : TmR (U =>U)
  pairTy'LamTy = def "pairTy'LamTy" (pairTy'LamTy # lamU \A -> RHS (Pi (A =>U) (const (A =>U))))

  pairTy'Lam : TmR (Pi U pairTy'LamTy)
  pairTy'Lam = def "pairTy'Lam" (pairTy'Lam # lam \A -> pairTy'Lam $ A # lam \B -> pairTy'Lam $ A $ B # lamU \x -> RHS (B $u x => Sigma A B))

  pairTy' : TmR (Pi U pairTy'')
  pairTy' = def "pairTy'" (pairTy' # lam \A -> pairTy' $ A # lamU \B -> pairTy' $ A $u B # RHS (Pi A (pairTy'Lam $ A $ B)))

  pairTy : TmR (U =>U)
  pairTy = def "pairTy" (pairTy # lamU \A -> RHS (Pi (A =>U) (pairTy' $ A)))

  pair' : TmR (Pi U pairTy)
  pair' = def "pair" (pair' # lam \A -> pair' $ A # lam \B -> pair' $ A $ B # lam \x -> pair' $ A $ B $ x # lam \y -> pair' $ A $ B $ x $ y # pairL (RHS x) (RHS y))

  pair : (x : TmR A) -> TmR (B $u x) -> TmR (Sigma A B)
  pair x y = pair' $ _ $ _ $ x $ y

  ite : TmR (U => U => (Bool =>U))
  ite = def "ite" (ite # lam \A -> ite $ A # lam \A' -> ite $ A $ A' # lamU \b -> ite $ A $ A' $u b #
            (matchFalse b \_ -> RHS A )
         || (matchTrue  b \_ -> RHS A')
    )

  _⊎_ : TyR -> TyR -> TyR
  A ⊎ A' = Sigma Bool (ite $ A $ A')

  Left : TmR A -> TmR (A ⊎ A')
  Left a = pair False a

  Right : TmR A' -> TmR (A ⊎ A')
  Right a = pair True a

  matchLeft : (x : TmR (A ⊎ A')) -> ((l : TmR A) -> TmR (Id (Left l) x) -> TmLR A'') -> TmLR A''
  matchLeft {A} {A'} x f = matchFalse (fst x) \e -> f (coe believeMe (snd x)) (coe believeMe (Refl {A = A ⊎ A'} {x = x}))

  matchRight : (x : TmR (A ⊎ A')) -> ((l : TmR A') -> TmR (Id (Right l) x) -> TmLR A'') -> TmLR A''
  matchRight {A} {A'} x f = matchTrue (fst x) \e -> f (coe believeMe (snd x)) (coe believeMe (Refl {A = A ⊎ A'} {x = x}))

  Newtype : Name -> TyR -> TyR
  Newtype n A = Record n Top (const A) tt

  ------------------------

  Nat : TyR
  Nat = Newtype "Nat" (Top ⊎ Nat)

  Zero : TmR Nat
  Zero = def "Z" (Zero # wrap (RHS (Left {A = Top} tt)))

  Suc' : TmR (Nat => Nat)
  Suc' = def "S" (Suc' # lam \n -> Suc' $ n # wrap (RHS (Right {A' = Nat} n)))

  Suc : TmR Nat -> TmR Nat
  Suc n = Suc' $ n

  {-
  add : Nat -> Nat -> Nat
  add = { n. m. proj n => Left  _ $ m
        ; n. m. proj n => Right n $ Suc (add n m)
        }
  -}
  add' : TmR (Nat => Nat => Nat)
  add' = def "add" ( add' #
              (lam \n -> add' $ n # lam \m -> add' $ n $ m # matchLeft  (proj n) \_ _ -> RHS m)
           || (lam \n -> add' $ n # lam \m -> add' $ n $ m # matchRight (proj n) \n _ -> RHS (Suc (add' $ n $ m)))
         )

  add : TmR Nat -> TmR Nat -> TmR Nat
  add n m = add' $ n $ m

  testAdd : add (Suc Zero) (Suc Zero) ~ Suc (Suc Zero)
  testAdd = refl

  postulated : TmR Nat
  postulated = def "n" (postulated # fail)

  testAdd' : show (add postulated (Suc Zero)) ~ "add n (S Z)"
  testAdd' = refl

  testAdd'' : show (add' $ Suc Zero) ~ "add (S Z)"
  testAdd'' = refl

  testAdd''' : show add' ~ "add"
  testAdd''' = refl

  Stream : TyR -> TyR

  StreamFun : TmR (U => U)
  StreamFun = def "StreamFun" (StreamFun # lam \A -> RHS (A × Stream A))

  Stream = Record' "Stream" U StreamFun

  headTy : TmR (U => U)
  headTy = def "headTy" (headTy # lam \A -> RHS (Stream A => A))

  head' : TmR (Pi' U headTy)
  head' = def "head" (head' # lam \A -> head' $ A # lam \s -> RHS (fst (proj s)))

  head : TmR (Stream A) -> TmR A
  head s = head' $ _ $ s

  tailTy : TmR (U => U)
  tailTy = def "tailTy" (tailTy # lam \A -> RHS (Stream A => Stream A))

  tail' : TmR (Pi' U tailTy)
  tail' = def "tail" (tail' # lam \A -> tail' $ A # lam \s -> RHS (snd (proj s)))

  tail : TmR (Stream A) -> TmR (Stream A)
  tail s = tail' $ _ $ s

  map' : TmR ((Nat => Nat) => Stream Nat => Stream Nat)
  map' = def "map" (map' # lam \f -> map' $ f # lam \s -> map' $ f $ s # wrap (proj (map' $ f $ s) # pairL (RHS (Suc' $ (f $ fst (proj s)))) (RHS (map' $ f $ snd (proj s)))))

  repeat' : TmR (Nat => Stream Nat)
  repeat' = def "repeat" (repeat' # lam \x -> repeat' $ x # wrap (proj (repeat' $ x) # pairL (RHS x) (RHS (repeat' $ x))))

  repeat : TmR Nat -> TmR (Stream Nat)
  repeat x = repeat' $ x

  from' : TmR (Nat => Stream Nat)
  from' = def "from" (from' # lam \x -> from' $ x # wrap (proj (from' $ x) # pairL (RHS x) (RHS (from' $ Suc x))))

  from : TmR Nat -> TmR (Stream Nat)
  from x = from' $ x

  comp : TmR ((Nat => Nat) => (Nat => Nat) => Nat => Nat)
  comp = def "comp" (comp # lam \f -> comp $ f # lam \g -> comp $ f $ g # lam \x -> RHS (f $ (g $ x)))

  nats = from Zero

  testSucNats : show (tail (tail (map' $ (add' $ Suc (Suc Zero)) $ nats)))
              ~ "map (add (S (S Z))) (from (S (S Z)))"
  testSucNats = refl

  argFun : TmR (Bool => U)
  argFun = def "argFun" (argFun #
        (lam \b -> argFun $ b # matchFalse b \_ -> RHS Bool)
     || (lam \b -> argFun $ b # matchTrue  b \_ -> RHS (Bool => Bool))
    )

  {-
  varArg : (b : Bool) -> if b then Bool -> Bool else Bool
  varArg False = False
  varArg True False = True
  varArg True True  = False
  -}

  varArg : TmR (Pi' Bool argFun)
  varArg = def "varArg" (varArg #
        (lam \b -> varArg $ b # matchFalse b \e -> jRule e (\y _ -> argFun $ y) (RHS False))
     || (lam \b -> varArg $ b # matchTrue  b \e -> jRule e (\y _ -> argFun $ y) (lam \c -> varArg $ True $ c # matchFalse c \_ -> RHS True))
     || (lam \b -> varArg $ b # matchTrue  b \e -> jRule e (\y _ -> argFun $ y) (lam \c -> varArg $ True $ c # matchTrue  c \_ -> RHS False))
    )

  testVarArg : show (varArg $ False) ~ "False"
  testVarArg = refl

  testVarArg' : show (varArg $ True) ~ "varArg True"
  testVarArg' = refl

  testVarArg'' : show (varArg $ True $ True) ~ "False"
  testVarArg'' = refl

  testVarArg''' : show (varArg $ True $ False) ~ "True"
  testVarArg''' = refl

