{-# OPTIONS --type-in-type --no-positivity-check --rewriting --prop --injective-type-constructors --hidden-argument-puns --erasure --with-K --no-termination-check #-}

open import Prelude
open import Parser

postulate impossible1 impossible2 impossible3 impossible4 impossible5 impossible6 : A
postulate TODO1 TODO2 TODO3 TODO4 TODO5 TODO6 TODO7 TODO8 TODO9 : A

------------------------------------------------------

data Con : Set

variable    G* G*' G*'' : Con
variable @0 G  G'  G''  : Con

data Ty : @0 Con -> Set

variable    a* a*' a*'' : Ty G
variable @0 a  a'  a''  : Ty G

record FreeVar (@0 a : Ty G) : Set     -- name which does not occur in the context

variable    v* v*' v*'' : FreeVar a
variable @0 v  v'  v''  : FreeVar a

{-# ETA_EQUALITY #-}
record FreeVar' (@0 G : Con) : Set where
  inductive
  constructor FV
  field
    {fvTy} : Ty G
    fv     : FreeVar fvTy

open FreeVar' public

variable    w* w*' w*'' : FreeVar' G
variable @0 w  w'  w''  : FreeVar' G

infixl 4 _>>_
data Con where
  []   :                            Con
  _>>_ : (G : Con) -> FreeVar' G -> Con

data TmR : @0 Ty G -> Set    -- terms which are not U

-- types = {U; U-typed terms witch are not U}
data Ty where
  U  :                Ty G
  El : TmR (U {G}) -> Ty G

----------

-- terms = {types; terms witch are not types}
@0 Tm : Ty G -> Set
Tm (U {G}) = Ty G               -- "Bálint Török" style equality
Tm (El a)  = TmR (El a)

rToTm : TmR a* -> Tm a*
rToTm {a* = U   } x = El x
rToTm {a* = El _} x =    x

------------

-- erased De-Bruijn index
data @0 OccursIn : @0 Name -> @0 Con -> Prop

record FreeVar {G} a where
  coinductive
  field
    varName       : Name
    @0 varIsFresh : OccursIn varName G -> bot

open FreeVar public

instance
  HasName[FreeVar] : HasName (FreeVar a)
  HasName[FreeVar] .nameOf = varName

instance
  HasName[FreeVar'] : HasName (FreeVar' G)
  HasName[FreeVar'] .nameOf w = varName (fv w)

data OccursIn where
  Here  : @0 (nameOf v ~ n) -> OccursIn n (G >> w)
  There : OccursIn n G ->      OccursIn n (G >> w)

postulate @0 believeMeFresh : OccursIn n G -> bot

newFreeVar : {{MonadSupply M}} -> NameStr -> M (FreeVar {G} a)
newFreeVar s = do
  n <- newName s
  pure (record {varName = n; varIsFresh = believeMeFresh})

newFreeVar'' : {{MonadSupply M}} -> NameStr -> M (FreeVar' G ** \w -> fvTy w ~e' a*)
newFreeVar'' s = do
  v <- newFreeVar s
  pure (FV v , refl)

builtinFreeVar : (s : string) -> @0 {{tokenClass (MkToken NoLoc s) ~ just Var}} -> nat -> FreeVar a
builtinFreeVar s n = record {varName = builtinName s n; varIsFresh = believeMeFresh}

@0 GlobalVar : @0 Ty [] -> Set
GlobalVar a = FreeVar a


------------ substitutions

data Sub' (@0 G : Con) : @0 Con -> Set

@0 Sub : @0 Con -> @0 Con -> Set
Sub G G' = Sub' G' G

_[_]u : Ty G -> Sub G G' -> Ty G'

_[_]r : TmR a -> (xs : Sub G G') -> Tm (a [ xs ]u)

U    [ xs ]u = U
El a [ xs ]u = a [ xs ]r

infixl 10 _[_]
_[_] : Tm a* -> (xs : Sub G G') -> Tm (a* [ xs ]u)
_[_] {a* = U   } a xs = a [ xs ]u
_[_] {a* = El _} a xs = a [ xs ]r

data Sub' G where
  tt  : Sub' G []
  _,_ : (xs : Sub' G G') -> Tm {G} (fvTy w* [ xs ]u) ->  Sub' G (G' >> w*)

fstSub : Sub' G (G' >> w) -> Sub' G G'
fstSub (xs , _) = xs

infixr 8 _`comp`_
_`comp`_ : Sub G G' -> Sub G' G'' -> Sub G G''

postulate @0 ssU : (a : Ty G) {xs : Sub G G'} {xs' : Sub G' G''} -> a [ xs ]u [ xs' ]u ~ a [ xs `comp` xs' ]u

_`comp`_ tt _ = tt
_`comp`_ (_,_ {w*} xs x) xs' = xs `comp` xs' , subst (\a -> Tm a) (ssU (fvTy w*)) (x [ xs' ])

-- TODO: remove?
trFreeVar : (@0 f : Ty G -> Ty G') -> FreeVar a -> FreeVar (f a)
trFreeVar f v = record {varName = varName v; varIsFresh = believeMeFresh}

-- TODO: remove?
trFreeVar' : (Ty G -> Ty G') -> FreeVar' G -> FreeVar' G'
trFreeVar' f (FV {fvTy} v) = FV {fvTy = f fvTy} (record {varName = varName v; varIsFresh = believeMeFresh})


--------------------

idSub : Sub G* G*

weakenSubTr : Sub G G' -> Sub G (G' >> w)
weakenSubTr = coe (_ ~! _)

weakenSub : Sub G* (G* >> w)
weakenSub = weakenSubTr idSub

weakenSub2 : Sub G* (G* >> w >> w')
weakenSub2 = weakenSubTr weakenSub

weakenSub3 : Sub G* (G* >> w >> w' >> w'')
weakenSub3 = weakenSubTr weakenSub2

-- unsafe
strengthenSub : Sub (G* >> w*) G*
strengthenSub {w*} = _,_ {w* = w*} idSub impossible1

postulate @0 compIdSub : {xs : Sub G G'} -> xs `comp` idSub ~ xs
postulate @0 idSubComp : {xs : Sub G G'} -> idSub `comp` xs ~ xs

postulate @0 compWeakenSub' : {xs : Sub G G'} {ys : Sub G' G''} -> xs `comp` weakenSubTr {w = w} ys ~ weakenSubTr (xs `comp` ys)

@0 compWeakenSub : {xs : Sub G G'} -> xs `comp` weakenSub {w = w} ~ weakenSubTr xs
compWeakenSub {xs} = compWeakenSub' *~ cong weakenSubTr compIdSub

--------------------

infixl 10 _[_]nop
_[_]nop  : Tm {G} a -> (@0 xs : Sub G G') -> Tm (nopCompiled (\a -> a [ xs ]) a)
x [ s ]nop = nopCompiled (\x -> x [ s ]) x

infixl 10 _[_]Nop
_[_]Nop  : Tm {G} a -> (@0 xs : Sub G G') -> Tm (a [ xs ]nop)
x [ s ]Nop = coe (_ ~! _) x

lift : Tm a -> Tm {G} (a [ tt ]nop)
lift x = x [ tt ]nop

liftNop : Tm a -> Tm {G} (a [ tt ]nop)
liftNop x = x [ tt ]Nop

weaken : Tm {G} a -> Tm {G >> w} (a [ weakenSub ]nop)
weaken x = x [ weakenSub ]nop

weakenNop : Tm {G} a -> Tm {G >> w} (a [ weakenSub ]nop)
weakenNop x = x [ weakenSub ]Nop

freeVarToTm : (v : FreeVar {G} a*) -> Tm {G >> FV {fvTy = a*} v} (weaken a*)

freeVarToTm' : (w : FreeVar' G) -> Tm {G >> w} (weaken (fvTy w))
freeVarToTm' w = freeVarToTm (fv w)

idSub {G* = []} = tt
idSub {G* = G >> v} = weakenSub , freeVarToTm' v

weaken2 : Tm {G} a -> Tm {G >> w >> w'} (a [ weakenSub2 ]nop)
weaken2 x = x [ weakenSub2 ]nop

weaken3 : Tm {G} a -> Tm {G >> w >> w' >> w''} (a [ weakenSub3 ]nop)
weaken3 x = x [ weakenSub3 ]nop

strengthen : Tm {G >> w} a -> Tm {G} (a [ strengthenSub {w* = w} ]nop)
strengthen {w} x = x [ strengthenSub {w* = w} ]nop

strengthenNop : Tm {G >> w} a -> Tm {G} (a [ strengthenSub {w* = w} ]nop)
strengthenNop {w} x = x [ strengthenSub {w* = w} ]Nop

postulate @0 [][] : a [ tt ] ~ a

-- TODO: require witness that varName is fresh in the extended context
weakenFreeVar : FreeVar {G} a -> FreeVar (weaken {w = w} a)
weakenFreeVar = trFreeVar weaken

weakenFreeVar' : FreeVar' G -> FreeVar' (G >> w)
weakenFreeVar' = trFreeVar' weaken

weakenFreeVar2 : FreeVar {G} a -> FreeVar (weaken2 {w = w} {w' = w'} a)
weakenFreeVar2 = trFreeVar weaken2

weakenFreeVar2' : FreeVar' G -> FreeVar' (G >> w >> w')
weakenFreeVar2' = trFreeVar' weaken2

strengthenFreeVar : FreeVar {G >> w} a -> FreeVar (strengthen a)
strengthenFreeVar {w} = trFreeVar (strengthen {w = w})

strengthenFreeVar' : FreeVar' (G >> w) -> FreeVar' G
strengthenFreeVar' {w} = trFreeVar' (strengthen {w = w})

------------

data Inductivity : Set where
  Ind   : Inductivity
  CoInd : Inductivity

variable    ind  : Inductivity
variable @0 ind0 : Inductivity

infixr 3 _=>_
_=>_  : Ty G -> Ty G -> Tm {G} U

variable    b  : Tm (a => U)
variable @0 b0 : Tm (a => U)

record RecordDesc (@0 ind : Inductivity) : Set where
  coinductive
  field
    recordName   : Name
    recordParams : Ty []
    recordFields : Tm (recordParams => U)

open RecordDesc public

variable rd : RecordDesc ind

instance
  HasName[RecordDesc] : HasName (RecordDesc ind0)
  HasName[RecordDesc] .nameOf = recordName

rParams : RecordDesc ind0 -> Ty G
rParams rd = lift (recordParams rd)

rFields : (rd : RecordDesc ind0) -> Tm {G} (rParams rd) -> Ty G

Top    :                                                 Tm {G} U
Either : Ty G -> Ty G ->                                 Tm {G} U
Id     : Tm {G} a* -> Tm a* ->                           Tm {G} U
Pi     : (a : Ty G) -> Tm (a => U) ->                    Tm {G} U
Sigma  : Inductivity -> (a : Ty G) -> Tm (a => U) ->     Tm {G} U
Record : (rd : RecordDesc ind) -> Tm {G} (rParams rd) -> Tm {G} U

infixl 9 _$u_
_$u_ : Tm (a* => a*') -> Tm a* -> Tm {G} a*'

infixl 9 _l$u_
_l$u_ : Tm (a* => a*') -> Tm {G} (lift a*) -> Tm {G} (lift a*')

infixl 9 _w$u_
_w$u_ : Tm (a* => a*') -> Tm {G >> w} (weaken a*) -> Tm {G >> w} (weaken a*')


record TmN (@0 a : Ty G) : Set

data TmR where
  Top#    :                                                 TmR {G} U
  Either# : Ty G -> Ty G ->                                 TmR {G} U
  Id#     : Tm {G} a* -> Tm a* ->                           TmR {G} U
  _=>#_   : Ty G -> Ty G ->                                 TmR {G} U
  Pi#     : (a : Ty G) -> Tm (a => U) ->                    TmR {G} U
  Sigma#  : Inductivity -> (a : Ty G) -> Tm (a => U) ->     TmR {G} U
  Record# : (rd : RecordDesc ind) -> Tm {G} (rParams rd) -> TmR {G} U
  TT      :                                                 TmR {G}  Top
  Left    : Tm a*  ->                                       TmR {G} (Either a* a*')
  Right   : Tm a*' ->                                       TmR {G} (Either a* a*')
  Wrap    : {ps : Tm (rParams rd)} -> Tm (rFields rd ps) -> TmR {G} (Record rd ps)
  _,_     : (x : Tm a*) -> Tm (b $u x) ->                   TmR {G} (Sigma ind a* b)
  Refl    : {x : Tm {G} a*} ->                              TmR {G} (Id x x)
  Neut    :                                        TmN a -> TmR {G}  a
  JPTyLam   :                                                TmR {G} (a* => U)
  JPTyLam'  : Tm a* ->                                       TmR {G} (a* => U)
  LSolveFun : Tm a* ->                                       TmR {G} (a* => U)
  EWrapFun  : {ps : Tm (rParams rd)} -> Tm (Record rd ps) -> TmR {G} (rFields rd ps => U)

Top           = El  Top#
Either a a'   = El (Either# a a')
Id x y        = El (Id# x y)
a => a'       = El (a =># a')
Pi a b        = El (Pi# a b)
Sigma ind a b = El (Sigma# ind a b)
Record rd ps  = El (Record# rd ps)

---------

_[_]n  : TmN a -> (xs : Sub G G') -> Tm (a [ xs ])

postulate @0 []$u : {b : Tm {G} (a => U)} {x : _} {xs : Sub G G'} -> (b $u x) [ xs ] ~ subst (\a -> Tm a) ((a => U) [ xs ] ~! (a [ xs ] => U)) (b [ xs ]) $u x [ xs ]

V0 : Tm {G >> w*} (weaken (fvTy w*))
V0 {w*} = freeVarToTm' w*

Top#             [ xs ]r = Top
Either# a a'     [ xs ]r = Either (a [ xs ]) (a' [ xs ])
Id# x y          [ xs ]r = Id (x [ xs ]) (y [ xs ])
(a =># a')       [ xs ]r = a [ xs ] => a' [ xs ]
Pi# a b          [ xs ]r = Pi (a [ xs ]) (b [ xs ])
Sigma# ind a b   [ xs ]r = Sigma ind (a [ xs ]) (b [ xs ])
Record# rd ps    [ xs ]r = Record rd (subst (\a -> Tm a) (ssU (recordParams rd)) (ps [ xs ]))
TT               [ xs ]r = TT
Left  x          [ xs ]r = Left  (x [ xs ])
Right x          [ xs ]r = Right (x [ xs ])
_,_ {b} x y      [ xs ]r = x [ xs ] , subst (\a -> Tm a) ([]$u {b = b}) (y [ xs ])
Wrap {rd} {ps} x [ xs ]r = Wrap (subst (\a -> Tm a) (_ ~! _) (x [ xs ]))
Refl             [ xs ]r = Refl
JPTyLam          [ xs ]r = JPTyLam
JPTyLam' x       [ xs ]r = JPTyLam' (x [ xs ])
LSolveFun x      [ xs ]r = LSolveFun (x [ xs ])
EWrapFun x       [ xs ]r = coe (_ ~! _) (EWrapFun (x [ xs ]))
Neut n           [ xs ]r = n [ xs ]n

_l$u_ {a*} {a*'} f x = _$u_ {a* = lift a*}{--} {a*' = lift a*'}{--} (lift f) x

_w$u_ {a*} {a*'} f x = _$u_ {a* = weaken a*} {a*' = weaken a*'} (weaken f) x

postulate @0 []$u' : {b : Tm {G} (a => U)} {x : _} {xs : Sub G G'} -> (b $u x) [ xs ] ~ b [ xs ] $u x [ xs ]

postulate @0 []lift$u : {b : Tm {[]} (a => U)} {x : Tm {G} (lift a)} {xs : Sub G G'} -> (b l$u x) [ xs ] ~ b l$u subst (\a -> Tm a) (ssU a) (x [ xs ])

postulate @0 []weakenSub : {xs : Sub G G'} {x : Tm (fvTy w [ xs ])} -> weakenSub {w = w} `comp` ( xs , x ) ~ xs

@0 weaken[] : {xs : Sub G G'} {x : Tm (fvTy w [ xs ])} (a : Ty G) -> weaken {w = w} a [ xs , x ] ~ a [ xs ]
weaken[] a = ssU a *~ cong (_[_] a) []weakenSub

@0 strengthen[] : {xs : Sub G G'} {x : Tm (fvTy w [ xs ])} (a : Ty (G >> w)) -> a [ xs , x ] ~ strengthen a [ xs ]
strengthen[] a = cong (_[_] a) (_ ~! _) *~ sym (ssU a)

postulate @0 []weakenSub2 : {xs : Sub G G'} {x : Tm (fvTy w [ xs ])} {x' : Tm (fvTy w' [ xs , x ])} ->
                           weakenSub2 {w = w} {w' = w'} `comp` ((xs , x) , x') ~ xs

@0 weaken2[] : {xs : Sub G G'} {x : Tm (fvTy w [ xs ])} {x' : Tm (fvTy w' [ xs , x ])} (a'' : Ty G) ->
                           weaken2 {w = w} {w' = w'} a'' [ (xs , x) , x' ] ~ a'' [ xs ]
weaken2[] a'' = ssU a'' *~ cong (_[_] a'') []weakenSub2

---------------------

rFields rd x = recordFields rd l$u x

---------------------

data TmFL  : @0 Ty G -> Set
data TmLR  : @0 Ty G -> Set    -- second-order LHS continuation  glued with spine

@0 TmTr : @0 Ty G -> Set
TmTr a = Tm a -> TmLR a

record TopDef : Set where
  coinductive
  field
    topDefName  : Name
    topDefTy    : Ty []
    topDefFBody : TmFL topDefTy
    topDefBody  : TmLR topDefTy
--  TODO:  topDefGlued : flToL[] (topDefFBody topDef) (preDef topDef) ~ topDefBody topDef

open TopDef public

instance
  HasName[TopDef] : HasName TopDef
  HasName[TopDef] .nameOf = topDefName

flToL[] : TmFL {[]} a* -> TmTr a*


mkDef : (td : TopDef) -> Tm (topDefTy td)

variable td : TopDef

-----------------

-- name which occurs in the context
record OccVar (@0 a : Ty G) : Set where
  coinductive
  field
    occVarName    : Name
    @0 occursIn   : OccursIn occVarName G

open OccVar public

instance
  HasName[OccVar] : HasName (OccVar a)
  HasName[OccVar] .nameOf = occVarName

postulate @0 believeMeOccurs : OccursIn n G

weakenOccVar : OccVar a -> OccVar {G >> w} (weaken a)
weakenOccVar v = record {occVarName = occVarName v; occursIn = believeMeOccurs}

strengthenOccVar : OccVar a -> OccVar {G} (strengthen a)
strengthenOccVar v = record {occVarName = occVarName v; occursIn = believeMeOccurs}

occVarToTm : OccVar a* -> Tm {G} a*

freeVarToOccVar : FreeVar {G} a -> OccVar {G >> w} (weaken a)
freeVarToOccVar v = record {occVarName = varName v; occursIn = believeMeOccurs}

freeVarToTm {a*} v = occVarToTm {a* = weaken a*}{--} (freeVarToOccVar v)

--------------

first : Tm (Sigma ind a* b) -> Tm {G} a*

infixl 9 _$_
_$_  : Tm (Pi a* b) -> (x : Tm a*) -> Tm {G} (b $u x)

data TmSE : @0 Ty G -> Set

data TmS : @0 Ty G -> Set

sToTm : TmS a* -> Tm {G} a*

appU : TmN (a* => a*') -> Tm a* -> TmS {G} a*'

Neut f      $u x = sToTm (appU f x)
JPTyLam {a*} $u x = Pi a* (JPTyLam' x)
JPTyLam' x  $u y = Id x y => U
LSolveFun y $u x = Id x y
EWrapFun x  $u y = Id (Wrap y) x

data TmS where    -- Spine
  -- inductive and coinductive eliminators
  AppU : TmN (a* => a*') -> Tm a* ->                     TmS {G} a*'
  App  : TmN (Pi a* b) -> (x : Tm a*) ->                 TmS {G} (b $u x)
  Fst  :      TmN (Sigma ind a* b) ->                    TmS {G} a*
  Snd  : (x : TmN (Sigma ind a* b)) ->                   TmS {G} (b $u first (Neut x))
  Proj : {ps : Tm (rParams rd)} -> TmN (Record rd ps) -> TmS {G} (rFields rd ps)
  --
  Def  :                                (td : TopDef) -> TmS {[]} (topDefTy td)
  Var  :                                     OccVar a -> TmS {G} a
  SId  :                                      TmSE a* -> TmS {G} a*
  J : {x y : Tm {G} a*} (e : TmN (Id x y)) (P : Tm (Pi a* JPTyLam)) -> Tm (P $ _ $ x $u Refl) -> TmS {G} (P $ _ $ y $u Neut e)
  Sym : {x y : Tm {G} a*} -> TmN (Id x y) ->             TmS {G} (Id y x)
  Coerce : TmN (Id a* a*') -> Tm a* ->                   TmS {G} a*'

appU = AppU

occVarToTm v = sToTm (Var v)


proj : {ps : Tm (rParams rd)} -> Tm (Record rd ps) -> Tm {G} (rFields rd ps)

data TmSE where
  -- EitherCong / EitherApp
  EitherA : {a a' b b' : _} -> TmN (Id a a') -> Tm  (Id b b') -> TmSE {G} (Id (Either a b) (Either a' b'))  -- TODO: eliminate (replace with j or refl match)
  EitherB : {a    b b' : _} ->                  TmN (Id b b') -> TmSE {G} (Id (Either a b) (Either a  b'))  -- TODO: eliminate
  -- EitherInjFst, EitherInjSnd
  Either1 : {a a' b b' : _} -> TmN {G} (Id (Either a b) (Either a' b')) -> TmSE (Id a a')
  Either2 : {a a' b b' : _} -> TmN {G} (Id (Either a b) (Either a' b')) -> TmSE (Id b b')
  WrapCong : {rd : RecordDesc ind} {ps : Tm {G} (rParams rd)} {x y : Tm (rFields rd ps)} -> TmN (Id x y) -> TmSE {G} (Id {a* = Record rd ps} (Wrap x) (Wrap y))  -- TODO: eliminate
  CongRight : {x y : Tm {G} a*'} -> TmN (Id x y) -> TmSE {G} (Id {a* = Either a* a*'} (Right x) (Right y))



Neut f $ x = sToTm (App f x)

infixl 9 _w$_
_w$_ : Tm (Pi a* b) -> (x : Tm {G >> w} (weaken a*)) -> Tm {G >> w} (b w$u x)
_w$_ {a*} {b} f x = _$_ {a* = weaken a*} {b = weaken b} (weaken f) x

first (x , _)  = x
first (Neut x) = sToTm (Fst x)

second : (x : Tm (Sigma ind a* b)) -> Tm {G} (b $u first x)
second (_ , x)  = x
second (Neut x) = sToTm (Snd x)

proj (Wrap x) = x
proj (Neut x) = sToTm (Proj x)

coerce : Tm (Id a* a*') -> Tm a* -> Tm {G} a*'
coerce Refl x = x
coerce (Neut e) x = sToTm (Coerce e x)

j : {x y : Tm {G} a*} (e : Tm (Id x y)) (P : Tm (Pi a* JPTyLam)) -> Tm (P $ _ $ x $u Refl) -> Tm (P $ _ $ y $u e)
j Refl     P w = w
j (Neut e) P w = sToTm (J e P w)

symm : {x y : Tm {G} a*} -> Tm (Id x y) -> Tm (Id y x)
symm Refl = Refl
symm (Neut e) = sToTm (Sym e)

mkDef td = sToTm (Def td)

V1 : Tm {G >> w* >> w'} (weaken2 (fvTy w*))
V1 {w*} = occVarToTm {a* = weaken2 (fvTy w*)}{--} (record {occVarName = nameOf w*; occursIn = believeMeOccurs})

V2 : Tm {G >> w* >> w' >> w''} (weaken3 (fvTy w*))
V2 {w*} = occVarToTm {a* = weaken3 (fvTy w*){--}} (record {occVarName = nameOf w*; occursIn = believeMeOccurs})

--------

index : OccVar {G} a -> (xs : Sub G G') -> Tm (a [ xs ])
index n tt = impossible2
index {a} n (_,_ {G'} {w*} xs x) = decHasName n w* & \where
  nothing  -> subst (\a -> Tm a) (strengthen a [ xs ] ~! a [ xs , x ]) (index (strengthenOccVar {a = a} n) xs)
  (just e) -> subst (\a -> Tm a) (fvTy w* [ xs ] ~! a [ xs , x ]) x

congProj : {rd : RecordDesc Ind} {ps : _} {x y : Tm {G} (Record rd ps)} -> Tm (Id x y) -> Tm (Id (proj x) (proj y))
congProj {rd} {ps} Refl = Refl {a* = rFields rd ps}{--}
congProj (Neut x) = TODO8

congLeft : {x y : Tm {G} a*} -> Tm (Id x y) -> Tm (Id {a* = Either a* a*'} (Left x) (Left y))
congLeft Refl = Refl
congLeft (Neut x) = TODO5

congRight : {x y : Tm {G} a*'} -> Tm (Id x y) -> Tm (Id {a* = Either a* a*'} (Right x) (Right y))
congRight Refl = Refl
congRight {G} (Neut x) = sToTm {G = G} (SId (CongRight x))

wrapCong : {rd : RecordDesc ind} {ps : Tm {G} (rParams rd)} {x y : Tm (rFields rd ps)} -> Tm (Id x y) -> Tm {G} (Id {a* = Record rd ps} (Wrap x) (Wrap y))
wrapCong Refl = Refl
wrapCong (Neut e) = sToTm (SId (WrapCong e))

congWrap : {rd : RecordDesc ind} {ps : _} {x y : Tm {G} (rFields rd ps)} -> Tm (Id x y) -> Tm (Id {a* = Record rd ps} (Wrap x) (Wrap y))
congWrap = wrapCong

injProj : {rd : RecordDesc ind} {ps : _} {x y : Tm {G} (Record rd ps)} -> Tm (Id (proj x) (proj y)) -> Tm (Id x y)
injProj {rd} {ps} e = coe (_ ~! _) (congWrap {rd = rd} {ps = ps} e)

injLeft : {x y : Tm {G} a*} -> Tm (Id {a* = Either a* a*'} (Left x) (Left y)) -> Tm (Id x y)
injLeft Refl = Refl
injLeft (Neut x) = TODO5

injRight : {x y : Tm {G} a*'} -> Tm (Id {a* = Either a* a*'} (Right x) (Right y)) -> Tm (Id x y)
injRight Refl = Refl
injRight (Neut x) = TODO7

eEither : {a a' b b' : _} -> Tm (Id a a') -> Tm (Id b b') -> Tm {G} (Id (Either a b) (Either a' b'))
eEither (Neut e) e' = sToTm (SId (EitherA e e'))
eEither Refl (Neut e') = sToTm (SId (EitherB e'))
eEither Refl Refl = Refl

eEither1 : {a a' b b' : _} -> Tm {G} (Id (Either a b) (Either a' b')) -> Tm (Id a a')
eEither1 Refl = Refl
eEither1 (Neut e) = sToTm (SId (Either1 e))

eEither2 : {a a' b b' : _} -> Tm {G} (Id (Either a b) (Either a' b')) -> Tm (Id b b')
eEither2 Refl = Refl
eEither2 (Neut e) = sToTm (SId (Either2 e))

_[_]se : TmSE {G} a -> (xs : Sub G G') -> Tm (a [ xs ])

_[_]s  : TmS  {G} a -> (xs : Sub G G') -> Tm (a [ xs ])
AppU    f x [ xs ]s = f [ xs ]n $u x [ xs ]
App {b} f x [ xs ]s = subst (\a -> Tm a) (sym ([]$u {b = b})) (f [ xs ]n $ x [ xs ])
Fst     s   [ xs ]s = first (s [ xs ]n)
Snd {b} s   [ xs ]s = subst (\a -> Tm a) (cong (\k -> b [ xs ] $u k) (first (s [ xs ]n) ~! first (Neut s) [ xs ]) *~ sym ([]$u {b = b})) (second (s [ xs ]n))
Proj {rd} x [ xs ]s = subst (\a -> Tm a) (sym ([]lift$u {b = recordFields rd})) (proj (x [ xs ]n))
Def td      [ tt ]s = liftNop (mkDef td)
Var v       [ xs ]s = index v xs
SId e       [ xs ]s = e [ xs ]se
Coerce e x  [ xs ]s = coerce (e [ xs ]n) (x [ xs ])
Sym e       [ xs ]s = symm (e [ xs ]n)
J e P x     [ xs ]s = coe (_ ~! _) (j (e [ xs ]n) (P [ xs ]) (coe (_ ~! _) (x [ xs ])))

EitherA e e' [ xs ]se = eEither (e [ xs ]n) (e' [ xs ])
EitherB e    [ xs ]se = eEither Refl (e [ xs ]n)
Either1 e    [ xs ]se = eEither1 (e [ xs ]n)
Either2 e    [ xs ]se = eEither2 (e [ xs ]n)
_[_]se {G} {G'} (WrapCong {ind} {rd} {ps} {x} {y} e) xs
     = coe (_ ~! _) (wrapCong {ind = ind} {G = G'} {rd = rd} {ps = coe (_ ~! _) (ps [ xs ])} {x = coe (_ ~! _) (x [ xs ])} {y = coe (_ ~! _) (y [ xs ])} (coe (_ ~! _) (e [ xs ]n)))
CongRight e  [ xs ]se = congRight (e [ xs ]n)

------------------------------

data TmL : @0 Ty G -> Set    -- second-order LHS

data TmLR where    -- second-order LHS continuation
  LHS : TmL a* -> TmLR a*
  RHS : Tm  a* -> TmLR a*                    -- Ret

------------------------

sToLR : TmS a* -> TmLR a*

{-# ETA_EQUALITY #-}
record TmN a where
  inductive
  constructor Glue
  field
    nToS   : TmS a
    nToL   : TmL a
    @0 nEq : sToLR nToS ~ LHS nToL

open TmN public

n [ xs ]n = nToS n [ xs ]s

glue : (s : TmS a*) (lr : TmLR a*) -> @0 sToLR s ~ lr -> Tm a*
glue s (RHS r) e = r
glue s (LHS l) e = rToTm (Neut (Glue s l e))

sToTm s = glue s (sToLR s) refl


---------------

data TmSL : @0 Ty G -> Set where    -- Strict second-order LHS
  -- coinductive constructors (second order) 
  LamU    : (     Tm a*  -> TmLR a*'   ) ->                      TmSL {G} (a* => a*')
  Lam     : ((x : Tm a*) -> TmLR (b $u x)) ->                   TmSL {G} (Pi a* b)
  _,_     : {x : Tm a*} -> (x' : TmLR a*) -> TmLR (b $u x) ->    TmSL {G} (Sigma ind a* b)
  Wrap    : {ps : Tm (rParams rd)}  -> TmLR (rFields rd ps) -> TmSL {G} (Record rd ps)

data TmL where
  -- inductive eliminators (second order)
  Stuck   :                     TmL a*
  -- pattern matching constructors (second order)
  Fail    :                     TmL a*
  Or      : TmSL a* -> TmLR a* -> TmL a*
  Strict  :           TmSL a* -> TmL a*


-----------

infixr 2 _||_
_||_ : TmLR a* -> TmLR a* -> TmLR a*
RHS x          || _ = RHS x
LHS Fail       || x = x
LHS (Strict l) || x = LHS (Or l x)
LHS (Or a b)   || x = LHS (Or a (b || x))
LHS Stuck      || _ = LHS Stuck

mapLR : (TmSL a* -> TmLR a*') -> (Tm a* -> Tm a*') -> TmL a* -> TmLR a*'
mapLR f g Fail            = LHS Fail
mapLR f g (Strict x)      = f x
mapLR f g (Or x (RHS x')) = f x || RHS (g x')
mapLR f g (Or x (LHS x')) = f x || mapLR f g x'
mapLR f g Stuck           = LHS Stuck

mapLR-Sigma : (p : TmN (Sigma ind a* b)) -> TmLR {G} (b $u first (Neut p))
mapLR-Sigma (Glue _ (Strict (_,_ {b} _ y))  _) = subst (\k -> TmLR (b $u k)) (_ ~! _) y  
mapLR-Sigma (Glue s (Or (_ , y) (LHS x')) _) = coe (_ ~! _) y || coe (_ ~! _) (mapLR-Sigma (Glue s x' (sToLR s ~! LHS x')))
mapLR-Sigma (Glue _ (Or (_ , y) (RHS x')) _) = coe (_ ~! _) y || RHS (coe (_ ~! _) (second x'))
mapLR-Sigma (Glue _ Fail  _) = LHS Fail
mapLR-Sigma (Glue _ Stuck _) = LHS Stuck

postulate @0 topDefTyClosed : TmLR {G} (lift (topDefTy td)) ~ TmLR {[]} (topDefTy td)

sToLR (AppU n x) = mapLR (\{(LamU f) -> f x}) (\f -> f $u x) (nToL n)
sToLR (App  n x) = mapLR (\{(Lam  f) -> f x}) (\f -> f $  x) (nToL n)
sToLR (Fst  n  ) = mapLR (\{(x' , _)  -> x'})  first         (nToL n)
sToLR (Proj n  ) = mapLR (\{(Wrap x) -> x  })  proj          (nToL n)
sToLR (Snd  x  ) = mapLR-Sigma x
sToLR (Def  td ) = topDefBody td
sToLR (Var _   )   = LHS Stuck
sToLR (SId _   )   = LHS Stuck
sToLR (Coerce _ _) = LHS Stuck
sToLR (Sym _)      = LHS Stuck
sToLR (J e P w)    = LHS Stuck


---------------------------------------

occursR : OccVar {G} a' -> TmR {G} a -> maybe top

occurs : OccVar {G} a' -> Tm {G} a* -> maybe top
occurs {a* = U}    _ U      = pure _
occurs {a* = U}    v (El a) = occursR v a
occurs {a* = El _} v  x     = occursR v x

occursN : OccVar {G} a' -> TmN {G} a -> maybe top

occursR v Top#             = do pure _
occursR v (Either# a a')   = do _ <- occurs v a; _ <- occurs v a'; pure _
occursR v (a =># a')       = do _ <- occurs v a; _ <- occurs v a'; pure _
occursR v (Pi# a b)        = do _ <- occurs v a; _ <- occurs v b ; pure _
occursR v (Sigma# ind a b) = do _ <- occurs v a; _ <- occurs v b ; pure _
occursR v (Id# x x')       = do _ <- occurs v x; _ <- occurs v x'; pure _
occursR v (Record# rd x)   = do _ <- occurs v x; pure _
occursR v TT               = do pure _
occursR v (Left  x)        = do _ <- occurs v x; pure _
occursR v (Right x)        = do _ <- occurs v x; pure _
occursR v (Wrap  x)        = do _ <- occurs v x; pure _
occursR v (x , y)          = do _ <- occurs v x; _ <- occurs v y; pure _
occursR v Refl             = do pure _
occursR v JPTyLam          = do pure _
occursR v (JPTyLam' x)     = do _ <- occurs v x; pure _
occursR v (LSolveFun x)    = do _ <- occurs v x; pure _
occursR v (EWrapFun x)     = do _ <- occurs v x; pure _
occursR v (Neut n)         = occursN v n

postulate occursSE : OccVar {G} a' -> TmSE {G} a -> maybe top    -- TODO

occursS : OccVar {G} a' -> TmS {G} a -> maybe top
occursS v (AppU f x) = do _ <- occursN v f; _ <- occurs v x; pure _
occursS v (App  f x) = do _ <- occursN v f; _ <- occurs v x; pure _
occursS v (Fst x)    = do _ <- occursN v x; pure _
occursS v (Snd x)    = do _ <- occursN v x; pure _
occursS v (Proj x)   = do _ <- occursN v x; pure _
occursS v (Def x)    = do pure _
occursS v (SId x)    = occursSE v x
occursS v (Coerce e x) = do _ <- occursN v e; _ <- occurs v x; pure _
occursS v (Sym e) = do _ <- occursN v e; pure _
occursS v (J e P w)    = do _ <- occursN v e; _ <- occurs v P; _ <- occurs v w; pure _       -- TODO: hidden arguments?
occursS v (Var n) = decHasName v n & \where
  nothing  -> pure _
  (just _) -> nothing

occursN v n = occursS v (nToS n)

maybeStrengthen : (x : Tm {G >> w*} a*) -> maybe (Tm (strengthen a*) ** \x' -> x' ~e' strengthenNop x)
maybeStrengthen {w*} {a*} x = do
  _ <- occurs {a' = weaken (fvTy w*)}{--} (freeVarToOccVar (fv w*)) x
  pure (strengthenNop x , refl)

--------------------------------------------------- context equivalences

data EquivTy : @0 Ty G -> @0 Ty G -> Set

backwardTy : EquivTy {G} a* a*' -> (xs : Sub G G') -> Tm (a*' [ xs ]) -> Tm (a* [ xs ])

forwardTy : EquivTy {G} a* a*' -> (xs : Sub G G') -> Tm (a* [ xs ]) -> Tm (a*' [ xs ])

--------------

{-# ETA_EQUALITY #-}
record Equiv (@0 G G' : Con) : Set where
  inductive
  constructor MkEq
  field
    subForward  : Sub G  G'
    subBackward : Sub G' G
    @0 forwardBackward : subForward `comp` subBackward ~ idSub
    @0 backwardForward : subBackward `comp` subForward ~ idSub

open Equiv public

EId : Equiv G* G*
EId = MkEq idSub idSub compIdSub compIdSub

EComp : Equiv G G'' -> Equiv G'' G' -> Equiv G G'
EComp (MkEq a b ab ba) (MkEq a' b' ab' ba') = MkEq (a `comp` a') (b' `comp` b) (_ ~! _) (_ ~! _)

ESym : Equiv G G' -> Equiv G' G
ESym (MkEq a b ab ba) = MkEq b a ba ab

trTm : (E : Equiv G G') -> Tm {G} a* -> Tm {G'} (a* [ subForward E ])
trTm E x = x [ subForward E ]

trFreeVarE : (@0 E : Equiv G G') -> FreeVar a -> FreeVar (trTm E a)
trFreeVarE E = trFreeVar (trTm E)

trFreeVarE' : (E : Equiv G G') -> FreeVar' G -> FreeVar' G'
trFreeVarE' E = trFreeVar' (trTm E)

ETy : EquivTy (fvTy w*) (fvTy w*') -> Equiv (G* >> w*) (G* >> w*')
ETy E = MkEq (weakenSub , backwardTy E weakenSub V0) (weakenSub , forwardTy E weakenSub V0) (_ ~! _) (_ ~! _)

ELift : (E : Equiv G G') -> Equiv (G >> w*) (G' >> trFreeVarE' E w*)
ELift {w*} E@(MkEq a b ab ba)
  = MkEq (weakenSubTr a , subst (\a -> Tm a) (ssU (fvTy w*) *~ cong (\s -> fvTy w* [ s ]u) compWeakenSub) (V0 {w* = trFreeVarE' E w*}))
         (weakenSubTr b , subst (\a -> Tm a) (cong (\s -> fvTy w* [ s ]u) (sym (compWeakenSub' *~ cong weakenSubTr ab)) *~ sym (ssU (fvTy w*))) (V0 {w* = w*}))
         (_ ~! _)
         (_ ~! _)

ESwap : Equiv (G* >> w* >> weakenFreeVar' w*') (G* >> w*' >> weakenFreeVar' w*)
ESwap {w*} {w*'} = MkEq ((weakenSub2 , subst (\a -> Tm a) (_ ~! _) (V0 {w* = weakenFreeVar' w* })) , subst (\a -> Tm a) (_ ~! _) (V1 {w* = w*'}))
                      ((weakenSub2 , subst (\a -> Tm a) (_ ~! _) (V0 {w* = weakenFreeVar' w*'})) , subst (\a -> Tm a) (_ ~! _) (V1 {w* = w* }))
                      (_ ~! _)
                      (_ ~! _)

ETop : Equiv (G* >> FV {fvTy = Top} v*) G*
ETop = MkEq (idSub , TT) weakenSub (_ ~! _) (_ ~! _)

EPack : {v1 : _} {v2 : _} -> Equiv (G* >> FV {fvTy = Sigma Ind a* b} v*) (G* >> FV {fvTy = a*} v1 >> FV {fvTy = b w$u V0} v2)
EPack {v*} {v1} {v2} = MkEq (weakenSub2 , V1 , coe (_ ~! _) (V0 {w* = FV v2}))
                           ((weakenSub , first (V0 {w* = FV v*})) , coe (_ ~! _) (second (V0 {w* = FV v*})))
                           (_ ~! _)
                           (_ ~! _)

postulate
  @0 trTyForward : (a : Ty G) (E : Equiv G G') {xs : Sub G G''} -> a [ xs ] ~ trTm E a [ subBackward E `comp` xs ]

-------------------------------------

data TmFL where    -- First-order  LHS
  -- coinductive constructors (first order)
  FLamU   : TmFL {G >> w*} (weaken a*')      -> TmFL {G} (fvTy w* => a*')
  FLam    : TmFL {G >> w*} (b w$u V0) -> TmFL {G} (Pi (fvTy w*) b)
  _,_     : {x : Tm a*} (x' : TmFL a*) -> TmFL (b $u x) -> TmFL {G} (Sigma ind a* b)

  FWrap   : {ps : Tm (rParams rd)} -> TmFL (rFields rd ps) -> TmFL {G} (Record rd ps)
  -- inductive eliminators (first order)
  MatchPair : (p : Tm (Sigma ind (fvTy w*) b)) {v' : _} {v'' : _} ->
    TmFL {G >> w*
            >> FV {fvTy = b w$u V0} v'
            >> FV {fvTy = Id {a* = Sigma ind _ _} (V1 , subst (\a -> Tm a) (_ ~! _) (V0 {w* = FV v'})) (weaken2 p)} v''
         } (weaken3 a*'') -> TmFL {G} a*''
  MatchLeft  : (x : Tm (Either (fvTy w*) a*)) {v' : _} -> TmFL {G >> w* >> FV {fvTy = Id (Left  V0) (weaken x)} v'} (weaken2 a*'') -> TmFL {G} a*''
  MatchRight : (x : Tm (Either a* (fvTy w*))) {v' : _} -> TmFL {G >> w* >> FV {fvTy = Id (Right V0) (weaken x)} v'} (weaken2 a*'') -> TmFL {G} a*''
  EqRule     : {a : _} (E : Equiv G G*') -> TmFL (trTm E a) -> TmFL a
  FFail   : TmFL {G} a*
  FOr     : TmFL a* -> TmFL a* -> TmFL {G} a*
  --
  FRHS    : Tm a* -> TmFL {G} a*


--------------

wrap : {ps : Tm (rParams rd)} -> TmTr (rFields rd ps) -> TmTr {G} (Record rd ps)
wrap f r = LHS (Strict (Wrap (f (proj r))))

pairL : (n : Tm (Sigma ind a* b)) -> (x : TmTr a*) -> TmTr (b $u first n) -> TmLR {G} (Sigma ind a* b)
pairL n x y = LHS (Strict (x (first n) , y (second n)))

postulate @0 pairFstSnd : {p : Tm {G} (Sigma ind a* b)} -> (first p , second p) ~ p
postulate @0 wrapProj : {ps : _} {x : Tm {G} (Record rd ps)} -> Wrap (proj x) ~ x

matchPair : (p : Tm {G} (Sigma ind a* b)) -> ((x : Tm a*) (y : Tm (b $u x)) -> Tm (Id (x , y) p) -> TmTr a*'') -> TmTr {G} a*''
matchPair x f n = f (first x) (second x) (subst (\k -> Tm (Id k x)) (sym pairFstSnd) Refl) n

matchLeft : (x : Tm {G} (Either a* a*')) -> ((y : Tm a*) -> Tm (Id (Left y) x) -> TmTr a*'') -> TmTr {G} a*''
matchLeft (Left  y) f n = f y Refl n
matchLeft (Right _) f n = LHS Fail
matchLeft (Neut  _) f n = LHS Stuck

matchRight : (x : Tm {G} (Either a* a*')) -> ((y : Tm a*') -> Tm (Id (Right y) x) -> TmTr a*'') -> TmTr {G} a*''
matchRight (Right y) f n = f y Refl n
matchRight (Left  _) f n = LHS Fail
matchRight (Neut  _) f n = LHS Stuck

jRule : {x y : Tm {G} a*}
  (tm : Tm (Id x y)) ->
  (P : (y : Tm a*) -> Tm (Id x y) -> Ty G) ->
  TmTr (P x Refl) -> TmTr (P y tm)
jRule Refl     P l n = l n
jRule (Neut _) P l n = LHS Stuck

postulate @0 []weaken$uV0 : {b : Tm {G} (fvTy w* => U)} {xs : Sub G G'} {x : Tm (fvTy w* [ xs ])} -> (b w$u V0 {w* = w*}) [ xs , x ] ~ b [ xs ] $u x

flToL : TmFL a* -> (xs : Sub G* []) -> TmTr (a* [ xs ])
flToL (FLamU {a*'} f) = \xs n -> LHS (Strict (LamU \x -> subst TmTr (weaken[] a*')          (flToL f (xs , x)) (n $u x)))
flToL (FLam  {b}  f) = \xs n -> LHS (Strict (Lam  \x -> subst TmTr ([]weaken$uV0 {b = b}) (flToL f (xs , x)) (n $  x)))
flToL (x' , y) = \xs n -> pairL n (flToL x' xs) (coe (_ ~! _) (flToL y xs))
flToL (FWrap {rd} {ps} x)    = \xs -> wrap (subst TmTr ([]lift$u {b = recordFields rd}) (flToL x xs))
flToL {a*} (MatchPair {b} p {v'} {v''} f) = \xs -> matchPair (p [ xs ]) \x y r ->
     let y' = subst (\a -> Tm a) ((b [ xs ]r) $u x ~! (b w$u V0) [ xs , x ]u) y
  in let r' = subst (\a -> Tm a) (Id (x , y) (p [ xs ]r) ~! _ {-Id (V1 {w* = _}) (V0 {w* = _})-}) r
  in subst TmTr (_ ~! _) (flToL f (((xs , x) , y') , r')) -- (_,_ {w* = FV v''} (_,_ {w* = FV v'} (xs , x) y') r'))
flToL {a*} (MatchLeft  x f) = \xs -> matchLeft  (x [ xs ]) \y r -> subst TmTr (weaken2[] a*) (flToL f ((xs , y) , coe (_ ~! _) r))
flToL {a*} (MatchRight x f) = \xs -> matchRight (x [ xs ]) \y r -> subst TmTr (weaken2[] a*) (flToL f ((xs , y) , coe (_ ~! _) r))
flToL FFail        = \xs n -> LHS Fail
flToL (FOr l r)    = \xs n -> flToL l xs n || flToL r xs n
flToL (EqRule {a} E w) = \xs n -> subst (\a -> TmLR a) (sym (trTyForward a E))
  (flToL w (subBackward E `comp` xs)
  (subst (\a -> Tm a) (trTyForward a E) n))
flToL (FRHS x)     = \xs n -> RHS (x [ xs ])

flToL[] t = subst TmTr [][] (flToL t tt)

def'' : GlobalVar a* -> TmFL a* -> Tm a*
def'' {a*} n t = x where

  x : Tm a*

  d1 : TopDef
  topDefName  d1 = nameOf n
  topDefTy    d1 = a*
  topDefFBody d1 = t
  topDefBody  d1 = flToL[] t x

  x = mkDef d1

---------------------

@0 ReflectCon : @0 Con -> @0 FreeVar' [] -> Set
ReflectCon G v = Equiv ([] >> v) G

{-# ETA_EQUALITY #-}
record ReflectedCon (@0 G : Con) : Set where
  inductive
  constructor MkECon
  field
    {eConVar} : FreeVar' []
    eEquiv    : ReflectCon G eConVar

open ReflectedCon public

mkELam : {{MonadSupply M}} -> ReflectCon G* w* -> Ty G* -> M (Tm (fvTy w* => U))
mkELam {w*} r a' = do
  n <- newFreeVar (GeneratedVar "elam")
  pure (def'' n (FLamU {w* = w*} (EqRule r (FRHS a'))))

reflectCon : {{MonadSupply M}} -> (G* : Con) -> M (ReflectedCon G*)
reflectCon [] = do
  v , refl <- newFreeVar'' (GeneratedVar "cv")
  pure (MkECon {eConVar = v} ETop)
reflectCon (G >> v0) = do
  MkECon {eConVar} E <- reflectCon G
  la <- mkELam E (fvTy v0)
  v , refl <- newFreeVar'' {- {a = Sigma Ind (fvTy eConVar) la} -} (GeneratedVar "cv")
  let v0' = subst (\a -> FreeVar a) (trTm (ESym E) (fvTy v0) ~! la w$u V0) (trFreeVarE (ESym E) (fv v0))
  pure (coe (_ ~! _) (MkECon {eConVar = v} (EComp (EPack {b = la} {v1 = fv eConVar} {v2 = v0'}) (ELift {w* = FV v0'} E))))

----------------------------------

---------------------------------- printing

printTm   : {{Monad M}} -> Tm   {G} a* -> M Doc
printTmS  : {{Monad M}} -> TmS  {G} a -> M Doc
printTmSE : {{Monad M}} -> TmSE {G} a -> M Doc
printTmR  : {{Monad M}} -> TmR  {G} a -> M Doc

instance
  ToDocM[Tm] : {{_ : Monad M}} -> ToDocM (Tm {G} a*) M
  ToDocM[Tm] .toDocM = printTm

instance
  ToDocM[TmR] : {{_ : Monad M}} -> ToDocM (TmR {G} a) M
  ToDocM[TmR] .toDocM = printTmR

instance
  ToDocM[TmS] : {{_ : Monad M}} -> ToDocM (TmS {G} a) M
  ToDocM[TmS] .toDocM = printTmS

instance
  ToDocM[TmN] : {{_ : Monad M}} -> ToDocM (TmN {G} a) M
  ToDocM[TmN] {M} .toDocM n = toDocM {M = M} (nToS n)

instance
  ToDocM[TmSE] : {{_ : Monad M}} -> ToDocM (TmSE {G} a) M
  ToDocM[TmSE] .toDocM = printTmSE


printTm {a* = U   }  U     = kwm "U"
printTm {a* = U   } (El a) = printTmR a
printTm {a* = El _}  x     = printTmR x

printTmR Top#             = kwm "Top"
printTmR (Either# a a')   = kwm "+"     (toDocM a) (toDocM a')
printTmR (a =># a')       = kwm "->"    (toDocM a) (toDocM a')
printTmR (Pi#    a b)     = kwm "Pi"    (toDocM a) (toDocM b)
printTmR (Sigma# ind a b) = kwm "Sigma" (toDocM a) (toDocM b)
printTmR (Id# x y)        = kwm "=="    (toDocM x) (toDocM y)
printTmR (Record# rd ps)  = kwm " "     (nameToDocM rd) (toDocM ps)
printTmR TT               = kwm "TT"
printTmR (Left  x)        = kwm "Left"  (toDocM x)
printTmR (Right x)        = kwm "Right" (toDocM x)
printTmR (Wrap x)         = kwm "Wrap"  (toDocM x)
printTmR (x , y)          = kwm ","     (toDocM x) (toDocM y)
printTmR Refl             = kwm "Refl"
printTmR JPTyLam          = pure (Var (MkToken NoLoc "jPTyLam"))
printTmR (JPTyLam' x)     = kwm " " (pure (Var (MkToken NoLoc "jPTyLam'"))) (toDocM x)
printTmR (LSolveFun x)    = kwm " " (pure (Var (MkToken NoLoc "LSolveFun"))) (toDocM x)
printTmR (EWrapFun x)     = kwm " " (pure (Var (MkToken NoLoc "EWrapFun"))) (toDocM x)
printTmR (Neut n)         = toDocM n

printTmS (Def td)     = nameToDocM td
printTmS (Var n)      = nameToDocM n
printTmS (Proj x  )   = kwm "proj" (toDocM x)
printTmS (Fst  x  )   = kwm "fst"  (toDocM x)
printTmS (Snd  x  )   = kwm "snd"  (toDocM x)
printTmS (AppU f x)   = kwm " "    (toDocM f) (toDocM x)
printTmS (App  f x)   = kwm " "    (toDocM f) (toDocM x)
printTmS (SId e)      = toDocM e
printTmS (Coerce e x) = kwm "coerce" (toDocM e) (toDocM x)
printTmS (Sym e)      = kwm "sym"    (toDocM e)
printTmS (J e P w)    = kwm "jRule"  (toDocM e) (toDocM P) (toDocM w)

printTmSE e = kwm "TODO"

instance
  ShowM[Con] : {{_ : Monad M}} -> ShowM Con M
  ShowM[Con] .showM = showCon  where

    showCon : {{_ : Monad M}} -> Con -> M stringBuilder
    showCon [] = pure ""
    showCon (G >> v) = showCon G <>m pure "\n" <>m show <$> kwm ":" (nameToDocM v) (toDocM (fvTy v))

instance
  ShowM[Tm] : {{_ : Monad M}} -> ShowM (Tm {G} a*) M
  ShowM[Tm] .showM t = toDocM t <&> show

instance
  ShowM[TmR] : {{_ : Monad M}} -> ShowM (TmR {G} a*) M
  ShowM[TmR] .showM t = toDocM t <&> show

instance
  ShowM[TmS] : {{_ : Monad M}} -> ShowM (TmS {G} a*) M
  ShowM[TmS] .showM t = showM (sToTm t)

------------------------------------

{-# ETA_EQUALITY #-}
record TyTm (@0 G : Con) : Set where
  inductive
  constructor tyTm
  field
    {typeOf} : Ty G
    termOf   : Tm typeOf

open TyTm public

liftTyTm : TyTm [] -> TyTm G
liftTyTm (tyTm x) = tyTm (liftNop x)

weakenTyTm : TyTm G -> TyTm (G >> w*)
weakenTyTm (tyTm {typeOf} x) = tyTm {typeOf = weaken typeOf}{--} (weakenNop x)

instance
  ShowM[TyTm] : {{_ : Monad M}} -> ShowM (TyTm G) M
  ShowM[TyTm] .showM t = showM (termOf t) <>m pure " : " <>m showM (typeOf t)

---------------------------------- context with Definitions

infixl 4 _>let_:=_
data DCon (@0 G : Con) : Set where
  []        : DCon G
  _>let_:=_ : (dG : DCon G) (w : FreeVar' G) -> Tm (fvTy w) -> DCon  G

infixl 4 _>>d_
_>>d_ : DCon G -> (w : FreeVar' G) -> DCon (G >> w)
[]             >>d _ = []
G >let v' := x >>d w = G >>d w >let weakenFreeVar' v' := weakenNop x 

variable dG : DCon G

trDCon' : Sub G* G' -> DCon G'
trDCon' {G* = []} tt = []
trDCon' {G* = G >> w} (_,_ {w*} xs x) = trDCon' xs >let trFreeVar' (\a -> a [ xs ]) w* := x

trDCon : Equiv G* G' -> DCon G* -> DCon G'
trDCon E [] = trDCon' (subForward E)
trDCon E (dG >let v := x) = trDCon E dG >let trFreeVarE' E v := trTm E x


instance
  ShowM[DCon] : {{_ : Monad M}} -> ShowM (DCon G*) M
  ShowM[DCon] .showM = showCon  where

    showCon : {{_ : Monad M}} -> DCon G* -> M stringBuilder
    showCon {G*} [] = showM G*
    showCon (G >let v := x) = showCon G <>m pure "\n" <>m show <$> kwm ":" (kwm "=" (nameToDocM v) (toDocM x)) (toDocM (fvTy v))

printGoal : {{_ : MonadError stringBuilder M}} -> DCon G* -> Ty G* -> M A
printGoal dG a = do
  ls <- showM dG
  a <- showM a
  throwError (ls <> "\n----------------\n? : " <> a)

----------------------------------

@0 NameMap : (@0 Ty [] -> Set) -> Set

variable @0 W : @0 Ty [] -> Set

emptySM     :                                      NameMap W
insertSM    : GlobalVar a* -> W a* -> NameMap W -> NameMap W
deleteSM    : GlobalVar a* ->         NameMap W -> NameMap W
lookupSM    : GlobalVar a* ->         NameMap W -> maybe (W a*)
lookupSMStr : Token ->                NameMap W -> maybe (Ty [] ** \a -> pair (GlobalVar a) (W a))

NameMap P = list (Ty [] ** \a -> pair (GlobalVar a) (P a))

emptySM = []

insertSM s a m = (_ , s , a) :: m

deleteSM s [] = []
deleteSM s ((_ , n , x) :: sm) = decHasName n s & \where
  (just _) -> deleteSM s sm
  nothing  -> (_ , n , x) :: deleteSM s sm

lookupSM s [] = nothing
lookupSM s ((_ , n , x) :: sm) = decHasName n s <&>match & \where
  (just refl) -> just x
  nothing     -> lookupSM s sm

lookupSMStr s [] = nothing
lookupSMStr s ((_ , n , x) :: sm) = matchName s n & \where
  true  -> just (_ , n , x)
  false -> lookupSMStr s sm

@0 Ctx : Set
Ctx = NameMap \a -> Tm a



--------------

@0 Fill : @0 Ty [] -> Set
Fill a = (@0 C : Set) -> Tm a -> C -> C

@0 Fills = NameMap Fill


@0 error : Set
error = stringBuilder


record TCState : Set where
  constructor MkTCState
  field
    counter   : nat
    logState  : stringBuilder
--    showEnv   : ShowEnv
--    atExpEnv  : AtExpEnv

open TCState public

{-# ETA_EQUALITY #-}
record TCEnv : Set where
  inductive
  constructor MkTCEnv
  field
    globalEnv : Ctx
    fillEnv   : Fills

open TCEnv public

-- type checking monad
record TC (@0 A : Set) : Set where
  coinductive
  field
    getTC : TCEnv -> TCState -> pair TCState (either error A)

open TC public


--------------------------


runTC : TC A -> either error A
runTC tc = pair.snd (getTC tc (MkTCEnv emptySM {- [] -} {- emptyECon -} emptySM) (MkTCState 1000 ""))

instance
  Monad[TC] : Monad TC 
  getTC (Monad[TC] .pure x) _ c = c , right x
  getTC (Monad[TC] ._>>=_ m f) ctx c = getTC m ctx c & \where
    (c , left  e) -> c , left e
    (c , right x) -> getTC (f x) ctx c

instance
  MonadError[TC] : MonadError stringBuilder TC
  getTC (MonadError[TC] .throwError e) _ c = c , left e

mFix : (A -> TC A) -> TC A
getTC (mFix {A} f) ctx c = p where

  x : A

  p : pair TCState (either error A)
  p = getTC (f x) ctx c

  x = fromRight (snd p) {{TODO9}}

catchError : TC A -> (error -> TC A) -> TC A
getTC (catchError m f) ctx c = getTC m ctx c & \where
  (c , left  e) -> getTC (f e) ctx c
  (c , right x) -> c , right x

log : stringBuilder -> TC top
getTC (log s) ctx (MkTCState c l) = MkTCState c (l <> "\n" <> s) , right tt

getLog : TC stringBuilder
getTC getLog ctx s@(MkTCState c l) = s , right l

addGlobal : GlobalVar a* -> Tm a* -> TC A -> TC A
getTC (addGlobal s d m) (MkTCEnv g {- l l' -} f) = getTC m (MkTCEnv (insertSM s d g) {-l l' -} f)

lookupCon : (G : Con) -> Token -> maybe (TyTm G)
lookupCon [] _ = nothing
lookupCon (G >> v) s = matchName s v & \where
  true  -> just (tyTm (V0 {w* = v}))
  false -> weakenTyTm <$> lookupCon G s

lookupDCon : DCon G* -> Token -> maybe (TyTm G*)
lookupDCon {G*} [] t = lookupCon G* t
lookupDCon (G >let v := x) s = matchName s v & \where
  true -> just (tyTm x)
  false -> lookupDCon G s

lookupTm : DCon G* -> Token -> TC (TyTm G*)
getTC (lookupTm G s) env c = lookupDCon G s & \where
  (just d)  -> c , right d
  nothing -> lookupSMStr s (globalEnv env) & \where
      (just (a , n , x))  -> c , right (liftTyTm (tyTm x))
      nothing             -> c , left ("Not defined: " <> showWithLoc s)

futureTC : GlobalVar a* -> (Tm a* -> TC A) -> TC A
futureTC n f = future \get set -> addFill n set (f get)  where

  addFill : GlobalVar a* -> Fill a* -> TC A -> TC A
  getTC (addFill s d m) (MkTCEnv g f) = getTC m (MkTCEnv g (insertSM s d f))

lookupFill : Token -> ({a : Ty []} -> GlobalVar a -> Fill a -> TC A) -> TC A -> TC A
lookupFill n cont err = do
  just (_ , n , f) <- lookupFill' n  where  nothing -> err
  delFill n (cont n f)
 where
  delFill : GlobalVar a* -> TC A -> TC A
  getTC (delFill s m) (MkTCEnv g f) = getTC m (MkTCEnv g (deleteSM s f))

  lookupFill' : Token -> TC (maybe (Ty [] ** \a -> pair (GlobalVar a) (Fill a)))
  getTC (lookupFill' s) env c = c , right (lookupSMStr s (fillEnv env))

instance
  MonadSupply[TC] : MonadSupply TC
  getTC (MonadSupply[TC] .newId) ctx (MkTCState c l) = MkTCState (suc c) l , right c

instance
  IsString[TC_String] : IsString (TC string)
  IsString[TC_String] .fromString s = pure s

instance
  IsString[TC_StringBuilder] : IsString (TC stringBuilder)
  IsString[TC_StringBuilder] .fromString s = pure (fromString s)


---------------

data @0 _~[_]~_ : @0 Tm a -> @0 a ~ a' -> @0 Tm a' -> Prop
data _~[_]~_ where
  refl : {@0 x : Tm {G} a*} -> x ~[ refl ]~ x

@0 _$u~_  : {x x' : _} -> (b : Tm (a* => a*')) -> x ~ x' -> b $u x ~ b $u x'
_ $u~ refl = refl

postulate @0 eta=>     : {f f' : Tm {G} (fvTy w* => a')} -> f w$u V0 {w* = w*} ~ f' w$u V0 -> f ~ f'
postulate @0 etaPi     : {f f' : Tm {G} (Pi (fvTy w*) b)} -> weaken {w = w*} f $ V0 {w* = w*} ~ weaken f' $ V0 -> f ~ f'
postulate @0 etaTop    : {x x' : Tm {G} Top} -> x ~ x'
postulate @0 etaId     : {x y  : Tm {G} a} {e e' : Tm (Id x y)} -> e ~ e'
postulate @0 etaSigma  : {f f' : Tm {G} (Sigma Ind a b)} -> (e : first f ~ first f') -> second f ~[ b $u~ e ]~ second f' -> f ~ f'
postulate @0 etaRecord : {ps : _} {f f' : Tm {G} (Record {ind = Ind} rd ps)} -> (e : proj f ~ proj f') -> f ~ f'

convertS : (s : TmS {G} a*) (s' : TmS a*') -> TC (_~e_ {Ty G ** TmS} (_ , s) (_ , s'))

convert' : (@0 e : a* ~ a*') -> (x : Tm a*) (x' : Tm {G} a*') -> TC (Emb (x ~[ e ]~ x'))

convert : (x y : Tm {G} a*) -> TC (x ~e y)

convertN : (s : TmN {G} a*) (s' : TmN a*') -> TC (_~e_ {Ty G ** TmN} (_ , s) (_ , s'))
convertN n n' = do
  refl <- convertS (nToS n) (nToS n') <&>match
  pure (emb (_ ~! _))

convertR : (x y : TmR {G} a*) -> TC (x ~e y)
convertR Top# Top#  = pure (emb refl)
convertR (Either# a b) (Either# a' b') = do
  refl <- convert a a' <&>match
  refl <- convert b b' <&>match
  pure (emb refl)
convertR (a =># b) (a' =># b') = do
  refl <- convert a a' <&>match
  refl <- convert b b' <&>match
  pure (emb refl)
convertR (Pi# a b) (Pi# a' b') = do
  refl <- convert a a' <&>match
  refl <- convert b b' <&>match
  pure (emb refl)
convertR (Sigma# Ind a b) (Sigma# Ind a' b') = do
  refl <- convert a a' <&>match
  refl <- convert b b' <&>match
  pure (emb refl)
convertR (Sigma# CoInd a b) (Sigma# CoInd a' b') = do
  refl <- convert a a' <&>match
  refl <- convert b b' <&>match
  pure (emb refl)
convertR (Id# {a*} x y) (Id# {a* = a*'} x' y') = do
  refl <- convert a* a*' <&>match
  refl <- convert x x' <&>match
  refl <- convert y y' <&>match
  pure (emb refl)
convertR a@(Record# rd x) a'@(Record# rd' x') = do
  just refl <- pure (decHasName rd rd' <&>match) where
    nothing -> throwErrorM (showM a <>m "  =?=  " <>m showM a')
  refl <- convert x x' <&>match
  pure (emb refl)
convertR {G} {a* = El (a =># a')} f f' = do
  v , refl <- newFreeVar'' (GeneratedVar "v")
  emb e <- convert {G = G >> v} {a* = weaken a'} (f w$u V0) (f' w$u V0)
  pure (emb (eta=> e))
convertR {G} {a* = El (Pi# a b)} f f' = do
  v , refl <- newFreeVar'' {a* = a} (GeneratedVar "v")
  emb e <- convert {G = G >> v} {a* = b w$u V0} (f w$ V0) (f' w$ V0)
  pure (emb (etaPi e))
convertR (Neut n) (Neut n') = do
  refl <- convertN n n' <&>match
  pure (emb refl)
convertR {a* = El Top#} _ _ = do
  pure (emb etaTop)
convertR {a* = El (Sigma# Ind a b)} x x' = do
  emb e <- convert (first x) (first x')
  emb e' <- convert' (b $u~ e) (second x) (second x')
  pure (emb (etaSigma e e'))
convertR {a* = El (Record# {ind = Ind} a b)} x x' = do
  emb e <- convert (proj x) (proj x')
  pure (emb (etaRecord e))
convertR (Left x) (Left x') = do
  refl <- convert x x' <&>match
  pure (emb refl)
convertR (Right x) (Right x') = do
  refl <- convert x x' <&>match
  pure (emb refl)
convertR {a* = El (Id# _ _)} _ _ = do
  pure (emb etaId)
convertR x y = throwErrorM (showM x <>m "  =?=  " <>m showM y)

convert {a* = U} U    U     = pure (emb refl)
convert {a* = U} (El a) (El a')  = do
  refl <- convertR a a' <&>match
  pure (emb refl)
convert {a* = U} x y = throwErrorM (showM x <>m "  =?=  " <>m showM y)
convert {a* = El _} x y  = do
  refl <- convertR x y <&>match
  pure (emb refl)

convert' e x x' = do
  refl <- pure (match e)
  refl <- convert x x' <&>match
  pure (emb refl)

convertS x@(Var v) y@(Var v') = decHasName v v' <&>match & \where
  (just refl) -> pure (emb refl)
  nothing  -> throwErrorM (showM x <>m "  =?=  " <>m showM y)
convertS x@(Def td) y@(Def td') = decHasName td td' <&>match & \where
  (just refl) -> pure (emb refl)
  nothing  -> throwErrorM (showM x <>m "  =?=  " <>m showM y)
convertS (AppU f x) (AppU f' x') = do
  refl <- convertN f f' <&>match
  refl <- convert x x' <&>match
  pure (emb refl)
convertS (App f x) (App f' x') = do
  refl <- convertN f f' <&>match
  refl <- convert  x x' <&>match
  pure (emb refl)
convertS (Fst x) (Fst x') = do
  refl <- convertN x x' <&>match
  pure (emb refl)
convertS (Snd x) (Snd x') = do
  refl <- convertN x x' <&>match
  pure (emb refl)
convertS (Proj x) (Proj x') = do
  refl <- convertN x x' <&>match
  pure (emb refl)
convertS x y = throwErrorM (showM x <>m "  =?=  " <>m showM y)

convertMaybe : (x y : Tm {G} a*) -> TC (maybe (x ~e y))
convertMaybe x y = catchError (convert x y <&> just) \_ -> pure nothing


---------------------------------

expectVar : ((s : NameStr) -> TC A) -> Doc -> TC A
expectVar f (Var n) = f (MkNameStr n)
expectVar _ d = throwError ("variable name expected instead of: " <> show d)

newFreeVar' : Doc -> TC (FreeVar' G ** \w -> pair Doc (fvTy w ~e' a*))
newFreeVar' (KW (MkToken l ".") $d n $d d) = do
  n <- expectVar newFreeVar n
  pure (FV n , d , refl)
newFreeVar' d = throwError ("lambda expected instead of: " <> show d)

--------------------

-- TODO: should be *convertible* to a variable
matchVar'' : (s : TmR a) -> maybe (OccVar {G} a)
matchVar'' (Neut (Glue (Var n) _ _)) = just n
matchVar'' _ = nothing

matchVarX : {a : _} (s : Tm a) -> maybe (OccVar {G} a)
matchVarX {a = U} U = nothing
matchVarX {a = U} (El s) = matchVar'' s
matchVarX {a = El _} s = matchVar'' s

---------

occVarToFreeVar : OccVar a -> FreeVar (strengthen a)
occVarToFreeVar s = record {varName = nameOf s; varIsFresh = believeMeFresh}

occVarToFreeVar' : OccVar {G >> w*} a* ->
  maybe (FreeVar (strengthen a*) ** \v' -> G >> FV v' ~e' G >> w*)
occVarToFreeVar' {G} {w*} s = decHasName w* s & \where
  (just _) -> just (_ , match (G >> FV (occVarToFreeVar s) ~! G >> w*))
  nothing  -> nothing

decLS' : {a : Ty (G >> w*)} (x : OccVar a) ->
  maybe (FreeVar' G ** \v' -> pair (G >> v' ~e' G >> w*) (strengthen a ~e fvTy v'))
decLS' s = occVarToFreeVar' s & \where
  (just (_ , e)) -> just (_ , e , emb refl)
  nothing  -> nothing

tmToFreeVar : Tm {G >> w*} a* ->
  maybe (FreeVar (strengthen a*) ** \v' -> G >> FV v' ~e' G >> w*)
tmToFreeVar x = do
  sv <- matchVarX x
  v , e <- occVarToFreeVar' sv
  pure (v , e)

@0 ETr : @0 Con -> Set
ETr G = Con ** \G' -> Equiv G G'

strengthenM : (x : Tm {G >> w*} a*) -> TC (Tm (strengthen a*) ** \x' -> x' ~e' strengthenNop x)
strengthenM x = try ("can't lift " <>m showM x) (pure (maybeStrengthen x))

-------------

data GCon (@0 G : Con) : Set

joinCon : GCon G* -> Con

data GCon G where
  []   : GCon G
  _>>_ : (gG : GCon G) -> FreeVar' (joinCon gG) -> GCon G

joinCon {G*} []    = G*
joinCon (gG >> v) = joinCon gG >> v

---------------

data RGCon (@0 G : Con) : Set where
  []   : RGCon G
  _<<_ : (w : _) -> RGCon (G >> w) -> RGCon G

joinRCon : RGCon G* -> Con
joinRCon {G*} [] = G*
joinRCon (v << gG) = joinRCon gG

concatGRG : (gG : GCon G) -> RGCon (joinCon gG) -> RGCon G
concatGRG []        acc = acc
concatGRG (gG >> v) acc = concatGRG gG (v << acc)

reverseG : GCon G -> RGCon G
reverseG gG = concatGRG gG []

---------------

@0 SubTr : @0 Con -> @0 Con -> Set
SubTr G G' = {G'' : Con} -> Sub G' G'' -> Sub G G''

weakenSubG : (gG : GCon G') -> SubTr G' (joinCon gG)    -- TODO: @0
weakenSubG []        xs       = xs
weakenSubG (gG >> v) (xs , _) = weakenSubG gG xs
{-
varsG : {gG : GCon G} -> Sub G (joinCon gG)
varsG {G} {gG} = weakenSubG gG idSub
-}
weakenSubRG : (rG : RGCon G') -> SubTr G' (joinRCon rG)    -- TODO: @0
weakenSubRG []        xs = xs
weakenSubRG (_ << rG) xs = fstSub (weakenSubRG rG xs)

@0 varsRG : (rG : RGCon G*) -> Sub G* (joinRCon rG)
varsRG rG = weakenSubRG rG idSub

liftRG : (@0 rG : RGCon G) -> Tm a* -> Tm (a* [ varsRG rG ]nop)
liftRG rG x = x [ varsRG rG ]nop

--------------

trRCon' : Equiv G G' -> RGCon G -> RGCon G'
trRCon' E [] = []
trRCon' E (v << rG) = trFreeVarE' E v << trRCon' (ELift E) rG

trRCon : Equiv G G' -> RGCon G -> RGCon G'
trRCon E rG = nopCompiled (trRCon' E) rG

deepEquiv : (rG : RGCon G) (E : Equiv G G') -> Equiv (joinRCon rG) (joinRCon (trRCon E rG))
deepEquiv [] E = E
deepEquiv (v << rG) E = deepEquiv rG (ELift E)

eSwap : Equiv (G* >> w* >> w*') (G* >> strengthenFreeVar' w*' >> weakenFreeVar' w*)
eSwap {G*} {w* = v0} {w*' = v1} = subst (\k -> Equiv k (G* >> v1' >> v0')) (G* >> v0 >> weakenFreeVar' v1' ~! G* >> v0 >> v1) (ESwap {w* = v0} {w*' = v1'})
 where
  v0' = weakenFreeVar' v0
  v1' = strengthenFreeVar' v1

--------------------

nameHint : Doc -> NameStr
nameHint (Var n) = MkNameStr n
nameHint _ = GeneratedVar "w"

@0 PatItem : @0 Con -> Set
PatItem G = pair Doc (TyTm G)

@0 PatItems : @0 Con -> Set
PatItems G = list (PatItem G)

trTyTm : Equiv G G' -> TyTm G -> TyTm G'
trTyTm E (tyTm x) = tyTm (trTm E x)

trItems : Equiv G G' -> PatItems G -> PatItems G'
trItems E [] = []
trItems E ((d , x) :: is) = (d , trTyTm E x) :: trItems E is

weakenItems : PatItems G -> PatItems (G >> w)
weakenItems = coe (_ ~! _)  -- TODO?

---------------------------------------------------------------------------------

MatchWrap'  : {rd : RecordDesc ind} {ps : Tm (rParams rd)} (x : Tm (Record rd ps)) {v : _} {v' : _} -> TmFL {G* >> FV {fvTy = rFields rd ps} v >> FV {fvTy = Id (Wrap (subst (\a -> Tm a) ([]lift$u {b = recordFields rd}) V0)) (weaken x)} v'} (weaken2 a*'') -> TC (TmFL {G*} a*'')

----------------------------------------------------

infer : DCon G* -> Doc -> TC (TyTm G*)

checkTop : DCon G* -> Doc -> (a : Ty G*) -> TC (Tm a)

check : DCon G* -> Doc -> (a : Ty G*) -> TC (Tm a)
check G d@(KW (MkToken l "wrap"))                 a = checkTop G d a
check G d@(KW (MkToken l "undefined"))            a = checkTop G d a
check G d@(KW (MkToken l ";")          $d _ $d _) a = checkTop G d a
check G d@(KW (MkToken l ".")          $d _ $d _) a = checkTop G d a
check G d@(KW (MkToken l "&")          $d _ $d _) a = checkTop G d a
check G d@(KW (MkToken l "|")          $d _ $d _) a = checkTop G d a
check G d@(KW (MkToken l "matchWrap")  $d _ $d _) a = checkTop G d a
check G d@(KW (MkToken l "matchPair")  $d _ $d _) a = checkTop G d a
check G d@(KW (MkToken l "matchLeft")  $d _ $d _) a = checkTop G d a
check G d@(KW (MkToken l "matchRight") $d _ $d _) a = checkTop G d a
check G d@(KW (MkToken l "matchRefl")  $d _ $d _) a = checkTop G d a
check G (KW (MkToken l "Refl")) a = do
  El (Id# x y) , refl <- matchM a where ty -> throwError "check/Refl"
  refl <- convert x y <&>match
  pure Refl
check G (KW (MkToken l "Left") $d x) a = do
  El (Either# a a') , refl <- matchM a where ty -> throwError "check/Left"
  x <- check G x a
  pure (Left x)
check G (KW (MkToken l "Right") $d x) a = do
  El (Either# a a') , refl <- matchM a where ty -> throwError "check/Right"
  x <- check G x a'
  pure (Right x)
check G (KW (MkToken l "Wrap") $d x) a = do
  El (Record# rd ps) , refl <- matchM a where ty -> throwError "check/Wrap"
  x <- check G x (rFields rd ps)
  pure (Wrap x)
check G (KW (MkToken l ",") $d x $d y) a = do
  El (Sigma# ind a b) , refl <- matchM a where ty -> throwError "check/,"
  x <- check G x a
  y <- check G y (b $u x)
  pure (x , y)
check G (KW (MkToken l "?")) a = printGoal G a
check G d a = do
  t <- infer G d
  refl <- convert (typeOf t) a <&>match
  pure (termOf t)

infer G (KW (MkToken l "?")) = throwError "can't infer ?"
infer G (KW (MkToken l "U")) = do
  pure (tyTm U)
infer G (KW (MkToken l "Top")) = do
  pure (tyTm Top)
infer G (KW (MkToken l "TT")) = do
  pure (tyTm TT)
infer G (KW (MkToken l "proj") $d d) = do
  tyTm {typeOf = El (Record# _ _)} x <- infer G d  where
    t -> throwErrorM ("proj: " <>m showM t)
  pure (tyTm (proj x))
infer G (KW (MkToken l "fst") $d d) = do
  tyTm {typeOf = El (Sigma# _ _ _)} x <- infer G d  where
    t -> throwErrorM ("fst: " <>m showM t)
  pure (tyTm (first x))
infer G (KW (MkToken l "snd") $d d) = do
  tyTm {typeOf = El (Sigma# _ _ _)} x <- infer G d  where
    t -> throwErrorM ("fst: " <>m showM t)
  pure (tyTm (second x))
infer G (KW (MkToken l "+") $d a $d a') = do
  a  <- check G a  U
  a' <- check G a' U
  pure (tyTm (Either a a'))
infer G (KW (MkToken l "->") $d a $d a') = do
  a  <- check G a  U
  a' <- check G a' U
  pure (tyTm (a => a'))
infer G (KW (MkToken l "Pi") $d a $d b) = do
  a <- check G a U
  b <- check G b (a => U)
  pure (tyTm (Pi a b))
infer G (KW (MkToken l "Sigma") $d a $d b) = do
  a <- check G a U
  b <- check G b (a => U)
  pure (tyTm (Sigma Ind a b))
infer G (KW (MkToken l "CoSigma") $d a $d b) = do
  a <- check G a U
  b <- check G b (a => U)
  pure (tyTm (Sigma CoInd a b))
infer G (KW (MkToken l "==") $d x $d y) = do
  x <- infer G x
  y <- check G y (typeOf x)
  pure (tyTm (Id (termOf x) y))
infer G (KW (MkToken l " ") $d f $d x) = infer G f >>= \where
  (tyTm {typeOf = El (a =># a')} f) -> do
    x <- check G x a
    pure (tyTm (f $u x))
  (tyTm {typeOf = El (Pi# a b)} f) -> do
    x <- check G x a
    pure (tyTm (f $ x))
  t -> throwErrorM ("matchPi: " <>m showM t)
infer G (Var n) = lookupTm G n
infer G d = throwError ("infer: " <> show d)

checkLHS : (dG : DCon G*) -> Doc -> {a : Ty G*} -> Tm a -> TC (TmFL a)

lrSolve : (G : Con) {a : Ty G} -> Tm a -> TC (ETr G)

checkPattern : (dG : DCon G*) -> PatItems G* -> Doc -> {a' : Ty G*} -> Tm a' -> TC (TmFL a')
checkPattern G [] body x' = checkLHS G body x'
checkPattern {G* = G} dG ((p , tyTm {typeOf} sc) :: is) body x' = p & \where
  (Var n) -> do
    v , refl <- newFreeVar'' (MkNameStr n)
    checkPattern (dG >let v := sc) is body x'
  (KW (MkToken l "Wrap") $d d) -> do
    El (Record# _ _) , refl <- matchM typeOf where ty -> throwError "checkPattern/Wrap"
    z , refl <- newFreeVar'' (nameHint d)
    e , refl <- newFreeVar'' (GeneratedVar "e")
    G' , E <- lrSolve (G >> z >> e) (freeVarToTm' e)
    let dG' = trDCon E (dG >>d z >>d e)
    w <- checkPattern dG' ((d , tyTm (trTm E (V1 {w* = z}))) :: trItems E (weakenItems (weakenItems is))) body (trTm E (weaken2 x'))
    MatchWrap' sc (EqRule E w)
  (KW (MkToken l "Left") $d d) -> do
    El (Either# _ _) , refl <- matchM typeOf where ty -> throwError "checkPattern/Left"
    z , refl <- newFreeVar'' (nameHint d)
    e , refl <- newFreeVar'' (GeneratedVar "e")
    G' , E <- lrSolve (G >> z >> e) (freeVarToTm' e)
    let dG' = trDCon E (dG >>d z >>d e)
    w <- checkPattern dG' ((d , tyTm (trTm E (V1 {w* = z}))) :: trItems E (weakenItems (weakenItems is))) body (trTm E (weaken2 x'))
    pure (MatchLeft sc (EqRule E w))
  (KW (MkToken l "Right") $d d) -> do
    El (Either# _ _) , refl <- matchM typeOf where ty -> throwError "checkPattern/Right"
    z , refl <- newFreeVar'' (nameHint d)
    e , refl <- newFreeVar'' (GeneratedVar "e")
    G' , E <- lrSolve (G >> z >> e) (freeVarToTm' e)
    let dG' = trDCon E (dG >>d z >>d e)
    w <- checkPattern dG' ((d , tyTm (trTm E (V1 {w* = z}))) :: trItems E (weakenItems (weakenItems is))) body (trTm E (weaken2 x'))
    pure (MatchRight sc (EqRule E w))
  (KW (MkToken l "Refl")) -> do
    El (Id# _ _) , refl <- matchM typeOf where ty -> throwError "checkPattern/Refl"
    G' , E <- lrSolve G sc
    let dG' = trDCon E dG
    w <- checkPattern dG' (trItems E is) body (trTm E x')
    pure (EqRule E w)
  (KW (MkToken l "TT")) -> do
    El Top# , refl <- matchM typeOf where ty -> throwError "checkPattern/Top"
    checkPattern dG is body x'
  (KW (MkToken l ",") $d d1 $d d2) -> do
    El (Sigma# _ _ _) , refl <- matchM typeOf where ty -> throwError "checkPattern/,"
    z1 , refl <- newFreeVar'' (nameHint d1)
    z2 , refl <- newFreeVar'' (nameHint d2)
    e  , refl <- newFreeVar'' (GeneratedVar "e")
    G' , E <- lrSolve (G >> z1 >> z2 >> e) (freeVarToTm' e)
    let dG' = trDCon E (dG >>d z1 >>d z2 >>d e)
    w <- checkPattern dG' ((d1 , tyTm (trTm E (V2 {w* = z1}))) :: (d2 , tyTm (trTm E (V1 {w* = z2}))) :: trItems E (weakenItems (weakenItems (weakenItems is)))) body (trTm E (weaken3 x'))
    pure (MatchPair sc (EqRule E w))
  d -> throwError ("checkPattern: " <> show d)

checkLHS {G* = g} G p {a} z = p & \where
  (KW (MkToken _ ";") $d (KW (MkToken l "<-") $d p $d e) $d d) -> do
    e <- infer G e
    checkPattern G ((p , e) :: []) d z
  (KW (MkToken l ".") $d n $d t) -> do
    El (_ =># _) , refl <- matchM a where
      (El (Pi# _ _) , refl) -> do
        v , refl <- newFreeVar'' (nameHint n)
        t <- checkPattern (G >>d v) ((n , tyTm (freeVarToTm' v)) :: []) t (weaken z $ V0)
        pure (FLam t)
      (a , refl) -> throwErrorM ("not a Pi type at " <>m showM l <>m ": " <>m showM a)
    v , refl <- newFreeVar'' (nameHint n)
    t <- checkPattern (G >>d v) ((n , tyTm (freeVarToTm' v)) :: []) t (z w$u V0 {w* = v})
    pure (FLamU t)
  (KW (MkToken l "&") $d x $d y) -> do
    El (Sigma# _ _ _) , refl <- matchM a where ty -> throwError "checkLHS/&"
    x <- checkLHS G x (first z)
    y <- checkLHS G y (second z)
    pure (x , y)
  (KW (MkToken _ "|") $d l $d r) -> do
    l <- checkLHS G l z
    r <- checkLHS G r z
    pure (FOr l r)
  (KW (MkToken l "wrap") $d x) -> do
    El (Record# _ _) , refl <- matchM a where ty -> throwError "checkLHS/wrap"
    x <- checkLHS G x (proj z)
    pure (FWrap x)
  (KW (MkToken l "undefined")) -> do
    pure FFail
  (KW (MkToken l "matchWrap") $d x $d f) -> do
    tyTm {typeOf = El (Record# _ _)} x <- infer G x where
      t -> throwErrorM ("matchWrap at " <>m showM l <>m ": " <>m showM t)
    v  , f , refl <- newFreeVar' f
    v' , f , refl <- newFreeVar' f
    t <- checkLHS (G >>d v >>d v') f (weaken2 z)
    MatchWrap' x t
  (KW (MkToken l "matchPair") $d x $d f) -> do
    tyTm {typeOf = El (Sigma# _ _ _)} x <- infer G x where
      t -> throwErrorM ("matchPair at " <>m showM l <>m ": " <>m showM t)
    v   , f , refl <- newFreeVar' f
    v'  , f , refl <- newFreeVar' f
    v'' , f , refl <- newFreeVar' f
    t <- checkLHS (G >>d v >>d v' >>d v'') f (weaken3 z)
    pure (MatchPair x t)
  (KW (MkToken l "matchLeft") $d x $d f) -> do
    tyTm {typeOf = El (Either# _ _)} x <- infer G x where
      t -> throwErrorM ("matchLeft at " <>m showM l <>m ": " <>m showM t)
    v  , f , refl <- newFreeVar' f
    v' , f , refl <- newFreeVar' f
    t <- checkLHS (G >>d v >>d v') f (weaken2 z)
    pure (MatchLeft x t)
  (KW (MkToken l "matchRight") $d x $d f) -> do
    tyTm {typeOf = El (Either# _ _)} x <- infer G x where
      t -> throwErrorM ("matchRight at " <>m showM l <>m ": " <>m showM t)
    v  , f , refl <- newFreeVar' f
    v' , f , refl <- newFreeVar' f
    t <- checkLHS (G >>d v >>d v') f (weaken2 z)
    pure (MatchRight x t)
  (KW (MkToken l "matchRefl") $d e $d w) -> do
    tyTm e <- infer G e
    G' , E <- lrSolve g e
    let dG' = trDCon E G
    w <- checkLHS dG' w (trTm E z)
    pure (EqRule E w)
  d -> do
    t <- check G d a
    pure (FRHS t)

checkTop {G* = G} dG d aa = do
  MkECon {eConVar} E <- reflectCon G
  l1 <- mkELam E aa
  topdef <- mFix {A = Tm {[]} (Pi (fvTy eConVar) l1)} \z -> do
    e <- checkLHS (trDCon (ESym E) dG) d (weaken z $ coe (_ ~! _) (V0 {w* = eConVar}))
    n2 <- newFreeVar (GeneratedVar "liftedLam")
    pure (def'' n2 (FLam {w* = eConVar} (coe (_ ~! _) e)))
  pure (subst (\a -> Tm a) (_ ~! _) (trTm E (weakenNop topdef $ V0)))

checkLHS'' : GlobalVar a* -> Doc -> TC (Tm a*)
checkLHS'' n t = do
  mFix \dd -> do
    t <- checkLHS [] t dd
    pure (def'' n t)

inferTop : TC A -> Doc -> TC A
inferTop {A} cont (KW (MkToken _ ";") $d d $d ds') = d & \where
  (KW (MkToken l "=") $d n $d (KW (MkToken _ "record") $d ps $d fs)) -> do
    ps <- check [] ps U
    fs <- check [] fs (ps => U)
    dn <- expectVar newFreeVar n
    n <- newFreeVar (GeneratedVar "rlam")
    v <- newFreeVar (GeneratedVar "ps")
    let d = record {recordName = nameOf dn; recordParams = ps; recordFields = fs}
    let w = FV {fvTy = ps} v
    let l = def'' n (FLamU {w* = w} {a*' = U} (FRHS (Record {ind = Ind} d (coe (_ ~! _) (V0 {w* = w})))))
    addGlobal dn l (inferTop cont ds')
  (KW (MkToken l "=") $d n $d (KW (MkToken _ "corecord") $d ps $d fs)) -> do
    ps <- check [] ps U
    fs <- check [] fs (ps => U)
    dn <- expectVar newFreeVar n
    n <- newFreeVar (GeneratedVar "rlam")
    v <- newFreeVar (GeneratedVar "ps")
    let d = record {recordName = nameOf dn; recordParams = ps; recordFields = fs}
    let w = FV {fvTy = ps} v
    let l = def'' n (FLamU {w* = w} {a*' = U} (FRHS (Record {ind = CoInd} d (coe (_ ~! _) (V0 {w* = w})))))
--    let l = def'' n (FLamU {w* = FV {fvTy = ps} v} {a' = U} (FRHS (Record {ind = CoInd} d V0)))
    addGlobal dn l (inferTop cont ds')
  (KW (MkToken l "=") $d (KW (MkToken l' ":") $d n $d a) $d t) -> do
    a <- check [] a U
    n <- expectVar (newFreeVar {a = a}) n
    d <- checkLHS'' n t
    addGlobal n d (inferTop cont ds')
  (KW (MkToken l "=") $d Var n $d t) -> do
    lookupFill {A = A} n (\n fill -> do
      t <- checkLHS'' n t
      fill _ t (inferTop {A = A} cont ds')
     ) (do
      t <- infer [] t
      n <- newFreeVar (MkNameStr n)
      s <- showM t
      sn <- nameToDocM n
      _ <- log (show sn <> " =    " <> s)
      addGlobal n (termOf t) (inferTop cont ds')
     )
  (KW (MkToken l ":") $d n $d a) -> do
    a <- check [] a U
    n <- expectVar (newFreeVar {a = a}) n
    futureTC n \t' -> addGlobal n t' (inferTop cont ds')
  d -> throwError ("inferTop bad declaration: " <> show d)
inferTop cont (KW (MkToken _ "EndOfFile")) = cont
inferTop cont d = throwError ("inferTop: " <> show d)

----------------------------------------

inferSingle : Doc -> TC (TyTm [])
inferSingle d = inferTop cont d where
  cont : TC (TyTm [])
  cont = lookupTm [] "main"


tc : string -> either error top
tc s = runTC (parse s >>= inferTop (pure tt))

@0 tcS : string -> either error (TyTm [])
tcS s = runTC (parse s >>= inferSingle)

@0 tc' : (s : string) -> @0 {{IsRight (tcS s)}} -> TyTm []
tc' s = fromRight (tcS s)

tc'' : string -> stringBuilder
tc'' s = runTC ((parse s >>= inferSingle) >>= \t -> showM t) & \where
  (right s) -> s
  (left s) -> "error: " <> s


@0 testTC0 : tc' "main : U = U"
       ~ tyTm U
testTC0 = refl

@0 testTC1 : tc' "f : Top -> U  = x. Top;  main = U"
       ~ tyTm U
testTC1 = refl

@0 testTC1' : tc' "f = TT;  main = f"
       ~ tyTm TT
testTC1' = refl

@0 testTC2 : tc' "idU = U; main : U + U = Left idU"
       ~ tyTm {typeOf = Either U U} (Left U)
testTC2 = refl

@0 testTC2' : tc' "idU : U -> U  = x . U; main = idU U"
       ~ tyTm U
testTC2' = refl


-----------------

data EquivTy where
--  EId'   : EquivTy a* a*
--  EComp' : EquivTy a* a*' -> EquivTy a*' a*'' -> EquivTy a* a*''
--  ESym'  : EquivTy a* a*' -> EquivTy a*' a*
  ESymEq : {x y : Tm {G} a*} -> EquivTy (Id x y) (Id y x)
  EEq   : Tm (Id a* a*') -> EquivTy a* a*'
  EDel  : {a : Ty G} {x : Tm a} -> EquivTy (Id x x) Top
  ELSolve : {w : FreeVar' G} (y : Tm (fvTy w)) -> EquivTy (Sigma Ind (fvTy w) (LSolveFun y)) Top
  EWrap : {rd : RecordDesc ind} {ps : Tm {G} (rParams rd)} (x : Tm (Record rd ps)) ->
               EquivTy Top (Sigma Ind (rFields rd ps) (EWrapFun x))
  EIdProj : {ps : _} {x y : Tm {G} (Record {ind = Ind} rd ps)} -> EquivTy (Id x y) (Id (proj x) (proj y))
  EIdLeft : {x y : Tm {G} a*} -> EquivTy (Id {a* = Either a* a*'} (Left x) (Left y)) (Id x y)
  EIdRight : {x y : Tm {G} a*'} -> EquivTy (Id {a* = Either a* a*'} (Right x) (Right y)) (Id x y)


--forwardTy EId' xs x = x
--forwardTy (EComp' E E') xs x = forwardTy E' xs (forwardTy E xs x)
--forwardTy (ESym' E) xs x = backwardTy E xs x
forwardTy (EEq e) xs x = coerce (e [ xs ]) x
forwardTy EDel xs x = TT
forwardTy (ELSolve y) xs x = TT
forwardTy ESymEq xs x = symm x
forwardTy (EWrap y) xs x = proj y [ xs ] , coe (_ ~! _) (Refl {x = y [ xs ]})
forwardTy EIdProj  xs x = coe (_ ~! _) (congProj x)
forwardTy EIdLeft  xs x = injLeft x
forwardTy EIdRight xs x = injRight x
--forwardTy EWrapEq xs x = {!congg Wrap x!}
--forwardTy (ETrEq e) xs x = {!!}
--forwardTy (ELeft y) xs x = {!!} , {!!}

--backwardTy EId' xs x = x
--backwardTy (EComp' E E') xs x = backwardTy E xs (backwardTy E' xs x)
--backwardTy (ESym' E) xs x = forwardTy E xs x
backwardTy (EEq e) xs x = coerce (symm e [ xs ]) x
backwardTy EDel xs x = Refl
backwardTy (ELSolve y) xs x = y [ xs ] , coe (_ ~! _) (Refl {x = y [ xs ]})
backwardTy ESymEq xs x = symm x
backwardTy (EWrap y) xs x = TT
backwardTy EIdProj  xs x = injProj (coe (_ ~! _) x)
backwardTy EIdLeft  xs x = congLeft x
backwardTy EIdRight xs x = congRight x
--backwardTy EWrapEq xs x = {!!}
--backwardTy (ETrEq e) xs x = {!!}
--backwardTy (ELeft y) xs x = TT


MatchWrap' {rd} {ps} x {v} {v'} fl = do
--  vG <- newFreeVar (GeneratedVar "v")
  vA <- newFreeVar (GeneratedVar "v")
  vB , refl <- newFreeVar'' (GeneratedVar "v")
  pure (EqRule (EComp (ESym (ETop {v* = vA})) (EComp (ETy {w*' = vB} (EWrap x)) (EPack {v1 = v} {v2 = coe (_ ~! _) v'}))) (coe (_ ~! _) fl))



-----------------

lSolveBubble :
  (rG : RGCon (G* >> w*))
  {y : Tm (liftRG rG (weaken (fvTy w*)))} (v : _)
  -> TC (ETr (joinRCon rG >> FV {fvTy = Id (liftRG rG (V0 {w* = w*})) y} v))
lSolveBubble {G* = G} {w*} [] {y} v = do
  vG <- newFreeVar {a = fvTy w*} (GeneratedVar "v")
  y' , refl <- strengthenM y
  vA <- newFreeVar (GeneratedVar "v")
  vB , refl <- newFreeVar'' (GeneratedVar "v")
  let sol = EComp (ESym (EPack {v* = vA} {v1 = fv w*} {v2 = subst (\a -> FreeVar a) (_ ~! _) v})) (EComp (ETy {w*' = vB} (ELSolve {w = FV vG} (subst (\a -> Tm a) (_ ~! _) y'))) ETop)
  pure (subst ETr (_ ~! _) (_ , sol))
lSolveBubble {G* = G} {w*} (w1 << rG) {y} v = do
  a1 , refl <- strengthenM (fvTy w1)
  let ee = eSwap {w* = w*} {w*' = w1}
  G'' , E <- lSolveBubble (trRCon ee rG) {y = coe (_ ~! _) y} (coe (_ ~! _) v)
  pure (subst ETr (_ ~! _) (G'' , EComp (ELift {w* = FV v} (deepEquiv rG ee)) (coe (_ ~! _) E)))

rSolveBubble :
  (rG : RGCon (G* >> w*))
  {x : Tm (liftRG rG (weaken (fvTy w*)))} (v : _)
  -> TC (ETr (joinRCon rG >> FV {fvTy = Id x (liftRG rG (V0 {w* = w*}))} v))
rSolveBubble {G* = G} {w*} rG {x} v = do
  v' <- newFreeVar {a = Id (liftRG rG (V0 {w* = w*})) x} (GeneratedVar "v")
  _ , E <- lSolveBubble {G} {w* = w*} rG {x} v'
  pure (_ , EComp (ETy ESymEq) E)

lSolveFindVar :
  {G : Con} {a : Ty G} {x : OccVar a} {rG : RGCon G} {y : Tm (liftRG rG a)} (v : _)
  -> TC (ETr (joinRCon rG >> FV {fvTy = Id (liftRG rG (occVarToTm x)) y} v))

rSolveFindVar :
  {G : Con} {a : Ty G} {y : OccVar a} {rG : RGCon G} {x : Tm (liftRG rG a)} (v : FreeVar (Id x (liftRG rG (occVarToTm y))))
  -> TC (ETr (joinRCon rG >> FV v))
rSolveFindVar {G} {a} {y} {rG} {x} v = do
  v' <- newFreeVar {a = Id (liftRG rG (occVarToTm y)) x} (GeneratedVar "v")
  G'' , E <- lSolveFindVar {G} {a} {y} {rG} {x} v'
  pure (_ , EComp (ETy ESymEq) E)

@0 lSolveLift :
  {G : Con} {gG : GCon G} {aw : Ty (joinCon gG)} (vw : FreeVar aw)
  (rG : RGCon (joinCon gG >> FV vw))
  -> Sub G (joinRCon rG)
lSolveLift {G} {gG} vw rG = weakenSubG gG (fstSub (varsRG rG))

lSolveMidBubble :
  {G : Con} {a : Ty G} (x : OccVar a)
  {gG : GCon G} {aw : Ty (joinCon gG)} (vw : FreeVar aw)
  {rG : RGCon (joinCon gG >> FV vw)} {y : Tm (a [ lSolveLift vw rG ]nop)} (v : FreeVar (Id (occVarToTm x [ lSolveLift vw rG ]nop) y))
  -> TC (ETr (joinRCon rG >> FV v))
lSolveMidBubble {G} {a} x {gG} {aw} vw {rG = []} {y} v = maybeStrengthen y & \where
  nothing -> do
    _ , E <- lSolveFindVar {x = x} {rG = reverseG (gG >> FV vw)} {y = coe (_ ~! _) y} (coe (_ ~! _) v)
    pure (subst ETr (_ ~! _) (_ , E))
  (just (y' , refl)) -> do
    let v' = strengthenFreeVar v
    let vw' = weakenFreeVar {w = FV v'} vw
    G'' , E <- lSolveFindVar {x = x} {rG = reverseG gG} {y = coe (_ ~! _) y'} (coe (_ ~! _) v')
    pure (subst ETr (_ ~! _) (_ , EComp (eSwap {w* = FV vw} {w*' = FV v}) (ELift {G = joinCon gG >> FV v'} {G' = G''} {w* = FV vw'} (coe (_ ~! _) E))))
lSolveMidBubble {G} {a} x {gG} {aw} vw {rG = rG@(w << rG')} {y} v = maybeStrengthen (fvTy w) & \where
  nothing -> do
    _ , E <- lSolveFindVar {x = x} {rG = concatGRG (gG >> FV vw) rG} {y = coe (_ ~! _) y} (coe (_ ~! _) v)
    pure (subst ETr (_ ~! _) (_ , E))
  (just (az' , refl)) -> do
    let vz' = strengthenFreeVar (fv w)
    G'' , E <- lSolveMidBubble x {gG = gG >> FV vz'} {aw = weaken aw} (weakenFreeVar vw) {rG = subst RGCon (_ ~! _) rG'} {y = coe (_ ~! _) y} (coe (_ ~! _) v)
    pure (subst ETr (_ ~! _) (G'' , EComp (ELift {w* = FV v} (deepEquiv rG' (eSwap {w* = FV vw} {w*' = w}))) (coe (_ ~! _) E)))

lSolveFindVar {G = []} _ = impossible3
lSolveFindVar {G = G >> v1} {a} {x} {rG} {y} v = decLS' x & \where
  nothing  -> do
    _ , E <- lSolveMidBubble (strengthenOccVar x) {gG = []} (fv v1) {rG = rG} {y = coe (_ ~! _) y} (coe (_ ~! _) v)
    pure (subst ETr (_ ~! _) (_ , E))
  (just (v2 , refl , emb e)) -> do
    _ , E <- lSolveBubble rG {y = coe (Tm (liftRG rG a) ~! Tm (liftRG rG (weaken (fvTy v2)))) y} (coe (_ ~! _) v)
    pure (subst ETr (_ ~! _) (_ , E))

lrSolveFindVar :
  {G : Con} {a : Ty G} {x : OccVar a} {y : OccVar a} (v : FreeVar (Id (occVarToTm x) (occVarToTm y)))
  -> TC (ETr (G >> FV v))
lrSolveFindVar {G = []} _ = impossible4
lrSolveFindVar {G = G >> v1} {a} {x} {y} v = decLS' x & \where
  nothing  -> decLS' y & \where
    nothing -> do
      let v' = coe (_ ~! _) (strengthenFreeVar v)
      G'' , E <- lrSolveFindVar {G = G} {x = strengthenOccVar x} {y = strengthenOccVar y} v'
      pure (subst ETr (_ ~! _) (_ , EComp (eSwap {w* = v1} {w*' = FV v}) (ELift {G = _} {G' = G''} {w* = weakenFreeVar' v1} (coe (_ ~! _) E))))
    (just (v2 , refl , emb e)) -> do
      _ , E <- rSolveBubble {w* = v2} [] {x = coe (Tm a ~! Tm (liftRG [] (weaken (fvTy v2)))) (occVarToTm x)} (coe (_ ~! _) v)
      pure (subst ETr (_ ~! _) (_ , E))
  (just (v2 , refl , emb e)) -> do
    _ , E <- lSolveBubble {w* = v2} [] {y = coe (Tm a ~! Tm (liftRG [] (weaken (fvTy v2)))) (occVarToTm y)} (coe (_ ~! _) v)
    pure (subst ETr (_ ~! _) (_ , E))

lrSolveIdFound : (G : Con) {a : Ty G} {x y : Tm a} (v : FreeVar (Id x y)) -> TC (ETr (G >> FV v))

injRules : (G : Con) {a : Ty G} {x y : Tm a} (v : FreeVar (Id x y)) -> TC (ETr (G >> FV v))
injRules G {a = El (Record# {ind = Ind} rd _)} {x} {y} v = do
  v' <- newFreeVar (GeneratedVar "v")
  G'' , E <- lrSolveIdFound G {x = proj x} {y = proj y} v'
  pure (_ , EComp (ETy EIdProj) E)
injRules G {a = El (Either# a b)} {x = Left x} {y = Left y} v = do
  v' <- newFreeVar (GeneratedVar "v")
  G'' , E <- lrSolveIdFound G {x = x} {y = y} v'
  pure (_ , EComp (ETy EIdLeft) E)
injRules G {a = El (Either# a b)} {x = Right x} {y = Right y} v = do
  v' <- newFreeVar (GeneratedVar "v")
  G'' , E <- lrSolveIdFound G {x = x} {y = y} v'
  pure (_ , EComp (ETy EIdRight) E)
injRules G {a = El (Sigma# ind a b)} {x} {y} v = do    -- TODO: both ind allowed?
  v' <- newFreeVar (GeneratedVar "v")
  G1 , E1 <- lrSolveIdFound G {x = first x} {y = first y} v'
--  v'' <- newFreeVar (GeneratedVar "v")
--  G2 , E2 <- lrSolveIdFound G {x = second x} {y = second y} v''
  throwError "TODO: injectivity for pairs"
injRules G {a} {x} {y} v = throwErrorM ("refl solve failed: " <>m showM x <>m " =?= " <>m showM y)

lrSolveIdFound G {a} {x} {y} v = do
  nothing <- convertMaybe x y <&> _<&>match where
    (just refl) -> do
      v , refl <- newFreeVar'' (GeneratedVar "v")
      pure (_ , EComp (ETy {w*' = v} EDel) ETop)
  matchVarX x & \where
    (just x) -> matchVarX y & \where
      (just y) -> coe (_ ~! _) (lrSolveFindVar {x = x} {y = y} (coe (_ ~! _) v))
      nothing -> coe (_ ~! _) (lSolveFindVar {x = x} {rG = []} {y = subst (\a -> Tm a) (a ~! a [ varsRG [] ]) y} (coe (_ ~! _) v))
    nothing -> matchVarX y & \where
      (just y) -> coe (_ ~! _) (rSolveFindVar {y = y} {rG = []} {x = subst (\a -> Tm a) (a ~! a [ varsRG [] ]) x} (coe (_ ~! _) v))
      nothing -> injRules G {x = x} {y = y} v

checkIdPos : {a : Ty (G* >> w*)} {x y : Tm a} -> OccVar (Id x y) ->
  maybe (Ty G* ** \a' -> Tm a' ** \x' -> Tm a' ** \y' -> FreeVar (Id x' y') ** \v' -> G* >> FV v' ~e' G* >> w*)
checkIdPos s = occVarToFreeVar' s <&> \(_ , e) -> (_ , _ , _ , _ , e)

lrSolveId : (G : Con) {a : Ty G} {x y : Tm a} -> OccVar (Id x y) -> TC (ETr G)
lrSolveId []       _ = impossible5
lrSolveId (G >> _) n = checkIdPos n & \where
  (just (_ , _ , _ , v' , refl)) -> lrSolveIdFound G v'
  nothing  -> do
    _ , E <- lrSolveId G (strengthenOccVar n)
    pure (_ , ELift E)

lrSolve G {a = El (Id# x y)} s = matchVarX s & \where
   nothing  -> throwError "left solve failed (2)"
   (just n) -> lrSolveId G n
lrSolve _ _ = throwError "left solve failed (1)"


-----------------------------------------


mainTC : string -> TC stringBuilder
mainTC s = do
  d <- parse s
  _ <- inferTop (pure {A = top} tt) d
  getLog

main' : string -> string
main' s = runStringBuilder (fromEither (runTC (mainTC s)) <> "\n")

outName : string -> string
outName s = "/tmp/" <> hashString s <> ".csipout"

diff : string -> string -> string
diff s s' = s == s' & \where
  true -> "OK\n"
  false -> "results differ!\n"

main : IO top
main = getArgs >>= \where
  ("diff" :: fs) -> do
    _ <- flip mapM fs \f -> do
      s <- readFile f
      let res = main' s
      res' <- readFile (outName s)
      putStr (diff res res')
    pure tt
  (f :: []) -> do
    s <- readFile f
    let res = main' s
    _ <- writeFile (outName s) res
    putStr res
  _ -> putStr "Usage: Csip FILENAME\n"


