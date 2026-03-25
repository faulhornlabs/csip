module CoreC

import public Data.Fin
import Control.Function.FunExt

%default total
%hide Prelude.cong
%hide Prelude.(<=>)
%hide Prelude.Ops.infix.(<=>)
%hide Prelude.Ops.infixr.(::)
%hide Builtin.replace

public export infixl 9 $$
public export infixr 6 ::
public export infixr 9 =.=
public export infixr 9 :.:
--infixr 6 :s:
public export infixr 5 +
public export infix  2 <=>
public export infix 3 =/=
public export infix 0 =|=
public export infixr 1 =#=
public export infixr 9 <.>
public export infixr 6 :*:
public export infixr 6 =>>

{-
record Eq {a : Type} (T : a -> a -> Type) where
    constructor MkEq
    ParamTy : Type
    transf : {0 va, vb : a} -> {eq : va `T` vb} -> (1 vc : a) -> (1 p : (1 _ : ParamTy) -> Type) -> Type
    substs : {0 va, vb : a} -> (0 p : (1 _ : ParamTy) -> Type) -> (eq : va `T` vb) -> (1 px : transf {eq = eq} va p) -> transf {eq = eq} vb p


%hint
eqq : {a : Type} -> Eq {a} (Equal)
eqq = MkEq a (\vc, p => p vc) (\p, Refl, px => px)

replace : (eq : Eq t) => {0 va, vb : a} -> {0 p : (1 _ : ParamTy eq) -> Type} -> (val : va `t` vb) -> (1 px : transf eq {eq = val} va p) -> transf eq {eq = val} vb p
replace {eq = eq} {p = p} val px = (substs eq p val px)

EQ' : {a : Type} -> {t : a -> a -> Type} -> (eq : Eq {a = a} t) => Type
EQ' = (x : a) -> (y : a) -> t x y

--%rewrite (===) replace
 -}

public export
(=.=) : 
    (1 _ : x === y)
    -> (1 _ : y === z)
    -> x === z
Refl =.= a = a

public export
coe : (1 _ : a) -> (0 _ : a === b) -> b
coe a Refl = a

public export
(:.:) : 
    (0 e : x === y) ->
    (0 e' : y === z) ->
    coe (coe w e) e' === coe w (e =.= e')
Refl :.: Refl = Refl

--- Seems like K works in Idris
public export
idRefl : {auto 0 cid : x} -> {auto 0 e : x === x} -> (coe cid e) === cid
idRefl {e = Refl} = Refl

public export
cong : 
    (0 f : a -> b) ->
    (0 _ : x === y)
    -> f x === f y
cong _ Refl = Refl

public export
subst : 
    (0 p : a -> Type) ->
    (0 eq : u === v) ->
    (1 x : p u) -> p v
subst p e x = coe x (cong p e)

namespace Eq
    public export
    replace :
        {auto 0 p : a -> Type} ->
        (0 _ : u = v) ->
        (1 x : p u) -> p v
    replace = subst p

public export
(=#=) : {0 b : (0 _ : a) -> Type} -> {0 va, va' : a} -> { 0 vb : b va} -> {0 vb' : b va'} ->
    (0 e : va === va') -> (0 _ : subst (\t => b t) e vb === vb') ->
    (===) {a = (DPair a (\v => b v))} (MkDPair va vb)  (MkDPair va' vb')
Refl =#= Refl = Refl

public export
not : Type -> Type
not a = a -> Void

public export
(=/=) : a -> a -> Type
a =/= b = not (a === b)

public export
etaDPair : {auto 0 k : DPair _ _} -> (MkDPair (fst k) (snd k)) === k
etaDPair {k = (MkDPair _ _)} = Refl

public export
etaDFun : {auto 0 f : (0 _ : a) -> b } -> (\x => f x) === f
etaDFun = Refl

public export
decFin : (1 i , j : Fin n)  -> Dec (i === j)
decFin FZ FZ = Yes Refl
decFin FZ (FS _) = No $ \case Refl impossible
decFin (FS _) FZ = No $ \case Refl impossible
decFin (FS n) (FS m) with (decFin n m)
    decFin (FS m) (FS m) | (Yes Refl) = Yes Refl
    decFin (FS n) (FS m) | (No f) = No (\Refl => f Refl)


namespace FinVec
    public export
    data FinVec : (0 n : Nat) -> (0 _ : Fin n -> Type) -> Type where
        Nil : FinVec Z p
        (::) : p FZ -> FinVec n (\f => p (FS f)) -> FinVec (S n) p

public export
indexFinVec : (1 _ : FinVec n p) -> (1 f : Fin n) -> p f
indexFinVec (x :: y) (FZ ) = x
indexFinVec (x :: xs) (FS y) = indexFinVec xs y

public export
coveredBy : {auto 0 tag : Fin n} -> FinVec n (\ f => tag =/= f) -> a
coveredBy vs = void (indexFinVec {p = \f => tag =/= f} vs tag Refl)

public export
record (<=>) (0 a , b : Type) where
    constructor MkEquiv
    forward  : a -> b
    backward : b -> a
    0 isLInv : (0 x : _) -> backward (forward x) === x
    0 isRInv : (0 x : _) -> forward (backward x) === x


public export
solveBy :
    (e : a <=> b) ->
    (0 p : a -> Type) ->
    (1 _ : (1 y : b) -> p (backward e y)) ->
    (x : a) ->
    p x
solveBy e p subgoal x = rewrite sym (isLInv e x) in (subgoal (forward e x))

public export
idEquiv : a <=> a
idEquiv = MkEquiv id id (\_ => Refl) (\_ => Refl)

public export
weaken : (0 _ : a === b) -> a <=> b
weaken Refl = idEquiv

public export
symEquiv : a <=> b -> b <=> a
symEquiv e = MkEquiv (backward e) (forward e) (isRInv e) (isLInv e)

--isoq : Eq {a = DPair Type (\x => x)}
--isoq = MkEq (\a, b => fst a <=> fst b) (symEquiv) (\va,vb,dp,c,r => snd dp ?_) ?__

public export
(<.>) : a <=> b -> b <=> c -> a <=> c
l <.> r = let
    public export
    chain : {0 a : _} -> {0 b : _} -> {0 ch : _} ->
        (f : a -> b) -> (f' : b -> ch ) ->
        (g : b -> a) -> (g' : ch -> b) ->
        ((0 x : _) -> g' (f' x) === x) ->
        ((0 x : _) -> g (f x) === x) ->
        (0 x : _) -> g (g' (f' (f x))) === x
    chain f f' g g' e1 e2 x = cong g (e1 $ f x) =.= e2 x
 in MkEquiv 
    (\e => forward r (forward l e))
    (\e => backward l (backward r e))
    (chain (forward l) (forward r) (backward l) (backward r) (isLInv r) (isLInv l))
    (chain (backward r) (backward l) (forward r) (forward l) (isRInv l) (isRInv r))

public export
delete : x === x <=> Unit
delete = MkEquiv 
    (\_     => ()   )
    (\_     => Refl )
    (\Refl  => Refl )
    (\()    => Refl ) -- Idris somehow unable to use Unit eta

public export
solveRight : {auto va : a} -> DPair a (\v => va === v ) <=> Unit
solveRight = MkEquiv 
    (\(MkDPair _ Refl)   => ()           )
    (\_             => (MkDPair _ Refl)  )
    (\(MkDPair _ Refl)   => Refl         )
    (\()            => Refl         )

public export
solveLeft : {auto va : a} -> DPair a (\v => v === va) <=> Unit
solveLeft = MkEquiv 
    (\(MkDPair _ Refl)   => ()           )
    (\_             => (MkDPair _ Refl)  )
    (\(MkDPair _ Refl)   => Refl         )
    (\()            => Refl         )

public export
decompEq : {auto 0 b : (0 _ : a) -> Type} -> {auto 0 va , va' : a} ->
    {auto 0 vb : b va} -> {auto 0 vb' : b va'} ->
        (MkDPair {p = (\t => b t)} va vb) === (va' ** vb')
    <=>
        DPair (va === va') (\e => subst (\t => b t) e vb === vb')
decompEq = MkEquiv 
    (\Refl              => (MkDPair Refl Refl))
    (\(MkDPair Refl Refl)    => Refl          )
    (\Refl => Refl                       )
    (\(MkDPair Refl Refl)    => Refl          )

public export
VoidFst : (DPair Void (\_ => b)) <=> Void
VoidFst = MkEquiv 
    fst
    (\_ impossible          )
    (\k => void $ fst k     )
    (\_ impossible          )

public export
VoidSnd : (DPair b (\_ => Void)) <=> Void
VoidSnd = MkEquiv 
    snd
    (\_ impossible          )
    (\k => void $ snd k     )
    (\_ impossible          )

---------------------

public export
unit : {auto 0 cc : _} -> DPair Unit (\_ => cc) <=> cc
unit = MkEquiv 
    snd
    (\vcc         => (MkDPair () vcc))
    (\(MkDPair () _) => Refl     )
    (\_         => Refl     )

public export
ignore : {auto 0 a : _} -> DPair a (\_ => Unit) <=> a
ignore = MkEquiv 
    fst
    (\a => (MkDPair a ()))
    (\(MkDPair _ ()) => Refl)
    (\_ => Refl)

--swap
public export
comm : {auto 0 ccc : (0 _ : _) -> (0 _ : _) -> Type} ->
        DPair a (\x => DPair b (\y => ccc x y))
    <=>
        DPair b (\y => DPair a (\x => ccc x y))
comm = MkEquiv 
    (\k => (MkDPair (k.snd.fst) (MkDPair (k.fst) (k.snd.snd))))
    (\k => (k.snd.fst ** k.fst ** k.snd.snd))
    (\(_ ** _ ** _) => Refl         )
    (\(_ ** _ ** _) => Refl         )

public export
assoc : {auto 0 b : (0 _ : _) -> Type} -> {auto 0 cccc : (0 x : a) -> (0 _ : b x) -> Type} ->
        DPair a (\ x => DPair (b x) (\ y => cccc x y))
    <=>
        (DPair (DPair a (\x => b x)) (\k => (cccc k.fst k.snd)))
assoc = MkEquiv 
    (\k     => ((k.fst ** k.snd.fst) ** snd (snd k))  )
    (\k   => (k.fst.fst ** k.fst.snd ** k.snd)    )
    (\(_ ** _ ** _)     => Refl             )
    (\((_ ** _) ** _)   => Refl             )

public export
second : ((0 x : ccccc) -> a x <=> b x) ->
        DPair ccccc a
    <=>
        DPair ccccc b
second f = MkEquiv 
    (\k => (k.fst ** forward (f k.fst) k.snd))
    (\k => (k.fst ** backward (f k.fst) k.snd))
    (\(x ** y) => cong (\z => (x ** z)) (isLInv (f x) y))
    (\(x ** y) => cong (\z => (x ** z)) (isRInv (f x) y))

public export
first : (e : a <=> a') ->
        DPair a b
    <=>
        DPair a' (\x => b (backward e x))
first {b = b} e = MkEquiv 
    (\k => (forward e k.fst ** subst b (sym $ isLInv e k.fst) k.snd))
    (\k => (backward e k.fst ** k.snd))
    (\(x ** _) => (isLInv e x) =#= Refl)
    (\(x ** _) => (isRInv e x) =#= Refl)

public export
solveL : {auto va : a} -> {auto 0 b : (0 v : a) -> (0 _ : v === va) -> Type} ->
  DPair a (\v => DPair  (v === va) (\g => b v g))  <=>  b va Refl
solveL = assoc {b = \v => v === va} {cccc = b} <.> first solveLeft <.> unit {cc = b va Refl} --symEquiv (assoc {a = a} {cccc = \x, y => b x y}) <.> first {b = \v => ?he} solveLeft <.> ?_unit

public export
solveR : {auto va : a} -> {auto 0 b : (0 v : a) -> (0 _ : va === v) -> Type} ->
  DPair a (\v => DPair (va === v) (\g => b v g)) <=> b va Refl
solveR = assoc {b = \v => va === v} {cccc = b} <.> first solveRight <.> unit {cc = b ((backward solveRight ()) .fst) ((backward solveRight ()) .snd)}

public export
decomp : {auto 0 b : a -> Type} -> {auto 0 va, va' : a} -> {auto 0 vb : b va} -> {auto 0 vb' : b va'} -> 
        {0 ce : (0 _ : (===) (MkDPair {p = b} va vb) (MkDPair {p = b} va' vb')) -> Type} ->
        (<=>)
        (DPair ((MkDPair {p = b} va vb) === (MkDPair {p = b} va' vb')) (\v => ce v))
        (DPair (va === va') (\e => DPair ((subst b e vb) === vb') (\e' => ce (e =#= e'))))
--decomp = first decompEq <.> (symEquiv assoc)
decomp = MkEquiv 
    (\k@(Refl ** _ ) => (Refl ** (Refl ** k.snd)))
    (\arg@(Refl ** Refl ** _) => (Refl ** arg.snd.snd))
    (\(Refl ** _) => Refl)
    (\(Refl ** Refl ** _) => Refl)

public export
sndComm : {auto 0 a, b : _} -> {auto 0 aa : (0 _ : a) -> Type} -> {auto 0 c6 : (0 _ : a) -> (0 _ : b) -> Type} -> ((0 e : a) -> aa e <=> DPair b (\t => c6 e t)) ->
        DPair a (\a => aa a)
    <=>
        DPair b (\y => DPair a (\x => c6 x y))
sndComm f = second {ccccc = a} f <.> comm {ccc = c6}

public export
sndAssoc : {auto 0 a : _} -> {auto 0 aa, b : a -> Type} -> {auto 0 c7 : (0 x : a) -> (0 _ : b x) -> Type} ->
    ((0 x : a) -> aa x <=> (DPair (b x) (\vb => c7 x vb))) ->
        (DPair a  aa)
    <=>
        DPair (DPair a b ) (\k => c7 (fst k) (snd k))
sndAssoc f = second (\x => f x) {ccccc = a} <.> assoc {b = \v => b v} {cccc = c7}

public export
sndVoid : (f : (0 e : a) -> b e <=> Void) ->
        DPair a b
    <=>
        Void
sndVoid f = second (\x => f x) <.> VoidSnd

---------------------

namespace Ty
    public export
    data Ty : Type
namespace Tm
    public export
    data Tm : (1 _ : Ty) -> Type

namespace Tys
    public export
    data Tys : Type where
        Nil : Tys
        (::): (t : Ty) -> (Tm t -> Tys) -> Tys

public export
Tms : (1 _ : Tys) -> Type
Tms Nil = Unit
Tms (t :: ts) = DPair (Tm t) (\ x => Tms (ts x))

namespace DCDesc
    public export
    record DCDesc (indices : Tys) where
        constructor DCD
        name  : String -- for Display
        args  : Tys
        sub     : Tms args -> Tms indices

namespace TCDesc
    public export
    record TCDesc where
        constructor TCD
        name : String
        indices : Tys
        numOfCstrs : Nat
        descs : Fin numOfCstrs -> DCDesc indices

    public export
    DcFin : TCDesc -> Type
    DcFin d = Fin d.numOfCstrs

    public export
    dcArgs : (d : TCDesc) -> (DcFin d) -> Tys
    dcArgs d n = DCDesc.args (d.descs n)

    public export
    sub : (d : TCDesc) -> (c8 : DcFin d) -> Tms (TCDesc.dcArgs d c8) -> Tms (TCDesc.indices d)
    sub d vc8 = DCDesc.sub (d.descs vc8)

namespace RCDesc
    public export
    record RCDesc where
        constructor RTCD
        tcName : String -- type constructor name for pretty printing
        dcName : String -- data constructor name for pretty printing
        params : Tys
        args : Tms params -> Tys

namespace Ty
    public export
    covering
    data Ty where
        U : Ty
        Pi : (a : Ty) -> (1 _ : (Tm a -> Ty)) -> Ty
        -- Because of Pi, Idris think it's not strictly positive.
        -- I think this is because of mutual recursivity.
        -- Could somehow this be asserted?
        TC : (tc : _) -> Tms (TCDesc.indices tc) -> Ty
        RTC : (rc : _) -> Tms (RCDesc.params rc) -> Ty

    public export
    (:*:) : Ty -> Tys -> Tys
    a :*: as = a :: \_ => as

    public export
    (=>>) : Ty -> Ty -> Ty
    a =>> b = Pi a (\_ => b)

namespace Tm
    public export
    covering
    data Tm where
        Code : (1 _ : Ty) -> Tm U
        Lam : {0 a : Ty} -> {0 b : Tm a -> Ty} -> (1 _ : (x : Tm a) -> Tm (b x)) -> Tm (Pi a b)
        DC : (1 tag : DcFin tc) -> (1 args : Tms (TCDesc.dcArgs tc tag)) -> Tm (TC tc (sub tc tag args))
        RDC : {0 is : _} -> (1 args : Tms (args rc is)) -> Tm (RTC rc is)

    public export
    El : (1 _ : Tm U )-> Ty
    El (Code t) = t

    public export
    ($$) : {0 a : Ty} -> {0 b : Tm a -> Ty} -> (1 _ : Tm (Pi a b)) -> (x : Tm a) -> Tm (b x)
    ($$) (Lam f) = f -- (Lam f) $$ x = f x is a bad implementation, because the Idris can't solve ($$) (Lam f) === f

    public export
    proj : {0 params : _} -> (1 _ : Tm (RTC rc params)) -> Tms (args rc params)
    proj (RDC args) = args

    covering
    public export
    betaU : El (Code a) === a
    betaU = Refl

    public export
    covering
    etaU : {0 a : Tm U} -> a === Code (El a)
    etaU {a = Code _} = Refl

    covering
    public export
    betaPi : {0 b : _} -> {0 f : (x : Tm a) -> Tm (b x)} -> {0 x : Tm a} -> (Lam f $$ x) === (f x)
    betaPi = Refl

    public export
    etaPi : {0 f : Tm (Pi a b)} -> f === Lam (\x => f $$ x)
    etaPi {f = Lam _} = Refl

    covering
    public export
    etaRecord : {0 params : _} -> {0 t : Tm (RTC rc params)} -> t === RDC (proj t)
    etaRecord {t = RDC _} = Refl

    public export
    dcTag : {0 indices : _} -> (Tm (TC tc indices)) -> DcFin tc
    dcTag (DC constr _) = constr

namespace IndEq
    public export
    covering
    (=|=) : {0 tc : _} ->
            {0 ind : _} ->
            {0 ind' : _} ->
            Tm (TC tc ind) ->
            Tm (TC tc ind') ->
                Type
    a =|= b = (a = b)

    public export
    covering
    ifTag : {0 tc : _} -> {0 indices : _} ->
            (tag : DcFin tc) ->
            (tm : Tm (TC tc indices)) ->
            (match : (args' : Tms (TCDesc.dcArgs tc tag)) -> DC tag args' =|= tm -> a) ->
            (fail : (Tm.dcTag tm =/= tag) -> a) ->
            a
    ifTag tag (DC tag' l) match fail with (decFin tag' tag)
        ifTag tag' (DC tag' l) match fail | (Yes Refl) = match l Refl
        _ | (No f) = fail f

public export
covering
matchCode : Tm U <=> Ty
matchCode = MkEquiv 
    (\ e => El e)
    (\ e => Code e)
    (\(Code _) => Refl)
    (\_ => Refl)

public export
covering
injCode : Code a === Code a' <=> a === a'
injCode = MkEquiv 
    (\Refl => Refl)
    (\Refl => Refl)
    (\Refl => Refl)
    (\Refl => Refl)

public export
covering
matchLam : {0 a : Ty} -> {0 b : Tm a -> Ty} -> Tm (Pi a b) <=> ((x : Tm a) -> Tm (b x))
matchLam = MkEquiv 
    (\e => ($$) e)
    (\e => Lam e)
    (\(Lam _) => Refl)
    (\_ => Refl)

public export
covering
matchRefl : {auto 0 is, is' : _} -> {auto 0 t : Tm (TC tc is)} -> {auto 0 t' : Tm (TC tc is')} -> (t =|= t') <=> (MkDPair is t) === (MkDPair is' t')
matchRefl = MkEquiv 
    (\Refl => Refl)
    (\Refl => Refl)
    (\Refl => Refl)
    (\Refl => Refl)

public export
covering
conflict : {0 tc : TCDesc} -> {0 t, t' : DcFin tc} -> {args : Tms (dcArgs tc t)} ->
    {args' : Tms (dcArgs tc t')} ->
    t =/= t' ->
    (DC {tc} t args =|= DC {tc} t' args') <=> Void
conflict ne = MkEquiv 
    (\Refl => ne Refl)
    (\ _ impossible)
    (\Refl =>let
        uniq : {0 is : Tms (TCDesc.indices tc)} -> {0 t : Tm (TC tc is)} -> {0 a : t =|= t} -> a === Refl
        uniq {a = Refl} = Refl
     in uniq)
    (\ _ impossible)

public export
covering
EqIso : {auto 0 tc : _} -> {0 is : Tms (TCDesc.indices tc)} -> {0 t , t' : Tm (TC tc is)} ->
    t === t' <=> (t =|= t')
EqIso = MkEquiv 
    (\Refl => Refl)
    (\Refl => Refl)
    (\Refl => Refl)
    (\Refl => Refl)

public export
interface UIP where
    uip : (u , v : a === b) -> u === v

public export
interface FunExt => UIP => InProp where

