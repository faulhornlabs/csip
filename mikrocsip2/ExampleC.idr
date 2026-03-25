module ExampleC

import CoreC

%default total
%hide Prelude.cong
%hide Prelude.(<=>)
%hide Prelude.Ops.infix.(<=>)
%hide Prelude.Ops.infixr.(::)

covering
public export
IdDesc : TCDesc
IdDesc = TCD "Id" (U :: \a => El a :*: El a :*: Nil) 1 $ 
    \ FZ => DCD "Refl" (U :: \a => El a :*: Nil) $ \k => (fst k ** fst (snd k) ** fst (snd k) ** ())

covering
Id : {a : _} -> Tm a -> Tm a -> Ty
Id x y = TC IdDesc (Code a ** x ** y ** ())

covering
refl : {a : _} -> {x : Tm a} -> Tm (Id x x)
refl {a} {x} = DC FZ (Code a ** x ** ())



covering
J' : {a : _} -> {b : Tm a} -> (p : (x : Tm a) -> Tm (Id b x) -> Ty) ->
    Tm (p b ExampleC.refl) ->
    (x : Tm a) -> (e : Tm (Id b x)) -> Tm (p x e)
J' {a = a} {b = b} p w x e =
    ifTag 0 e
        (\k, ee => 
            solveBy equivTel
            (\(_ ** _ ** p ** _ ** x ** e ** _ ** _ ** ()) => Tm (p x e))
            (\(a ** b ** p ** w ** x ** e ** a' ** x' ** ee ** ()) =>
                solveBy equivCode
                (\(_ ** _ ** p ** _ ** x ** e ** _ ** _ ** _ ** ()) => Tm (p x e))
                (\(a ** b ** p ** w ** x ** e ** a' ** x' ** ee ** ()) =>
                    solveBy equiv12
                    (\(_ ** _ ** p ** _ ** x ** e ** _ ** _ ** _ ** ()) => Tm (p x e))
                    (\(_ ** _ ** _ ** w ** ()) => ?w)
                    (a ** b ** p ** w ** x ** e ** a' ** x' ** ee ** ())
                )
                (a ** b ** p ** w ** x ** e ** a' ** x' ** ee ** ())
            )
            (a ** b ** p ** w ** x ** e ** k ** ee ** ())
        )
        (\f0 => coveredBy {tag = dcTag e} (f0 :: Nil))
    where
        equivTel : (
            a : Ty **
            b : Tm a **
            p : ((x : Tm a) -> Tm (Id b x) -> Ty) **
            w : Tm (p b ExampleC.refl) **
            x : Tm a **
            e : Tm (Id b x) **
            ax : (DPair (Tm U) (\u => DPair (Tm (El u)) (\_ => ()))) **
            DPair (DC 0 ax =|= e) $ \ee =>
            ()
        ) <=> (
            a : Ty **
            b : Tm a **
            p : ((x : Tm a) -> Tm (Id b x) -> Ty) **
            w : Tm (p b ExampleC.refl) **
            x : Tm a **
            e : Tm (Id b x) **
            DPair (Tm U) $ \a' =>
            DPair (Tm (El a')) $ \x' =>
            DPair ((DC 0 (a' ** x' ** ())) =|= e) $ \ee =>
            ()
        )
        equivTel = second $ \a => second $ \b => second $ \p => second $ \w => second $ \x => second $ \e =>
                    (first (second $ \u => ignore {a = Tm (El u)})) <.> (symEquiv (assoc {b = \a' => Tm (El a')} {cccc = \x, y => DPair (DC 0 (x ** (y ** ())) =|= e) (\_ => Unit)}))

        equivCode : (
            a : Ty **
            b : Tm a **
            p : ((x : Tm a) -> Tm (Id b x) -> Ty) **
            w : Tm (p b ExampleC.refl) **
            x : Tm a **
            e : Tm (Id b x) **
            DPair (Tm U) $ \a' =>
            DPair (Tm (El a')) $ \x' =>
            DPair ((DC 0 (a' ** x' ** ())) =|= e) $ \ee =>
            ()
        ) <=> (
            a : Ty **
            b : Tm a **
            p : ((x : Tm a) -> Tm (Id b x) -> Ty) **
            w : Tm (p b ExampleC.refl) **
            x : Tm a **
            e : Tm (Id b x) **
            DPair Ty $ \a'' =>
            DPair (Tm a'') $ \x' =>
            DPair ((DC 0 (Code a'' ** x' ** ())) =|= e) $ \ee =>
            ()
        )
        equivCode = second $ \_ => second $ \_ => second $ \_ => second $ \_ => second $ \_ => second $ \_ =>
            first matchCode

        equiv12 : (
            a : Ty **
            b : Tm a **
            p : ((x : Tm a) -> Tm (Id b x) -> Ty) **
            w : Tm (p b ExampleC.refl) **
            x : Tm a **
            DPair (Tm (Id b x)) $ \e =>
            DPair Ty $ \a'' =>
            DPair (Tm a'') $ \x' =>
            DPair (refl {a = a''} {x = x'} =|= e) $ \ee =>
            ()
        ) <=> (
            a : Ty **
            b : Tm a **
            p : ((x : Tm a) -> Tm (Id b x) -> Ty) **
            w : Tm (p b ExampleC.refl) **
            ()
        )
        equiv12 = second $ \a => second $ \b => second $ \p => second $ \w =>
            second {ccccc = Tm a} (\x => second {ccccc = Tm (Id b x)} $ \e =>
                second (\a' =>
                    (sndComm {a = Tm a'} {b = a' === a} {aa = \x' => DPair (ExampleC.refl {x = x'} =|= e) (\_ => Unit)}
                        {c6 = \z , u =>
                            DPair (subst (\v => Tms (El v :: \_ => El v :: \_ => [])) (backward injCode u) (z ** z ** ()) === (b ** x ** ())) (\e' => DPair (subst (\is => Tm (TC IdDesc is)) (backward injCode u =#= e') refl === e) (\_ => ()))}
                            --(subst (\v => Tms (El v :: \_ => El v :: \_ => [])) (backward injCode u) (z ** z ** ()) === (b ** x ** ()))
                            --(\e' => DPair (subst (\is => Tm (TC IdDesc is)) (backward injCode u =#= e') refl === e)) (\_ => ())}
                        (\_ => first ?matchRefl 
                        <.> decomp {b = \v => ?bav} {va = ?vav} {va' = ?va'v} {vb = ?vbv} {vb' = ?vb'v} {ce = ?ceq}
                        <.> ?decomp_ <.> first injCode))
                        --<.> second {ccccc = a' === a} (\_ => second (\_ =>solveL))
                        <.> ?é
                        --?g
                    ) <.> ?e
            ) <.> ?f
{-
 = sec \a -> sec \b -> sec \P -> sec \w ->
        (sec \x -> sec \e ->
            (sec \a' -> sndSwap {Tm a'} {a' ≡ a} {λ x' → refl ≡≡ e × (λ _ → T)} {λ z x₁ →
                subst (λ x₂ → Tms (El x₂ :× El x₂ :× [])) (backward injCode x₁)
                  (z , z , tt)
                  ≡ (b , x , tt)
                  ×
                  (λ e' →
                     subst (λ is → Tm (TC IdDesc is)) (backward injCode x₁ ,≡ e') refl ≡
                     e
                     × (λ e'' → T))} \_ ->
                decomp
              ∘ decomp
              ∘ first injCode
            )
          ∘ solveL
          ∘ (sec \_ -> decomp)
          ∘ solveL
        )
      ∘ (sec \_ -> sndSwap \_ -> decomp)
      ∘ solveR
      ∘ (sec \_ -> delete')
      ∘ solveR
 -}
{-        equiv12 = second $ \a => second $ \b => second $ \p => second $ \w => 
                (second $ \ x => second $ \e => ?t1
                {-
                (sndAssoc {b = \a'' => 
                        DPair (Tm a'') (\x' => ((DC {tc = IdDesc} FZ (Code a'' ** (x' ** ())) =|= e)))
                    } {c = \ _ , _ => Unit} (\a'' =>
                        
                    -- This was my own try on the matter. Now I think I understand the concept more clearly

                        sndComm {b = Tm a''} {c = \_ , _ => Unit} (\ x' => first (matchRefl <.> decompEq) <.> first 
                            (first (decompEq <.> first injCode ))
                        <.> (symEquiv (assoc {c = \_ , _ => Unit })) <.> second (\_ => ignore) 
                        <.> first (second (\p => rewrite p in decompEq) <.> assoc 
                        <.> second (\ p => decompEq <.> second (\_ => delete) <.> ignore)) <.> ?args <.> ignore <.> symEquiv ignore) <.> second (\_ => ignore) <.> ?t10 <.> symEquiv ignore
                        )
                        ) 
                     -}
                )
            <.>
                ?t2


            (second $ \_ => second $ \_ => sndAssoc (\_ => sndComm (\_ => first (matchRefl <.> decompEq) <.> (symEquiv (assoc {c = \_ , _ => Unit} )) <.> first decompEq <.> symEquiv (assoc {c = \fb, _ => _ fb}) <.> first injCode))
                        <.> first solveLeft <.> unit <.> sndAssoc (\_ => first decompEq <.> symEquiv assoc {b = ?_0}) <.> first solveLeft <.> unit) <.> sndAssoc (\_ => sndComm (\_ => first decompEq <.> (symEquiv assoc)))
                        <.> (first solveRight) <.> unit <.> sndAssoc (\_ => first delete <.> unit ) <.> (first solveRight) <.> unit
-}

public export
TopDesc : RCDesc
TopDesc = RTCD "Top" "Top" [] (\_ => [])

covering
public export
Top : Ty
Top = RTC TopDesc ()

covering
public export
tt : Tm Top
tt = RDC ()

covering
etaTop : {c : Tm Top -> Ty} -> Tm (Pi Top $ \ x => c x =>> c ExampleC.tt)
etaTop = Lam $ \(RDC ()) => Lam $ \cx => cx