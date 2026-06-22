{-# OPTIONS --type-in-type --no-positivity-check --no-termination-check --rewriting --prop --injective-type-constructors --hidden-argument-puns #-}
open import TCMonad
module Printer (TC : Set -> Set) {{m : TCMonad TC}} where
open import Prelude
open import Model
open import Parser

printName' : Name -> Doc
printName' n = Var (pr (nameStr n)) {{believeMe~}} where
    pr : String -> String
    pr "lam" = "lam" <> showNat (nameId n)
    pr "v"   = "v"   <> showNat (nameId n)
    pr n     = n

printName : Name -> TC Doc
printName n = pure (printName' n)

printTm    : Tm    a -> TC Doc
printSpine : Spine a -> TC Doc

printSpine (Head (named n Stuck)) = printName n
printSpine {a} e@(Head (named n l)) = do
    _ <- do
        let n' = MkTName {a = a} n
        False <- lookupShow n'  where
            True -> pure tt
        _ <- addShow n' (Var "IN_PROGRESS")
        e <- printTm (spineToTm e)
        _ <- delShow n'
        _ <- addShow (MkTName {a = a} n) e
        pure tt
    printName n
printSpine (s $  x) = printSpine s $m printTm x
printSpine (_$$_ {a} s x) = isTy a & \where
        True  -> printSpine s
        False -> printSpine s $m printTm x
    where
        isTy' : {a : _} -> Spine a -> Bool
        isTy' (Head n) = nameStr (name n) == "Ty"
        isTy' _ = False

        isTy : Ty -> Bool
        isTy (NU (NeU' {s} _)) = isTy' s
        isTy _ = False

printTm {a = U} U           = KWm "U" []
printTm {a = U} Top         = KWm "Top" []
printTm {a = U} Bot         = KWm "Bot" []
printTm {a = U} (a => a')   = printTm a [ "->" ]m printTm a'
printTm {a = U} (a * a')    = printTm a [ "*"  ]m printTm a'
printTm {a = U} (a \/ a')    = printTm a [ "+"  ]m printTm a'
printTm {a = U} (Pi a b)    = KWm "Pi"      (printTm a :: printTm b :: [])
printTm {a = U} (Sigma a b) = KWm "Sigma"   (printTm a :: printTm b :: [])
printTm {a = U} (Id x y)    = printTm x [ "=="  ]m printTm y
printTm {a = U} (Rec rc x)  = printName (name rc) $m printTm x
printTm {a = U} (NU (NeU' {s} _)) = printSpine s
printTm {a = a => a'} t = do
    n <- newNameT "v"
    printName (tName n) [ "." ]m printTm (t # var n)
printTm {a = Pi a b} t = do
    n <- newNameT "v"
    printName (tName n) [ "." ]m printTm (t ## var n)
printTm {a = NU _} TT        = KWm "TT" []
printTm {a = NU _} (x ,  y)  = printTm x [ ","  ]m printTm y
printTm {a = NU _} (x ,, y)  = printTm x [ ","  ]m printTm y
printTm {a = NU _} (Left  x) = KWm "Left"  (printTm x :: [])
printTm {a = NU _} (Right x) = KWm "Right" (printTm x :: [])
printTm {a = NU _} Refl      = KWm "Refl" []
printTm {a = NU _} (Wrap {rc} args) = KWm "Wrap" (printTm args :: [])
printTm {a = NU _} (NeNU {s} _) = printSpine s

----

showTm : Tm a -> TC StringBuilder
showTm t = do
    t <- printTm t
    pure (showDoc t)

showSpine : Spine a -> TC StringBuilder
showSpine t = do
    t <- printSpine t
    pure (showDoc t)
