{-# OPTIONS --type-in-type --no-positivity-check --no-termination-check --rewriting --prop --injective-type-constructors --hidden-argument-puns #-}
module TCMonad where

open import Prelude
open import Model
open import Parser

record TCMonad (TC : Set -> Set) : Set where
    field
        {{[m]}} : MonadError StringBuilder TC
        lookupShow : TName a -> TC Bool
        addShow : TName a -> Doc -> TC T
        delShow : TName a -> TC T
        newNameT : String -> TC (TName a)
        addLocal : TName a -> TC A -> TC A

open TCMonad {{...}} hiding ([m]) public
