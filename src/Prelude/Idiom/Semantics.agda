{-# OPTIONS --type-in-type #-}
module Prelude.Idiom.Semantics where

record Bracket (A : Set) : Set where
  field
    Sem : Set
    ⟦_⟧ : A → Sem

open Bracket ⦃ ... ⦄ public

{-# DISPLAY Bracket.⟦_⟧ _ x = ⟦ x ⟧ #-}
