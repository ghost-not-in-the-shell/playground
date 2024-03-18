module Prelude.Sigma where
open import Agda.Primitive

infixr 4 _,_

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

{-# BUILTIN SIGMA Σ #-}

infix 2 Σ-syntax

Σ-syntax : ∀ (A : Set) → (A → Set) → Set
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

infix 2 ∃-syntax

∃-syntax : ∀ {A : Set} → (A → Set) → Set
∃-syntax = Σ _

syntax ∃-syntax (λ x → B) = ∃[ x ] B

infixr 2 _×_

_×_ : Set → Set → Set
A × B = Σ[ _ ∈ A ] B
