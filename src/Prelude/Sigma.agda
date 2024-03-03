{-# OPTIONS --type-in-type #-}
module Prelude.Sigma where
open import Agda.Primitive
open import Prelude.Function
open import Prelude.Idiom

infixr 4 _,_
record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

{-# BUILTIN SIGMA Σ #-}

infix 2 Σ-syntax
Σ-syntax : ∀ (A : Set) (B : A → Set) → Set
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

infix 2 ∃-syntax
∃-syntax : ∀ {A : Set} (B : A → Set) → Set
∃-syntax = Σ _

syntax ∃-syntax (λ x → B) = ∃[ x ] B

instance
  𝐒𝐞𝐭-cartesian : Cartesian Function
  𝐒𝐞𝐭-cartesian = record
    { _×_ = λ A B → Σ[ _ ∈ A ] B
    ; π₁ = fst
    ; π₂ = snd
    ; <_,_> = λ f g x → f x , g x
    }
