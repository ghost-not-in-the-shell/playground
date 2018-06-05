module Jellyfish.Prelude.Product where
open import Agda.Primitive

infixr 5 _,_
record Σ {𝔞 𝔟} (A : Set 𝔞) (B : A → Set 𝔟) : Set (𝔞 ⊔ 𝔟) where
  constructor _,_
  field
    π₁ : A
    π₂ : B π₁

open Σ public

∃ : ∀ {𝔞 𝔟} {A : Set 𝔞} (B : A → Set 𝔟) → Set (𝔞 ⊔ 𝔟)
∃ B = Σ _ B

infixr 2 _×_
_×_ : ∀ {𝔞 𝔟} (A : Set 𝔞) (B : Set 𝔟) → Set (𝔞 ⊔ 𝔟)
A × B = Σ A (λ _ → B)
