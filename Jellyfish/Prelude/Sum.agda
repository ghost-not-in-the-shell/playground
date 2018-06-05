module Jellyfish.Prelude.Sum where
open import Agda.Primitive

infixl 1 _∐_
data _∐_ {𝔞 𝔟} (A : Set 𝔞) (B : Set 𝔟) : Set (𝔞 ⊔ 𝔟) where
  inj₁ : A → A ∐ B
  inj₂ : B → A ∐ B
