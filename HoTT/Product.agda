module Product where
open import Agda.Primitive

record Σ {𝔞 𝔟} (A : Set 𝔞) (B : A → Set 𝔟) : Set (𝔞 ⊔ 𝔟) where
  constructor _,_
  field
    π₁ : A
    π₂ : B π₁

open Σ public
