{-# OPTIONS --type-in-type #-}
module NaturalTransformation.Equivalence where
open import Prelude
open import Category.Base
open import Category.Functor
open import Functor.Base
open import Isomorphism
open import NaturalTransformation.Base

component-≅ : ∀ {𝓒 𝓓} {𝓕 𝓖 : 𝓒 ⟶ 𝓓} {α : 𝓕 ⟹ 𝓖}
  → Isomorphism (𝓕𝓾𝓷 𝓒 𝓓) α
  → ∀ A → Isomorphism 𝓓 (α ₍ A ₎)
component-≅ α A = record
  { inverse = (α ⁻¹) ₍ A ₎
  ; isoˡ = cong _₍ A ₎ $ isoˡ α
  ; isoʳ = cong _₍ A ₎ $ isoʳ α
  }

infix 4 _≃_
record _≃_ 𝓒 𝓓 : Set where
  field
    to   : 𝓒 ⟶ 𝓓
    from : 𝓓 ⟶ 𝓒

    unit   : id₍ 𝓒 ₎ ≅ from ∘ to [ 𝓕𝓾𝓷 𝓒 𝓒 ]
    counit : to ∘ from ≅ id₍ 𝓓 ₎ [ 𝓕𝓾𝓷 𝓓 𝓓 ]
