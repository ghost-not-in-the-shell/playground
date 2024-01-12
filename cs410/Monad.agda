{-# OPTIONS --type-in-type #-}
module Monad where
open import Prelude
open import Category
open import Category.Category

record Monad {𝓒 : Category} (𝓜 : 𝓒 ⟶ 𝓒) : Set where
  field
    unit : id ⟹ 𝓜
    mult : 𝓜 ∘ 𝓜 ⟹ 𝓜

    identityˡ : ∀ {A} → 𝓜 ₁(unit ₍ A ₎) ∘ mult ₍ A ₎ ≡ id
    identityʳ : ∀ {A} → mult ₍ A ₎ ∘ unit ₍ 𝓜 ₀(A) ₎ ≡ id
    assoc : ∀ {A} → mult ⋆ ∘ mult ₍ 𝓜 ₀(A) ₎ ≡ mult ⋆ ∘ 𝓜 ₁(mult ₍ A ₎)

open Monad public

record MonadicOp {𝓒 : Category} (𝓜 : 𝓒 ⟶ 𝓒) : Set where
  field
    return : ∀ {A} → 𝓒 ∣ A ⟶ 𝓜 ₀(A)
    join   : ∀ {A} → 𝓒 ∣ 𝓜 ₀(𝓜 ₀(A)) ⟶ 𝓜 ₀(A)

open MonadicOp ⦃...⦄ public
