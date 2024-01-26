--{-# OPTIONS --type-in-type #-}
module Adjunction.Base where
open import Prelude
open import Category.Base
open import Functor.Base
open import NaturalTransformation.Base

record Adjunction {𝓒 𝓓} (𝓛 : 𝓒 ⟶ 𝓓) (𝓡 : 𝓓 ⟶ 𝓒) : Set where
  field
    unit   : id₍ 𝓒 ₎ ⟹ 𝓡 ∘ 𝓛
    counit : 𝓛 ∘ 𝓡 ⟹ id₍ 𝓓 ₎

    -- counit ∘ˡ 𝓛 : (𝓛 ∘ 𝓡) ∘ 𝓛 ⟹ id₍ 𝓓 ₎ ∘ 𝓛
    -- 𝓛 ∘ʳ unit   : 𝓛 ∘ id₍ 𝓒 ₎ ⟹ 𝓛 ∘ (𝓡 ∘ 𝓛)
    zig : ∀ {X} → (counit ∘ˡ 𝓛)₍ X ₎ ∘ (𝓛 ∘ʳ unit)₍ X ₎ ≡ id₍ 𝓛 ₎ ₍ X ₎
    zag : ∀ {Y} → (𝓡 ∘ʳ counit)₍ Y ₎ ∘ (unit ∘ˡ 𝓡)₍ Y ₎ ≡ id₍ 𝓡 ₎ ₍ Y ₎

infix 4 _⊣_
_⊣_ : ∀ {𝓒 𝓓} → 𝓒 ⟶ 𝓓 → 𝓓 ⟶ 𝓒 → Set
𝓛 ⊣ 𝓡 = Adjunction 𝓛 𝓡
