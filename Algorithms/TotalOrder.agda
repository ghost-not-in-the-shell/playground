module Algorithms.TotalOrder where
open import Algorithms.Equality
open import Algorithms.Miscellaneous

record TotalOrder 𝑎 ℓ : Set (lsuc (𝑎 ⊔ ℓ)) where
  infix 4 _≤_
  infix 4 _≥_
  field
    Carrier : Set 𝑎
    _≤_     : Carrier → Carrier → Set ℓ

  _≥_ = flip _≤_

  field
    reflexive : ∀ {x} → x ≤ x
    antisym   : ∀ {x y} → x ≤ y → x ≥ y → x ≡ y
    trans     : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    total     : ∀ x y → x ≤ y ⊎ x ≥ y

  min : Carrier → Carrier → Carrier
  min x y with total x y
  ... | inj₁ _ = x
  ... | inj₂ _ = y

  ⟨_,_⟩ : ∀ {x a b} → x ≤ a → x ≤ b → x ≤ min a b
  ⟨_,_⟩ {a = a} {b} x≤a x≤b with total a b
  ... | inj₁ _ = x≤a
  ... | inj₂ _ = x≤b
