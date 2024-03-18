{-# OPTIONS --type-in-type #-}
module Prelude.Preorder where
open import Prelude.Equality
open import Prelude.Function
open import Prelude.Op

Refl : ∀ {A : Set} → (A → A → Set) → Set
Refl _≤_ = ∀ {x} → x ≤ x

Trans : ∀ {A : Set} → (A → A → Set) → Set
Trans _≤_ = ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z

Prop : ∀ {A : Set} → (A → A → Set) → Set
Prop _≤_ = ∀ {x y} {p q : x ≤ y} → p ≡ q

record Preorder : Set where
  field
    Carrier : Set
    _≤_ : Carrier → Carrier → Set

    ≤-refl  : Refl  _≤_
    ≤-trans : Trans _≤_
    ≤-prop  : Prop  _≤_

record MonotoneMap (𝑷 𝑸 : Preorder) : Set where
  private
    module 𝑷 = Preorder 𝑷
    module 𝑸 = Preorder 𝑸
  field
    map : 𝑷.Carrier → 𝑸.Carrier
    monotone : ∀ {x y} → x 𝑷.≤ y → map x 𝑸.≤ map y

open MonotoneMap public

𝓟𝓻𝓮-categorical : CategoricalOp MonotoneMap
𝓟𝓻𝓮-categorical = record
  { id = record
    { map      = id
    ; monotone = id
    }
  ; _∘_ = λ 𝒈 𝒇 → record
    { map      = map      𝒈 ∘ map      𝒇
    ; monotone = monotone 𝒈 ∘ monotone 𝒇
    }
  }
