{-# OPTIONS --type-in-type #-}
module Prelude.Preorder where
open import Prelude.Equality

Refl : ∀ {A : Set} → (A → A → Set) → Set
Refl _≤_ = ∀ {x} → x ≤ x

Trans : ∀ {A : Set} → (A → A → Set) → Set
Trans _≤_ = ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z

Antisym : ∀ {A : Set} → (A → A → Set) → Set
Antisym _≤_ = ∀ {x y} {p q : x ≤ y} → p ≡ q

record Preorder : Set where
  field
    carrier : Set
    _≤_ : carrier → carrier → Set

    ≤-refl : Refl _≤_
    ≤-trans : Trans _≤_
    ≤-antisym : Antisym _≤_

record MonotoneMap (𝑷 𝑸 : Preorder) : Set where
  private
    module 𝑷 = Preorder 𝑷
    module 𝑸 = Preorder 𝑸
  field
    map : 𝑷.carrier → 𝑸.carrier
    monotone : ∀ {x y} → x 𝑷.≤ y → map x 𝑸.≤ map y

open MonotoneMap public
