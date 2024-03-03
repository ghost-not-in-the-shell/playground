{-# OPTIONS --type-in-type #-}
module Prelude.Star where
open import Prelude.Function

infixl 4 _◅_
data Star {A : Set} (≤ : A → A → Set) : A → A → Set where
  ε   : ∀ {x} → x ⟨ Star ≤ ⟩ x
  _◅_ : ∀ {x y z} → x ⟨ ≤ ⟩ y → y ⟨ Star ≤ ⟩ z → x ⟨ Star ≤ ⟩ z

private
  variable
    A : Set
    ≤ : A → A → Set
    x y z : A

infixl 4 _◅◅_
_◅◅_ : x ⟨ Star ≤ ⟩ y → y ⟨ Star ≤ ⟩ z → x ⟨ Star ≤ ⟩ z
ε      ◅◅ qs = qs
p ◅ ps ◅◅ qs = p ◅ (ps ◅◅ qs)

infixr 4 _▻_
pattern _▻_ ps p = p ◅ ps

infixr 4 _▻▻_
_▻▻_ : y ⟨ Star ≤ ⟩ z → x ⟨ Star ≤ ⟩ y → x ⟨ Star ≤ ⟩ z
_▻▻_ = flip _◅◅_
