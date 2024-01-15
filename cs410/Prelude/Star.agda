{-# OPTIONS --type-in-type #-}
module Prelude.Star where
open import Prelude.Equality
open import Prelude.Function
open import Prelude.Op

infixl 4 _◅_
data Star {A : Set} (≤ : A → A → Set) : A → A → Set where
  ε   : ∀ {x}                                  → x ⟨ Star ≤ ⟩ x
  _◅_ : ∀ {x y z} → x ⟨ ≤ ⟩ y → y ⟨ Star ≤ ⟩ z → x ⟨ Star ≤ ⟩ z

infixl 4 _◅◅_
_◅◅_ : ∀ {A ≤} {x y z : A} → x ⟨ Star ≤ ⟩ y → y ⟨ Star ≤ ⟩ z → x ⟨ Star ≤ ⟩ z
ε      ◅◅ qs = qs
p ◅ ps ◅◅ qs = p ◅ (ps ◅◅ qs)

infixr 4 _▻_
pattern _▻_ ps p = p ◅ ps

infixr 4 _▻▻_
_▻▻_ : ∀ {A ≤} {x y z : A} → y ⟨ Star ≤ ⟩ z → x ⟨ Star ≤ ⟩ y → x ⟨ Star ≤ ⟩ z
_▻▻_ = flip _◅◅_

gmap : ∀ {A B ≤ ⊆} {f : A → B}
  → (∀ {x y} → x ⟨      ≤ ⟩ y → f x ⟨      ⊆ ⟩ f y)
  → (∀ {x y} → x ⟨ Star ≤ ⟩ y → f x ⟨ Star ⊆ ⟩ f y)
gmap g ε = ε
gmap g (p ◅ ps) = g p ◅ gmap g ps
