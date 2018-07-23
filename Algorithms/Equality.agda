module Algorithms.Equality where
open import Agda.Builtin.Equality public

infixr 5 _⋮_
infixl 5 _⟨$⟩_
infixl 5 _⟨*⟩_

sym : ∀ {𝑎} {A : Set 𝑎} {x y : A}
  → x ≡ y
  → y ≡ x
sym refl = refl

_⋮_ : ∀ {𝑎} {A : Set 𝑎} {x y z : A}
  → x ≡ y
  → y ≡ z
  → x ≡ z
refl ⋮ refl = refl

_⟨$⟩_ : ∀ {𝑎 𝑏} {A : Set 𝑎} {B : Set 𝑏} (f : A → B) {x₁ x₂}
  →   x₁ ≡   x₂
  → f x₁ ≡ f x₂
f ⟨$⟩ refl = refl

_⟨*⟩_ : ∀ {𝑎 𝑏} {A : Set 𝑎} {B : Set 𝑏} {f₁ f₂ : A → B} {x₁ x₂}
  →    f₁ ≡    f₂
  →    x₁ ≡    x₂
  → f₁ x₁ ≡ f₂ x₂
refl ⟨*⟩ refl = refl

_⟦_⟫ : ∀ {𝑎} {A B : Set 𝑎} → A → A ≡ B → B
x ⟦ refl ⟫ = x

module ≡-Reasoning where
  infix  1 begin_
  infixr 2 _↓⟨_⟩_
  infixr 2 _↑⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {𝑎} {A : Set 𝑎} {x y : A}
    → x ≡ y
    → x ≡ y
  begin x≡y = x≡y

  _↓⟨_⟩_ : ∀ {𝑎} {A : Set 𝑎} (x {y z} : A)
    → x ≡ y
    → y ≡ z
    → x ≡ z
  x ↓⟨ x≡y ⟩ y≡z = x≡y ⋮ y≡z

  _↑⟨_⟩_ : ∀ {𝑎} {A : Set 𝑎} (x {y z} : A)
    → y ≡ x
    → y ≡ z
    → x ≡ z
  x ↑⟨ y≡x ⟩ y≡z = sym y≡x ⋮ y≡z

  _∎ : ∀ {𝑎} {A : Set 𝑎} (x : A)
    → x ≡ x
  x ∎ = refl

open ≡-Reasoning public
