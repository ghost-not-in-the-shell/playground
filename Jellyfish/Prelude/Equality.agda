module Jellyfish.Prelude.Equality where
open import Agda.Builtin.Equality public
open import Jellyfish.Prelude.Sum
open import Jellyfish.Prelude.Dec
open import Jellyfish.Prelude.Monad

_⁻¹ : ∀ {𝔞} {A : Set 𝔞} {x y : A} → x ≡ y → y ≡ x
refl ⁻¹ = refl

infixr 4 _⋮_
_⋮_ : ∀ {𝔞} {A : Set 𝔞} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ⋮ refl = refl

infixl 4 _⟨$⟩_
_⟨$⟩_ : ∀ {𝔞 𝔟} {A : Set 𝔞} {B : Set 𝔟} (f : A → B)
  → ∀ {x y} → x ≡ y → f x ≡ f y
f ⟨$⟩ refl = refl

infixl 4 _⟨*⟩_
_⟨*⟩_ : ∀ {𝔞 𝔟} {A : Set 𝔞} {B : Set 𝔟} {f g : A → B} → f ≡ g
  → ∀ {x y} → x ≡ y → f x ≡ g y
refl ⟨*⟩ refl = refl

_⟦_⟫ : ∀ {𝔞} {A B : Set 𝔞} → A → A ≡ B → B
x ⟦ refl ⟫ = x

module ≡-Reasoning where
  infix  1 begin_
  infixr 2 _↓⟨_⟩_
  infixr 2 _↑⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {𝔞} {A : Set 𝔞} {x y : A}
    → x ≡ y
    → x ≡ y
  begin x≡y = x≡y

  _↓⟨_⟩_ : ∀ {𝔞} {A : Set 𝔞} {y z : A}
    → (x : A)
    → x ≡ y
    → y ≡ z
    → x ≡ z
  x ↓⟨ x≡y ⟩ y≡z = x≡y ⋮ y≡z

  _↑⟨_⟩_ : ∀ {𝔞} {A : Set 𝔞} {y z : A}
    → (x : A)
    → y ≡ x
    → y ≡ z
    → x ≡ z
  x ↑⟨ y≡x ⟩ y≡z = y≡x ⁻¹ ⋮ y≡z

  _∎ : ∀ {𝔞} {A : Set 𝔞}
    → (x : A)
    → x ≡ x
  x ∎ = refl

open ≡-Reasoning public

record Eq {𝔞} (A : Set 𝔞) : Set 𝔞 where
  field
    _≟_ : ∀ (x y : A) → Dec (x ≡ y)

open Eq ⦃...⦄ public

{-# DISPLAY Eq._≟_ _ = _≟_ #-}
