module Identity where

infix 4 _≡_
data _≡_ {𝔞} {A : Set 𝔞} : A → A → Set 𝔞 where
  refl : ∀ {x} → x ≡ x

infix 4 ≡₍₎-syntax
≡₍₎-syntax : ∀ {𝔞} (A : Set 𝔞) → A → A → Set 𝔞
≡₍₎-syntax A x y = x ≡ y

syntax ≡₍₎-syntax A x y = x ≡₍ A ₎ y

refl₍_₎ : ∀ {𝔞} {A : Set 𝔞} (x : A) → x ≡ x
refl₍ x ₎ = refl

sym : ∀ {𝔞} {A : Set 𝔞} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {𝔞} {A : Set 𝔞} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

ap : ∀ {𝔞 𝔟} {A : Set 𝔞} {B : Set 𝔟} (f : A → B) → ∀ {x y} → x ≡ y → f x ≡ f y
ap f refl = refl

transport : ∀ {𝔞 𝔭} {A : Set 𝔞} (P : A → Set 𝔭) → ∀ {x y} → x ≡ y → P x → P y
transport P refl = λ u → u

PathOver : ∀ {𝔞 𝔭} {A : Set 𝔞} (P : A → Set 𝔭) → ∀ {x y} → x ≡ y → P x → P y → Set 𝔭
PathOver P p u v = transport P p u ≡ v

syntax PathOver P p u v = u ≡ v [ P ↓ p ]

_∗ : ∀ {𝔞 𝔭} {A : Set 𝔞} {P : A → Set 𝔭} → ∀ {x y} → x ≡ y → P x → P y
p ∗ = transport _ p

apd : ∀ {𝔞 𝔭} {A : Set 𝔞} {P : A → Set 𝔭} (f : ∀ x → P x) → ∀ {x y} → (p : x ≡ y) → f x ≡ f y [ P ↓ p ]
apd f refl = refl

module ≡-Reasoning where
  infix  1 begin_
  infixr 2 _↓⟨_⟩_
  infixr 2 _↑⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {𝔞} {A : Set 𝔞} {x y : A}
    → x ≡ y
    → x ≡ y
  begin x≡y = x≡y

  _↓⟨_⟩_ : ∀ {𝔞} {A : Set 𝔞} (x {y z} : A)
    → x ≡ y
    → y ≡ z
    → x ≡ z
  x ↓⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _↑⟨_⟩_ : ∀ {𝔞} {A : Set 𝔞} (x {y z} : A)
    → y ≡ x
    → y ≡ z
    → x ≡ z
  x ↑⟨ y≡x ⟩ y≡z = trans (sym y≡x) y≡z

  _∎ : ∀ {𝔞} {A : Set 𝔞} (x : A) → x ≡ x
  x ∎ = refl

open ≡-Reasoning public
