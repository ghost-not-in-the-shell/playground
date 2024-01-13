module Equality where

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

refl₍_₎ : ∀ {A} (x : A) → x ≡ x
refl₍ x ₎ = refl {x = x}

{-# BUILTIN EQUALITY _≡_ #-}

infix 4 PathAt
PathAt : ∀ (A : Set) (x y : A) → Set
PathAt A x y = _≡_ {A} x y

syntax PathAt A x y = x ≡ y [ A ]

sym : ∀ {A} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

pure : ∀ {A} (x : A) → x ≡ x
pure x = refl₍ x ₎

infixl 4 _<*>_
_<*>_ : ∀ {A B} {f₁ f₂ : A → B} {x₁ x₂ : A}
  → f₁ ≡ f₂
  → x₁ ≡ x₂
  → f₁ x₁ ≡ f₂ x₂
refl <*> refl = refl

cong : ∀ {A B} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f = refl <*>_

subst : ∀ {A x y} (P : A → Set) → x ≡ y → P x → P y
subst P refl u = u

infix 4 PathOver
PathOver : ∀ {A x y} (P : A → Set) → x ≡ y → P x → P y → Set
PathOver P p u v = subst P p u ≡ v

syntax PathOver P p u v = u ≡ v [ P ↓ p ]

module UIP where
  uip : ∀ {A} {x y : A} (p q : x ≡ y) → p ≡ q
  uip refl refl = refl

open UIP public

module Extensionality where
  postulate
    λ⁼ : ∀ {A : Set} {P : A → Set} {f g : (x : A) → P x} → (∀ (x) → f(x) ≡ g(x)) → f ≡ g
    ƛ⁼ : ∀ {A : Set} {P : A → Set} {f g : {x : A} → P x} → (∀ {x} → f{x} ≡ g{x}) → f ≡ g [ (∀ {x} → P x) ]

open Extensionality public

module ≡-Reasoning where
  infix  1 begin_
  infixr 2 _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {A} {x y : A} → x ≡ y → x ≡ y
  begin x≡y = x≡y

  _≡⟨_⟩_ : ∀ {A} x {y z : A} → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ {A} (x : A) → x ≡ x
  x ∎ = refl₍ x ₎

open ≡-Reasoning public
