{-# OPTIONS --type-in-type #-}
module Prelude.Equality where

private
  variable
    A B C : Set
    x y z : A

infix 4 _≡_
data _≡_ {A} : A → A → Set where
  refl : ∀ {x} → x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

pattern refl₍_₎ x = refl {x = x}

sym : x ≡ y → y ≡ x
sym refl = refl

trans : x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

pure : ∀ (x : A) → x ≡ x
pure = refl₍_₎

_<*>_ : ∀ {f g : A → B} → f ≡ g → x ≡ y → f x ≡ g y
refl <*> refl = refl

subst : ∀ (P : A → Set) → x ≡ y → P x → P y
subst P refl u = u

infix 4 PathAt
PathAt : ∀ (A : Set) (x y : A) → Set
PathAt A x y = x ≡ y

syntax PathAt A x y = x ≡ y [ A ]

infix 4 PathOver
PathOver : ∀ (P : A → Set) → x ≡ y → P x → P y → Set
PathOver P p u v = subst P p u ≡ v

syntax PathOver P p u v = u ≡ v [ P ↓ p ]

module UIP where
  uip : ∀ (p q : x ≡ y) → p ≡ q
  uip refl refl = refl

open UIP public

module Extensionality where
  postulate
    λ⁼ : ∀ {P : A → Set} {f g : (x : A) → P x} → (∀ (x) → f(x) ≡ g(x)) → f ≡ g
    ƛ⁼ : ∀ {P : A → Set} {f g : {x : A} → P x} → (∀ {x} → f{x} ≡ g{x}) → f ≡ g [ (∀ {x} → P x) ]

open Extensionality public

module ≡-Reasoning where
  infix  1 begin_
  infixr 2 step-≡ step-⟲
  infix  3 _∎

  begin_ : x ≡ y → x ≡ y
  begin x≡y = x≡y

  step-≡ : ∀ (x : A) → x ≡ y → y ≡ z → x ≡ z
  step-≡ _ refl refl = refl

  step-⟲ : ∀ (x : A) → y ≡ x → y ≡ z → x ≡ z
  step-⟲ _ refl refl = refl

  _∎ : ∀ (x : A) → x ≡ x
  x ∎ = refl

  syntax step-≡ x x≡y y≡z = x ≡⟨ x≡y ⟩ y≡z
  syntax step-⟲ x y≡x y≡z = x ≡⟨ y≡x ⟲⟩ y≡z

open ≡-Reasoning public
