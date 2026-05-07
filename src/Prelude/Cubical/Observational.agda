module Prelude.Cubical.Observational where
open import Prelude.Prim
open import Prelude.Cubical.Base
open import Prelude.Cubical.HLevel

record Extensional (A : Type) : Type where
  no-eta-equality
  infix 4 _≈_
  field
    _≈_ : A → A → Type
    ext : ∀ {x y} → x ≈ y → x ≡ y

open Extensional ⦃...⦄ public

Pathᵉ : ∀ {A} → Extensional A → A → A → Type
Pathᵉ Aᵉ = _≈_ ⦃ Aᵉ ⦄

private variable
  A : Type
  B : A → Type

instance
  default-extensional : Extensional A
  default-extensional = record
    { _≈_ = _≡_
    ; ext = λ p → p
    }

  {-# INCOHERENT default-extensional #-}

  Π-extensional : ⦃ Bᵉ : ∀ {x} → Extensional (B x) ⦄
    → Extensional (∀ x → B x)
  Π-extensional {A} {B} ⦃ Bᵉ ⦄ = record
    { _≈_ = _≈′_
    ; ext = ext′
    } where _≈′_ : (f g : ∀ x → B x) → Type
            f ≈′ g = ∀ x → Pathᵉ Bᵉ (f x) (g x)

            ext′ : {f g : ∀ x → B x} → f ≈′ g → f ≡ g
            ext′ p = λ i x → ext ⦃ Bᵉ ⦄ (p x) i

  Πᵢ-extensional : ⦃ Bᵉ : ∀ {x} → Extensional (B x) ⦄
    → Extensional (∀ {x} → B x)
  Πᵢ-extensional {A} {B} ⦃ Bᵉ ⦄ = record
    { _≈_ = _≈′_
    ; ext = ext′
    } where _≈′_ : (f g : ∀ {x} → B x) → Type
            f ≈′ g = ∀ {x} → Pathᵉ Bᵉ f g

            ext′ : {f g : ∀ {x} → B x} → f ≈′ g → f ≡ g [ i ↦ (∀ {x} → B x) ]
            ext′ = λ p i {x} → ext ⦃ Bᵉ ⦄ (p {x}) i


injection→extensional : ∀ {A B} → is-set B
  → {f : A → B}
  → (inj : ∀ {x y} → f x ≡ f y → x ≡ y)
  → ⦃ Bᵉ : Extensional B ⦄
  → Extensional A
injection→extensional {A} {B} square {f} inj ⦃ Bᵉ ⦄ = record
  { _≈_ = _≈′_
  ; ext = ext′
  } where _≈′_ : (x y : A) → Type
          x ≈′ y = Pathᵉ (Bᵉ) (f x) (f y)

          ext′ : {x y : A} → x ≈′ y → x ≡ y
          ext′ p = inj (ext ⦃ Bᵉ ⦄ p)
