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

≈[]-syntax : (A : Type) ⦃ _ : Extensional A ⦄ → A → A → Type
≈[]-syntax A x y = _≈_ {A = A} x y

infix 4 ≈[]-syntax
syntax ≈[]-syntax A x y = x ≈ y [ A ]

private variable
  A B : Type
  P : A → Type

instance
  default-extensional : Extensional A
  default-extensional = record
    { _≈_ = _≡_
    ; ext = λ p → p
    }

  {-# INCOHERENT default-extensional #-}

  →‿extensional : ⦃ Extensional B ⦄
    → Extensional (A → B)
  →‿extensional = record
    { _≈_ = _≈′_
    ; ext = ext′
    } where _≈′_ : (f g : A → B) → Type
            f ≈′ g = ∀ x → f x ≈ g x

            ext′ : {f g : A → B} → f ≈′ g → f ≡ g
            ext′ p i x = ext (p x) i

  Π-extensional : ⦃ ∀ {x} → Extensional (P x) ⦄
    → Extensional (∀ x → P x)
  Π-extensional = record
    { _≈_ = _≈′_
    ; ext = ext′
    } where _≈′_ : (f g : ∀ x → P x) → Type
            f ≈′ g = ∀ x → f x ≈ g x

            ext′ : {f g : ∀ x → P x} → f ≈′ g → f ≡ g
            ext′ p i x = ext (p x) i

  {-# OVERLAPPABLE Π-extensional #-}

  Πᵢ-extensional : ⦃ ∀ {x} → Extensional (P x) ⦄
    → Extensional (∀ {x} → P x)
  Πᵢ-extensional {A} {P} ⦃ sb ⦄ = record
    { _≈_ = _≈′_
    ; ext = ext′
    } where _≈′_ : (f g : ∀ {x} → P x) → Type
            f ≈′ g = ∀ {x} → f ≈ g [ P x ]

            ext′ : ∀ {f g : ∀ {x} → P x} → f ≈′ g → f ≡ g [ i ↦ (∀ {x} → P x) ]
            ext′ = λ p i {x} → ext (p {x}) i

injection→extensional : is-set B
  → {f : A → B}
  → (inj : ∀ {x y} → f x ≡ f y → x ≡ y)
  → ⦃ _ : Extensional B ⦄
  → Extensional A
injection→extensional square {f} inj = record
  { _≈_ = λ x y → f x ≈ f y
  ; ext = λ p → inj (ext p)
  }
