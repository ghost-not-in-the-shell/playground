module Prelude.Cubical.Observational where
open import Prelude.Prim
open import Prelude.Cubical.Base
open import Prelude.Cubical.HLevel

record Extensional (A : Type) : Type where
  field
    _≈_ : A → A → Type
    ext : ∀ {x y} → x ≈ y → x ≡ y

open Extensional ⦃...⦄ public

private variable
  A B : Type

instance
  default-extensional : Extensional A
  default-extensional = record
    { _≈_ = _≡_
    ; ext = λ p → p
    }

  {-# INCOHERENT default-extensional #-}

injection→extensional : is-set B
  → {f : A → B}
  → (inj : ∀ {x y} → f x ≡ f y → x ≡ y)
  → ⦃ _ : Extensional B ⦄
  → Extensional A
injection→extensional square {f} inj = record
  { _≈_ = λ x y → f x ≈ f y
  ; ext = λ p → inj (ext p)
  }
