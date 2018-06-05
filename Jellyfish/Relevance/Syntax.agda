module Jellyfish.Relevance.Syntax where
open import Jellyfish.Prelude hiding (_∋_)

infix 4 _∋_
data _∋_ : ∀ {Γ : Con} → Subset Γ → Ty → Set where
  ze : ∀ {Γ} {Φ : Subset Γ} {A}                           → Φ ▻ inside {x = A} ∋ A
  su : ∀ {Γ} {Φ : Subset Γ} {A B} {side : Side B} → Φ ∋ A → Φ ▻   side         ∋ A

infix 4 _⊢_
data _⊢_ {Γ : Con} (Φ : Subset Γ) : Ty → Set where
  lit : Nat
      -------
      → Φ ⊢ ℕ

  add : Φ ⊢ ℕ
      → Φ ⊢ ℕ
      -------
      → Φ ⊢ ℕ

  sub : Φ ⊢ ℕ
      → Φ ⊢ ℕ
      -------
      → Φ ⊢ ℕ

  mul : Φ ⊢ ℕ
      → Φ ⊢ ℕ
      -------
      → Φ ⊢ ℕ

  ifz : ∀ {A}
    → Φ ⊢ ℕ
    → Φ ⊢ A
    → Φ ⊢ A
    -------
    → Φ ⊢ A

  var : ∀ {A}
    → Φ ∋ A
    -------
    → Φ ⊢ A

  lam : ∀ {A B}
    → ↑⁽ A ⁾ Φ ⊢ B
    ------------------
    →        Φ ⊢ A ⇒ B

  app : ∀ {A B}
    → Φ ⊢ A ⇒ B
    → Φ ⊢ A
    -----------
    → Φ ⊢ B

  lεt : ∀ {A B}
    →        Φ ⊢ A
    → ↑⁽ A ⁾ Φ ⊢ B
    --------------
    →        Φ ⊢ B
