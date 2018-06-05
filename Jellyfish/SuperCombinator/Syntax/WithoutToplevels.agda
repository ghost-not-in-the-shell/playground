module Jellyfish.SuperCombinator.Syntax.WithoutToplevels where
open import Jellyfish.Prelude

infix 4 _⊢_
data _⊢_ (Γ : Con) : Ty → Set where
  lit : Nat
      -------
      → Γ ⊢ ℕ

  add : Γ ⊢ ℕ
      → Γ ⊢ ℕ
      -------
      → Γ ⊢ ℕ

  sub : Γ ⊢ ℕ
      → Γ ⊢ ℕ
      -------
      → Γ ⊢ ℕ

  mul : Γ ⊢ ℕ
      → Γ ⊢ ℕ
      -------
      → Γ ⊢ ℕ

  ifz : ∀ {A}
    → Γ ⊢ ℕ
    → Γ ⊢ A
    → Γ ⊢ A
    -------
    → Γ ⊢ A

  var : ∀ {A}
    → Γ ∋ A
    -------
    → Γ ⊢ A

  cls : ∀ {A⃗ A B}
    → A⃗ ▻ A ⊢ B
    → Γ ∋⃗ A⃗
    -----------
    → Γ ⊢ A ⇒ B

  app : ∀ {A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
    -----------
    → Γ ⊢ B

  lεt : ∀ {A B}
    → Γ     ⊢ A
    → Γ ▻ A ⊢ B
    -----------
    → Γ     ⊢ B
