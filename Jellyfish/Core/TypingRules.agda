module Jellyfish.Core.TypingRules where
open import Jellyfish.Prelude
open import Jellyfish.Core.Syntax.Untyped

mutual
  infix 4 _⊢_⇛_
  data _⊢_⇛_ (Γ : Con) : Tm (length Γ) → Ty → Set where
    lit : ∀ (n : Nat)
      ---------------
      → Γ ⊢ lit n ⇛ ℕ

    add : ∀ {e₁ e₂}
      → Γ ⊢        e₁ ⇚ ℕ
      → Γ ⊢        e₂ ⇚ ℕ
      -------------------
      → Γ ⊢ add e₁ e₂ ⇛ ℕ

    sub : ∀ {e₁ e₂}
      → Γ ⊢        e₁ ⇚ ℕ
      → Γ ⊢        e₂ ⇚ ℕ
      -------------------
      → Γ ⊢ sub e₁ e₂ ⇛ ℕ

    mul : ∀ {e₁ e₂}
      → Γ ⊢        e₁ ⇚ ℕ
      → Γ ⊢        e₂ ⇚ ℕ
      -------------------
      → Γ ⊢ mul e₁ e₂ ⇛ ℕ

    ifz/t : ∀ {A e₁ e₂ e₃}
      → Γ ⊢           e₁ ⇚ ℕ
      → Γ ⊢           e₂ ⇛ A
      → Γ ⊢           e₃ ⇚ A
      ----------------------
      → Γ ⊢ ifz e₁ e₂ e₃ ⇛ A

    ifz/f : ∀ {A e₁ e₂ e₃}
      → Γ ⊢           e₁ ⇚ ℕ
      → Γ ⊢           e₂ ⇚ A
      → Γ ⊢           e₃ ⇛ A
      ----------------------
      → Γ ⊢ ifz e₁ e₂ e₃ ⇛ A

    var : ∀ x
      ------------------------
      → Γ ⊢ var x ⇛ lookup Γ x

    app : ∀ {A B e₁ e₂}
      → Γ ⊢        e₁ ⇛ A ⇒ B
      → Γ ⊢        e₂ ⇚ A
      -----------------------
      → Γ ⊢ app e₁ e₂ ⇛ B

    lεt : ∀ {A B e₁ e₂}
      → Γ     ⊢        e₁ ⇛ A
      → Γ ▻ A ⊢        e₂ ⇛ B
      -----------------------
      → Γ     ⊢ lεt e₁ e₂ ⇛ B

    the : ∀ A {e}
      → Γ ⊢ e       ⇚ A
      -----------------
      → Γ ⊢ the A e ⇛ A

  infix 4 _⊢_⇚_
  data _⊢_⇚_ (Γ : Con) : Tm (length Γ) → Ty → Set where
    lam : ∀ {A B e}
      → Γ ▻ A ⊢     e ⇚ B
      -----------------------
      → Γ     ⊢ lam e ⇚ A ⇒ B

    _⇛⇚_ : ∀ {A ⁇ e}
      → Γ ⊢ e ⇛ ⁇
      → ⁇ ≡ A
      -----------
      → Γ ⊢ e ⇚ A
