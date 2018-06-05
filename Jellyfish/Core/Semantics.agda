module Jellyfish.Core.Semantics where
open import Jellyfish.Prelude
open import Jellyfish.Core.Syntax.Typed

mutual
  {-# TERMINATING #-}
  ⟦_⟧ : Ty → Set
  ⟦ ℕ     ⟧ = Nat
  ⟦ A ⇒ B ⟧ = ∃ λ Γ → Env Γ × Γ ▻ A ⊢ B

  Env : Con → Set
  Env Γ = All ⟦_⟧ Γ

mutual
  {-# TERMINATING #-}
  eval : ∀ {Γ} (ρ : Env Γ) → ∀ {A} → Γ ⊢ A → ⟦ A ⟧
  eval ρ (lit n)        = n
  eval ρ (add e₁ e₂)    = (eval ρ e₁) + (eval ρ e₂)
  eval ρ (sub e₁ e₂)    = (eval ρ e₁) - (eval ρ e₂)
  eval ρ (mul e₁ e₂)    = (eval ρ e₂) * (eval ρ e₂)
  eval ρ (ifz e₁ e₂ e₃) = case eval ρ e₁ of λ where
                            (zero)  → eval ρ e₂
                            (suc n) → eval ρ e₃
  eval ρ (var x)        = find ρ x
  eval ρ (lam e)        = (_ , ρ , e)
  eval ρ (app e₁ e₂)    = apply (eval ρ e₁) (eval ρ e₂)
  eval ρ (lεt e₁ e₂)    = let a = eval ρ e₁
                          in eval (ρ ▻ a) e₂

  apply : ∀ {A B} → (∃ λ Γ′ → Env Γ′ × Γ′ ▻ A ⊢ B) → ⟦ A ⟧ → ⟦ B ⟧
  apply (_ , ρ′ , e) a = eval (ρ′ ▻ a) e

infix 4 _⊢_⇓_
data _⊢_⇓_ {Γ} (ρ : Env Γ) : ∀ {A} → Γ ⊢ A → ⟦ A ⟧ → Set where
  lit : ∀ n
    ---------------
    → ρ ⊢ lit n ⇓ n

  add : ∀ {e₁ e₂ n₁ n₂}
    → ρ ⊢ e₁        ⇓ n₁
    → ρ ⊢ e₂        ⇓ n₂
    -------------------------
    → ρ ⊢ add e₁ e₂ ⇓ n₁ + n₂

  sub : ∀ {e₁ e₂ n₁ n₂}
    → ρ ⊢ e₁        ⇓ n₁
    → ρ ⊢ e₂        ⇓ n₂
    -------------------------
    → ρ ⊢ sub e₁ e₂ ⇓ n₁ - n₂

  mul : ∀ {e₁ e₂ n₁ n₂}
    → ρ ⊢ e₁        ⇓ n₁
    → ρ ⊢ e₂        ⇓ n₂
    -------------------------
    → ρ ⊢ mul e₁ e₂ ⇓ n₁ * n₂

  ifz/t : ∀ {A e₁ e₂ e₃} {a : ⟦ A ⟧}
    → ρ ⊢ e₁           ⇓ zero
    → ρ ⊢ e₂           ⇓ a
    -------------------------
    → ρ ⊢ ifz e₁ e₂ e₃ ⇓ a

  ifz/f : ∀ {A e₁ e₂ e₃ n} {a : ⟦ A ⟧}
    → ρ ⊢ e₁           ⇓ suc n
    → ρ ⊢ e₃           ⇓ a
    --------------------------
    → ρ ⊢ ifz e₁ e₂ e₃ ⇓ a

  var : ∀ {A} (x : Γ ∋ A)
    ----------------------
    → ρ ⊢ var x ⇓ find ρ x

  lam : ∀ {A B} {e : Γ ▻ A ⊢ B}
    -------------------------
    → ρ ⊢ lam e ⇓ (_ , ρ , e)

  app : ∀ {A B e₁ e₂} {Γ′ e} {ρ′ : Env Γ′} {a : ⟦ A ⟧} {b : ⟦ B ⟧}
    → ρ      ⊢ e₁        ⇓ (_ , ρ′ , e)
    → ρ      ⊢ e₂        ⇓ a
    → ρ′ ▻ a ⊢ e         ⇓ b
    -----------------------------------
    → ρ      ⊢ app e₁ e₂ ⇓ b

  lεt : ∀ {A B e₁ e₂} {a : ⟦ A ⟧} {b : ⟦ B ⟧}
    → ρ     ⊢ e₁        ⇓ a
    → ρ ▻ a ⊢ e₂        ⇓ b
    -----------------------
    → ρ     ⊢ lεt e₁ e₂ ⇓ b
