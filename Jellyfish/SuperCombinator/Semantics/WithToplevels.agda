module Jellyfish.SuperCombinator.Semantics.WithToplevels where
open import Jellyfish.Prelude
open import Jellyfish.SuperCombinator.Syntax.WithToplevels

mutual
  {-# TERMINATING #-}
  Val : List Sig → Ty → Set
  Val Ε ℕ       = Nat
  Val Ε (A ⇒ B) = ∃ λ Γ → Env Ε Γ × Ε [ Γ ▻ A ]⊢ B

  Env : List Sig → Con → Set
  Env Ε Γ = All (Val Ε) Γ

mutual
  {-# TERMINATING #-}
  eval : ∀ {Ε Γ} (d⃗ : Defs Ε) (ρ : Env Ε Γ) → ∀ {A} → Ε [ Γ ]⊢ A → Val Ε A
  eval d⃗ ρ (lit n)        = n
  eval d⃗ ρ (add e₁ e₂)    = eval d⃗ ρ e₁ + eval d⃗ ρ e₂
  eval d⃗ ρ (sub e₁ e₂)    = eval d⃗ ρ e₁ - eval d⃗ ρ e₂
  eval d⃗ ρ (mul e₁ e₂)    = eval d⃗ ρ e₁ * eval d⃗ ρ e₂
  eval d⃗ ρ (ifz e₁ e₂ e₃) = case eval d⃗ ρ e₁ of λ where
                             (zero)  → eval d⃗ ρ e₂
                             (suc n) → eval d⃗ ρ e₃
  eval d⃗ ρ (var x)        = find ρ x
  eval d⃗ ρ (cls f x⃗)      = (_ , map (find ρ) x⃗ , find d⃗ f)
  eval d⃗ ρ (app e₁ e₂)    = apply d⃗ (eval d⃗ ρ e₁) (eval d⃗ ρ e₂)
  eval d⃗ ρ (lεt e₁ e₂)    = let a = eval d⃗ ρ e₁
                            in eval d⃗ (ρ ▻ a) e₂

  apply : ∀ {Ε A B} → Defs Ε → Val Ε (A ⇒ B) → Val Ε A → Val Ε B
  apply d⃗ (_ , ρ′ , e) a = eval d⃗ (ρ′ ▻ a) e

infix 4 _[_]⊢_⇓_
data _[_]⊢_⇓_ {Ε Γ} (d⃗ : Defs Ε) (ρ : Env Ε Γ) : ∀ {A} → Ε [ Γ ]⊢ A → Val Ε A → Set where
  lit : ∀ n
    --------------------
    → d⃗ [ ρ ]⊢ lit n ⇓ n

  add : ∀ {e₁ e₂ n₁ n₂}
    → d⃗ [ ρ ]⊢ e₁        ⇓ n₁
    → d⃗ [ ρ ]⊢ e₂        ⇓ n₂
    ------------------------------
    → d⃗ [ ρ ]⊢ add e₁ e₂ ⇓ n₁ + n₂

  sub : ∀ {e₁ e₂ n₁ n₂}
    → d⃗ [ ρ ]⊢ e₁        ⇓ n₁
    → d⃗ [ ρ ]⊢ e₂        ⇓ n₂
    ------------------------------
    → d⃗ [ ρ ]⊢ sub e₁ e₂ ⇓ n₁ - n₂

  mul : ∀ {e₁ e₂ n₁ n₂}
    → d⃗ [ ρ ]⊢ e₁        ⇓ n₁
    → d⃗ [ ρ ]⊢ e₂        ⇓ n₂
    ------------------------------
    → d⃗ [ ρ ]⊢ mul e₁ e₂ ⇓ n₁ * n₂

  ifz/t : ∀ {A e₁ e₂ e₃} {a : Val Ε A}
    → d⃗ [ ρ ]⊢ e₁           ⇓ zero
    → d⃗ [ ρ ]⊢ e₂           ⇓ a
    ------------------------------
    → d⃗ [ ρ ]⊢ ifz e₁ e₂ e₃ ⇓ a

  ifz/f : ∀ {A e₁ e₂ e₃ n} {a : Val Ε A}
    → d⃗ [ ρ ]⊢ e₁           ⇓ suc n
    → d⃗ [ ρ ]⊢ e₃           ⇓ a
    -------------------------------
    → d⃗ [ ρ ]⊢ ifz e₁ e₂ e₃ ⇓ a

  var : ∀ {A} (x : Γ ∋ A)
    ---------------------------
    → d⃗ [ ρ ]⊢ var x ⇓ find ρ x

  cls : ∀ {A⃗ A B} {f : Ε ∋ (A⃗ ▻ A) , B} {x⃗ : Γ ∋⃗ A⃗}
    ----------------------------------------------------
    → d⃗ [ ρ ]⊢ cls f x⃗ ⇓ (_ , map (find ρ) x⃗ , find d⃗ f)

  app : ∀ {A B e₁ e₂} {Γ′ e} {ρ′ : Env Ε Γ′} {a : Val Ε A} {b : Val Ε B}
    → d⃗ [ ρ      ]⊢ e₁        ⇓ (_ , ρ′ , e)
    → d⃗ [ ρ      ]⊢ e₂        ⇓ a
    → d⃗ [ ρ′ ▻ a ]⊢ e         ⇓ b
    ----------------------------------------
    → d⃗ [ ρ      ]⊢ app e₁ e₂ ⇓ b

  lεt : ∀ {A B e₁ e₂} {a : Val Ε A} {b : Val Ε B}
    → d⃗ [ ρ     ]⊢ e₁        ⇓ a
    → d⃗ [ ρ ▻ a ]⊢ e₂        ⇓ b
    ----------------------------
    → d⃗ [ ρ     ]⊢ lεt e₁ e₂ ⇓ b
