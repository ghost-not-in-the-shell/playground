module Jellyfish.Relevance.Semantics where
open import Jellyfish.Prelude          renaming (_∋_ to _∋𝓢_)
open import Jellyfish.Relevance.Syntax renaming (_∋_ to _∋𝓘_)

⌈_⌉∋ : ∀ {Γ A} {⌊Γ⌋ : Subset Γ} → ⌊Γ⌋ ∋𝓘 A → ⌈ ⌊Γ⌋ ⌉ ∋𝓢 A
⌈ ze ⌉∋ = ze
⌈_⌉∋ {⌊Γ⌋ = _ ▻ outside} (su x) =    ⌈ x ⌉∋
⌈_⌉∋ {⌊Γ⌋ = _ ▻  inside} (su x) = su ⌈ x ⌉∋

mutual
  {-# TERMINATING #-}
  ⟦_⟧ : Ty → Set
  ⟦ ℕ     ⟧ = Nat
  ⟦ A ⇒ B ⟧ = ∃ λ Γ → ∃ λ (⌊Γ⌋ : Subset Γ) → Env ⌊Γ⌋ × ↑⁽ A ⁾ ⌊Γ⌋ ⊢ B

  Env : ∀ {Γ} (⌊Γ⌋ : Subset Γ) → Set
  Env ⌊Γ⌋ = All ⟦_⟧ ⌈ ⌊Γ⌋ ⌉

mutual
  {-# TERMINATING #-}
  eval : ∀ {Γ} {⌊Γ⌋ : Subset Γ} (⌊ρ⌋ : Env ⌊Γ⌋) → ∀ {A} → ⌊Γ⌋ ⊢ A → ⟦ A ⟧
  eval ⌊ρ⌋ (lit n)        = n
  eval ⌊ρ⌋ (add e₁ e₂)    = eval ⌊ρ⌋ e₁ + eval ⌊ρ⌋ e₂
  eval ⌊ρ⌋ (sub e₁ e₂)    = eval ⌊ρ⌋ e₁ - eval ⌊ρ⌋ e₂
  eval ⌊ρ⌋ (mul e₁ e₂)    = eval ⌊ρ⌋ e₁ * eval ⌊ρ⌋ e₂
  eval ⌊ρ⌋ (ifz e₁ e₂ e₃) = case eval ⌊ρ⌋ e₁ of λ where
                            (zero)  → eval ⌊ρ⌋ e₂
                            (suc n) → eval ⌊ρ⌋ e₃
  eval ⌊ρ⌋ (var x)        = find ⌊ρ⌋ ⌈ x ⌉∋
  eval ⌊ρ⌋ (lam e)        = _ , _ , ⌊ρ⌋ , e
  eval ⌊ρ⌋ (app e₁ e₂)    = apply (eval ⌊ρ⌋ e₁) (eval ⌊ρ⌋ e₂)
  eval ⌊ρ⌋ (lεt e₁ e₂)    = let a = eval ⌊ρ⌋ e₁
                          in eval (⌊ρ⌋ ▻ a) e₂

  apply : ∀ {A B} → ⟦ A ⇒ B ⟧ → ⟦ A ⟧ → ⟦ B ⟧
  apply (_ , _ , ρ′ , e) a = eval (ρ′ ▻ a) e

infix 4 _⊢_⇓_
data _⊢_⇓_ {Γ} {⌊Γ⌋ : Subset Γ} (⌊ρ⌋ : Env ⌊Γ⌋) : ∀ {A} → ⌊Γ⌋ ⊢ A → ⟦ A ⟧ → Set where
  lit : ∀ n
    -----------------
    → ⌊ρ⌋ ⊢ lit n ⇓ n

  add : ∀ {e₁ e₂ n₁ n₂}
    → ⌊ρ⌋ ⊢ e₁        ⇓ n₁
    → ⌊ρ⌋ ⊢ e₂        ⇓ n₂
    ---------------------------
    → ⌊ρ⌋ ⊢ add e₁ e₂ ⇓ n₁ + n₂

  sub : ∀ {e₁ e₂ n₁ n₂}
    → ⌊ρ⌋ ⊢ e₁        ⇓ n₁
    → ⌊ρ⌋ ⊢ e₂        ⇓ n₂
    ---------------------------
    → ⌊ρ⌋ ⊢ sub e₁ e₂ ⇓ n₁ - n₂

  mul : ∀ {e₁ e₂ n₁ n₂}
    → ⌊ρ⌋ ⊢ e₁        ⇓ n₁
    → ⌊ρ⌋ ⊢ e₂        ⇓ n₂
    ---------------------------
    → ⌊ρ⌋ ⊢ mul e₁ e₂ ⇓ n₁ * n₂

  ifz/t : ∀ {A e₁ e₂ e₃} {a : ⟦ A ⟧}
    → ⌊ρ⌋ ⊢ e₁           ⇓ zero
    → ⌊ρ⌋ ⊢ e₂           ⇓ a
    ---------------------------
    → ⌊ρ⌋ ⊢ ifz e₁ e₂ e₃ ⇓ a

  ifz/f : ∀ {A e₁ e₂ e₃ n} {a : ⟦ A ⟧}
    → ⌊ρ⌋ ⊢ e₁           ⇓ suc n
    → ⌊ρ⌋ ⊢ e₃           ⇓ a
    ----------------------------
    → ⌊ρ⌋ ⊢ ifz e₁ e₂ e₃ ⇓ a

  var : ∀ {A} (x : ⌊Γ⌋ ∋𝓘 A)
    -------------------------------
    → ⌊ρ⌋ ⊢ var x ⇓ find ⌊ρ⌋ ⌈ x ⌉∋

  lam : ∀ {A B} {e : ↑⁽ A ⁾ ⌊Γ⌋ ⊢ B}
    ---------------------------------
    → ⌊ρ⌋ ⊢ lam e ⇓ (_ , _ , ⌊ρ⌋ , e)

  app : ∀ {A B e₁ e₂} {Γ′} {⌊Γ′⌋ : Subset Γ′} {e : ↑⁽ A ⁾ ⌊Γ′⌋ ⊢ B} {⌊ρ′⌋ : Env ⌊Γ′⌋} {a : ⟦ A ⟧} {b : ⟦ B ⟧}
    → ⌊ρ⌋      ⊢ e₁        ⇓ (_ , _ , ⌊ρ′⌋ , e)
    → ⌊ρ⌋      ⊢ e₂        ⇓ a
    → ⌊ρ′⌋ ▻ a ⊢ e         ⇓ b
    -------------------------------------------
    → ⌊ρ⌋      ⊢ app e₁ e₂ ⇓ b

  lεt : ∀ {A B e₁ e₂} {a : ⟦ A ⟧} {b : ⟦ B ⟧}
    → ⌊ρ⌋     ⊢ e₁        ⇓ a
    → ⌊ρ⌋ ▻ a ⊢ e₂        ⇓ b
    -------------------------
    → ⌊ρ⌋     ⊢ lεt e₁ e₂ ⇓ b
