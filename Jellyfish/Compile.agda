module Jellyfish.Compile where
open import Jellyfish.Prelude hiding (_▻▻_; _▻▻▻_)
open import Jellyfish.Core.Syntax.Typed
open import Jellyfish.AbstractMachine.Syntax
open import Jellyfish.Core.Semantics            renaming (⟦_⟧ to ⟦_⟧𝓢; Env to Env𝓢)
open import Jellyfish.AbstractMachine.Semantics renaming (⟦_⟧ to ⟦_⟧𝓣; Env to Env𝓣)

compile⊢ : ∀ {Γ Σ A} → Γ ⊢ A → Code⋆ [ Γ , Σ ] [ Γ , Σ ▻ A ]
compile⊢ (lit n)        = ε ▻ lit n
compile⊢ (add e₁ e₂)    = compile⊢ e₁ ▻▻ (compile⊢ e₂ ▻ add)
compile⊢ (sub e₁ e₂)    = compile⊢ e₁ ▻▻ (compile⊢ e₂ ▻ sub)
compile⊢ (mul e₁ e₂)    = compile⊢ e₁ ▻▻ (compile⊢ e₂ ▻ mul)
compile⊢ (ifz e₁ e₂ e₃) = compile⊢ e₁ ▻ ifz (compile⊢ e₂) (compile⊢ e₃)
compile⊢ (var x)        = ε ▻ var x
compile⊢ (lam e)        = ε ▻ lam (compile⊢ e)
compile⊢ (app e₁ e₂)    = compile⊢ e₁ ▻▻ (compile⊢ e₂ ▻ app)
compile⊢ (lεt e₁ e₂)    = (compile⊢ e₁ ▻ push) ▻▻ (compile⊢ e₂ ▻ pop)

mutual
  {-# TERMINATING #-}
  compile⟦⟧ : ∀ {A} → ⟦ A ⟧𝓢 → ⟦ A ⟧𝓣
  compile⟦⟧ {ℕ}     n           = n
  compile⟦⟧ {A ⇒ B} (_ , ρ , e) = _ , compileᵉⁿᵛ ρ , compile⊢ e

  compileᵉⁿᵛ : ∀ {Γ} → Env𝓢 Γ → Env𝓣 Γ
  compileᵉⁿᵛ = map compile⟦⟧

compile✓ : ∀ {Γ Σ A} {ρ : Env𝓢 Γ} {σ : Stack Σ} {e : Γ ⊢ A} {a : ⟦ A ⟧𝓢}
  → ρ ⊢ e ⇓ a
  → Step⋆ (compile⊢ e) [ compileᵉⁿᵛ ρ , σ ] [ compileᵉⁿᵛ ρ , σ ▻ compile⟦⟧ a ]
compile✓ (lit n) = ε ▻ lit n
compile✓ (add d₁ d₂) = compile✓ d₁ ▻▻▻ (compile✓ d₂ ▻ add)
compile✓ (sub d₁ d₂) = compile✓ d₁ ▻▻▻ (compile✓ d₂ ▻ sub)
compile✓ (mul d₁ d₂) = compile✓ d₁ ▻▻▻ (compile✓ d₂ ▻ mul)
compile✓ (ifz/t d₁ d₂) = compile✓ d₁ ▻ ifz/t (compile✓ d₂)
compile✓ (ifz/f d₁ d₃) = compile✓ d₁ ▻ ifz/f (compile✓ d₃)
compile✓ {ρ = ρ} (var x) rewrite (find-map x compile⟦⟧ ρ)⁻¹ = ε ▻ var x
compile✓ lam = ε ▻ lam
compile✓ (app d₁ d₂ d₃) = compile✓ d₁ ▻▻▻ (compile✓ d₂ ▻ app (compile✓ d₃))
compile✓ (lεt d₁ d₂) = (compile✓ d₁ ▻ push) ▻▻▻ (compile✓ d₂ ▻ pop)
