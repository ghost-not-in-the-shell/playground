module Jellyfish.Trivial where
open import Jellyfish.Prelude
open import Jellyfish.Core.Syntax.Typed                          renaming (_⊢_ to _⊢𝓢_)
open import Jellyfish.SuperCombinator.Syntax.WithoutToplevels    renaming (_⊢_ to _⊢𝓣_)
open import Jellyfish.Core.Semantics                             renaming (⟦_⟧ to ⟦_⟧𝓢; Env to Env𝓢; _⊢_⇓_ to _⊢𝓢_⇓_)
open import Jellyfish.SuperCombinator.Semantics.WithoutToplevels renaming (⟦_⟧ to ⟦_⟧𝓣; Env to Env𝓣; _⊢_⇓_ to _⊢𝓣_⇓_)

convert⊢ : ∀ {Γ A} → Γ ⊢𝓢 A → Γ ⊢𝓣 A
convert⊢ (lit n)        = lit n
convert⊢ (add e₁ e₂)    = add (convert⊢ e₁) (convert⊢ e₂)
convert⊢ (sub e₁ e₂)    = sub (convert⊢ e₁) (convert⊢ e₂)
convert⊢ (mul e₁ e₂)    = mul (convert⊢ e₁) (convert⊢ e₂)
convert⊢ (ifz e₁ e₂ e₃) = ifz (convert⊢ e₁) (convert⊢ e₂) (convert⊢ e₃)
convert⊢ (var x)        = var x
convert⊢ (lam e)        = cls (convert⊢ e) id∋⃗
convert⊢ (app e₁ e₂)    = app (convert⊢ e₁) (convert⊢ e₂)
convert⊢ (lεt e₁ e₂)    = lεt (convert⊢ e₁) (convert⊢ e₂)

mutual
  {-# TERMINATING #-}
  convert⟦⟧ : ∀ {A} → ⟦ A ⟧𝓢 → ⟦ A ⟧𝓣
  convert⟦⟧ {ℕ}     n           = n
  convert⟦⟧ {A ⇒ B} (_ , ρ , e) = (_ , convertᵉⁿᵛ ρ , convert⊢ e)

  convertᵉⁿᵛ : ∀ {Γ} → Env𝓢 Γ → Env𝓣 Γ
  convertᵉⁿᵛ = map convert⟦⟧

private
  map-find-id∋⃗ : ∀ {Γ} (ρ : Env𝓢 Γ)
    → map (find (convertᵉⁿᵛ ρ)) id∋⃗ ≡ convertᵉⁿᵛ ρ
  map-find-id∋⃗ ε       = refl
  map-find-id∋⃗ (ρ ▻ a) = (_▻ convert⟦⟧ a ⟨$⟩ map-resp-∘₂ id∋⃗) ⁻¹
                       ⋮ (_▻ convert⟦⟧ a ⟨$⟩ map-find-id∋⃗ ρ)

convert✓ : ∀ {Γ A} {ρ : Env𝓢 Γ} {e : Γ ⊢𝓢 A} {a : ⟦ A ⟧𝓢}
  →            ρ ⊢𝓢          e ⇓           a
  → convertᵉⁿᵛ ρ ⊢𝓣 convert⊢ e ⇓ convert⟦⟧ a
convert✓ (lit n)        = lit n
convert✓ (add d₁ d₂)    = add (convert✓ d₁) (convert✓ d₂)
convert✓ (sub d₁ d₂)    = sub (convert✓ d₁) (convert✓ d₂)
convert✓ (mul d₁ d₂)    = mul (convert✓ d₁) (convert✓ d₂)
convert✓ (ifz/t d₁ d₂)  = ifz/t (convert✓ d₁) (convert✓ d₂)
convert✓ (ifz/f d₁ d₃)  = ifz/f (convert✓ d₁) (convert✓ d₃)
convert✓ {ρ = ρ} (var x)
  = var x ⟦ (λ - → convertᵉⁿᵛ ρ ⊢𝓣 convert⊢ (var x) ⇓ -)           ⟨$⟩ find-map x convert⟦⟧ ρ ⟫
convert✓ {ρ = ρ} (lam {e = e})
  = cls   ⟦ (λ - → convertᵉⁿᵛ ρ ⊢𝓣 convert⊢ (lam e) ⇓ (_ , - , _)) ⟨$⟩ map-find-id∋⃗ ρ ⟫
convert✓ (app d₁ d₂ d₃) = app (convert✓ d₁) (convert✓ d₂) (convert✓ d₃)
convert✓ (lεt d₁ d₂)    = lεt (convert✓ d₁) (convert✓ d₂)
