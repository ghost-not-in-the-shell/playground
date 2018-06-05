module Jellyfish.LambdaLift where
open import Jellyfish.Prelude
open import Jellyfish.SuperCombinator.Syntax.WithoutToplevels
open import Jellyfish.SuperCombinator.Syntax.WithToplevels
open import Jellyfish.SuperCombinator.Semantics.WithoutToplevels renaming (Env to Env𝓢)
open import Jellyfish.SuperCombinator.Semantics.WithToplevels    renaming (Env to Env𝓣)

sig : ∀ {Γ A} → Γ ⊢ A → List Sig
sig (lit n)        = ε
sig (add e₁ e₂)    = sig e₁ ▻▻ sig e₂
sig (sub e₁ e₂)    = sig e₁ ▻▻ sig e₂
sig (mul e₁ e₂)    = sig e₁ ▻▻ sig e₂
sig (ifz e₁ e₂ e₃) = (sig e₁ ▻▻ sig e₂) ▻▻ sig e₃
sig (var x)        = ε
sig (cls {A⃗} {A} {B} e x⃗) = sig e ▻ ((A⃗ ▻ A) , B)
sig (app e₁ e₂)    = sig e₁ ▻▻ sig e₂
sig (lεt e₁ e₂)    = sig e₁ ▻▻ sig e₂

lift⊢ : ∀ {Ε₁ Γ A}
  → Defs Ε₁
  → (e : Γ ⊢ A)
  → Defs (Ε₁ ▻▻ sig e) × (Ε₁ ▻▻ sig e) [ Γ ]⊢ A
lift⊢ d⃗ (lit n) = d⃗ , lit n

lift⊢ {Ε₁} d⃗ (add e₁ e₂) with lift⊢ d⃗  e₁
... | (d⃗₁ , e₁′)         with lift⊢ d⃗₁ e₂
... | (d⃗₂ , e₂′) rewrite ▻▻-assoc Ε₁ (sig e₁) (sig e₂)
  = d⃗₂ , add (▻▻-wk⊢ (sig e₂) e₁′ ⟦ (_[ _ ]⊢ _) ⟨$⟩ ▻▻-assoc Ε₁ (sig e₁) (sig e₂) ⟫) e₂′

lift⊢ {Ε₁} d⃗ (sub e₁ e₂) with lift⊢ d⃗  e₁
... | (d⃗₁ , e₁′)         with lift⊢ d⃗₁ e₂
... | (d⃗₂ , e₂′) rewrite ▻▻-assoc Ε₁ (sig e₁) (sig e₂)
  = d⃗₂ , sub (▻▻-wk⊢ (sig e₂) e₁′ ⟦ (_[ _ ]⊢ _) ⟨$⟩ ▻▻-assoc Ε₁ (sig e₁) (sig e₂) ⟫) e₂′
lift⊢ {Ε₁} d⃗ (mul e₁ e₂) with lift⊢ d⃗  e₁
... | (d⃗₁ , e₁′)         with lift⊢ d⃗₁ e₂
... | (d⃗₂ , e₂′) rewrite ▻▻-assoc Ε₁ (sig e₁) (sig e₂)
  = d⃗₂ , mul (▻▻-wk⊢ (sig e₂) e₁′ ⟦ (_[ _ ]⊢ _) ⟨$⟩ ▻▻-assoc Ε₁ (sig e₁) (sig e₂) ⟫) e₂′

lift⊢ {Ε₁} d⃗ (ifz e₁ e₂ e₃) with lift⊢ d⃗  e₁
... | (d⃗₁ , e₁′)            with lift⊢ d⃗₁ e₂
... | (d⃗₂ , e₂′)            with lift⊢ d⃗₂ e₃
... | (d⃗₃ , e₃′)
  = d⃗₃ ⟦ (λ - → All (λ sig → - [ π₁ sig ]⊢ π₂ sig) -) ⟨$⟩ (▻▻-assoc (Ε₁ ▻▻ sig e₁) (sig e₂) (sig e₃)
                                                        ⋮ ▻▻-assoc Ε₁ (sig e₁) (sig e₂ ▻▻ sig e₃)
                                                        ⋮ (Ε₁ ▻▻_ ⟨$⟩ ▻▻-assoc (sig e₁) (sig e₂) (sig e₃))⁻¹) ⟫
                                                          , ifz (▻▻-wk⊢ (sig e₂ ▻▻ sig e₃) e₁′ ⟦ (_[ _ ]⊢ _) ⟨$⟩ (▻▻-assoc Ε₁ (sig e₁) (sig e₂ ▻▻ sig e₃) ⋮ (Ε₁ ▻▻_ ⟨$⟩ ▻▻-assoc (sig e₁) (sig e₂) (sig e₃))⁻¹) ⟫)
                                                                (▻▻-wk⊢ (sig e₃) e₂′           ⟦ (_[ _ ]⊢ _) ⟨$⟩ (▻▻-assoc (Ε₁ ▻▻ sig e₁) (sig e₂) (sig e₃) ⋮ ▻▻-assoc Ε₁ (sig e₁) (sig e₂ ▻▻ sig e₃) ⋮ (Ε₁ ▻▻_ ⟨$⟩ ▻▻-assoc (sig e₁) (sig e₂) (sig e₃)) ⁻¹) ⟫)
                                                                (e₃′                           ⟦ (_[ _ ]⊢ _) ⟨$⟩ (▻▻-assoc (Ε₁ ▻▻ sig e₁) (sig e₂) (sig e₃) ⋮ ▻▻-assoc Ε₁ (sig e₁) (sig e₂ ▻▻ sig e₃) ⋮ (Ε₁ ▻▻_ ⟨$⟩ ▻▻-assoc (sig e₁) (sig e₂) (sig e₃)) ⁻¹) ⟫)

lift⊢ {Ε₁} d⃗ (var x) = d⃗ , var x

lift⊢ {Ε₁} d⃗ (cls {A⃗} {A} {B} e x⃗) with lift⊢ d⃗ e
... | (d⃗′ , e′) rewrite (▻▻-assoc Ε₁ (sig e) (ε ▻ ((A⃗ ▻ A) , B)))⁻¹
  = (map (▻▻-wk⊢ (ε ▻ ((A⃗ ▻ A) , B))) (d⃗′ ▻ e′)) , cls ze x⃗

lift⊢ {Ε₁} d⃗ (app e₁ e₂) with lift⊢ d⃗  e₁
... | (d⃗₁ , e₁′)         with lift⊢ d⃗₁ e₂
... | (d⃗₂ , e₂′) rewrite ▻▻-assoc Ε₁ (sig e₁) (sig e₂)
  = d⃗₂ , app (▻▻-wk⊢ (sig e₂) e₁′ ⟦ (_[ _ ]⊢ _) ⟨$⟩ ▻▻-assoc Ε₁ (sig e₁) (sig e₂) ⟫) e₂′

lift⊢ {Ε₁} d⃗ (lεt e₁ e₂) with lift⊢ d⃗  e₁
... | (d⃗₁ , e₁′)         with lift⊢ d⃗₁ e₂
... | (d⃗₂ , e₂′) rewrite ▻▻-assoc Ε₁ (sig e₁) (sig e₂)
  = d⃗₂ , lεt (▻▻-wk⊢ (sig e₂) e₁′ ⟦ (_[ _ ]⊢ _) ⟨$⟩ ▻▻-assoc Ε₁ (sig e₁) (sig e₂) ⟫) e₂′

{-
mutual
  {-# TERMINATING #-}
  liftᵛᵃˡ : ∀ {Ε A} → Defs Ε → ⟦ A ⟧ → Val Ε A
  liftᵛᵃˡ {A = ℕ}     d⃗ n           = n
  liftᵛᵃˡ {A = A ⇒ B} d⃗ (_ , ρ , e) = {!(_ , liftᵉⁿᵛ d⃗ ρ , lift⊢ e)!}

  liftᵉⁿᵛ : ∀ {Ε Γ} → Defs Ε → Env𝓢 Γ → Env𝓣 Ε Γ
  liftᵉⁿᵛ d⃗ ρ = map (liftᵛᵃˡ d⃗) ρ
-}
