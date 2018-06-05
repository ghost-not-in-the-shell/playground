module Jellyfish.Strengthening where
open import Jellyfish.Prelude             renaming (_∋_ to _∋𝓢_)
open import Jellyfish.Core.Syntax.Typed   renaming (_⊢_ to _⊢𝓢_)
open import Jellyfish.Relevance.Syntax    renaming (_∋_ to _∋𝓘_; _⊢_ to _⊢𝓘_)
open import Jellyfish.Core.Semantics      renaming (⟦_⟧ to ⟦_⟧𝓢; Env to Env𝓢; _⊢_⇓_ to _⊢𝓢_⇓_)
open import Jellyfish.Relevance.Semantics renaming (⟦_⟧ to ⟦_⟧𝓘; Env to Env𝓘; _⊢_⇓_ to _⊢𝓘_⇓_)

FV : ∀ {Γ A} → Γ ⊢𝓢 A → Subset Γ
FV (lit n)        = ∅
FV (add e₁ e₂)    = FV e₁ ∪ FV e₂
FV (sub e₁ e₂)    = FV e₁ ∪ FV e₂
FV (mul e₁ e₂)    = FV e₁ ∪ FV e₂
FV (ifz e₁ e₂ e₃) = FV e₁ ∪ FV e₂ ∪ FV e₃
FV (var x)        = ⁅ x ⁆
FV (lam e)        = ↓ FV e
FV (app e₁ e₂)    = FV e₁ ∪ FV e₂
FV (lεt e₁ e₂)    = FV e₁ ∪ ↓ FV e₂

Subset→∋⃗ : ∀ {Γ} (⌊Γ⌋ : Subset Γ) → Γ ∋⃗ ⌈ ⌊Γ⌋ ⌉
Subset→∋⃗ ε = ε
Subset→∋⃗ (⌊Γ⌋ ▻ outside) = map su (Subset→∋⃗ ⌊Γ⌋)
Subset→∋⃗ (⌊Γ⌋ ▻  inside) = map su (Subset→∋⃗ ⌊Γ⌋) ▻ ze

strengthen∋ : ∀ {Γ A} (x : Γ ∋𝓢 A) → ⁅ x ⁆ ∋𝓘 A
strengthen∋ ze     = ze
strengthen∋ (su x) = su (strengthen∋ x)

∪ˡ-weaken∋ : ∀ {Γ A} {⌊Γ⌋₁ : Subset Γ} ⌊Γ⌋₂ → ⌊Γ⌋₁ ∋𝓘 A → ⌊Γ⌋₁ ∪ ⌊Γ⌋₂ ∋𝓘 A
∪ˡ-weaken∋ (⌊Γ⌋₂ ▻ outside) ze = ze
∪ˡ-weaken∋ (⌊Γ⌋₂ ▻  inside) ze = ze
∪ˡ-weaken∋ {⌊Γ⌋₁ = ⌊Γ⌋₁ ▻ outside} (⌊Γ⌋₂ ▻ outside) (su x) = su (∪ˡ-weaken∋ ⌊Γ⌋₂ x)
∪ˡ-weaken∋ {⌊Γ⌋₁ = ⌊Γ⌋₁ ▻  inside} (⌊Γ⌋₂ ▻ outside) (su x) = su (∪ˡ-weaken∋ ⌊Γ⌋₂ x)
∪ˡ-weaken∋ {⌊Γ⌋₁ = ⌊Γ⌋₁ ▻ outside} (⌊Γ⌋₂ ▻  inside) (su x) = su (∪ˡ-weaken∋ ⌊Γ⌋₂ x)
∪ˡ-weaken∋ {⌊Γ⌋₁ = ⌊Γ⌋₁ ▻  inside} (⌊Γ⌋₂ ▻  inside) (su x) = su (∪ˡ-weaken∋ ⌊Γ⌋₂ x)

∪ʳ-weaken∋ : ∀ {Γ A} {⌊Γ⌋₂ : Subset Γ} ⌊Γ⌋₁ → ⌊Γ⌋₂ ∋𝓘 A → ⌊Γ⌋₁ ∪ ⌊Γ⌋₂ ∋𝓘 A
∪ʳ-weaken∋ (⌊Γ⌋₁ ▻ outside) ze = ze
∪ʳ-weaken∋ (⌊Γ⌋₁ ▻  inside) ze = ze
∪ʳ-weaken∋ {⌊Γ⌋₂ = ⌊Γ⌋₂ ▻ outside} (⌊Γ⌋₁ ▻ outside) (su x) = su (∪ʳ-weaken∋ ⌊Γ⌋₁ x)
∪ʳ-weaken∋ {⌊Γ⌋₂ = ⌊Γ⌋₂ ▻  inside} (⌊Γ⌋₁ ▻ outside) (su x) = su (∪ʳ-weaken∋ ⌊Γ⌋₁ x)
∪ʳ-weaken∋ {⌊Γ⌋₂ = ⌊Γ⌋₂ ▻ outside} (⌊Γ⌋₁ ▻  inside) (su x) = su (∪ʳ-weaken∋ ⌊Γ⌋₁ x)
∪ʳ-weaken∋ {⌊Γ⌋₂ = ⌊Γ⌋₂ ▻  inside} (⌊Γ⌋₁ ▻  inside) (su x) = su (∪ʳ-weaken∋ ⌊Γ⌋₁ x)

∪ˡ-weaken⊢ : ∀ {Γ A} {⌊Γ⌋₁ : Subset Γ} ⌊Γ⌋₂ → ⌊Γ⌋₁ ⊢𝓘 A → ⌊Γ⌋₁ ∪ ⌊Γ⌋₂ ⊢𝓘 A
∪ˡ-weaken⊢ ⌊Γ⌋₂ (lit n)        = lit n
∪ˡ-weaken⊢ ⌊Γ⌋₂ (add e₁ e₂)    = add (∪ˡ-weaken⊢ ⌊Γ⌋₂ e₁) (∪ˡ-weaken⊢ ⌊Γ⌋₂ e₂)
∪ˡ-weaken⊢ ⌊Γ⌋₂ (sub e₁ e₂)    = sub (∪ˡ-weaken⊢ ⌊Γ⌋₂ e₁) (∪ˡ-weaken⊢ ⌊Γ⌋₂ e₂)
∪ˡ-weaken⊢ ⌊Γ⌋₂ (mul e₁ e₂)    = mul (∪ˡ-weaken⊢ ⌊Γ⌋₂ e₁) (∪ˡ-weaken⊢ ⌊Γ⌋₂ e₂)
∪ˡ-weaken⊢ ⌊Γ⌋₂ (ifz e₁ e₂ e₃) = ifz (∪ˡ-weaken⊢ ⌊Γ⌋₂ e₁) (∪ˡ-weaken⊢ ⌊Γ⌋₂ e₂) (∪ˡ-weaken⊢ ⌊Γ⌋₂ e₃)
∪ˡ-weaken⊢ ⌊Γ⌋₂ (var x)        = var (∪ˡ-weaken∋ ⌊Γ⌋₂ x)
∪ˡ-weaken⊢ ⌊Γ⌋₂ (lam e)        = lam (∪ˡ-weaken⊢ (↑ ⌊Γ⌋₂) e)
∪ˡ-weaken⊢ ⌊Γ⌋₂ (app e₁ e₂)    = app (∪ˡ-weaken⊢ ⌊Γ⌋₂ e₁) (∪ˡ-weaken⊢ ⌊Γ⌋₂ e₂)
∪ˡ-weaken⊢ ⌊Γ⌋₂ (lεt e₁ e₂)    = lεt (∪ˡ-weaken⊢ ⌊Γ⌋₂ e₁) (∪ˡ-weaken⊢ (↑ ⌊Γ⌋₂) e₂)

∪ʳ-weaken⊢ : ∀ {Γ A} {⌊Γ⌋₂ : Subset Γ} ⌊Γ⌋₁ → ⌊Γ⌋₂ ⊢𝓘 A → ⌊Γ⌋₁ ∪ ⌊Γ⌋₂ ⊢𝓘 A
∪ʳ-weaken⊢ ⌊Γ⌋₁ (lit n)        = lit n
∪ʳ-weaken⊢ ⌊Γ⌋₁ (add e₁ e₂)    = add (∪ʳ-weaken⊢ ⌊Γ⌋₁ e₁) (∪ʳ-weaken⊢ ⌊Γ⌋₁ e₂)
∪ʳ-weaken⊢ ⌊Γ⌋₁ (sub e₁ e₂)    = sub (∪ʳ-weaken⊢ ⌊Γ⌋₁ e₁) (∪ʳ-weaken⊢ ⌊Γ⌋₁ e₂)
∪ʳ-weaken⊢ ⌊Γ⌋₁ (mul e₁ e₂)    = mul (∪ʳ-weaken⊢ ⌊Γ⌋₁ e₁) (∪ʳ-weaken⊢ ⌊Γ⌋₁ e₂)
∪ʳ-weaken⊢ ⌊Γ⌋₁ (ifz e₁ e₂ e₃) = ifz (∪ʳ-weaken⊢ ⌊Γ⌋₁ e₁) (∪ʳ-weaken⊢ ⌊Γ⌋₁ e₂) (∪ʳ-weaken⊢ ⌊Γ⌋₁ e₃)
∪ʳ-weaken⊢ ⌊Γ⌋₁ (var x)        = var (∪ʳ-weaken∋ ⌊Γ⌋₁ x)
∪ʳ-weaken⊢ ⌊Γ⌋₁ (lam e)        = lam (∪ʳ-weaken⊢ (↑ ⌊Γ⌋₁) e)
∪ʳ-weaken⊢ ⌊Γ⌋₁ (app e₁ e₂)    = app (∪ʳ-weaken⊢ ⌊Γ⌋₁ e₁) (∪ʳ-weaken⊢ ⌊Γ⌋₁ e₂)
∪ʳ-weaken⊢ ⌊Γ⌋₁ (lεt e₁ e₂)    = lεt (∪ʳ-weaken⊢ ⌊Γ⌋₁ e₁) (∪ʳ-weaken⊢ (↑ ⌊Γ⌋₁) e₂)

⁅_⁆-weaken∋ : ∀ {Γ A B} {⌊Γ⌋ : Subset Γ} (x : Γ ∋𝓢 A) → ⌊Γ⌋ ∋𝓘 B → ⌊Γ⌋ ∪ ⁅ x ⁆ ∋𝓘 B
⁅ ze   ⁆-weaken∋ ze = ze
⁅ su x ⁆-weaken∋ ze = ze
⁅_⁆-weaken∋ {⌊Γ⌋ = ⌊Γ⌋ ▻ outside} (ze)   (su y) rewrite ∪-identityʳ ⌊Γ⌋ = su y
⁅_⁆-weaken∋ {⌊Γ⌋ = ⌊Γ⌋ ▻  inside} (ze)   (su y) rewrite ∪-identityʳ ⌊Γ⌋ = su y
⁅_⁆-weaken∋ {⌊Γ⌋ = ⌊Γ⌋ ▻ outside} (su x) (su y) = su (⁅ x ⁆-weaken∋ y)
⁅_⁆-weaken∋ {⌊Γ⌋ = ⌊Γ⌋ ▻  inside} (su x) (su y) = su (⁅ x ⁆-weaken∋ y)

⁅_⁆-weaken⊢ : ∀ {Γ A B} {⌊Γ⌋ : Subset Γ} (x : Γ ∋𝓢 A) → ⌊Γ⌋ ⊢𝓘 B → ⌊Γ⌋ ∪ ⁅ x ⁆ ⊢𝓘 B
⁅ x ⁆-weaken⊢ (lit n)        = lit n
⁅ x ⁆-weaken⊢ (add e₁ e₂)    = add (⁅ x ⁆-weaken⊢ e₁) (⁅ x ⁆-weaken⊢ e₂)
⁅ x ⁆-weaken⊢ (sub e₁ e₂)    = sub (⁅ x ⁆-weaken⊢ e₁) (⁅ x ⁆-weaken⊢ e₂)
⁅ x ⁆-weaken⊢ (mul e₁ e₂)    = mul (⁅ x ⁆-weaken⊢ e₁) (⁅ x ⁆-weaken⊢ e₂)
⁅ x ⁆-weaken⊢ (ifz e₁ e₂ e₃) = ifz (⁅ x ⁆-weaken⊢ e₁) (⁅ x ⁆-weaken⊢ e₂) (⁅ x ⁆-weaken⊢ e₃)
⁅ x ⁆-weaken⊢ (var y)        = var (⁅ x ⁆-weaken∋ y)
⁅ x ⁆-weaken⊢ (lam e)        = lam (⁅ su x ⁆-weaken⊢ e)
⁅ x ⁆-weaken⊢ (app e₁ e₂)    = app (⁅ x ⁆-weaken⊢ e₁) (⁅ x ⁆-weaken⊢ e₂)
⁅ x ⁆-weaken⊢ (lεt e₁ e₂)    = lεt (⁅ x ⁆-weaken⊢ e₁) (⁅ su x ⁆-weaken⊢ e₂)

↑↓-weaken⊢ : ∀ {Γ A B} {⌊Γ⌋ : Subset (Γ ▻ A)} → ⌊Γ⌋ ⊢𝓘 B → ↑⁽ A ⁾ ↓ ⌊Γ⌋ ⊢𝓘 B
↑↓-weaken⊢ {⌊Γ⌋ = ⌊Γ⌋} e rewrite ↑↓≡∪⁅ze⁆ ⌊Γ⌋ = ⁅ ze ⁆-weaken⊢ e

strengthen⊢ : ∀ {Γ A} (e : Γ ⊢𝓢 A) → FV e ⊢𝓘 A
strengthen⊢ (lit n)        = lit n
strengthen⊢ (add e₁ e₂)    = add (∪ˡ-weaken⊢ (FV e₂) (strengthen⊢ e₁))
                                 (∪ʳ-weaken⊢ (FV e₁) (strengthen⊢ e₂))
strengthen⊢ (sub e₁ e₂)    = sub (∪ˡ-weaken⊢ (FV e₂) (strengthen⊢ e₁))
                                 (∪ʳ-weaken⊢ (FV e₁) (strengthen⊢ e₂))
strengthen⊢ (mul e₁ e₂)    = mul (∪ˡ-weaken⊢ (FV e₂) (strengthen⊢ e₁))
                                 (∪ʳ-weaken⊢ (FV e₁) (strengthen⊢ e₂))
strengthen⊢ (ifz e₁ e₂ e₃) = ifz (∪ˡ-weaken⊢ (FV e₂ ∪ FV e₃) (strengthen⊢ e₁))
                                 (∪ʳ-weaken⊢ (FV e₁) (∪ˡ-weaken⊢ (FV e₃) (strengthen⊢ e₂)))
                                 (∪ʳ-weaken⊢ (FV e₁) (∪ʳ-weaken⊢ (FV e₂) (strengthen⊢ e₃)))
strengthen⊢ (var x)        = var (strengthen∋ x)
strengthen⊢ (lam e)        = lam (↑↓-weaken⊢ (strengthen⊢ e))
strengthen⊢ (app e₁ e₂)    = app (∪ˡ-weaken⊢ (FV e₂) (strengthen⊢ e₁)) (∪ʳ-weaken⊢ (FV e₁) (strengthen⊢ e₂))
strengthen⊢ (lεt e₁ e₂)    = lεt (∪ˡ-weaken⊢ (↓ FV e₂) (strengthen⊢ e₁))
                                 (∪ʳ-weaken⊢ (↑ FV e₁) (↑↓-weaken⊢ (strengthen⊢ e₂)))

⌈_⌉⊢ : ∀ {Γ A} {⌊Γ⌋ : Subset Γ} → ⌊Γ⌋ ⊢𝓘 A → ⌈ ⌊Γ⌋ ⌉ ⊢𝓢 A
⌈ lit n        ⌉⊢ = lit n
⌈ add e₁ e₂    ⌉⊢ = add ⌈ e₁ ⌉⊢ ⌈ e₂ ⌉⊢
⌈ sub e₁ e₂    ⌉⊢ = sub ⌈ e₁ ⌉⊢ ⌈ e₂ ⌉⊢
⌈ mul e₁ e₂    ⌉⊢ = mul ⌈ e₁ ⌉⊢ ⌈ e₂ ⌉⊢
⌈ ifz e₁ e₂ e₃ ⌉⊢ = ifz ⌈ e₁ ⌉⊢ ⌈ e₂ ⌉⊢ ⌈ e₃ ⌉⊢
⌈ var x        ⌉⊢ = var ⌈ x ⌉∋
⌈ lam e        ⌉⊢ = lam ⌈ e ⌉⊢
⌈ app e₁ e₂    ⌉⊢ = app ⌈ e₁ ⌉⊢ ⌈ e₂ ⌉⊢
⌈ lεt e₁ e₂    ⌉⊢ = lεt ⌈ e₁ ⌉⊢ ⌈ e₂ ⌉⊢

mutual
  {-# TERMINATING #-}
  strengthen⟦⟧ : ∀ {A} → ⟦ A ⟧𝓢 → ⟦ A ⟧𝓘
  strengthen⟦⟧ {ℕ}     n           = n
  strengthen⟦⟧ {A ⇒ B} (_ , ρ , e) = (_ , _ , strengthenᵉⁿᵛ (↓ FV e) ρ , ↑↓-weaken⊢ (strengthen⊢ e))

  strengthenᵉⁿᵛ : ∀ {Γ} (⌊Γ⌋ : Subset Γ) → Env𝓢 Γ → Env𝓘 ⌊Γ⌋
  strengthenᵉⁿᵛ ⌊Γ⌋ ρ = map strengthen⟦⟧ (trim ⌊Γ⌋ ρ)

postulate
  strengthen✓ : ∀ {Γ A} {ρ : Env𝓢 Γ} {e : Γ ⊢𝓢 A} {a : ⟦ A ⟧𝓢}
    →                      ρ ⊢𝓢             e ⇓              a
    → strengthenᵉⁿᵛ (FV e) ρ ⊢𝓘 strengthen⊢ e ⇓ strengthen⟦⟧ a

mutual
  {-# TERMINATING #-}
  inject⟦⟧ : ∀ {A} → ⟦ A ⟧𝓘 → ⟦ A ⟧𝓢
  inject⟦⟧ {ℕ} n = n
  inject⟦⟧ {A ⇒ B} (_ , ⌊Γ⌋ , ρ , e) = (_ , injectᵉⁿᵛ ⌊Γ⌋ ρ , ⌈ e ⌉⊢)

  injectᵉⁿᵛ : ∀ {Γ} (⌊Γ⌋ : Subset Γ) → Env𝓘 ⌊Γ⌋ → Env𝓢 ⌈ ⌊Γ⌋ ⌉
  injectᵉⁿᵛ ⌊Γ⌋ = map inject⟦⟧

inject✓ : ∀ {Γ A} {⌊Γ⌋ : Subset Γ} {ρ : Env𝓘 ⌊Γ⌋} {e : ⌊Γ⌋ ⊢𝓘 A} {a : ⟦ A ⟧𝓘}
  →               ρ ⊢𝓘   e    ⇓          a
  → injectᵉⁿᵛ ⌊Γ⌋ ρ ⊢𝓢 ⌈ e ⌉⊢ ⇓ inject⟦⟧ a
inject✓ (lit n)        = lit n
inject✓ (add d₁ d₂)    = add (inject✓ d₁) (inject✓ d₂)
inject✓ (sub d₁ d₂)    = sub (inject✓ d₁) (inject✓ d₂)
inject✓ (mul d₁ d₂)    = mul (inject✓ d₁) (inject✓ d₂)
inject✓ (ifz/t d₁ d₂)  = ifz/t (inject✓ d₁) (inject✓ d₂)
inject✓ (ifz/f d₁ d₃)  = ifz/f (inject✓ d₁) (inject✓ d₃)
inject✓ {ρ = ρ} (var x) rewrite (find-map ⌈ x ⌉∋ inject⟦⟧ ρ)⁻¹
  = var ⌈ x ⌉∋
inject✓ lam            = lam
inject✓ (app d₁ d₂ d₃) = app (inject✓ d₁) (inject✓ d₂) (inject✓ d₃)
inject✓ (lεt d₁ d₂)    = lεt (inject✓ d₁) (inject✓ d₂)
