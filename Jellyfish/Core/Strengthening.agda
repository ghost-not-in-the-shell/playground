module Jellyfish.Core.Strengthening where
open import Jellyfish.Prelude
open import Jellyfish.Core.Type
open import Jellyfish.Core.Context
open import Jellyfish.Core.Syntax

FV : ∀ {Γ A} → Γ ⊢ A → Subset Γ
FV (lit n)        = ∅
FV (add e₁ e₂)    = FV e₁ ∪ FV e₂
FV (sub e₁ e₂)    = FV e₁ ∪ FV e₂
FV (mul e₁ e₂)    = FV e₁ ∪ FV e₂
FV (ifz e₁ e₂ e₃) = FV e₁ ∪ FV e₂ ∪ FV e₃
FV (var x)        = ⁅ x ⁆
FV (lam e)        = ↓ FV e
FV (app e₁ e₂)    = FV e₁ ∪ FV e₂
FV (lεt e₁ e₂)    = FV e₁ ∪ ↓ FV e₂

infix 4 _∣_∋_
data _∣_∋_ : ∀ Γ → Subset Γ → Ty → Set where
  ze : ∀ {Γ} {Φ : Subset Γ} {A}                    → Γ ▻ A ∣ Φ ▻ inside ∋ A
  su : ∀ {Γ} {Φ : Subset Γ} {A B side} → Γ ∣ Φ ∋ A → Γ ▻ B ∣ Φ ▻   side ∋ A

infix 4 _∣_⊢_
data _∣_⊢_ (Γ : Con) (Φ : Subset Γ) : Ty → Set where
  lit : Nat
      -----------
      → Γ ∣ Φ ⊢ ℕ

  add : Γ ∣ Φ ⊢ ℕ
      → Γ ∣ Φ ⊢ ℕ
      -----------
      → Γ ∣ Φ ⊢ ℕ

  sub : Γ ∣ Φ ⊢ ℕ
      → Γ ∣ Φ ⊢ ℕ
      -----------
      → Γ ∣ Φ ⊢ ℕ

  mul : Γ ∣ Φ ⊢ ℕ
      → Γ ∣ Φ ⊢ ℕ
      -----------
      → Γ ∣ Φ ⊢ ℕ

  ifz : ∀ {A}
    → Γ ∣ Φ ⊢ ℕ
    → Γ ∣ Φ ⊢ A
    → Γ ∣ Φ ⊢ A
    -----------
    → Γ ∣ Φ ⊢ A

  var : ∀ {A}
    → Γ ∣ Φ ∋ A
    -----------
    → Γ ∣ Φ ⊢ A

  lam : ∀ {A B}
    → Γ ▻ A ∣ ↑ Φ ⊢ B
    ---------------------
    → Γ     ∣   Φ ⊢ A ⇒ B

  app : ∀ {A B}
    → Γ ∣ Φ ⊢ A ⇒ B
    → Γ ∣ Φ ⊢ A
    ---------------
    → Γ ∣ Φ ⊢ B

  lεt : ∀ {A B}
    → Γ     ∣   Φ ⊢ A
    → Γ ▻ A ∣ ↑ Φ ⊢ B
    -----------------
    → Γ     ∣   Φ ⊢ B

⌈_⌉∋ : ∀ {Γ Φ A} → Γ ∣ Φ ∋ A → ⌈ Φ ⌉ ∋ A
⌈ ze ⌉∋ = ze
⌈_⌉∋ {Φ = Φ ▻ outside} (su x) =    ⌈ x ⌉∋
⌈_⌉∋ {Φ = Φ ▻  inside} (su x) = su ⌈ x ⌉∋

⌈_⌉⊢ : ∀ {Γ Φ A} → Γ ∣ Φ ⊢ A → ⌈ Φ ⌉ ⊢ A
⌈ lit n        ⌉⊢ = lit n
⌈ add e₁ e₂    ⌉⊢ = add ⌈ e₁ ⌉⊢ ⌈ e₂ ⌉⊢
⌈ sub e₁ e₂    ⌉⊢ = sub ⌈ e₁ ⌉⊢ ⌈ e₂ ⌉⊢
⌈ mul e₁ e₂    ⌉⊢ = mul ⌈ e₁ ⌉⊢ ⌈ e₂ ⌉⊢
⌈ ifz e₁ e₂ e₃ ⌉⊢ = ifz ⌈ e₁ ⌉⊢ ⌈ e₂ ⌉⊢ ⌈ e₃ ⌉⊢
⌈ var x        ⌉⊢ = var ⌈ x ⌉∋
⌈ lam e        ⌉⊢ = lam ⌈ e ⌉⊢
⌈ app e₁ e₂    ⌉⊢ = app ⌈ e₁ ⌉⊢ ⌈ e₂ ⌉⊢
⌈ lεt e₁ e₂    ⌉⊢ = lεt ⌈ e₁ ⌉⊢ ⌈ e₂ ⌉⊢


strengthen∋ : ∀ {Γ A} (x : Γ ∋ A) → Γ ∣ ⁅ x ⁆ ∋ A
strengthen∋ ze     = ze
strengthen∋ (su x) = su (strengthen∋ x)

∪ˡ-weaken∋ : ∀ {Γ Φ₁ A} Φ₂ → Γ ∣ Φ₁ ∋ A → Γ ∣ Φ₁ ∪ Φ₂ ∋ A
∪ˡ-weaken∋ (Φ₂ ▻ outside) ze = ze
∪ˡ-weaken∋ (Φ₂ ▻  inside) ze = ze
∪ˡ-weaken∋ {Φ₁ = Φ₁ ▻ outside} (Φ₂ ▻ outside) (su x) = su (∪ˡ-weaken∋ Φ₂ x)
∪ˡ-weaken∋ {Φ₁ = Φ₁ ▻  inside} (Φ₂ ▻ outside) (su x) = su (∪ˡ-weaken∋ Φ₂ x)
∪ˡ-weaken∋ {Φ₁ = Φ₁ ▻ outside} (Φ₂ ▻  inside) (su x) = su (∪ˡ-weaken∋ Φ₂ x)
∪ˡ-weaken∋ {Φ₁ = Φ₁ ▻  inside} (Φ₂ ▻  inside) (su x) = su (∪ˡ-weaken∋ Φ₂ x)

∪ʳ-weaken∋ : ∀ {Γ Φ₂ A} Φ₁ → Γ ∣ Φ₂ ∋ A → Γ ∣ Φ₁ ∪ Φ₂ ∋ A
∪ʳ-weaken∋ (Φ₁ ▻ outside) ze = ze
∪ʳ-weaken∋ (Φ₁ ▻  inside) ze = ze
∪ʳ-weaken∋ {Φ₂ = Φ₂ ▻ outside} (Φ₁ ▻ outside) (su x) = su (∪ʳ-weaken∋ Φ₁ x)
∪ʳ-weaken∋ {Φ₂ = Φ₂ ▻  inside} (Φ₁ ▻ outside) (su x) = su (∪ʳ-weaken∋ Φ₁ x)
∪ʳ-weaken∋ {Φ₂ = Φ₂ ▻ outside} (Φ₁ ▻  inside) (su x) = su (∪ʳ-weaken∋ Φ₁ x)
∪ʳ-weaken∋ {Φ₂ = Φ₂ ▻  inside} (Φ₁ ▻  inside) (su x) = su (∪ʳ-weaken∋ Φ₁ x)

∪ˡ-weaken⊢ : ∀ {Γ Φ₁ A} Φ₂ → Γ ∣ Φ₁ ⊢ A → Γ ∣ Φ₁ ∪ Φ₂ ⊢ A
∪ˡ-weaken⊢ Φ₂ (lit n)        = lit n
∪ˡ-weaken⊢ Φ₂ (add e₁ e₂)    = add (∪ˡ-weaken⊢ Φ₂ e₁) (∪ˡ-weaken⊢ Φ₂ e₂)
∪ˡ-weaken⊢ Φ₂ (sub e₁ e₂)    = sub (∪ˡ-weaken⊢ Φ₂ e₁) (∪ˡ-weaken⊢ Φ₂ e₂)
∪ˡ-weaken⊢ Φ₂ (mul e₁ e₂)    = mul (∪ˡ-weaken⊢ Φ₂ e₁) (∪ˡ-weaken⊢ Φ₂ e₂)
∪ˡ-weaken⊢ Φ₂ (ifz e₁ e₂ e₃) = ifz (∪ˡ-weaken⊢ Φ₂ e₁) (∪ˡ-weaken⊢ Φ₂ e₂) (∪ˡ-weaken⊢ Φ₂ e₃)
∪ˡ-weaken⊢ Φ₂ (var x)        = var (∪ˡ-weaken∋ Φ₂ x)
∪ˡ-weaken⊢ Φ₂ (lam e)        = lam (∪ˡ-weaken⊢ (↑ Φ₂) e)
∪ˡ-weaken⊢ Φ₂ (app e₁ e₂)    = app (∪ˡ-weaken⊢ Φ₂ e₁) (∪ˡ-weaken⊢ Φ₂ e₂)
∪ˡ-weaken⊢ Φ₂ (lεt e₁ e₂)    = lεt (∪ˡ-weaken⊢ Φ₂ e₁) (∪ˡ-weaken⊢ (↑ Φ₂) e₂)

∪ʳ-weaken⊢ : ∀ {Γ Φ₂ A} Φ₁ → Γ ∣ Φ₂ ⊢ A → Γ ∣ Φ₁ ∪ Φ₂ ⊢ A
∪ʳ-weaken⊢ Φ₁ (lit n)        = lit n
∪ʳ-weaken⊢ Φ₁ (add e₁ e₂)    = add (∪ʳ-weaken⊢ Φ₁ e₁) (∪ʳ-weaken⊢ Φ₁ e₂)
∪ʳ-weaken⊢ Φ₁ (sub e₁ e₂)    = sub (∪ʳ-weaken⊢ Φ₁ e₁) (∪ʳ-weaken⊢ Φ₁ e₂)
∪ʳ-weaken⊢ Φ₁ (mul e₁ e₂)    = mul (∪ʳ-weaken⊢ Φ₁ e₁) (∪ʳ-weaken⊢ Φ₁ e₂)
∪ʳ-weaken⊢ Φ₁ (ifz e₁ e₂ e₃) = ifz (∪ʳ-weaken⊢ Φ₁ e₁) (∪ʳ-weaken⊢ Φ₁ e₂) (∪ʳ-weaken⊢ Φ₁ e₃)
∪ʳ-weaken⊢ Φ₁ (var x)        = var (∪ʳ-weaken∋ Φ₁ x)
∪ʳ-weaken⊢ Φ₁ (lam e)        = lam (∪ʳ-weaken⊢ (↑ Φ₁) e)
∪ʳ-weaken⊢ Φ₁ (app e₁ e₂)    = app (∪ʳ-weaken⊢ Φ₁ e₁) (∪ʳ-weaken⊢ Φ₁ e₂)
∪ʳ-weaken⊢ Φ₁ (lεt e₁ e₂)    = lεt (∪ʳ-weaken⊢ Φ₁ e₁) (∪ʳ-weaken⊢ (↑ Φ₁) e₂)

⁅_⁆-weaken∋ : ∀ {Γ Φ A B} (x : Γ ∋ A) → Γ ∣ Φ ∋ B → Γ ∣ Φ ∪ ⁅ x ⁆ ∋ B
⁅ ze   ⁆-weaken∋ ze = ze
⁅ su x ⁆-weaken∋ ze = ze
⁅_⁆-weaken∋ {Φ = Φ ▻ outside} (ze)   (su y) rewrite ∪-identityʳ Φ = su y
⁅_⁆-weaken∋ {Φ = Φ ▻  inside} (ze)   (su y) rewrite ∪-identityʳ Φ = su y
⁅_⁆-weaken∋ {Φ = Φ ▻ outside} (su x) (su y) = su (⁅ x ⁆-weaken∋ y)
⁅_⁆-weaken∋ {Φ = Φ ▻  inside} (su x) (su y) = su (⁅ x ⁆-weaken∋ y)

⁅_⁆-weaken⊢ : ∀ {Γ Φ A B} (x : Γ ∋ A) → Γ ∣ Φ ⊢ B → Γ ∣ Φ ∪ ⁅ x ⁆ ⊢ B
⁅ x ⁆-weaken⊢ (lit n)        = lit n
⁅ x ⁆-weaken⊢ (add e₁ e₂)    = add (⁅ x ⁆-weaken⊢ e₁) (⁅ x ⁆-weaken⊢ e₂)
⁅ x ⁆-weaken⊢ (sub e₁ e₂)    = sub (⁅ x ⁆-weaken⊢ e₁) (⁅ x ⁆-weaken⊢ e₂)
⁅ x ⁆-weaken⊢ (mul e₁ e₂)    = mul (⁅ x ⁆-weaken⊢ e₁) (⁅ x ⁆-weaken⊢ e₂)
⁅ x ⁆-weaken⊢ (ifz e₁ e₂ e₃) = ifz (⁅ x ⁆-weaken⊢ e₁) (⁅ x ⁆-weaken⊢ e₂) (⁅ x ⁆-weaken⊢ e₃)
⁅ x ⁆-weaken⊢ (var y)        = var (⁅ x ⁆-weaken∋ y)
⁅ x ⁆-weaken⊢ (lam e)        = lam (⁅ su x ⁆-weaken⊢ e)
⁅ x ⁆-weaken⊢ (app e₁ e₂)    = app (⁅ x ⁆-weaken⊢ e₁) (⁅ x ⁆-weaken⊢ e₂)
⁅ x ⁆-weaken⊢ (lεt e₁ e₂)    = lεt (⁅ x ⁆-weaken⊢ e₁) (⁅ su x ⁆-weaken⊢ e₂)

↑↓-weaken⊢ : ∀ {Γ A B Φ} → Γ ▻ A ∣ Φ ⊢ B → Γ ▻ A ∣ ↑ ↓ Φ ⊢ B
↑↓-weaken⊢ {Φ = Φ} e rewrite ↑↓≡∪⁅ze⁆ Φ = ⁅ ze ⁆-weaken⊢ e

strengthen∃ : ∀ {Γ A} → Γ ⊢ A → ∃ λ Φ → Γ ∣ Φ ⊢ A
strengthen∃ (lit n) = ∅ , lit n

strengthen∃ (add e₁ e₂) with strengthen∃ e₁ | strengthen∃ e₂
... | (Φ₁ , e₁′) | (Φ₂ , e₂′) = Φ₁ ∪ Φ₂ , add (∪ˡ-weaken⊢ Φ₂ e₁′) (∪ʳ-weaken⊢ Φ₁ e₂′)

strengthen∃ (sub e₁ e₂) with strengthen∃ e₁ | strengthen∃ e₂
... | (Φ₁ , e₁′) | (Φ₂ , e₂′) = Φ₁ ∪ Φ₂ , sub (∪ˡ-weaken⊢ Φ₂ e₁′) (∪ʳ-weaken⊢ Φ₁ e₂′)

strengthen∃ (mul e₁ e₂) with strengthen∃ e₁ | strengthen∃ e₂
... | (Φ₁ , e₁′) | (Φ₂ , e₂′) = Φ₁ ∪ Φ₂ , mul (∪ˡ-weaken⊢ Φ₂ e₁′) (∪ʳ-weaken⊢ Φ₁ e₂′)

strengthen∃ (ifz e₁ e₂ e₃) with strengthen∃ e₁ | strengthen∃ e₂ | strengthen∃ e₃
... | (Φ₁ , e₁′) | (Φ₂ , e₂′) | (Φ₃ , e₃′) = Φ₁ ∪ Φ₂ ∪ Φ₃ , ifz (∪ˡ-weaken⊢ (Φ₂ ∪ Φ₃) e₁′)
                                                                (∪ʳ-weaken⊢ Φ₁ (∪ˡ-weaken⊢ Φ₃ e₂′))
                                                                (∪ʳ-weaken⊢ Φ₁ (∪ʳ-weaken⊢ Φ₂ e₃′))

strengthen∃ (var x) = ⁅ x ⁆ , var (strengthen∋ x)

strengthen∃ (lam e) with strengthen∃ e
... | (Φ , e′) = ↓ Φ , lam (↑↓-weaken⊢ e′)

strengthen∃ (app e₁ e₂) with strengthen∃ e₁ | strengthen∃ e₂
... | (Φ₁ , e₁′) | (Φ₂ , e₂′) = Φ₁ ∪ Φ₂ , app (∪ˡ-weaken⊢ Φ₂ e₁′) (∪ʳ-weaken⊢ Φ₁ e₂′)

strengthen∃ (lεt e₁ e₂) with strengthen∃ e₁ | strengthen∃ e₂
... | (Φ₁ , e₁′) | (Φ₂ , e₂′) = Φ₁ ∪ ↓ Φ₂ , lεt (∪ˡ-weaken⊢ (↓ Φ₂) e₁′)
                                                (∪ʳ-weaken⊢ (↑ Φ₁) (↑↓-weaken⊢ e₂′))

strengthen⊢ : ∀ {Γ A} (e : Γ ⊢ A) → Γ ∣ FV e ⊢ A
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
