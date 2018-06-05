module Jellyfish.TypeCheck where
open import Jellyfish.Prelude
open import Jellyfish.Core.TypingRules
open import Jellyfish.Core.Syntax.Untyped
open import Jellyfish.Core.Syntax.Typed

mutual
  infer : ∀ Γ (e : Tm (length Γ)) → Maybe (∃ λ A → Γ ⊢ e ⇛ A)
  infer Γ (lit n)        = pure (ℕ , lit n)

  infer Γ (add e₁ e₂)    = check Γ e₁ ℕ >>= λ d₁ →
                           check Γ e₂ ℕ >>= λ d₂ →
                           pure (ℕ , add d₁ d₂)

  infer Γ (sub e₁ e₂)    = check Γ e₁ ℕ >>= λ d₁ →
                           check Γ e₂ ℕ >>= λ d₂ →
                           pure (ℕ , sub d₁ d₂)

  infer Γ (mul e₁ e₂)    = check Γ e₁ ℕ >>= λ d₁ →
                           check Γ e₂ ℕ >>= λ d₂ →
                           pure (ℕ , mul d₁ d₂)

  infer Γ (ifz e₁ e₂ e₃) = check Γ e₁ ℕ >>= λ d₁ →
                          (infer Γ e₂   >>= λ { (A , d₂) →
                           check Γ e₃ A >>= λ d₃ →
                           pure (A , ifz/t  d₁ d₂ d₃) })
                      <|> (infer Γ e₃   >>= λ { (A , d₃) →
                           check Γ e₂ A >>= λ d₂ →
                           pure (A , ifz/f d₁ d₂ d₃) })

  infer Γ (var x)        = pure (lookup Γ x , var x)

  infer Γ (lam e)        = nothing

  infer Γ (app e₁ e₂)    = infer Γ e₁ >>= λ where
                             (A ⇒ B , d₁) → check Γ e₂ A >>= λ d₂ →
                                            pure (B , app d₁ d₂)
                             _            → nothing

  infer Γ (lεt e₁ e₂)    = infer  Γ      e₁ >>= λ { (A , d₁) →
                           infer (Γ ▻ A) e₂ >>= λ { (B , d₂) →
                           pure (B , lεt d₁ d₂) }}

  infer Γ (the A e)      = check Γ e A >>= λ d →
                           pure (A , the A d)

  check : ∀ Γ (e : Tm (length Γ)) A → Maybe (Γ ⊢ e ⇚ A)
  check Γ (lam e) (A ⇒ B) = check (Γ ▻ A) e B >>= λ d →
                            pure (lam d)
  check Γ (lam e) _       = nothing

  check Γ e A             = infer Γ e >>= λ { (⁇ , d) →
                            case ⁇ ≟ A of λ where
                              (yes p) → pure (d ⇛⇚ p)
                              (no ¬p) → nothing }

mutual
  from-infer : ∀ {Γ e A} → Γ ⊢ e ⇛ A → Γ ⊢ A
  from-infer (lit n)          = lit n
  from-infer (add d₁ d₂)      = add (from-check d₁) (from-check d₂)
  from-infer (sub d₁ d₂)      = sub (from-check d₁) (from-check d₂)
  from-infer (mul d₁ d₂)      = mul (from-check d₁) (from-check d₂)
  from-infer (ifz/t d₁ d₂ d₃) = ifz (from-check d₁) (from-infer d₂) (from-check d₃)
  from-infer (ifz/f d₁ d₂ d₃) = ifz (from-check d₁) (from-check d₂) (from-infer d₃)
  from-infer (var x)          = var (Fin→∋ x)
  from-infer (app d₁ d₂)      = app (from-infer d₁) (from-check d₂)
  from-infer (lεt d₁ d₂)      = lεt (from-infer d₁) (from-infer d₂)
  from-infer (the A d)        = from-check d

  from-check : ∀ {Γ e A} → Γ ⊢ e ⇚ A → Γ ⊢ A
  from-check (lam d)            = lam (from-check d)
  from-check (d ⇛⇚ p) rewrite p = from-infer d
