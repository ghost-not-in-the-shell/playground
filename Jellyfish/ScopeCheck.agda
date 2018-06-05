module Jellyfish.ScopeCheck where
open import Jellyfish.Prelude
open import Jellyfish.Core.Syntax.Raw     renaming (Tm to Tm𝓢)
open import Jellyfish.Core.Syntax.Untyped renaming (Tm to Tm𝓣)

deBruijn-ize : ∀ (Γ : List String) → Tm𝓢 → Maybe (Tm𝓣 (length Γ))
deBruijn-ize Γ (lit n)        = pure (lit n)

deBruijn-ize Γ (add e₁ e₂)    = deBruijn-ize Γ e₁ >>= λ e₁′ →
                                deBruijn-ize Γ e₂ >>= λ e₂′ →
                                pure (add e₁′ e₂′)

deBruijn-ize Γ (sub e₁ e₂)    = deBruijn-ize Γ e₁ >>= λ e₁′ →
                                deBruijn-ize Γ e₂ >>= λ e₂′ →
                                pure (sub e₁′ e₂′)

deBruijn-ize Γ (mul e₁ e₂)    = deBruijn-ize Γ e₁ >>= λ e₁′ →
                                deBruijn-ize Γ e₂ >>= λ e₂′ →
                                pure (mul e₁′ e₂′)

deBruijn-ize Γ (ifz e₁ e₂ e₃) = deBruijn-ize Γ e₁ >>= λ e₁′ →
                                deBruijn-ize Γ e₂ >>= λ e₂′ →
                                deBruijn-ize Γ e₃ >>= λ e₃′ →
                                pure (ifz e₁′ e₂′ e₃′)

deBruijn-ize Γ (var x)        = index x Γ >>= λ x′ →
                                pure (var x′)

deBruijn-ize Γ (lam x e)      = deBruijn-ize (Γ ▻ x) e >>= λ e′ →
                                pure (lam e′)

deBruijn-ize Γ (app e₁ e₂)    = deBruijn-ize Γ e₁ >>= λ e₁′ →
                                deBruijn-ize Γ e₂ >>= λ e₂′ →
                                pure (app e₁′ e₂′)

deBruijn-ize Γ (lεt x e₁ e₂)  = deBruijn-ize  Γ      e₁ >>= λ e₁′ →
                                deBruijn-ize (Γ ▻ x) e₂ >>= λ e₂′ →
                                pure (lεt e₁′ e₂′)

deBruijn-ize Γ (the A e)      = deBruijn-ize Γ e >>= λ e′ →
                                pure (the A e′)
