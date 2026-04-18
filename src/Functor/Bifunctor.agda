module Functor.Bifunctor {𝓒₁ 𝓒₂ 𝓓} where
open import Prelude
open import Category.Base
open import Functor.Base

_₍_,-₎ : (𝐹 : 𝓒₁ × 𝓒₂ ⟶ 𝓓) (X : Ob 𝓒₁) → 𝓒₂ ⟶ 𝓓
𝐹 ₍ X ,-₎ = record
  { map₀ = λ A → 𝐹 ₀(X  , A)
  ; map₁ = λ f → 𝐹 ₁(id , f)
  ; resp-id = resp-id 𝐹
  ; resp-∘ = λ { {f = f} {g} → begin
    𝐹 ₁(id      , g ∘ f)      ≡⟨ cong (λ - → 𝐹 ₁(- , g ∘ f)) (∘-idʳ 𝓒₁) ⟨
    𝐹 ₁(id ∘ id , g ∘ f)      ≡⟨ resp-∘ 𝐹 ⟩
    𝐹 ₁(id , g) ∘ 𝐹 ₁(id , f) ∎ }
  }

_₍-,_₎ : (𝐹 : 𝓒₁ × 𝓒₂ ⟶ 𝓓) (X : Ob 𝓒₂) → 𝓒₁ ⟶ 𝓓
𝐹 ₍-, X ₎ = record
  { map₀ = λ A → 𝐹 ₀(A ,  X)
  ; map₁ = λ f → 𝐹 ₁(f , id)
  ; resp-id = resp-id 𝐹
  ; resp-∘ = λ { {f = f} {g} → begin
    𝐹 ₁(g ∘ f ,      id)      ≡⟨ cong (λ - → 𝐹 ₁(g ∘ f , -)) (∘-idˡ 𝓒₂) ⟨
    𝐹 ₁(g ∘ f , id ∘ id)      ≡⟨ resp-∘ 𝐹 ⟩
    𝐹 ₁(g , id) ∘ 𝐹 ₁(f , id) ∎ }
  }
