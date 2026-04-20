module Functor.Bifunctor {𝓒 𝓓 𝓔} where
open import Prelude
open import Category.Base
open import Functor.Base
open import Natural.Base
open ApplicativeReasoning

_₀₍_,-₎ : (𝐹 : 𝓒 × 𝓓 ⟶ 𝓔) (A : Ob 𝓒) → 𝓓 ⟶ 𝓔
𝐹 ₀₍ A ,-₎ = record
  { map₀ = λ S → 𝐹 ₀(A  , S)
  ; map₁ = λ p → 𝐹 ₁(id , p)
  ; resp-id = resp-id 𝐹
  ; resp-∘ = λ { {f = p} {q} → begin
    𝐹 ₁(id      , q ∘ p)      ≡⟨ ⦇ (𝐹 ₁_) ⦇ ∘-idʳ 𝓒 , - ⦈ ⦈ ⟨
    𝐹 ₁(id ∘ id , q ∘ p)      ≡⟨ resp-∘ 𝐹 ⟩
    𝐹 ₁(id , q) ∘ 𝐹 ₁(id , p) ∎ }
  }

_₀₍-,_₎ : (𝐹 : 𝓒 × 𝓓 ⟶ 𝓔) (S : Ob 𝓓) → 𝓒 ⟶ 𝓔
𝐹 ₀₍-, S ₎ = record
  { map₀ = λ A → 𝐹 ₀(A ,  S)
  ; map₁ = λ f → 𝐹 ₁(f , id)
  ; resp-id = resp-id 𝐹
  ; resp-∘ = λ { {f = f} {g} → begin
    𝐹 ₁(g ∘ f ,      id)      ≡⟨ ⦇ (𝐹 ₁_) ⦇ - , ∘-idˡ 𝓓 ⦈ ⦈ ⟨
    𝐹 ₁(g ∘ f , id ∘ id)      ≡⟨ resp-∘ 𝐹 ⟩
    𝐹 ₁(g , id) ∘ 𝐹 ₁(f , id) ∎ }
  }

_₁₍_,-₎ : (𝐹 : 𝓒 × 𝓓 ⟶ 𝓔) {A B : Ob 𝓒} (f : 𝓒 ⦅ A , B ⦆) → 𝐹 ₀₍ A ,-₎ ⟹ 𝐹 ₀₍ B ,-₎
𝐹 ₁₍ f ,-₎ = record
  { component = λ {S} → 𝐹 ₁(f , id)
  ; natural = λ { {f = g} → begin
    𝐹 ₁(f , id) ∘ 𝐹 ₁(id , g) ≡⟨ resp-∘ 𝐹 ⟨
    𝐹 ₁(f ∘ id , id ∘ g)      ≡⟨ ⦇ (𝐹 ₁_) ⦇ sym (∘-idˡʳ 𝓒) , ∘-idˡʳ 𝓓 ⦈ ⦈ ⟩
    𝐹 ₁(id ∘ f , g ∘ id)      ≡⟨ resp-∘ 𝐹 ⟩
    𝐹 ₁(id , g) ∘ 𝐹 ₁(f , id) ∎ }
  }

_₁₍-,_₎ : (𝐹 : 𝓒 × 𝓓 ⟶ 𝓔) {S T : Ob 𝓓} (g : 𝓓 ⦅ S , T ⦆) → 𝐹 ₀₍-, S ₎ ⟹ 𝐹 ₀₍-, T ₎
𝐹 ₁₍-, g ₎ = record
  { component = λ {A} → 𝐹 ₁(id , g)
  ; natural = λ { {f = f} → begin
    𝐹 ₁(id , g) ∘ 𝐹 ₁(f , id) ≡⟨ resp-∘ 𝐹 ⟨
    𝐹 ₁(id ∘ f , g ∘ id)      ≡⟨ ⦇ (𝐹 ₁_) ⦇ ∘-idˡʳ 𝓒 , sym (∘-idˡʳ 𝓓) ⦈ ⦈ ⟩
    𝐹 ₁(f ∘ id , id ∘ g)      ≡⟨ resp-∘ 𝐹 ⟩
    𝐹 ₁(f , id) ∘ 𝐹 ₁(id , g) ∎ }
  }
