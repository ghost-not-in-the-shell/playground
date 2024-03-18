open import Category.Base
module Functor.Yoneda {𝓒 : Category} where
open import Prelude
open import Category.Functor
open import Category.Set
open import Functor.Base
open import Functor.Embedding
open import Functor.Hom
open import Natural.Base

𝓱₋ : 𝓒 ᵒᵖ ⟶ 𝓕𝓾𝓷 𝓒 𝓢𝓮𝓽
𝓱₋ = record
  { map₀ = 𝓱𝓸𝓶₍_,-₎₀
  ; map₁ = 𝓱𝓸𝓶₍_,-₎₁
  ; resp-id = natural⁼ $ ƛ⁼ $ λ⁼ λ _ → ∘-identityʳ 𝓒
  ; resp-∘  = natural⁼ $ ƛ⁼ $ λ⁼ λ _ → sym $ ∘-assoc 𝓒
  }

𝓱⁻ : 𝓒 ⟶ 𝓕𝓾𝓷 (𝓒 ᵒᵖ) 𝓢𝓮𝓽
𝓱⁻ = record
  { map₀ = 𝓱𝓸𝓶₍-,_₎₀
  ; map₁ = 𝓱𝓸𝓶₍-,_₎₁
  ; resp-id = natural⁼ $ ƛ⁼ $ λ⁼ λ _ → ∘-identityˡ 𝓒
  ; resp-∘  = natural⁼ $ ƛ⁼ $ λ⁼ λ _ → ∘-assoc 𝓒
  }
