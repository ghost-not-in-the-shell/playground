module Functor.Hom {𝓒} where
open import Prelude
open import Category.Base
open import Functor.Base
open import Functor.Bifunctor

𝐻𝑜𝑚₍-,_₎ : Ob 𝓒 → 𝓒 ᵒᵖ ⟶ 𝓢𝓮𝓽
𝐻𝑜𝑚₍-, X ₎ = record
  { map₀ = λ A → HomSet 𝓒 A X
  ; map₁ = λ f → _∘ f
  ; resp-id = ext λ _ → ∘-idʳ 𝓒
  ; resp-∘  = ext λ _ → sym (∘-assoc 𝓒)
  }

𝐻𝑜𝑚₍_,-₎ : Ob (𝓒 ᵒᵖ) → 𝓒 ⟶ 𝓢𝓮𝓽
𝐻𝑜𝑚₍ X ,-₎ = record
  { map₀ = λ A → HomSet 𝓒 X A
  ; map₁ = λ g → g ∘_
  ; resp-id = ext λ _ → ∘-idˡ 𝓒
  ; resp-∘  = ext λ _ → ∘-assoc 𝓒
  }

𝐻𝑜𝑚 : Bifunctor (𝓒 ᵒᵖ) 𝓒 𝓢𝓮𝓽
𝐻𝑜𝑚 = record
  { map₀ = HomSet 𝓒
  ; lmap = λ f → _∘ f
  ; rmap = λ g → g ∘_
  ; lmap-id = ext λ _ → ∘-idʳ 𝓒
  ; rmap-id = ext λ _ → ∘-idˡ 𝓒
  ; lmap-∘  = ext λ _ → sym (∘-assoc 𝓒)
  ; rmap-∘  = ext λ _ → ∘-assoc 𝓒
  ; lrmap   = ext λ _ → ∘-assoc 𝓒
  }

𝐻𝑜𝑚₍-,-₎ : 𝓒 ᵒᵖ × 𝓒 ⟶ 𝓢𝓮𝓽
𝐻𝑜𝑚₍-,-₎ = from-bifunctor 𝐻𝑜𝑚
