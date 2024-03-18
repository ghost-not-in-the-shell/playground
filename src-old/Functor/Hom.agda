open import Category.Base
module Functor.Hom {𝓒 : Category} where
open import Prelude
open import Category.Set
open import Category.Solver
open import Functor.Base
open import Natural.Base

𝓱𝓸𝓶₍_,-₎₀ : Ob (𝓒 ᵒᵖ) → 𝓒 ⟶ 𝓢𝓮𝓽
𝓱𝓸𝓶₍ X ,-₎₀ = record
  { map₀ = λ - → Hom 𝓒 X -
  ; map₁ = λ g → g ∘_
  ; resp-id = λ⁼ λ _ → ∘-identityˡ 𝓒
  ; resp-∘  = λ⁼ λ _ → ∘-assoc 𝓒
  }

𝓱𝓸𝓶₍_,-₎₁ : ∀ {X Y} → 𝓒 ᵒᵖ ∣ X ⟶ Y → 𝓱𝓸𝓶₍ X ,-₎₀ ⟹ 𝓱𝓸𝓶₍ Y ,-₎₀
𝓱𝓸𝓶₍ f ,-₎₁ = record
  { component = _∘ f
  ; natural = λ⁼ λ _ → ∘-assoc 𝓒
  }

𝓱𝓸𝓶₍-,_₎₀ : Ob 𝓒 → 𝓒 ᵒᵖ ⟶ 𝓢𝓮𝓽
𝓱𝓸𝓶₍-, X ₎₀ = record
  { map₀ = λ - → Hom 𝓒 - X
  ; map₁ = λ f → _∘ f
  ; resp-id = λ⁼ λ _ → ∘-identityʳ 𝓒
  ; resp-∘  = λ⁼ λ _ → sym $ ∘-assoc 𝓒
  }

𝓱𝓸𝓶₍-,_₎₁ : ∀ {X Y} → 𝓒 ∣ X ⟶ Y → 𝓱𝓸𝓶₍-, X ₎₀ ⟹ 𝓱𝓸𝓶₍-, Y ₎₀
𝓱𝓸𝓶₍-, g ₎₁ = record
  { component = g ∘_
  ; natural = λ⁼ λ _ → sym $ ∘-assoc 𝓒
  }

𝓱𝓸𝓶 : 𝓒 ᵒᵖ × 𝓒 ⟶ 𝓢𝓮𝓽
𝓱𝓸𝓶 = record
  { map₀ = λ (A , B) → Hom 𝓒 A B
  ; map₁ = λ (f , g) → λ - → g ∘ - ∘ f
  ; resp-id = λ⁼ λ _ → trans (∘-identityˡ 𝓒) (∘-identityʳ 𝓒)
  ; resp-∘  = λ { {f = f₁ , g₁} {f₂ , g₂} → λ⁼ λ - → 𝓒 ⊨begin
    (` g₂ ○ ` g₁) ○ ` - ○ (` f₁ ○ ` f₂)  ≡[ refl ]
    ` g₂ ○ (` g₁ ○ ` - ○ ` f₁) ○ ` f₂    ⟦∎⟧ }
  }
