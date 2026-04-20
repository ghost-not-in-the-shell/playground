module Diagram.Product.Properties {𝓒} where
open import Prelude
open import Category.Base
open import Diagram.Product 𝓒
open ApplicativeReasoning

module _ ⦃ _ : BinaryProduct ⦄ where
  open import Functor.Base
  open import Functor.Bifunctor
  open ×

  -×- : 𝓒 × 𝓒 ⟶ 𝓒
  -×- = record
    { map₀ = λ (A , B) → A ×  B
    ; map₁ = λ (f , g) → f ×₁ g
    ; resp-id = begin
      < id ∘ π₁ , id ∘ π₂ > ≡⟨ ⦇ < ∘-idˡ 𝓒 , ∘-idˡ 𝓒 > ⦈ ⟩
      <      π₁ ,      π₂ > ≡⟨ eta ⟩
                id          ∎
    ; resp-∘  = λ { {f = (f₁ , f₂)} {(g₁ , g₂)} → begin
       (g₁ ∘  f₁)     ×₁(g₂ ∘  f₂)       ≡⟨ refl ⟩
      <(g₁ ∘  f₁)∘ π₁ , (g₂ ∘  f₂)∘ π₂ > ≡⟨ ⦇ < ∘-assoc 𝓒 , ∘-assoc 𝓒 > ⦈ ⟩
      < g₁ ∘ (f₁ ∘ π₁),  g₂ ∘ (f₂ ∘ π₂)> ≡⟨ ×<> ⟨
       (g₁ ×₁ g₂)     ∘ (f₁ ×₁ f₂)       ∎ }
    }

  _×- : Ob 𝓒 → 𝓒 ⟶ 𝓒
  A ×- = _₀₍_,-₎ {𝓒} {𝓒} -×- A

  -×_ : Ob 𝓒 → 𝓒 ⟶ 𝓒
  -× B = _₀₍-,_₎ {𝓒} {𝓒} -×- B
