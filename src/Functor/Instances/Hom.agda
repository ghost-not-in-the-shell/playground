module Functor.Instances.Hom where
open import Prelude
open import Category.Base
open import Category.Instances.Functors
open import Functor.Base
open import Functor.Bifunctor.Curry
open import Natural.Base

infix 6 _⦅-,_⦆ _⦅_,-⦆ _⦅-,-⦆

_⦅-,_⦆ : ∀ 𝓒 → Ob 𝓒 → 𝓒 ᵒᵖ ⟶ 𝓢𝓮𝓽
𝓒 ⦅-, X ⦆ = record
  { map₀ = λ A → 𝓒 ⦅ A , X ⦆ , Hom-set 𝓒
  ; map₁ = λ f → _∘ f
  ; resp-id = ext λ _ → ∘-idʳ 𝓒
  ; resp-∘  = ext λ _ → sym (∘-assoc 𝓒)
  }

_⦅_,-⦆ : ∀ 𝓒 → Ob (𝓒 ᵒᵖ) → 𝓒 ⟶ 𝓢𝓮𝓽
𝓒 ⦅ X ,-⦆ = record
  { map₀ = λ A → 𝓒 ⦅ X , A ⦆ , Hom-set 𝓒
  ; map₁ = λ g → g ∘_
  ; resp-id = ext λ _ → ∘-idˡ 𝓒
  ; resp-∘  = ext λ _ → ∘-assoc 𝓒
  }

private
  _ : ∀ {𝓒} {X : Ob (𝓒 ᵒᵖ)} → 𝓒 ⦅ X ,-⦆ ≡ 𝓒 ᵒᵖ ⦅-, X ⦆
  _ = refl

ℎ⁻ : ∀ {𝓒} → 𝓒 ᵒᵖ ⟶ [ 𝓒 , 𝓢𝓮𝓽 ]
ℎ⁻ {𝓒} = record
  { map₀ = 𝓒 ⦅_,-⦆
  ; map₁ = λ f → record
    { component = _∘ f
    ; natural = ext λ _ → ∘-assoc 𝓒
    }
  ; resp-id = ext λ _ → ∘-idʳ 𝓒
  ; resp-∘  = ext λ _ → sym (∘-assoc 𝓒)
  }

ℎ₋ : ∀ {𝓒} → 𝓒 ⟶ [ 𝓒 ᵒᵖ , 𝓢𝓮𝓽 ]
ℎ₋ {𝓒} = record
  { map₀ = 𝓒 ⦅-,_⦆
  ; map₁ = λ g → record
    { component = g ∘_
    ; natural = ext λ _ → sym (∘-assoc 𝓒)
    }
  ; resp-id = ext λ _ → ∘-idˡ 𝓒
  ; resp-∘  = ext λ _ → ∘-assoc 𝓒
  }

private
  _ : ∀ {𝓒} → ℎ⁻ {𝓒} ≡ ℎ₋ {𝓒 ᵒᵖ}
  _ = refl

_⦅-,-⦆ : ∀ 𝓒 → 𝓒 ᵒᵖ ×̅ 𝓒 ⟶ 𝓢𝓮𝓽
𝓒 ⦅-,-⦆ = record
  { map₀ = λ A B → 𝓒 ⦅ A , B ⦆ , Hom-set 𝓒
  ; lmap = λ f → _∘ f
  ; rmap = λ g → g ∘_
  ; lmap-id = ext λ _ → ∘-idʳ 𝓒
  ; rmap-id = ext λ _ → ∘-idˡ 𝓒
  ; lmap-∘  = ext λ _ → sym (∘-assoc 𝓒)
  ; rmap-∘  = ext λ _ → ∘-assoc 𝓒
  ; lrmap   = ext λ _ → ∘-assoc 𝓒
  }

private
  _ : ∀ {𝓒 B} → Left (𝓒 ⦅-,-⦆) B ≡ 𝓒 ⦅-, B ⦆
  _ = refl

  _ : ∀ {𝓒 A} → Right (𝓒 ⦅-,-⦆) A ≡ 𝓒 ⦅ A ,-⦆
  _ = refl

  _ : ∀ {𝓒} → Curry (𝓒 ⦅-,-⦆) ≡ ℎ⁻
  _ = refl

  _ : ∀ {𝓒} → Curry (Flip (𝓒 ⦅-,-⦆)) ≡ ℎ₋
  _ = refl
