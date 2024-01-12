module Category.Category where
open import Prelude
open import Category.Base

private
  identity : ∀ {𝓒} → 𝓒 ⟶ 𝓒
  identity = record
    { map₀ = id
    ; map₁ = id
    ; resp-id = refl
    ; resp-∘  = refl
    }

  composition : ∀ {𝓒 𝓓 𝓔} → 𝓓 ⟶ 𝓔 → 𝓒 ⟶ 𝓓 → 𝓒 ⟶ 𝓔
  composition 𝓖 𝓕 = record
    { map₀ = 𝓖 ₀_ ∘ 𝓕 ₀_
    ; map₁ = 𝓖 ₁_ ∘ 𝓕 ₁_
    ; resp-id = trans (cong (𝓖 ₁_) (resp-id 𝓕)) (resp-id 𝓖)
    ; resp-∘  = trans (cong (𝓖 ₁_) (resp-∘  𝓕)) (resp-∘  𝓖)
    }

instance
  𝓒𝓪𝓽-op : Op Functor
  𝓒𝓪𝓽-op = record
    { id  = identity
    ; _∘_ = composition
    }

𝓒𝓪𝓽 : Category
𝓒𝓪𝓽 = record
  { ob = Category
  ; hom = Functor
  ; op = 𝓒𝓪𝓽-op
  ; ∘-identityˡ = functor⁼ (refl , refl)
  ; ∘-identityʳ = functor⁼ (refl , refl)
  ; ∘-assoc = functor⁼ (refl , refl)
  }
