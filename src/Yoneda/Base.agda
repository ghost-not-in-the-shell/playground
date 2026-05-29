module Yoneda.Base where
open import Prelude
open import Category.Base
open import Functor.Base
open import Functor.Instances.Hom
open import Natural.Base

module Covariant (𝓒 : Category) {𝐹 : 𝓒 ⟶ 𝓢𝓮𝓽} {A} where
  module _ {𝐹 : 𝓒 ⟶ 𝓢𝓮𝓽} {A : Ob 𝓒} where
  _↑ : ⌞ 𝐹 ₀(A) ⌟ → 𝓒 ⦅ A ,-⦆ ⟹ 𝐹
  _↑ u = record
    { component = λ f → 𝐹 ₁(f) $ u
    ; natural = λ {B C g} → ext λ f → cong (_$ u) (resp-∘ 𝐹)
--  ; natural = λ {B C g} → ext λ f → begin
--     (𝐹 ₁(g ∘     f) $ u) ≡⟨ cong (_$ u) (resp-∘ 𝐹) ⟩
--     (𝐹 ₁(g)∘ 𝐹 ₁(f) $ u) ∎
    }

  _↓ : 𝓒 ⦅ A ,-⦆ ⟹ 𝐹 → ⌞ 𝐹 ₀(A) ⌟
  _↓ α = α ₍ A ₎ $ id

  instance
    ↑-iso : is-iso Function _↑
    ↑-iso = record
      { bwd = _↓
      ; ∘-invˡ = ext λ u → begin
         (𝐹 ₁(id) $ u) ≡⟨ cong (_$ u) (resp-id 𝐹) ⟩
                    u  ∎
      ; ∘-invʳ = ext λ α f → begin
         (𝐹 ₁(f)$ α ₋ $ id₍ A ₎) ≡⟨ refl ⟩
         (𝐹 ₁(f)∘ α ₋ $ id₍ A ₎) ≡⟨ cong (_$ id) (natural α) ⟨
         (α ₋ ∘(f ∘_) $ id₍ A ₎) ≡⟨ refl ⟩
         (α ₋ $(f ∘_) $ id₍ A ₎) ≡⟨ refl ⟩
         (α ₋ $ f ∘     id₍ A ₎) ≡⟨ cong (α ₋ $_) (∘-idʳ 𝓒) ⟩
         (α ₋ $ f)               ∎
      }

module Contravariant (𝓒 : Category) = Covariant (𝓒 ᵒᵖ)
