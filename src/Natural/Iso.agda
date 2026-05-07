module Natural.Iso where
open import Prelude
open import Category.Assoc
open import Category.Base
open import Category.Instances.Functors
open import Functor.Base
open import Natural.Base

module _ {𝓒 𝓓} {𝐹 𝐺 : 𝓒 ⟶ 𝓓} (α : 𝐹 ⟹ 𝐺) where
  to-component : ⦃ _ : is-iso (Hom [ 𝓒 , 𝓓 ]) α ⦄ {A : Ob 𝓒} → is-iso (Hom 𝓓) (α ₍ A ₎)
  to-component {A} = record
    { bwd = α ⁻¹ ₍ A ₎
    ; ∘-invˡ = cong _₍ A ₎ $ ∘-invˡ α
    ; ∘-invʳ = cong _₍ A ₎ $ ∘-invʳ α
    }

  from-component : ⦃ _ : {A : Ob 𝓒} → is-iso (Hom 𝓓) (α ₍ A ₎) ⦄ → is-iso (Hom [ 𝓒 , 𝓓 ]) α
  from-component = record
    { bwd = record
      { component = λ A → (α ₍ A ₎)⁻¹
      ; natural = λ {A} {B} {f} →
        let α₋ : ∀ {A} → 𝓓 ⦅ 𝐹 ₀(A) , 𝐺 ₀(A) ⦆
            α₋ = α ₋
            α₋⁻¹ : ∀ {A} → 𝓓 ⦅ 𝐺 ₀(A) , 𝐹 ₀(A) ⦆
            α₋⁻¹ = (α ₋)⁻¹
        in begin
          α₋⁻¹ ∘ 𝐺 ₁(f)              ≡⟨ ∘-idʳ 𝓓 ⟨
         (α₋⁻¹ ∘ 𝐺 ₁(f))∘    id      ≡⟨ - ○ ∘-invʳ α₋ ⟨
         (α₋⁻¹ ∘ 𝐺 ₁(f))∘ α₋ ∘ α₋⁻¹  ≡⟨ ∘-assoc! 𝓓 ⟩
          α₋⁻¹ ∘(𝐺 ₁(f) ∘ α₋)∘ α₋⁻¹  ≡⟨ - ○ natural α ○ - ⟨
          α₋⁻¹ ∘(α₋ ∘ 𝐹 ₁(f))∘ α₋⁻¹  ≡⟨ ∘-assoc! 𝓓 ⟩
         (α₋⁻¹ ∘ α₋)∘ 𝐹 ₁(f) ∘ α₋⁻¹  ≡⟨ ∘-invˡ α₋ ○ - ⟩
               id   ∘ 𝐹 ₁(f) ∘ α₋⁻¹  ≡⟨ ∘-idˡ 𝓓 ⟩
                      𝐹 ₁(f) ∘ α₋⁻¹  ∎
      }
    ; ∘-invˡ = ext λ {A} → ∘-invˡ (α ₍ A ₎)
    ; ∘-invʳ = ext λ {A} → ∘-invʳ (α ₍ A ₎)
    }
