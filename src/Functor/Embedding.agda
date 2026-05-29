module Functor.Embedding {𝓒 𝓓} where
open import Prelude
open import Category.Base
open import Functor.Base

is-full : 𝓒 ⟶ 𝓓 → Type
is-full 𝐹 = ∀ {A B} → is-surj (_₁_ 𝐹 {A} {B})

is-faithful : 𝓒 ⟶ 𝓓 → Type
is-faithful 𝐹 = ∀ {A B} → is-inj (_₁_ 𝐹 {A} {B})

is-embedding : 𝓒 ⟶ 𝓓 → Type
is-embedding 𝐹 = ∀ {A B} → is-iso Function (_₁_ 𝐹 {A} {B})

module _ (𝐹 : 𝓒 ⟶ 𝓓) where
  private
    𝐹₁ : ∀ {A B} → 𝓒 ⦅ A , B ⦆ → 𝓓 ⦅ 𝐹 ₀(A) , 𝐹 ₀(B) ⦆
    𝐹₁ = 𝐹 ₁_

  reflect-≅ : ⦃ _ : is-embedding 𝐹 ⦄
    → ∀ {A B}
    → 𝓓 ⦅ 𝐹 ₀(A) ≅ 𝐹 ₀(B) ⦆
    → 𝓒 ⦅     A  ≅     B  ⦆
  reflect-≅ (fwd g) = record
    { fwd = 𝐹₁⁻¹(g)
    ; iso = record
      { bwd = 𝐹₁⁻¹(g ⁻¹)
      ; ∘-invˡ = iso→inj (𝐹 ₁_) $ begin
          𝐹₁(𝐹₁⁻¹(g ⁻¹) ∘    𝐹₁⁻¹(g)) ≡⟨ resp-∘ 𝐹 ⟩
          𝐹₁(𝐹₁⁻¹(g ⁻¹))∘ 𝐹₁(𝐹₁⁻¹(g)) ≡⟨ invʳ 𝐹₁ ○ invʳ 𝐹₁ ⟩
                  g ⁻¹  ∘         g   ≡⟨ ∘-invˡ g ⟩
                        id            ≡⟨ resp-id 𝐹 ⟨
                     𝐹₁(id)           ∎
      ; ∘-invʳ = iso→inj (𝐹 ₁_) $ begin
          𝐹₁(𝐹₁⁻¹(g) ∘    𝐹₁⁻¹(g ⁻¹)) ≡⟨ resp-∘ 𝐹 ⟩
          𝐹₁(𝐹₁⁻¹(g))∘ 𝐹₁(𝐹₁⁻¹(g ⁻¹)) ≡⟨ invʳ 𝐹₁ ○ invʳ 𝐹₁ ⟩
                  g  ∘         g ⁻¹   ≡⟨ ∘-invʳ g ⟩
                     id               ≡⟨ resp-id 𝐹 ⟨
                  𝐹₁(id)              ∎
      }
    } where 𝐹₁⁻¹ : ∀ {A B} → 𝓓 ⦅ 𝐹 ₀(A) , 𝐹 ₀(B) ⦆ → 𝓒 ⦅ A , B ⦆
            𝐹₁⁻¹ = 𝐹₁ ⁻¹
