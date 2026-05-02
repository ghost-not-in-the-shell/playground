module Diagram.Product.Properties {𝓒} where
open import Prelude
open import Category.Base
open import Diagram.Product 𝓒
open ApplicativeReasoning

module _ ⦃ _ : BinaryProduct ⦄ where
  open import Adjoint.UnitCounit
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

{-
  Δ⊣× : Δ {𝓒} ⊣ -×-
  Δ⊣× = record
    { unit = record
      { component = < id , id >
      ; natural = λ { {f = f} → begin
          < id , id > ∘ f ≡⟨ <>∘ ⟩
          < id ∘ f , id ∘ f > ≡⟨ ⦇ < ∘-idˡʳ 𝓒 , ∘-idˡʳ 𝓒 > ⦈ ⟩
          < f ∘ id , f ∘ id > ≡⟨ ×<> ⟨
          f ×₁ f ∘ < id , id > ∎ }
      }
    ; counit = record
      { component = π₁ , π₂
      ; natural = cong₂ _,_ commute₁ commute₂
      }
    ; zig = cong₂ _,_ commute₁ commute₂
    ; zag = begin
        π₁ ×₁ π₂ ∘ < id , id > ≡⟨ ×<> ⟩
      < π₁ ∘ id , π₂ ∘ id > ≡⟨ {!!} ⟩
      < π₁      , π₂      > ≡⟨ {!!} ⟩
        id ∎
    }
-}
