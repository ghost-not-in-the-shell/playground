{-# OPTIONS --type-in-type #-}
open import Category.Base
module Functor.Embedding {𝓒 𝓓} where
open import Prelude
open import Category.Set
open import Category.Solver
open import Functor.Base
open import Isomorphism

Embedding : 𝓒 ⟶ 𝓓 → Set
Embedding 𝓕 = ∀ {A B} → Isomorphism 𝓢𝓮𝓽 $ map₁ 𝓕 {A} {B}

-- ∀ {A B} → Hom 𝓒 A B ≅ Hom 𝓓 (𝓕 ₀(A)) (𝓕 ₀(B)) [ 𝓢𝓮𝓽 ]

module _ (𝓕 : 𝓒 ⟶ 𝓓) where
  Full∧Faithful→Embedding : Full 𝓕 → Faithful 𝓕 → Embedding 𝓕
  Full∧Faithful→Embedding full faithful = record
    { inverse = λ g → fst $ full g
    ; isoˡ = λ⁼ $ λ f → faithful $ snd $ full $ 𝓕 ₁(f)
    ; isoʳ = λ⁼ $ λ f → snd $ full f
    }

  Embedding→Full : Embedding 𝓕 → Full 𝓕
  Embedding→Full map = λ g → ∣ map ⁻¹ ∣ g , (isoʳ map <*> refl)

  Embedding→Faithful : Embedding 𝓕 → Faithful 𝓕
  Embedding→Faithful map {x = f} {g} = λ hyp → begin
    f                     ≡⟨ sym $ isoˡ map <*> refl   ⟩
    ∣ map ⁻¹ ∣ (∣ map ∣ f)  ≡⟨ cong ∣ map ⁻¹ ∣ hyp ⟩
    ∣ map ⁻¹ ∣ (∣ map ∣ g)  ≡⟨ isoˡ map <*> refl ⟩
    g                     ∎

  reflect-≅ : Embedding 𝓕 → ∀ {A B} → 𝓕 ₀(A) ≅ 𝓕 ₀(B) [ 𝓓 ] → A ≅ B [ 𝓒 ]
  reflect-≅ map (-, g) = ∣ map ⁻¹ ∣ ∣ g ∣ , record
    { inverse = ∣ map ⁻¹ ∣ ∣ g ⁻¹ ∣
    ; isoˡ = Embedding→Faithful map $ begin
      ∣ map ∣ (∣ map ⁻¹ ∣ ∣ g ⁻¹ ∣ ∘ ∣ map ⁻¹ ∣ ∣ g ∣)                  ≡⟨ resp-∘ 𝓕 ⟩
      ((∣ map ∣ ∘ ∣ map ⁻¹ ∣) ∣ g ⁻¹ ∣) ∘ ((∣ map ∣ ∘ ∣ map ⁻¹ ∣) ∣ g ∣)  ≡⟨ ⦇ (isoʳ map <*> refl) ∘ (isoʳ map <*> refl) ⦈ ⟩
      ∣ g ⁻¹ ∣ ∘ ∣ g ∣                                              ≡⟨ isoˡ g ⟩
      id                                                          ≡⟨ sym $ resp-id 𝓕 ⟩
      ∣ map ∣ id                                                  ∎
    ; isoʳ = Embedding→Faithful map $ begin
      ∣ map ∣ (∣ map ⁻¹ ∣ ∣ g ∣ ∘ ∣ map ⁻¹ ∣ ∣ g ⁻¹ ∣)                  ≡⟨ resp-∘ 𝓕 ⟩
      ((∣ map ∣ ∘ ∣ map ⁻¹ ∣) ∣ g ∣) ∘ ((∣ map ∣ ∘ ∣ map ⁻¹ ∣) ∣ g ⁻¹ ∣)  ≡⟨ ⦇ (isoʳ map <*> refl) ∘ (isoʳ map <*> refl) ⦈ ⟩
      ∣ g ∣ ∘ ∣ g ⁻¹ ∣                                              ≡⟨ isoʳ g ⟩
      id                                                          ≡⟨ sym $ resp-id 𝓕 ⟩
      ∣ map ∣ id                                                  ∎
    }
