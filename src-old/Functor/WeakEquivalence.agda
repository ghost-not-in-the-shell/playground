module Functor.WeakEquivalence {𝓒 𝓓} where
open import Prelude hiding (ε)
open import Category.Base
open import Category.Isomorphism
open import Category.Solver
open import Functor.Base
open import Functor.Embedding
open import Natural.Base
open import Natural.Equivalence
open import Natural.Isomorphism

record Equivalence (𝓕 : 𝓒 ⟶ 𝓓) : Set where
  field
    full     : Full     𝓕
    faithful : Faithful 𝓕

    inverse₀    : Ob 𝓓 → Ob 𝓒
    surjective₀ : ∀ A → 𝓕 ₀(inverse₀(A)) ≅ A [ 𝓓 ]

  embed : Embedding 𝓕
  embed = Full∧Faithful→Embedding 𝓕 full faithful

  private
    𝓕₁ : ∀ {A B} → 𝓒 ∣ A ⟶ B → 𝓓 ∣ 𝓕 ₀(A) ⟶ 𝓕 ₀(B)
    𝓕₁ = ∣ embed ∣

    𝓕₁⁻¹ : ∀ {A B} → 𝓓 ∣ 𝓕 ₀(A) ⟶ 𝓕 ₀(B) → 𝓒 ∣ A ⟶ B
    𝓕₁⁻¹ = ∣ embed ⁻¹ ∣

    𝓖₀ : Ob 𝓓 → Ob 𝓒
    𝓖₀ = inverse₀

    counit⋆ : ∀ {A} → Isomorphism 𝓓 _
    counit⋆ {A} = snd $ surjective₀ A

    ε : ∀ {A} → 𝓓 ∣ 𝓕 ₀(𝓖₀(A)) ⟶ A
    ε = ∣ counit⋆ ∣

    ε⁻¹ : ∀ {A} → 𝓓 ∣ A ⟶ 𝓕 ₀(𝓖₀(A))
    ε⁻¹ = ∣ counit⋆ ⁻¹ ∣

    𝓖₁ : ∀ {A B} → 𝓓 ∣ A ⟶ B → 𝓒 ∣ 𝓖₀(A) ⟶ 𝓖₀(B)
    𝓖₁ f = 𝓕₁⁻¹(ε⁻¹ ∘ f ∘ ε)

    𝓖 : 𝓓 ⟶ 𝓒
    𝓖 = record
      { map₀ = 𝓖₀
      ; map₁ = 𝓖₁
      ; resp-id = faithful $ begin
        (𝓕₁ ∘ 𝓕₁⁻¹) (ε⁻¹ ∘ id ∘ ε)  ≡⟨ isoʳ embed <*> refl ⟩
        ε⁻¹ ∘ id ∘ ε                ≡⟨ ⦇ refl ∘ ∘-identityˡ 𝓓 ⦈ ⟩
        ε⁻¹ ∘ ε                     ≡⟨ isoˡ counit⋆ ⟩
        id                          ≡⟨ sym $ resp-id 𝓕 ⟩
        𝓕₁(id)                      ∎
      ; resp-∘ = λ { {f = f} {g} → faithful $ 𝓓 ⊨begin
        `((𝓕₁ ∘ 𝓕₁⁻¹) (ε⁻¹ ∘ (g ∘ f) ∘ ε))                           ≡⟦ isoʳ embed <*> refl ⟧
        ` ε⁻¹ ○ (` g ○ ` f) ○ ` ε                                    ≡[ refl ]
        ` ε⁻¹ ○ ` g ○ `id ○ ` f ○ ` ε                                ≡⟦ sym ⦇ refl ∘ ⦇ refl ∘ ⦇ isoʳ counit⋆ ∘ refl ⦈ ⦈ ⦈ ⟧
        ` ε⁻¹ ○ ` g ○ (` ε ○ ` ε⁻¹) ○ ` f ○ ` ε                      ≡[ refl ]
        (` ε⁻¹ ○ ` g ○ ` ε) ○ (` ε⁻¹ ○ ` f ○ ` ε)                    ≡⟦ sym ⦇ (isoʳ embed <*> refl) ∘ (isoʳ embed <*> refl) ⦈ ⟧
        `((𝓕₁ ∘ 𝓕₁⁻¹) (ε⁻¹ ∘ g ∘ ε)) ○ `((𝓕₁ ∘ 𝓕₁⁻¹) (ε⁻¹ ∘ f ∘ ε))  ≡⟦ sym $ resp-∘ 𝓕 ⟧
        `(𝓕₁ (𝓕₁⁻¹ (ε⁻¹ ∘ g ∘ ε) ∘ 𝓕₁⁻¹ (ε⁻¹ ∘ f ∘ ε)))              ⟦∎⟧ }
      }

    counit : 𝓕 ∘ 𝓖 ⟹ id₍ 𝓓 ₎
    counit = record
      { component = ε
      ; natural = λ { {f = f} → 𝓓 ⊨begin
        `(ε ∘ (𝓕 ∘ 𝓖) ₁ f)              ≡⟦ refl ⟧
        `(ε ∘ 𝓕₁ (𝓕₁⁻¹ (ε⁻¹ ∘ f ∘ ε)))  ≡⟦ ⦇ refl ∘ (isoʳ embed <*> refl) ⦈ ⟧
        ` ε ○ ` ε⁻¹ ○ ` f ○ ` ε         ≡[ refl ]
        (` ε ○ ` ε⁻¹) ○ ` f ○ ` ε       ≡⟦ ⦇ isoʳ counit⋆ ∘ refl ⦈ ⟧
        `id ○ ` f ○ ` ε                 ≡[ refl ]
        ` f ○ ` ε                       ⟦∎⟧ }
      }

    unit : id₍ 𝓒 ₎ ⟹ 𝓖 ∘ 𝓕
    unit = record
      { component = 𝓕₁⁻¹ ε⁻¹
      ; natural = λ { {f = f} → faithful $ 𝓓 ⊨begin
        `(𝓕₁ (𝓕₁⁻¹ ε⁻¹ ∘ f))                           ≡⟦ resp-∘ 𝓕 ⟧
        `(𝓕₁ (𝓕₁⁻¹ ε⁻¹) ∘ 𝓕₁(f))                       ≡⟦ ⦇ (isoʳ embed <*> refl) ∘ refl ⦈ ⟧
        `(ε⁻¹ ∘ 𝓕₁(f))                                 ≡[ refl ]
        `(ε⁻¹ ∘ 𝓕₁(f)) ○ `id                           ≡⟦ sym ⦇ refl ∘ isoʳ counit⋆ ⦈  ⟧
        (` ε⁻¹ ○ `(𝓕₁ f)) ○ (` ε ○ ` ε⁻¹)              ≡[ refl ]
        (` ε⁻¹ ○ `(𝓕₁ f) ○ ` ε) ○ ` ε⁻¹                ≡⟦ sym ⦇ (isoʳ embed <*> refl) ∘ (isoʳ embed <*> refl) ⦈ ⟧
        `(𝓕₁ (𝓕₁⁻¹ (ε⁻¹ ∘ 𝓕₁ f ∘ ε)) ∘ 𝓕₁ (𝓕₁⁻¹ ε⁻¹))  ≡⟦ sym $ resp-∘ 𝓕 ⟧
        `(𝓕₁ (𝓕₁⁻¹ (ε⁻¹ ∘ 𝓕₁ f ∘ ε) ∘ 𝓕₁⁻¹ ε⁻¹))       ⟦∎⟧ }
      }

    unit⋆ : ∀ {A} → Isomorphism 𝓒 (unit ₍ A ₎)
    unit⋆ {A} = record
      { inverse = 𝓕₁⁻¹ ε
      ; isoˡ = faithful $ begin
        𝓕₁ (𝓕₁⁻¹ ε ∘ 𝓕₁⁻¹ ε⁻¹)       ≡⟨ resp-∘ 𝓕 ⟩
        𝓕₁ (𝓕₁⁻¹ ε) ∘ 𝓕₁ (𝓕₁⁻¹ ε⁻¹)  ≡⟨ ⦇ (isoʳ embed <*> refl) ∘ (isoʳ embed <*> refl) ⦈ ⟩
        ε ∘ ε⁻¹                      ≡⟨ isoʳ counit⋆ ⟩
        id                           ≡⟨ sym $ resp-id 𝓕 ⟩
        𝓕₁ id                        ∎
      ; isoʳ = faithful $ begin
        𝓕₁ (𝓕₁⁻¹ ε⁻¹ ∘ 𝓕₁⁻¹ ε)       ≡⟨ resp-∘ 𝓕 ⟩
        𝓕₁ (𝓕₁⁻¹ ε⁻¹) ∘ 𝓕₁ (𝓕₁⁻¹ ε)  ≡⟨ ⦇ (isoʳ embed <*> refl) ∘ (isoʳ embed <*> refl) ⦈ ⟩
        ε⁻¹ ∘ ε                      ≡⟨ isoˡ counit⋆ ⟩
        id                           ≡⟨ sym $ resp-id 𝓕 ⟩
        𝓕₁ id                        ∎
      }

  natural-equivalence : 𝓒 ≃ 𝓓
  natural-equivalence = record
    { to   = 𝓕
    ; from = 𝓖
    ; counit = counit , from-component≅ counit⋆
    ; unit   = unit   , from-component≅ unit⋆
    }
