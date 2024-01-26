{-# OPTIONS --type-in-type #-}
open import Category.Base
module Functor.Equivalence {𝓒 𝓓} where
open import Prelude
open import Category.Set
open import Category.Solver
open import Functor.Base
open import Functor.Embedding
open import Isomorphism
open import NaturalTransformation.Base
open import NaturalTransformation.Equivalence

record Equivalence (𝓕 : 𝓒 ⟶ 𝓓) : Set where
  field
    full : Full 𝓕
    faithful : Faithful 𝓕

    inverse₀ : Ob 𝓓 → Ob 𝓒
    surjective₀ : ∀ A → 𝓕 ₀(inverse₀ A) ≅ A [ 𝓓 ]

  surj : ∀ {A} → Isomorphism 𝓓 (fst (surjective₀ A))
  surj {A} = snd $ surjective₀ A

  embed : ∀ {A B} → Isomorphism 𝓢𝓮𝓽 $ map₁ 𝓕 {A} {B}
  embed = Full∧Faithful→Embedding 𝓕 full faithful

  private
    to : ∀ {A} → 𝓓 ∣ 𝓕 ₀(inverse₀ A) ⟶ A
    to = ∣ surj ∣

    from : ∀ {A} → 𝓓 ∣ A ⟶ 𝓕 ₀(inverse₀ A)
    from = surj ⁻¹

    𝓕₁ : ∀ {A B} → 𝓒 ∣ A ⟶ B → 𝓓 ∣ 𝓕 ₀(A) ⟶ 𝓕 ₀(B)
    𝓕₁ = ∣ embed ∣

    𝓕₁⁻¹ : ∀ {A B} → 𝓓 ∣ 𝓕 ₀(A) ⟶ 𝓕 ₀(B) → 𝓒 ∣ A ⟶ B
    𝓕₁⁻¹ = embed ⁻¹

  inverse₁ : ∀ {A B} → 𝓓 ∣ A ⟶ B → 𝓒 ∣ inverse₀ A ⟶ inverse₀ B
  inverse₁ {A} {B} f = 𝓕₁⁻¹ (from ∘ f ∘ to)

  inverse : 𝓓 ⟶ 𝓒
  inverse = record
    { map₀ = inverse₀
    ; map₁ = inverse₁
    ; resp-id = faithful $ begin
      (𝓕₁ ∘ 𝓕₁⁻¹) (from ∘ id ∘ to)  ≡⟨ isoʳ embed <*> refl ⟩
      from ∘ id ∘ to                ≡⟨ ⦇ refl ∘ ∘-identityˡ 𝓓 ⦈ ⟩
      from ∘ to                     ≡⟨ isoˡ surj ⟩
      id                            ≡⟨ sym $ resp-id 𝓕 ⟩
      𝓕₁ id                         ∎
    ; resp-∘  = λ { {f = f} {g} → faithful $ 𝓓 ⊨begin
      `((𝓕₁ ∘ 𝓕₁⁻¹) (from ∘ (g ∘ f) ∘ to))                            ≡⟦ isoʳ embed <*> refl ⟧
      ` from ○ (` g ○ ` f) ○ ` to                                      ≡[ refl ]
      ` from ○ ` g ○ `id ○ ` f ○ ` to                                  ≡⟦ sym ⦇ refl ∘ ⦇ refl ∘ ⦇ isoʳ surj ∘ refl ⦈ ⦈ ⦈ ⟧
      ` from ○ ` g ○ (` to ○ ` from) ○ ` f ○ ` to                      ≡[ refl ]
      (` from ○ ` g ○ ` to) ○ (` from ○ ` f ○ ` to)                    ≡⟦ sym ⦇ (isoʳ embed <*> refl) ∘ (isoʳ embed <*> refl) ⦈  ⟧
      `((𝓕₁ ∘ 𝓕₁⁻¹) (from ∘ g ∘ to)) ○ `((𝓕₁ ∘ 𝓕₁⁻¹) (from ∘ f ∘ to))  ≡⟦ sym $ resp-∘ 𝓕 ⟧
      `(𝓕₁ (𝓕₁⁻¹ (from ∘ g ∘ to) ∘ 𝓕₁⁻¹ (from ∘ f ∘ to)))              ⟦∎⟧
      }
    }

  private
    𝓖 = inverse

  counit : 𝓕 ∘ 𝓖 ⟹ id₍ 𝓓 ₎
  counit = record
    { component = to
    ; natural = λ { {f = f} → 𝓓 ⊨begin
      `(to ∘ (𝓕 ∘ 𝓖) ₁ f)                ≡⟦ refl ⟧
      `(to ∘ 𝓕₁ (𝓕₁⁻¹ (from ∘ f ∘ to)))  ≡⟦ ⦇ refl ∘ (isoʳ embed <*> refl) ⦈ ⟧
      ` to ○ ` from ○ ` f ○ ` to         ≡[ refl ]
      (` to ○ ` from) ○ ` f ○ ` to       ≡⟦ ⦇ isoʳ surj ∘ refl ⦈ ⟧
      `id ○ ` f ○ ` to                   ≡[ refl ]
      ` f ○ ` to                         ⟦∎⟧ }
    }

  counit← : id₍ 𝓓 ₎ ⟹ 𝓕 ∘ 𝓖
  counit← = record
    { component = from
    ; natural = λ { {f = f} → 𝓓 ⊨begin
      ` from ○ ` f                         ≡[ refl ]
      ` from ○ ` f ○ `id                   ≡⟦ sym ⦇ refl ∘ ⦇ refl ∘ isoʳ surj ⦈ ⦈ ⟧
      ` from ○ ` f ○ (` to ○ ` from)       ≡[ refl ]
      (` from ○ ` f ○ ` to) ○ ` from       ≡⟦ sym ⦇ (isoʳ embed <*> refl) ∘ refl ⦈ ⟧
      `(𝓕₁ (𝓕₁⁻¹ (from ∘ f ∘ to)) ∘ from)  ≡[ refl ]
      `((𝓕 ∘ 𝓖) ₁ f ∘ from)                ⟦∎⟧ }
    }

  unit : id₍ 𝓒 ₎ ⟹ 𝓖 ∘ 𝓕
  unit = record
    { component = 𝓕₁⁻¹ from
    ; natural = λ { {f = f} → faithful $ 𝓓 ⊨begin
      `(𝓕₁ (𝓕₁⁻¹ from ∘ f))                                ≡⟦ resp-∘ 𝓕 ⟧
      `(𝓕₁ (𝓕₁⁻¹ from) ∘ 𝓕₁ f)                             ≡⟦ ⦇ (isoʳ embed <*> refl) ∘ refl ⦈ ⟧
      `(from ∘ 𝓕₁ f)                                       ≡[ refl ]
      `(from ∘ 𝓕₁ f) ○ `id                                 ≡⟦ sym ⦇ refl ∘ isoʳ surj ⦈ ⟧
      (` from ○ `map 𝓕 (` f)) ○ (` to ○ ` from)            ≡[ refl ]
      (` from ○ `map 𝓕 (` f) ○ ` to) ○ ` from              ≡⟦ sym ⦇ (isoʳ embed <*> refl) ∘ (isoʳ embed <*> refl) ⦈ ⟧
      `(𝓕₁ (𝓕₁⁻¹ (from ∘ 𝓕₁ f ∘ to))) ○ `(𝓕₁ (𝓕₁⁻¹ from))  ≡⟦ sym $ resp-∘ 𝓕 ⟧
      `(𝓕₁ ((𝓖 ∘ 𝓕) ₁ f ∘ 𝓕₁⁻¹ from))                      ⟦∎⟧ }
    }

  unit← : 𝓖 ∘ 𝓕 ⟹ id₍ 𝓒 ₎
  unit← = record
    { component = 𝓕₁⁻¹ to
    ; natural = λ { {f = f} → faithful $ 𝓓 ⊨begin
      `(𝓕₁ (𝓕₁⁻¹ to ∘ (𝓖 ∘ 𝓕) ₁ f))                      ≡⟦ resp-∘ 𝓕 ⟧
      `(𝓕₁ (𝓕₁⁻¹ to)) ○ `(𝓕₁ (𝓕₁⁻¹ (from ∘ 𝓕₁ f ∘ to)))  ≡⟦ ⦇ (isoʳ embed <*> refl) ∘ (isoʳ embed <*> refl) ⦈ ⟧
      ` to ○ (` from ○ `(𝓕₁ f ∘ to))                     ≡[ refl ]
      (` to ○ ` from) ○ `(𝓕₁ f ∘ to)                     ≡⟦ ⦇ isoʳ surj ∘ refl ⦈ ⟧
      `id ○ `(𝓕₁ f ∘ to)                                 ≡[ refl ]
      `(𝓕₁ f ∘ to)                                       ≡⟦ sym ⦇ refl ∘ (isoʳ embed <*> refl) ⦈ ⟧
      `(𝓕₁ f ∘ 𝓕₁ (𝓕₁⁻¹ to))                             ≡⟦ sym $ resp-∘ 𝓕 ⟧
      `(𝓕₁ (f ∘ 𝓕₁⁻¹ to))                                ⟦∎⟧ }
    }

  natural-equivalence : 𝓒 ≃ 𝓓
  natural-equivalence = record
    { to = 𝓕
    ; from = 𝓖
    ; counit = counit , record
      { inverse = counit←
      ; isoˡ = natural⁼ $ ƛ⁼ $ isoˡ surj
      ; isoʳ = natural⁼ $ ƛ⁼ $ isoʳ surj
      }
    ; unit = unit , record
      { inverse = unit←
      ; isoˡ = natural⁼ $ ƛ⁼ $ faithful $ begin
        𝓕₁ (𝓕₁⁻¹ to ∘ 𝓕₁⁻¹ from)       ≡⟨ resp-∘ 𝓕 ⟩
        𝓕₁ (𝓕₁⁻¹ to) ∘ 𝓕₁ (𝓕₁⁻¹ from)  ≡⟨ ⦇ (isoʳ embed <*> refl) ∘ (isoʳ embed <*> refl) ⦈ ⟩
        to ∘ from                      ≡⟨ isoʳ surj ⟩
        id                             ≡⟨ sym $ resp-id 𝓕 ⟩
        𝓕₁ id                          ∎
      ; isoʳ = natural⁼ $ ƛ⁼ $ faithful $ begin
        𝓕₁ (𝓕₁⁻¹ from ∘ 𝓕₁⁻¹ to)       ≡⟨ resp-∘ 𝓕 ⟩
        𝓕₁ (𝓕₁⁻¹ from) ∘ 𝓕₁ (𝓕₁⁻¹ to)  ≡⟨ ⦇ (isoʳ embed <*> refl) ∘ (isoʳ embed <*> refl) ⦈ ⟩
        from ∘ to                      ≡⟨ isoˡ surj ⟩
        id                             ≡⟨ sym $ resp-id 𝓕 ⟩
        𝓕₁ id                          ∎
      }
    }
