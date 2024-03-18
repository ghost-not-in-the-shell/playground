module Natural.Equivalence where
open import Prelude hiding (ε)
open import Category.Base
open import Category.Functor
open import Category.Isomorphism
open import Category.Solver
open import Functor.Base
open import Functor.Embedding
open import Natural.Base
open import Natural.Isomorphism

infix 4 _≃_
record _≃_ 𝓒 𝓓 : Set where
  field
    to   : 𝓒 ⟶ 𝓓
    from : 𝓓 ⟶ 𝓒

    unit   : id₍ 𝓒 ₎ ≅ from ∘ to [ 𝓕𝓾𝓷 𝓒 𝓒 ]
    counit : to ∘ from ≅ id₍ 𝓓 ₎ [ 𝓕𝓾𝓷 𝓓 𝓓 ]

≃-sym : ∀ {𝓒 𝓓} → 𝓒 ≃ 𝓓 → 𝓓 ≃ 𝓒
≃-sym equiv = record
  { to   = from
  ; from = to
  ; unit  = ≅-sym counit
  ; counit = ≅-sym unit
  } where open _≃_ equiv

module Faithful {𝓒 𝓓} (equiv : 𝓒 ≃ 𝓓) where
  open _≃_ equiv

  private
    𝓕 = to
    𝓖 = from

    η = snd unit
    ε = snd counit

    lemma↷ : ∀ {A B} {f : 𝓒 ∣ A ⟶ B}
      → f ≡ ∣ η ⁻¹ ∣ ⋆ ∘ 𝓖 ₁(𝓕 ₁(f)) ∘ ∣ η ∣ ⋆
    lemma↷ {f = f} = begin
      f                               ≡⟨ sym $ ∘-identityˡ 𝓒 ⟩
      id ∘ f                          ≡⟨ sym ⦇ isoˡ (to-component≅ η) ∘ refl ⦈ ⟩
      (∣ η ⁻¹ ∣ ⋆ ∘ ∣ η ∣ ⋆) ∘ f          ≡⟨ ∘-assoc 𝓒 ⟩
      ∣ η ⁻¹ ∣ ⋆ ∘ ∣ η ∣ ⋆ ∘ f            ≡⟨ ⦇ refl ∘ natural ∣ η ∣ ⦈ ⟩
      ∣ η ⁻¹ ∣ ⋆ ∘ 𝓖 ₁(𝓕 ₁(f)) ∘ ∣ η ∣ ⋆  ∎

  faithful↷ : Faithful 𝓕
  faithful↷ {f = f} {g} hyp = begin
    f                               ≡⟨ lemma↷ ⟩
    ∣ η ⁻¹ ∣ ⋆ ∘ 𝓖 ₁(𝓕 ₁(f)) ∘ ∣ η ∣ ⋆  ≡⟨ ⦇ refl ∘ ⦇ cong (𝓖 ₁_) hyp ∘ refl ⦈ ⦈ ⟩
    ∣ η ⁻¹ ∣ ⋆ ∘ 𝓖 ₁(𝓕 ₁(g)) ∘ ∣ η ∣ ⋆  ≡⟨ sym lemma↷ ⟩
    g                               ∎

open Faithful public

faithful↶ : ∀ {𝓒 𝓓} (equiv : 𝓒 ≃ 𝓓) → Faithful (_≃_.from equiv)
faithful↶ equiv = faithful↷ $ ≃-sym equiv

module  Full {𝓒 𝓓} (equiv : 𝓒 ≃ 𝓓) where
  open _≃_ equiv

  private
    𝓕 = to
    𝓖 = from

    η = snd unit
    ε = snd counit

    `𝓕 : ∀ {A B} → Syn 𝓒 A B → Syn 𝓓 (𝓕 ₀(A)) (𝓕 ₀(B))
    `𝓕 = `map 𝓕

    `𝓖 : ∀ {A B} → Syn 𝓓 A B → Syn 𝓒 (𝓖 ₀(A)) (𝓖 ₀(B))
    `𝓖 = `map 𝓖

    `η : ∀ {A} → Syn 𝓒 A (𝓖 ₀(𝓕 ₀(A)))
    `η = `(∣ η ∣ ⋆)

    `η⁻¹ : ∀ {A} → Syn 𝓒 (𝓖 ₀(𝓕 ₀(A))) A
    `η⁻¹ = `(∣ η ⁻¹ ∣ ⋆)

    lemma₁ : ∀ {A} → 𝓖 ₁(𝓕 ₁(∣ η ∣ ₍ A ₎)) ≡ ∣ η ∣ ₍ 𝓖 ₀(𝓕 ₀(A)) ₎
    lemma₁ = cancelʳ (to-component≅ η) $ sym $ natural $ ∣ η ∣

    lemma₂ : ∀ {A} → 𝓖 ₁(𝓕 ₁(∣ η ⁻¹ ∣ ⋆)) ≡ ∣ η ⁻¹ ∣ ₍ 𝓖 ₀(𝓕 ₀(A)) ₎
    lemma₂ = cancelˡ (to-component≅ (η ⁻¹)) $ natural $ ∣ η ⁻¹ ∣

  full↷ : Full 𝓕
  full↷ g = ∣ η ⁻¹ ∣ ⋆ ∘ 𝓖 ₁(g) ∘ ∣ η ∣ ⋆ , faithful↶ equiv ( 𝓒 ⊨begin
    `𝓖(`𝓕(`η⁻¹ ○ `𝓖(` g) ○ `η))                  ≡[ refl ]
    `𝓖(`𝓕(`η⁻¹)) ○ `𝓖(`𝓕(`𝓖(` g))) ○ `𝓖(`𝓕(`η))  ≡⟦ ⦇ lemma₂ ∘ ⦇ refl ∘ lemma₁ ⦈ ⦈ ⟧
    `η⁻¹ ○ `𝓖(`𝓕(`𝓖(` g))) ○ `η                  ≡⟦ sym ⦇ refl ∘ natural ∣ η ∣ ⦈ ⟧
    `η⁻¹ ○ `η ○ `𝓖(` g)                          ≡[ refl ]
    (`η⁻¹ ○ `η) ○ `𝓖(` g)                        ≡⟦ ⦇ isoˡ (to-component≅ η) ∘ refl ⦈ ⟧
    `id ○ `𝓖(` g)                                ≡[ refl ]
    `𝓖(` g)                                      ⟦∎⟧ )

open Full public
