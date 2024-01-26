module Isomorphism where
open import Prelude
open import Category.Base

record Isomorphism 𝓒 {A B} (f : 𝓒 ∣ A ⟶ B) : Set where
  field
    inverse : 𝓒 ∣ B ⟶ A

  private
    f⁻¹ = inverse

  field
    isoˡ : f⁻¹ ∘ f ≡ id
    isoʳ : f ∘ f⁻¹ ≡ id

  ⁻¹-universalˡ : ∀ {⁇ : 𝓒 ∣ B ⟶ A}
    → ⁇ ∘ f ≡ id
    → ⁇ ≡ f⁻¹
  ⁻¹-universalˡ {⁇ = ⁇} ⁇-isoˡ = begin
    ⁇              ≡⟨ sym $ ∘-identityʳ 𝓒 ⟩
    ⁇ ∘ id         ≡⟨ sym ⦇ refl ∘ isoʳ ⦈ ⟩
    ⁇ ∘ (f ∘ f⁻¹)  ≡⟨ sym $ ∘-assoc 𝓒 ⟩
    (⁇ ∘ f) ∘ f⁻¹  ≡⟨ ⦇ ⁇-isoˡ ∘ refl ⦈ ⟩
    id ∘ f⁻¹       ≡⟨ ∘-identityˡ 𝓒 ⟩
    f⁻¹            ∎

  ⁻¹-universalʳ : ∀ {⁇ : 𝓒 ∣ B ⟶ A}
    → f ∘ ⁇ ≡ id
    → ⁇ ≡ f⁻¹
  ⁻¹-universalʳ {⁇ = ⁇} ⁇-isoʳ = begin
    ⁇ ≡⟨ sym $ ∘-identityˡ 𝓒 ⟩
    id ∘ ⁇         ≡⟨ sym ⦇ isoˡ ∘ refl ⦈ ⟩
    (f⁻¹ ∘ f) ∘ ⁇  ≡⟨ ∘-assoc 𝓒 ⟩
    f⁻¹ ∘ (f ∘ ⁇)  ≡⟨ ⦇ refl ∘ ⁇-isoʳ ⦈ ⟩
    f⁻¹ ∘ id       ≡⟨ ∘-identityʳ 𝓒 ⟩
    f⁻¹            ∎

  cancelˡ : ∀ {X} {a a′ : 𝓒 ∣ X ⟶ A}
    → f ∘ a ≡ f ∘ a′
    → a ≡ a′
  cancelˡ {a = a} {a′} hyp = begin
    a               ≡⟨ sym $ ∘-identityˡ 𝓒 ⟩
    id ∘ a          ≡⟨ sym ⦇ isoˡ ∘ refl ⦈ ⟩
    (f⁻¹ ∘ f) ∘ a   ≡⟨ ∘-assoc 𝓒 ⟩
    f⁻¹ ∘ (f ∘ a)   ≡⟨ ⦇ refl ∘ hyp ⦈ ⟩
    f⁻¹ ∘ (f ∘ a′)  ≡⟨ sym $ ∘-assoc 𝓒 ⟩
    (f⁻¹ ∘ f) ∘ a′  ≡⟨ ⦇ isoˡ ∘ refl ⦈ ⟩
    id ∘ a′         ≡⟨ ∘-identityˡ 𝓒 ⟩
    a′              ∎

  cancelʳ : ∀ {C} {g g′ : 𝓒 ∣ B ⟶ C}
    → g ∘ f ≡ g′ ∘ f
    → g ≡ g′
  cancelʳ {g = g} {g′} hyp = begin
    g ≡⟨ sym $ ∘-identityʳ 𝓒 ⟩
    g ∘ id          ≡⟨ sym ⦇ refl ∘ isoʳ ⦈ ⟩
    g ∘ (f ∘ f⁻¹)   ≡⟨ sym $ ∘-assoc 𝓒 ⟩
    (g ∘ f) ∘ f⁻¹   ≡⟨ ⦇ hyp ∘ refl ⦈ ⟩
    (g′ ∘ f) ∘ f⁻¹  ≡⟨ ∘-assoc 𝓒 ⟩
    g′ ∘ (f ∘ f⁻¹)  ≡⟨ ⦇ refl ∘ isoʳ ⦈ ⟩
    g′ ∘ id         ≡⟨ ∘-identityʳ 𝓒 ⟩
    g′              ∎

open Isomorphism public hiding (inverse)

infix 6 _⁻¹
_⁻¹ : ∀ {𝓒 A B} {f : 𝓒 ∣ A ⟶ B} → Isomorphism 𝓒 f → 𝓒 ∣ B ⟶ A
f ⁻¹ = Isomorphism.inverse f

∣_∣ : ∀ {𝓒 A B} {f : 𝓒 ∣ A ⟶ B} → Isomorphism 𝓒 f → 𝓒 ∣ A ⟶ B
∣_∣ {f = f} _ = f

infix 4 ≅-syntax
≅-syntax : ∀ 𝓒 → Ob 𝓒 → Ob 𝓒 → Set
≅-syntax 𝓒 A B = ∃[ f ] Isomorphism 𝓒 {A} {B} f

syntax ≅-syntax 𝓒 A B = A ≅ B [ 𝓒 ]
