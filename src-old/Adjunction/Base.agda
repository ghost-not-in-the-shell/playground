module Adjunction.Base where
open import Prelude
open import Category.Base
open import Category.Functor
open import Category.Isomorphism
open import Category.Set
open import Functor.Base
open import Functor.Hom
open import Natural.Base
open import Natural.Isomorphism

record Adjunction {𝓒 𝓓} (𝓛 : 𝓒 ⟶ 𝓓) (𝓡 : 𝓓 ⟶ 𝓒) : Set where
  infix 6 _♯ _♭
  field
    _♯ : ∀ {X Y} → 𝓒 ∣     X ⟶ 𝓡 ₀ Y → 𝓓 ∣ 𝓛 ₀ X ⟶     Y
    _♭ : ∀ {X Y} → 𝓓 ∣ 𝓛 ₀ X ⟶     Y → 𝓒 ∣     X ⟶ 𝓡 ₀ Y

    ♭∘♯ : ∀ {X Y} (f : 𝓒 ∣ X ⟶ 𝓡 ₀ Y) → (f ♯) ♭ ≡ f
    ♯∘♭ : ∀ {X Y} (g : 𝓓 ∣ 𝓛 ₀ X ⟶ Y) → (g ♭) ♯ ≡ g

    ♯-natural : ∀ {X₁ X₂ Y₁ Y₂} {f : 𝓒 ∣ X₂ ⟶ X₁} {g : 𝓓 ∣ Y₁ ⟶ Y₂}
      → _♯ ∘ (λ - → 𝓡 ₁ g ∘ - ∘ f) ≡ (λ - → g ∘ - ∘ 𝓛 ₁ f) ∘ _♯

  ♭-natural : ∀ {X₁ X₂ Y₁ Y₂} {f : 𝓒 ∣ X₂ ⟶ X₁} {g : 𝓓 ∣ Y₁ ⟶ Y₂}
    → _♭ ∘ (λ - → g ∘ - ∘ 𝓛 ₁ f) ≡ (λ - → 𝓡 ₁ g ∘ - ∘ f) ∘ _♭
  ♭-natural = natural ∣ ♯ ⁻¹ ∣
    where ♯⋆ : ∀ {X Y} → Isomorphism 𝓢𝓮𝓽 (_♯ {X} {Y})
          ♯⋆ = record
            { inverse = _♭
            ; isoˡ = λ⁼ ♭∘♯
            ; isoʳ = λ⁼ ♯∘♭
            }

          ∣♯∣ : 𝓕𝓾𝓷 (𝓒 ᵒᵖ × 𝓓) 𝓢𝓮𝓽 ∣ 𝓱𝓸𝓶 ∘ (id ᵒᵖ' ×₁ 𝓡) ⟶ 𝓱𝓸𝓶 ∘ (𝓛 ᵒᵖ' ×₁ id)
          ∣♯∣ = record
            { component = _♯
            ; natural = ♯-natural
            }

          ♯ : Isomorphism (𝓕𝓾𝓷 (𝓒 ᵒᵖ × 𝓓) 𝓢𝓮𝓽) ∣♯∣
          ♯ = from-component≅ ♯⋆

  ♯↑ : ∀ {A B C} {f : 𝓒 ∣ A ⟶ 𝓡 ₀ B} {g : 𝓓 ∣ B ⟶ C}
    → (𝓡 ₁ g ∘ f) ♯ ≡ g ∘ f ♯
  ♯↑ {f = f} {g} = begin
    (𝓡 ₁ g ∘ f) ♯       ≡⟨ sym $ cong _♯ ⦇ refl ∘ ∘-identityʳ 𝓒 ⦈ ⟩
    (𝓡 ₁ g ∘ f ∘ id) ♯  ≡⟨ ♯-natural <*> refl ⟩
    g ∘ f ♯ ∘ 𝓛 ₁ id    ≡⟨ ⦇ refl ∘ ⦇ refl ∘ resp-id 𝓛 ⦈ ⦈ ⟩
    g ∘ f ♯ ∘ id        ≡⟨ ⦇ refl ∘ ∘-identityʳ 𝓓 ⦈ ⟩
    g ∘ f ♯             ∎

  ♯↓ : ∀ {A B C} {f : 𝓒 ∣ A ⟶ B} {g : 𝓒 ∣ B ⟶ 𝓡 ₀ C}
    → (g ∘ f) ♯ ≡ g ♯ ∘ 𝓛 ₁ f
  ♯↓ {f = f} {g} = begin
    (g ∘ f) ♯           ≡⟨ sym $ cong _♯ $ ∘-identityˡ 𝓒 ⟩
    (id ∘ g ∘ f) ♯      ≡⟨ sym $ cong _♯ ⦇ resp-id 𝓡 ∘ refl ⦈ ⟩
    (𝓡 ₁ id ∘ g ∘ f) ♯  ≡⟨ ♯-natural <*> refl ⟩
    id ∘ g ♯ ∘ 𝓛 ₁ f    ≡⟨ ∘-identityˡ 𝓓 ⟩
    g ♯ ∘ 𝓛 ₁ f         ∎

  ♭↑ : ∀ {A B C} {f : 𝓒 ∣ A ⟶ B} {g : 𝓓 ∣ 𝓛 ₀ B ⟶ C}
    → g ♭ ∘ f ≡ (g ∘ 𝓛 ₁ f) ♭
  ♭↑ {f = f} {g} = begin
    g ♭ ∘ f             ≡⟨ sym $ ∘-identityˡ 𝓒 ⟩
    id ∘ g ♭ ∘ f        ≡⟨ sym ⦇ resp-id 𝓡 ∘ refl ⦈ ⟩
    𝓡 ₁ id ∘ g ♭ ∘ f    ≡⟨ sym $ ♭-natural <*> refl ⟩
    (id ∘ g ∘ 𝓛 ₁ f) ♭  ≡⟨ cong _♭ $ ∘-identityˡ 𝓓 ⟩
    (g ∘ 𝓛 ₁ f) ♭       ∎

  ♭↓ : ∀ {A B C} {f : 𝓓 ∣ 𝓛 ₀ A ⟶ B} {g : 𝓓 ∣ B ⟶ C}
    → 𝓡 ₁ g ∘ f ♭ ≡ (g ∘ f) ♭
  ♭↓ {f = f} {g} = begin
    𝓡 ₁ g ∘ f ♭         ≡⟨ sym ⦇ refl ∘ ∘-identityʳ 𝓒 ⦈ ⟩
    𝓡 ₁ g ∘ f ♭ ∘ id    ≡⟨ sym $ ♭-natural <*> refl ⟩
    (g ∘ f ∘ 𝓛 ₁ id) ♭  ≡⟨ cong _♭ ⦇ refl ∘ ⦇ refl ∘ resp-id 𝓛 ⦈ ⦈ ⟩
    (g ∘ f ∘ id) ♭      ≡⟨ cong _♭ ⦇ refl ∘ ∘-identityʳ 𝓓 ⦈ ⟩
    (g ∘ f) ♭           ∎

  counit : 𝓛 ∘ 𝓡 ⟹ id
  counit = record
    { component = id ♯
    ; natural = λ { {f = f} → begin
      id ♯ ∘ 𝓛 ₁ (𝓡 ₁ f)  ≡⟨ sym ♯↓ ⟩
      (id ∘ 𝓡 ₁ f) ♯      ≡⟨ cong _♯ $ ∘-identityˡʳ 𝓒 ⟩
      (𝓡 ₁ f ∘ id) ♯      ≡⟨ ♯↑ ⟩
      f ∘ id ♯            ∎ }
    }

  unit : id ⟹ 𝓡 ∘ 𝓛
  unit = record
    { component = id ♭
    ; natural = λ { {f = f} → begin
      id ♭ ∘ f            ≡⟨ ♭↑ ⟩
      (id ∘ 𝓛 ₁ f) ♭      ≡⟨ cong _♭ $ ∘-identityˡʳ 𝓓 ⟩
      (𝓛 ₁ f ∘ id) ♭      ≡⟨ sym ♭↓ ⟩
      𝓡 ₁ (𝓛 ₁ f) ∘ id ♭  ∎ }
    }

  zig : ∀ {A} → (counit ∘ˡ 𝓛)₍ A ₎ ∘ (𝓛 ∘ʳ unit)₍ A ₎ ≡ id
  zig = begin
    id ♯ ∘ 𝓛 ₁ (id ♭)  ≡⟨ sym ♯↓ ⟩
    (id ∘ id ♭) ♯      ≡⟨ cong _♯ $ ∘-identityˡ 𝓒 ⟩
    (id ♭) ♯           ≡⟨ ♯∘♭ _ ⟩
    id                 ∎

  zag : ∀ {A} → (𝓡 ∘ʳ counit)₍ A ₎ ∘ (unit ∘ˡ 𝓡)₍ A ₎ ≡ id
  zag = begin
    𝓡 ₁ (id ♯) ∘ id ♭  ≡⟨ ♭↓ ⟩
    (id ♯ ∘ id) ♭      ≡⟨ cong _♭ $ ∘-identityʳ 𝓓 ⟩
    (id ♯) ♭           ≡⟨ ♭∘♯ _ ⟩
    id                 ∎

infix 4 _⊣_
_⊣_ : ∀ {𝓒 𝓓} → 𝓒 ⟶ 𝓓 → 𝓓 ⟶ 𝓒 → Set
𝓛 ⊣ 𝓡 = Adjunction 𝓛 𝓡
