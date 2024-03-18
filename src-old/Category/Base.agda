{-# OPTIONS --type-in-type #-}
module Category.Base where
open import Prelude

record Category : Set where
  field
    Ob : Set
    Hom : Ob → Ob → Set
    ⦃ op ⦄ : CategoricalOp Hom

    ∘-identityˡ : ∀ {A B} {f : Hom A B} → id ∘ f ≡ f
    ∘-identityʳ : ∀ {A B} {f : Hom A B} → f ∘ id ≡ f
    ∘-assoc : ∀ {A B C D} {f : Hom A B} {g : Hom B C} {h : Hom C D}
      → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)

  id-universalˡ : ∀ {⁇ : ∀ {A} → Hom A A}
    → (∀ {A B} {f : Hom A B} → ⁇ ∘ f ≡ f)
    → ∀ {A} → ⁇ {A} ≡ id₍ A ₎
  id-universalˡ {⁇ = ⁇} ⁇-identityˡ = begin
    ⁇       ≡⟨ sym ∘-identityʳ ⟩
    ⁇ ∘ id  ≡⟨ ⁇-identityˡ ⟩
    id      ∎

  id-universalʳ : ∀ {⁇ : ∀ {A} → Hom A A}
    → (∀ {A B} {f : Hom A B} → f ∘ ⁇ ≡ f)
    → ∀ {A} → ⁇ {A} ≡ id₍ A ₎
  id-universalʳ {⁇ = ⁇} ⁇-identityʳ = begin
    ⁇       ≡⟨ sym ∘-identityˡ ⟩
    id ∘ ⁇  ≡⟨ ⁇-identityʳ ⟩
    id      ∎

  ∘-identityˡʳ : ∀ {A B} {f : Hom A B} → id ∘ f ≡ f ∘ id
  ∘-identityˡʳ = trans ∘-identityˡ $ sym ∘-identityʳ

  _ᵒᵖ : Category
  _ᵒᵖ = record
   { Ob  = Ob
   ; Hom = flip Hom
   ; op  = record
     { id  = id
     ; _∘_ = flip _∘_
     }
   ; ∘-identityˡ = ∘-identityʳ
   ; ∘-identityʳ = ∘-identityˡ
   ; ∘-assoc = sym ∘-assoc
   }

open Category public hiding (op)

infix 4 _∣_⟶_
_∣_⟶_ = Hom
{-# DISPLAY Hom 𝓒 A B = 𝓒 ∣ A ⟶ B #-}

dom : ∀ {𝓒 A B} → 𝓒 ∣ A ⟶ B → Ob 𝓒
dom {A = A} _ = A

cod : ∀ {𝓒 A B} → 𝓒 ∣ A ⟶ B → Ob 𝓒
cod {B = B} _ = B
