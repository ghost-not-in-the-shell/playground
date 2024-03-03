{-# OPTIONS --type-in-type #-}
module Category.Base where
open import Prelude hiding (id; id₍_₎; _∘_)

record Category : Set where
  infixr 5 _∘_
  field
    Ob  : Set
    Hom : Ob → Ob → Set
    ⦃ categorical ⦄ : Categorical Hom

  id : ∀ {A} → Hom A A
  id = Categorical.id categorical

  id₍_₎ : ∀ A → Hom A A
  id₍ A ₎ = Categorical.id₍_₎ categorical A

  _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C
  g ∘ f = Categorical._∘_ categorical g f

  field
    ∘-identityˡ : ∀ {A B} {f : Hom A B} → id ∘ f ≡ f
    ∘-identityʳ : ∀ {A B} {f : Hom A B} → f ∘ id ≡ f
    ∘-assoc : ∀ {A B C D} {f : Hom A B} {g : Hom B C} {h : Hom C D}
      → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)

  id-universalˡ : ∀ {⁇ : ∀ {A} → Hom A A}
    → (∀ {A B} {f : Hom A B} → ⁇ ∘ f ≡ f)
    → ∀ {A : Ob} → ⁇ ≡ id₍ A ₎
  id-universalˡ {⁇} ⁇-identityˡ = begin
    ⁇       ≡⟨ ∘-identityʳ ⟲⟩
    ⁇ ∘ id  ≡⟨ ⁇-identityˡ ⟩
    id      ∎

  id-universalʳ : ∀ {⁇ : ∀ {A} → Hom A A}
    → (∀ {A B} {f : Hom A B} → f ∘ ⁇ ≡ f)
    → ∀ {A : Ob} → ⁇ {A} ≡ id
  id-universalʳ {⁇} ⁇-identityʳ = begin
    ⁇       ≡⟨ ∘-identityˡ ⟲⟩
    id ∘ ⁇  ≡⟨ ⁇-identityʳ ⟩
    id      ∎

  ∘-identityˡʳ : ∀ {A B} {f : Hom A B} → id ∘ f ≡ f ∘ id
  ∘-identityˡʳ = trans ∘-identityˡ $ sym ∘-identityʳ

  _ᵒᵖ : Category
  _ᵒᵖ = record
    { Ob  = Ob
    ; Hom = flip Hom
    ; categorical = record
      { id  = id
      ; _∘_ = flip _∘_
      }
    ; ∘-identityˡ = ∘-identityʳ
    ; ∘-identityʳ = ∘-identityˡ
    ; ∘-assoc     = sym ∘-assoc
    }

open Category public hiding (id; id₍_₎; _∘_)

infix 4 _∣_⟶_
_∣_⟶_ = Hom
{-# DISPLAY Hom 𝓒 A B = 𝓒 ∣ A ⟶ B #-}

dom : ∀ {𝓒 A B} → 𝓒 ∣ A ⟶ B → Ob 𝓒
dom {A = A} _ = A

cod : ∀ {𝓒 A B} → 𝓒 ∣ A ⟶ B → Ob 𝓒
cod {B = B} _ = B
