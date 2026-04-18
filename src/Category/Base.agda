module Category.Base where
open import Prelude

record Category : Type where
  field
    Ob  : Type
    Hom : Ob → Ob → Type
    Hom-set : ∀ {A B} → is-set (Hom A B)

    ⦃ op ⦄ : CompositionalOp Hom

    ∘-idˡ : ∀ {A B} {f : Hom A B} → id ∘ f ≡ f
    ∘-idʳ : ∀ {A B} {f : Hom A B} → f ∘ id ≡ f
    ∘-assoc : ∀ {A B C D} {f : Hom A B} {g : Hom B C} {h : Hom C D}
      → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)

  ∘-idˡʳ : ∀ {A B} {f : Hom A B} → id ∘ f ≡ f ∘ id
  ∘-idˡʳ = trans ∘-idˡ (sym ∘-idʳ)

open Category public

infix 5 _⦅_,_⦆
_⦅_,_⦆ = Hom
{-# DISPLAY Hom = _⦅_,_⦆ #-}

private module Duality where
  instance
    opposite-category : Opposite Category Category
    opposite-category = record
      { opposite = λ 𝓒 → record
        { Ob  = Ob 𝓒
        ; Hom = flip (Hom 𝓒)
        ; Hom-set = Hom-set 𝓒
        ; op = record
          { id  = id
          ; _∘_ = flip _∘_
          }
        ; ∘-idˡ = ∘-idʳ 𝓒
        ; ∘-idʳ = ∘-idˡ 𝓒
        ; ∘-assoc = sym (∘-assoc 𝓒)
        }
      }

  _ : {𝓒 : Category} → (𝓒 ᵒᵖ)ᵒᵖ ≡ 𝓒
  _ = refl

open Duality public

infixr 5 _○_
_○_ : {Ob : Type} {Hom : Ob → Ob → Type} ⦃ _ : CompositionalOp Hom ⦄
  → {A B C : Ob} {f₀ f₁ : Hom A B} {g₀ g₁ : Hom B C}
  → g₀ ≡ g₁ → f₀ ≡ f₁ → g₀ ∘ f₀ ≡ g₁ ∘ f₁
g ○ f = cong₂ _∘_ g f
