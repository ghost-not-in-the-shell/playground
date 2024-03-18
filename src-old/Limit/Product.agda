open import Category.Base using (Category)
module Limit.Product (𝓒 : Category) where
open Category 𝓒
open import Prelude

record Product : Set where
  field
    ⦃ op ⦄ : ProductOp Hom

    β/π₁ : ∀ {A B X} {f : Hom X A} {g : Hom X B} → π₁ ∘ < f , g > ≡ f
    β/π₂ : ∀ {A B X} {f : Hom X A} {g : Hom X B} → π₂ ∘ < f , g > ≡ g
    <,>-universal : ∀ {A B X} {f : Hom X A} {g : Hom X B} {⁇ : Hom X (A × B)}
      → π₁ ∘ ⁇ ≡ f
      → π₂ ∘ ⁇ ≡ g
      → ⁇ ≡ < f , g >
