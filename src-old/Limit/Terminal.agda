open import Category.Base using (Category)
module Limit.Terminal (𝓒 : Category) where
open Category 𝓒
open import Prelude

record Terminal : Set where
  field
    ⦃ op ⦄ : TerminalOp Hom

    !-universal : ∀ {X} {⁇ : Hom X 𝟙}
      → ⁇ ≡ !
