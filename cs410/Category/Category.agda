module Category.Category where
open import Prelude
open import Category.Base
open import Functor.Base

𝓒𝓪𝓽 : Category
𝓒𝓪𝓽 = record
  { Ob  = Category
  ; Hom = Functor
  ; op  = 𝓒𝓪𝓽-categorical
  ; ∘-identityˡ = functor⁼ (refl , refl)
  ; ∘-identityʳ = functor⁼ (refl , refl)
  ; ∘-assoc     = functor⁼ (refl , refl)
  }
