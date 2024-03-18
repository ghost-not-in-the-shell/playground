module Category.Monoid where
open import Prelude
open import Category.Base hiding (Hom)

𝓜𝓸𝓷 : Category
𝓜𝓸𝓷 = record
  { Ob  = Monoid
  ; Hom = Homomorphism
  ; op  = 𝓜𝓸𝓷-categorical
  ; ∘-identityˡ = homomorphism⁼ refl
  ; ∘-identityʳ = homomorphism⁼ refl
  ; ∘-assoc     = homomorphism⁼ refl
  }

