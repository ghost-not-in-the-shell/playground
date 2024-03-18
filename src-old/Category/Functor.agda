open import Category.Base
module Category.Functor (𝓒 𝓓 : Category) where
open import Prelude
open import Functor.Base
open import Natural.Base

𝓕𝓾𝓷 : Category
𝓕𝓾𝓷 = record
  { Ob  = 𝓒 ⟶ 𝓓
  ; Hom = NaturalTransformation
  ; op  = 𝓕𝓾𝓷-categorical
  ; ∘-identityˡ = natural⁼ $ ƛ⁼ $ ∘-identityˡ 𝓓
  ; ∘-identityʳ = natural⁼ $ ƛ⁼ $ ∘-identityʳ 𝓓
  ; ∘-assoc     = natural⁼ $ ƛ⁼ $ ∘-assoc 𝓓
  }
