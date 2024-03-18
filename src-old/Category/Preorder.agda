module Category.Preorder where
open import Prelude
open import Category.Base

𝓟𝓻𝓮 : Category
𝓟𝓻𝓮 = record
  { Ob  = Preorder
  ; Hom = MonotoneMap
  ; op = 𝓟𝓻𝓮-categorical
  ; ∘-identityˡ = refl
  ; ∘-identityʳ = refl
  ; ∘-assoc     = refl
  }
