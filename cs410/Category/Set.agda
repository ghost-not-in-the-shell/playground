{-# OPTIONS --type-in-type #-}
module Category.Set where
open import Prelude
open import Category.Base

𝓢𝓮𝓽 : Category
𝓢𝓮𝓽 = record
  { ob  = Set
  ; hom = Function
  ; op  = 𝓢𝓮𝓽-categorical
  ; ∘-identityˡ = refl
  ; ∘-identityʳ = refl
  ; ∘-assoc     = refl
  }

𝓜𝓪𝔂𝓫𝓮 : 𝓢𝓮𝓽 ⟶ 𝓢𝓮𝓽
𝓜𝓪𝔂𝓫𝓮 = record
  { map₀ = Maybe
  ; map₁ = maybe
  ; resp-id = λ⁼ maybe-id
  ; resp-∘  = λ⁼ maybe-∘
  }

𝓛𝓲𝓼𝓽 : 𝓢𝓮𝓽 ⟶ 𝓢𝓮𝓽
𝓛𝓲𝓼𝓽 = record
  { map₀ = List
  ; map₁ = list
  ; resp-id = λ⁼ list-id
  ; resp-∘  = λ⁼ list-∘
  }
