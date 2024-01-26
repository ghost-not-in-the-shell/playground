module Functor.Maybe where
open import Prelude
open import Category.Base
open import Category.Set

𝓜𝓪𝔂𝓫𝓮 : 𝓢𝓮𝓽 ⟶ 𝓢𝓮𝓽
𝓜𝓪𝔂𝓫𝓮 = record
  { map₀ = Maybe
  ; map₁ = maybe
  ; resp-id = λ⁼ maybe-id
  ; resp-∘  = λ⁼ maybe-∘
  }
