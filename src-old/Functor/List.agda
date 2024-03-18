module Functor.List where
open import Prelude
open import Category.Base
open import Category.Set

𝓛𝓲𝓼𝓽 : 𝓢𝓮𝓽 ⟶ 𝓢𝓮𝓽
𝓛𝓲𝓼𝓽 = record
  { map₀ = List
  ; map₁ = list
  ; resp-id = λ⁼ list-id
  ; resp-∘  = λ⁼ list-∘
  }
