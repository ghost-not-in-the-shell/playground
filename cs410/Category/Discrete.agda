module Category.Discrete where
open import Prelude
open import Category.Base

𝓓𝓲𝓼𝓬𝓻𝓮𝓽𝓮 : Set → Category
𝓓𝓲𝓼𝓬𝓻𝓮𝓽𝓮 A = record
  { Ob  = A
  ; Hom = _≡_
  ; op  = record
    { id  = refl
    ; _∘_ = flip trans
    }
  ; ∘-identityˡ = uip _ _
  ; ∘-identityʳ = uip _ _
  ; ∘-assoc     = uip _ _
  }
