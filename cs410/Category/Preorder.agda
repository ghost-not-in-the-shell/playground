module Category.Preorder where
open import Prelude
open import Category.Base

private
  identity : ∀ {𝑷} → MonotoneMap 𝑷 𝑷
  identity = record
    { map      = id
    ; monotone = id
    }

  composition : ∀ {𝑷 𝑸 𝑹} → MonotoneMap 𝑸 𝑹 → MonotoneMap 𝑷 𝑸 → MonotoneMap 𝑷 𝑹
  composition 𝒈 𝒇 = record
    { map      = map      𝒈 ∘ map      𝒇
    ; monotone = monotone 𝒈 ∘ monotone 𝒇
    }

𝓞𝓻𝓭 : Category
𝓞𝓻𝓭 = record
  { Ob  = Preorder
  ; Hom = MonotoneMap
  ; op  = record
    { id  = identity
    ; _∘_ = composition
    }
  ; ∘-identityˡ = refl
  ; ∘-identityʳ = refl
  ; ∘-assoc = refl
  }
