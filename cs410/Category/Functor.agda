open import Category.Base
module Category.Functor (𝓒 : Category) (𝓓 : Category) where
open import Prelude

private
  identity : ∀ {𝓕 : 𝓒 ⟶ 𝓓} → 𝓕 ⟹ 𝓕
  identity = record
    { component = id
    ; natural = trans (∘-identityˡ 𝓓) (sym (∘-identityʳ 𝓓))
    }

  composition : ∀ {𝓕 𝓖 𝓗 : 𝓒 ⟶ 𝓓} → 𝓖 ⟹ 𝓗 → 𝓕 ⟹ 𝓖 → 𝓕 ⟹ 𝓗
  composition {𝓕} {𝓖} {𝓗} β α = record
     { component = β ⋆ ∘ α ⋆
     ; natural = λ { {f = f} → begin
       (β ⋆ ∘ α ⋆) ∘ 𝓕 ₁(f)  ≡⟨ ∘-assoc 𝓓 ⟩
       β ⋆ ∘ (α ⋆ ∘ 𝓕 ₁(f))  ≡⟨ ⦇ refl ∘ natural α ⦈ ⟩
       β ⋆ ∘ (𝓖 ₁(f) ∘ α ⋆)  ≡⟨ sym (∘-assoc 𝓓) ⟩
       (β ⋆ ∘ 𝓖 ₁(f)) ∘ α ⋆  ≡⟨ ⦇ natural β ∘ refl ⦈ ⟩
       (𝓗 ₁(f) ∘ β ⋆) ∘ α ⋆  ≡⟨ ∘-assoc 𝓓 ⟩
       𝓗 ₁(f) ∘ (β ⋆ ∘ α ⋆)  ∎ }
     }

instance
  𝓕𝓾𝓷-categorical : CategoricalOp NaturalTransformation
  𝓕𝓾𝓷-categorical = record
    { id  = identity
    ; _∘_ = composition
    }

𝓕𝓾𝓷 : Category
𝓕𝓾𝓷 = record
  { ob  = 𝓒 ⟶ 𝓓
  ; hom = NaturalTransformation
  ; op  = 𝓕𝓾𝓷-categorical
  ; ∘-identityˡ = natural⁼ $ ƛ⁼ $ ∘-identityˡ 𝓓
  ; ∘-identityʳ = natural⁼ $ ƛ⁼ $ ∘-identityʳ 𝓓
  ; ∘-assoc     = natural⁼ $ ƛ⁼ $ ∘-assoc 𝓓
  }
