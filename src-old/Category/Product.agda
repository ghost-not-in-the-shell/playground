{-# OPTIONS --type-in-type #-}
module Category.Product where
open import Prelude
open import Category.Base
open import Functor.Base

private
  _×'_ : Category → Category → Category
  𝓒 ×' 𝓓 = record
    { Ob  = Ob 𝓒 × Ob 𝓓
    ; Hom = λ (A₁ , A₂) (B₁ , B₂) → Hom 𝓒 A₁ B₁ × Hom 𝓓 A₂ B₂
    ; op  = record
      { id  = (id , id)
      ; _∘_ = λ (g₁ , g₂) (f₁ , f₂) → (g₁ ∘ f₁ , g₂ ∘ f₂)
      }
    ; ∘-identityˡ = ⦇ ∘-identityˡ 𝓒 , ∘-identityˡ 𝓓 ⦈
    ; ∘-identityʳ = ⦇ ∘-identityʳ 𝓒 , ∘-identityʳ 𝓓 ⦈
    ; ∘-assoc     = ⦇ ∘-assoc     𝓒 , ∘-assoc     𝓓 ⦈
    }

  π₁' : ∀ {𝓒 𝓓} → 𝓒 ×' 𝓓 ⟶ 𝓒
  π₁' = record
    { map₀ = π₁
    ; map₁ = π₁
    ; resp-id = refl
    ; resp-∘  = refl
    }

  π₂' : ∀ {𝓒 𝓓} → 𝓒 ×' 𝓓 ⟶ 𝓓
  π₂' = record
    { map₀ = π₂
    ; map₁ = π₂
    ; resp-id = refl
    ; resp-∘  = refl
    }

  <_,_>' : ∀ {𝓧 𝓒 𝓓} → 𝓧 ⟶ 𝓒 → 𝓧 ⟶ 𝓓 → 𝓧 ⟶ 𝓒 ×' 𝓓
  < 𝓕 , 𝓖 >' = record
    { map₀ = < 𝓕 ₀_ , 𝓖 ₀_ >
    ; map₁ = < 𝓕 ₁_ , 𝓖 ₁_ >
    ; resp-id = ⦇ resp-id 𝓕 , resp-id 𝓖 ⦈
    ; resp-∘  = ⦇ resp-∘  𝓕 , resp-∘  𝓖 ⦈
    }

instance
  𝓒𝓪𝓽-product : ProductOp Functor
  𝓒𝓪𝓽-product = record
    { _×_ = _×'_
    ; π₁ = π₁'
    ; π₂ = π₂'
    ; <_,_> = <_,_>'
    }
