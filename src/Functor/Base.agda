module Functor.Base where
open import Prelude
open import Category.Base

record Functor (𝓒 𝓓 : Category) : Type where
  field
    map₀ : Ob 𝓒 → Ob 𝓓
  private 𝐹₀ = map₀
  field
    map₁ : ∀ {A B} → 𝓒 ⦅ A , B ⦆ → 𝓓 ⦅ 𝐹₀(A) , 𝐹₀(B) ⦆
  private 𝐹₁ = map₁
  field
    resp-id : ∀ {A} → 𝐹₁(id) ≡ id₍ 𝐹₀(A) ₎
    resp-∘  : ∀ {A B C} {f : 𝓒 ⦅ A , B ⦆} {g : 𝓒 ⦅ B , C ⦆}
      → 𝐹₁(g ∘ f) ≡ 𝐹₁(g) ∘ 𝐹₁(f)

open Functor public renaming (map₀ to _₀_; map₁ to _₁_)

infix 4 _⟶_
_⟶_ = Functor
{-# DISPLAY Functor = _⟶_ #-}

private variable
  𝓒 𝓓 𝓔 𝓧 : Category

private module Duality where
  instance
    opposite-functor : Opposite (𝓒 ⟶ 𝓓) (𝓒 ᵒᵖ ⟶ 𝓓 ᵒᵖ)
    opposite-functor = record
      { opposite = λ 𝐹 → record
        { map₀ = 𝐹 ₀_
        ; map₁ = 𝐹 ₁_
        ; resp-id = resp-id 𝐹
        ; resp-∘  = resp-∘  𝐹
        }
      }

  _ : {𝐹 : 𝓒 ⟶ 𝓓} → (𝐹 ᵒᵖ)ᵒᵖ ≡ 𝐹
  _ = refl

open Duality public

private
  id′ : 𝓒 ⟶ 𝓒
  id′ = record
    { map₀ = id
    ; map₁ = id
    ; resp-id = refl
    ; resp-∘  = refl
    }

  _∘′_ : 𝓓 ⟶ 𝓔 → 𝓒 ⟶ 𝓓 → 𝓒 ⟶ 𝓔
  𝐺 ∘′ 𝐹 = record
    { map₀ = 𝐺 ₀_ ∘ 𝐹 ₀_
    ; map₁ = 𝐺 ₁_ ∘ 𝐹 ₁_
    ; resp-id = trans (cong (𝐺 ₁_) (resp-id 𝐹)) (resp-id 𝐺)
    ; resp-∘  = trans (cong (𝐺 ₁_) (resp-∘  𝐹)) (resp-∘  𝐺)
    }

instance
  𝓒𝓪𝓽-compositionalOp : CompositionalOp Functor
  𝓒𝓪𝓽-compositionalOp = record
    { id  = id′
    ; _∘_ = _∘′_
    }

private
  _×′_ : Category → Category → Category
  𝓒 ×′ 𝓓 = record
    { Ob  = Ob 𝓒 × Ob 𝓓
    ; Hom = λ (A₁ , A₂) (B₁ , B₂) → Hom 𝓒 A₁ B₁ × Hom 𝓓 A₂ B₂
    ; Hom-set = ×-is-set (Hom-set 𝓒) (Hom-set 𝓓)
    ; op = record
      { id  = (id , id)
      ; _∘_ = λ (g₁ , g₂) (f₁ , f₂) → (g₁ ∘ f₁ , g₂ ∘ f₂)
      }
    ; ∘-idˡ   = cong₂ _,_ (∘-idˡ 𝓒)   (∘-idˡ 𝓓)
    ; ∘-idʳ   = cong₂ _,_ (∘-idʳ 𝓒)   (∘-idʳ 𝓓)
    ; ∘-assoc = cong₂ _,_ (∘-assoc 𝓒) (∘-assoc 𝓓)
    }

  π₁′ : 𝓒 ×′ 𝓓 ⟶ 𝓒
  π₁′ = record
    { map₀ = π₁
    ; map₁ = π₁
    ; resp-id = refl
    ; resp-∘  = refl
    }

  π₂′ : 𝓒 ×′ 𝓓 ⟶ 𝓓
  π₂′ = record
    { map₀ = π₂
    ; map₁ = π₂
    ; resp-id = refl
    ; resp-∘  = refl
    }

  <_,_>′ : 𝓧 ⟶ 𝓒 → 𝓧 ⟶ 𝓓 → 𝓧 ⟶ 𝓒 ×′ 𝓓
  < 𝐹 , 𝐺 >′ = record
    { map₀ = < 𝐹 ₀_ , 𝐺 ₀_ >
    ; map₁ = < 𝐹 ₁_ , 𝐺 ₁_ >
    ; resp-id = cong₂ _,_ (resp-id 𝐹) (resp-id 𝐺)
    ; resp-∘  = cong₂ _,_ (resp-∘  𝐹) (resp-∘  𝐺)
    }

instance
  𝓒𝓪𝓽-productOp : ProductOp Functor
  𝓒𝓪𝓽-productOp = record
    { _×_ = _×′_
    ; π₁ = λ {𝓒 𝓓} → π₁′ {𝓒} {𝓓}
    ; π₂ = λ {𝓒 𝓓} → π₂′ {𝓒} {𝓓}
    ; <_,_> = <_,_>′
    }
