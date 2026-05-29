{-# OPTIONS --no-require-unique-meta-solutions #-}
module Category.Instances.Functors where
open import Prelude
open import Category.Assoc
open import Category.Base
open import Functor.Base
open import Functor.Bifunctor
open import Natural.Base
open ApplicativeReasoning

𝓕𝓾𝓷 : Category → Category → Category
𝓕𝓾𝓷 𝓒 𝓓 = record
  { Ob = 𝓒 ⟶ 𝓓
  ; Hom = NaturalTransformation
  ; Hom-set = NaturalTransformation-is-set
  ; ∘-idˡ   = ext λ {A} → 𝓓 .∘-idˡ
  ; ∘-idʳ   = ext λ {A} → 𝓓 .∘-idʳ
  ; ∘-assoc = ext λ {A} → 𝓓 .∘-assoc
  }

[_,_] = 𝓕𝓾𝓷
{-# DISPLAY 𝓕𝓾𝓷 = [_,_] #-}

private variable
  𝓒 𝓓 𝓧 : Category

private
  ev′ : [ 𝓒 , 𝓓 ] × 𝓒 ⟶ 𝓓
  ev′ {𝓓 = 𝓓} = record
    { map₀ = λ (𝐹 , A) → 𝐹 ₀(A)
    ; map₁ = λ {(𝐹 , A)} {(𝐺 , B)} (α , f) → 𝐺 ₁(f) ∘ α ₍ A ₎
    ; resp-id = λ {(𝐹 , A)} → begin
        𝐹 ₁(id) ∘ id ≡⟨ resp-id 𝐹 ○ - ⟩
            id  ∘ id ≡⟨ ∘-idˡ 𝓓 ⟩
                  id ∎
    ; resp-∘ = λ {(𝐹 , A)} {(𝐺 , B)} {(𝐻 , C)} {(α , f)} {(β , g)} → begin
        𝐻 ₁(g ∘     f)∘(β ₋ ∘ α ₋) ≡⟨ resp-∘ 𝐻 ○ - ⟩
       (𝐻 ₁ g ∘ 𝐻 ₁ f)∘(β ₋ ∘ α ₋) ≡⟨ ∘-assoc! 𝓓 ⟩
        𝐻 ₁ g ∘(𝐻 ₁(f)∘ β ₋)∘ α ₋  ≡⟨ - ○ natural β ○ - ⟨
        𝐻 ₁ g ∘(β ₋ ∘ 𝐺 ₁ f)∘ α ₋  ≡⟨ ∘-assoc! 𝓓 ⟩
       (𝐻 ₁ g ∘ β ₋)∘(𝐺 ₁ f ∘ α ₋) ∎
    }

  ƛ′ : 𝓧 × 𝓒 ⟶ 𝓓 → 𝓧 ⟶ [ 𝓒 , 𝓓 ]
  ƛ′ {𝓒 = 𝓒} 𝐹 = record
    { map₀ = λ A → 𝐹 ₀₍ A ,-₎
    ; map₁ = λ f → 𝐹 ₁₍ f ,-₎
    ; resp-id = ext λ {S} → resp-id 𝐹
    ; resp-∘ = λ {A B C f g} → ext λ {S} → begin
        𝐹 ₁(g ∘ f , id)          ≡⟨ ⦇ (𝐹 ₁_) ⦇ - , ∘-idʳ 𝓒 ⦈ ⦈ ⟨
        𝐹 ₁(g ∘ f , id ∘ id)     ≡⟨ resp-∘ 𝐹 ⟩
        𝐹 ₁(g , id)∘ 𝐹 ₁(f , id) ∎
    }

instance
  𝓒𝓪𝓽-exponentialOp : ExponentialOp Functor
  𝓒𝓪𝓽-exponentialOp = record
    { _⇒_ = [_,_]
    ; ev  = ev′
    ; ƛ   = ƛ′
    }
