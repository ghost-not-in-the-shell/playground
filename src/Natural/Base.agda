module Natural.Base where
open import Prelude
open import Category.Base
open import Functor.Base

record NaturalTransformation {𝓒 𝓓} (𝐹 𝐺 : 𝓒 ⟶ 𝓓) : Type where
  field
    component : ∀ {A} → 𝓓 ⦅ 𝐹 ₀(A) , 𝐺 ₀(A) ⦆
  private η = component
  field
    natural : ∀ {A B} {f : 𝓒 ⦅ A , B ⦆} → η ∘ 𝐹 ₁(f) ≡ 𝐺 ₁(f) ∘ η

open NaturalTransformation public

infix 4 _⟹_
_⟹_ = NaturalTransformation
{-# DISPLAY NaturalTransformation = _⟹_ #-}

private variable
  𝓒 𝓓 : Category
  𝐹 𝐺 : 𝓒 ⟶ 𝓓

instance
  natural-funlike : {𝐹 𝐺 : 𝓒 ⟶ 𝓓} → Funlike (𝐹 ⟹ 𝐺) (Ob 𝓒) λ A → 𝓓 ⦅ 𝐹 ₀(A) , 𝐺 ₀(A) ⦆
  natural-funlike = funlike-instance λ η A → η .component

{-# DISPLAY component α = α ▴ #-}

module _ {𝓒 𝓓} where
  private
    id′ : {𝐹 : 𝓒 ⟶ 𝓓} → 𝐹 ⟹ 𝐹
    id′ = record
      { component = id
      ; natural   = ∘-idˡʳ 𝓓
      }

    _∘′_ : {𝐹 𝐺 𝐻 : 𝓒 ⟶ 𝓓} → 𝐺 ⟹ 𝐻 → 𝐹 ⟹ 𝐺 → 𝐹 ⟹ 𝐻
    _∘′_ {𝐹} {𝐺} {𝐻} β α = record
      { component = β ▴ ∘ α ▴
      ; natural = λ { {f = f} → begin
       (β ▴   ∘ α ▴)   ∘ 𝐹 ₁(f)  ≡⟨ ∘-assoc 𝓓 ⟩
        β ▴   ∘(α ▴    ∘ 𝐹 ₁(f)) ≡⟨ - ○ natural α ⟩
        β ▴   ∘(𝐺 ₁(f) ∘ α ▴)    ≡⟨ ∘-assoc 𝓓 ⟨
       (β ▴   ∘ 𝐺 ₁(f))∘ α ▴     ≡⟨ natural β ○ - ⟩
       (𝐻 ₁(f)∘ β ▴)   ∘ α ▴     ≡⟨ ∘-assoc 𝓓 ⟩
        𝐻 ₁(f)∘(β ▴    ∘ α ▴)    ∎ }
      }

  instance
    𝓕𝓾𝓷-compositionalOp : CompositionalOp NaturalTransformation
    𝓕𝓾𝓷-compositionalOp = record
      { id  = id′
      ; _∘_ = _∘′_
      }

module 2-dimensional {𝓒 𝓓 𝓔} where
  whiskerˡ : (𝐹 : 𝓒 ⟶ 𝓓) {𝐺′ 𝐺″ : 𝓓 ⟶ 𝓔}
    → 𝐺′     ⟹ 𝐺″
    → 𝐺′ ∘ 𝐹 ⟹ 𝐺″ ∘ 𝐹
  whiskerˡ 𝐹 β = record
    { component = component β
    ; natural   = natural   β
    }

  whiskerʳ : {𝐹′ 𝐹″ : 𝓒 ⟶ 𝓓} (𝐺 : 𝓓 ⟶ 𝓔)
    →     𝐹′ ⟹     𝐹″
    → 𝐺 ∘ 𝐹′ ⟹ 𝐺 ∘ 𝐹″
  whiskerʳ {𝐹′} {𝐹″} 𝐺 α = record
    { component = λ {A} → 𝐺 ₁(α ₍ A ₎)
    ; natural = λ { {f = f} → begin
      𝐺 ₁(α ▴) ∘ 𝐺 ₁(𝐹′ ₁(f)) ≡⟨ resp-∘ 𝐺 ⟨
      𝐺 ₁(α ▴  ∘     𝐹′ ₁(f)) ≡⟨ cong (𝐺 ₁_) (natural α) ⟩
      𝐺 ₁(𝐹″ ₁(f)  ∘     α ▴) ≡⟨ resp-∘ 𝐺 ⟩
      𝐺 ₁(𝐹″ ₁(f)) ∘ 𝐺 ₁(α ▴) ∎ }
    }

  horizontal : {𝐹′ 𝐹″ : 𝓒 ⟶ 𝓓} {𝐺′ 𝐺″ : 𝓓 ⟶ 𝓔}
    → 𝐺′ ⟹ 𝐺″
    → 𝐹′ ⟹ 𝐹″
    → 𝐺′ ∘ 𝐹′ ⟹ 𝐺″ ∘ 𝐹″
  horizontal {𝐹′} {𝐺″ = 𝐺″} β α = whiskerʳ 𝐺″ α ∘ whiskerˡ 𝐹′ β

  infixr 5 whiskerˡ whiskerʳ horizontal
  syntax whiskerˡ 𝐹 β = β ∘ˡ 𝐹
  syntax whiskerʳ 𝐺 α = 𝐺 ∘ʳ α
  syntax horizontal α β = α ∗ β

open 2-dimensional public
