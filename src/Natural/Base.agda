module Natural.Base where
open import Prelude
open import Category.Base
open import Functor.Base

record NaturalTransformation {𝓒 𝓓} (𝐹 𝐺 : 𝓒 ⟶ 𝓓) : Type where
  constructor _,_
  field
    component : ∀ A → 𝓓 ⦅ 𝐹 ₀(A) , 𝐺 ₀(A) ⦆
  private η = component
  field
    natural : ∀ {A B} {f : 𝓒 ⦅ A , B ⦆} → η(B) ∘ 𝐹 ₁(f) ≡ 𝐺 ₁(f) ∘ η(A)

open NaturalTransformation public

infix 4 _⟹_
_⟹_ = NaturalTransformation
{-# DISPLAY NaturalTransformation = _⟹_ #-}

module _ {𝓒 𝓓} where
  instance
    natural-funlike : {𝐹 𝐺 : 𝓒 ⟶ 𝓓} → Funlike (𝐹 ⟹ 𝐺) (Ob 𝓒) λ A → 𝓓 ⦅ 𝐹 ₀(A) , 𝐺 ₀(A) ⦆
    natural-funlike = funlike-instance λ η A → η .component A

  {-# DISPLAY component α = α ₋ #-}

  NaturalTransformation-is-set : {𝐹 𝐺 : 𝓒 ⟶ 𝓓} → is-set (𝐹 ⟹ 𝐺)
  NaturalTransformation-is-set {𝐹} {𝐺} = iso→is-set iso NaturalTransformation′-is-set
    where NaturalTransformation′ : Type
          NaturalTransformation′ =
            Σ[ η ∈ (∀ A → 𝓓 ⦅ 𝐹 ₀(A) , 𝐺 ₀(A) ⦆) ]
              ∀ {A B} {f : 𝓒 ⦅ A , B ⦆} → η(B) ∘ 𝐹 ₁(f) ≡ 𝐺 ₁(f) ∘ η(A)

          NaturalTransformation′-is-set : is-set NaturalTransformation′
          NaturalTransformation′-is-set =
            Σ-is-set (Π-is-set (λ _ → Hom-set 𝓓))
              λ η → is-prop→is-set $
                Πᵢ-is-prop λ {A} →
                Πᵢ-is-prop λ {B} →
                Πᵢ-is-prop λ {f} →
                  Hom-set 𝓓 (η(B) ∘ 𝐹 ₁(f)) (𝐺 ₁(f) ∘ η(A))

          iso : NaturalTransformation′ ≅ NaturalTransformation 𝐹 𝐺
          iso = record
            { fwd = λ (η , natural) → (η , natural)
            ; iso = record
              { bwd = λ (η , natural) → (η , natural)
              ; ∘-invˡ = refl
              ; ∘-invʳ = refl
              }
            }

  private
    id′ : {𝐹 : 𝓒 ⟶ 𝓓} → 𝐹 ⟹ 𝐹
    id′ = record
      { component = λ _ → id
      ; natural   = ∘-idˡʳ 𝓓
      }

    _∘′_ : {𝐹 𝐺 𝐻 : 𝓒 ⟶ 𝓓} → 𝐺 ⟹ 𝐻 → 𝐹 ⟹ 𝐺 → 𝐹 ⟹ 𝐻
    _∘′_ {𝐹} {𝐺} {𝐻} β α = record
      { component = λ A → β ₍ A ₎ ∘ α ₍ A ₎
      ; natural = λ { {f = f} → begin
         (β ₋   ∘ α ₋)   ∘ 𝐹 ₁(f)  ≡⟨ ∘-assoc 𝓓 ⟩
          β ₋   ∘(α ₋    ∘ 𝐹 ₁(f)) ≡⟨ - ○ natural α ⟩
          β ₋   ∘(𝐺 ₁(f) ∘ α ₋)    ≡⟨ ∘-assoc 𝓓 ⟨
         (β ₋   ∘ 𝐺 ₁(f))∘ α ₋     ≡⟨ natural β ○ - ⟩
         (𝐻 ₁(f)∘ β ₋)   ∘ α ₋     ≡⟨ ∘-assoc 𝓓 ⟩
          𝐻 ₁(f)∘(β ₋    ∘ α ₋)    ∎ }
      }

  instance
    𝓕𝓾𝓷-compositionalOp : CompositionalOp NaturalTransformation
    𝓕𝓾𝓷-compositionalOp = record
      { id  = id′
      ; _∘_ = _∘′_
      }

    Natural-extensional : {𝐹 𝐺 : 𝓒 ⟶ 𝓓}
      → ⦃ _ : Extensional (∀ A → 𝓓 ⦅ 𝐹 ₀(A) , 𝐺 ₀(A) ⦆) ⦄
      → Extensional (𝐹 ⟹ 𝐺)
    Natural-extensional {𝐹} {𝐺} ⦃ Π-ext ⦄ = record
      { _≈_ = _≈′_
      ; ext = ext′
      } where
        _≈′_ : (α β : 𝐹 ⟹ 𝐺) → Type
        α ≈′ β = component α ≈ component β

        ext′ : {α β : 𝐹 ⟹ 𝐺} → α ≈′ β → α ≡ β
        ext′ {α , α-natural} {β , β-natural} p = λ i → record
          { component = ext p i
          ; natural = λ {A B f} →
              is-prop→PathP
                (λ i → Hom-set 𝓓 (ext ⦃ Π-ext ⦄ p i B ∘ 𝐹 ₁(f))
                                 (𝐺 ₁(f) ∘ ext ⦃ Π-ext ⦄ p i A))
                α-natural β-natural i
          }

module 2-dimensional {𝓒 𝓓 𝓔} where
  whiskerˡ : (𝐹 : 𝓒 ⟶ 𝓓) {𝐺′ 𝐺″ : 𝓓 ⟶ 𝓔}
    → 𝐺′     ⟹ 𝐺″
    → 𝐺′ ∘ 𝐹 ⟹ 𝐺″ ∘ 𝐹
  whiskerˡ 𝐹 β = record
    { component = λ A → β ₍ 𝐹 ₀(A) ₎
    ; natural   = natural   β
    }

  whiskerʳ : {𝐹′ 𝐹″ : 𝓒 ⟶ 𝓓} (𝐺 : 𝓓 ⟶ 𝓔)
    →     𝐹′ ⟹     𝐹″
    → 𝐺 ∘ 𝐹′ ⟹ 𝐺 ∘ 𝐹″
  whiskerʳ {𝐹′} {𝐹″} 𝐺 α = record
    { component = λ A → 𝐺 ₁(α ₍ A ₎)
    ; natural = λ { {f = f} → begin
        𝐺 ₁(α ₋) ∘ 𝐺 ₁(𝐹′ ₁(f)) ≡⟨ resp-∘ 𝐺 ⟨
        𝐺 ₁(α ₋  ∘     𝐹′ ₁(f)) ≡⟨ cong (𝐺 ₁_) (natural α) ⟩
        𝐺 ₁(𝐹″ ₁(f)  ∘     α ₋) ≡⟨ resp-∘ 𝐺 ⟩
        𝐺 ₁(𝐹″ ₁(f)) ∘ 𝐺 ₁(α ₋) ∎ }
    }

  horizontal : {𝐹′ 𝐹″ : 𝓒 ⟶ 𝓓} {𝐺′ 𝐺″ : 𝓓 ⟶ 𝓔}
    → 𝐺′ ⟹ 𝐺″
    → 𝐹′ ⟹ 𝐹″
    → 𝐺′ ∘ 𝐹′ ⟹ 𝐺″ ∘ 𝐹″
  horizontal {𝐹′} {𝐺″ = 𝐺″} β α = whiskerʳ 𝐺″ α ∘ whiskerˡ 𝐹′ β

  infixr 5 whiskerˡ whiskerʳ horizontal
  syntax whiskerˡ 𝐹 β = β =∙- 𝐹
  syntax whiskerʳ 𝐺 α = 𝐺 -∙= α
  syntax horizontal α β = α ∗ β

open 2-dimensional public
