module NaturalTransformation.Base where
open import Prelude
open import Category.Base
open import Functor.Base

record NaturalTransformation {𝓒 𝓓} (𝓕 𝓖 : 𝓒 ⟶ 𝓓) : Set where
  field
    component : ∀ {A} → 𝓓 ∣ 𝓕 ₀(A) ⟶ 𝓖 ₀(A)

  private
    η = component

  field
    natural : ∀ {A B} {f : 𝓒 ∣ A ⟶ B} → η ∘ 𝓕 ₁(f) ≡ 𝓖 ₁(f) ∘ η

open NaturalTransformation public

infix 4 _⟹_
_⟹_ = NaturalTransformation
{-# DISPLAY NaturalTransformation 𝓕 𝓖 = 𝓕 ⟹ 𝓖 #-}

infix 6 _⋆
_⋆ = component
{-# DISPLAY component α = α ⋆ #-}

infix 6 _₍_₎
_₍_₎ : ∀ {𝓒 𝓓} {𝓕 𝓖 : 𝓒 ⟶ 𝓓} (α : 𝓕 ⟹ 𝓖) (A : Ob 𝓒) → 𝓓 ∣ 𝓕 ₀(A) ⟶ 𝓖 ₀(A)
α ₍ A ₎ = component α {A = A}

natural⁼ : ∀ {𝓒 𝓓} {𝓕 𝓖 : 𝓒 ⟶ 𝓓} {α β : 𝓕 ⟹ 𝓖}
  → component α ≡ component β [ (∀ {A} → 𝓓 ∣ 𝓕 ₀(A) ⟶ 𝓖 ₀(A)) ]
  →           α ≡           β
natural⁼ {𝓒} {𝓓} {𝓕} {𝓖} {α} {β} refl = lemma (ƛ⁼ $ ƛ⁼ $ ƛ⁼ $ uip (natural α) (natural β))
  where Natural = ∀ {A B} {f : 𝓒 ∣ A ⟶ B} → β ⋆ ∘ 𝓕 ₁(f) ≡ 𝓖 ₁(f) ∘ β ⋆

        lemma : ∀ {α-natural β-natural : Natural}
                → α-natural ≡ β-natural [ Natural ]
                → record { component = component β; natural = α-natural }
                ≡ record { component = component β; natural = β-natural }
                [ 𝓕 ⟹ 𝓖 ]
        lemma refl = refl

module _ {𝓒 𝓓 : Category} where
  private
    identity : ∀ {𝓕 : 𝓒 ⟶ 𝓓} → 𝓕 ⟹ 𝓕
    identity = record
      { component = id
      ; natural = trans (∘-identityˡ 𝓓) (sym (∘-identityʳ 𝓓))
      }

    vertical : ∀ {𝓕 𝓖 𝓗 : 𝓒 ⟶ 𝓓} → 𝓖 ⟹ 𝓗 → 𝓕 ⟹ 𝓖 → 𝓕 ⟹ 𝓗
    vertical {𝓕} {𝓖} {𝓗} β α = record
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
      ; _∘_ = vertical
      }

whiskerˡ : ∀ {𝓒 𝓓 𝓔} (𝓕 : 𝓒 ⟶ 𝓓) {𝓖 𝓖′ : 𝓓 ⟶ 𝓔}
  → 𝓖     ⟹ 𝓖′
  → 𝓖 ∘ 𝓕 ⟹ 𝓖′ ∘ 𝓕
whiskerˡ 𝓕 {𝓖} {𝓖′} β = record
  { component = λ {A} → β ₍ 𝓕 ₀(A) ₎
  ; natural = natural β
  }

whiskerʳ : ∀ {𝓒 𝓓 𝓔} {𝓕 𝓕′ : 𝓒 ⟶ 𝓓} (𝓖 : 𝓓 ⟶ 𝓔)
  →     𝓕 ⟹     𝓕′
  → 𝓖 ∘ 𝓕 ⟹ 𝓖 ∘ 𝓕′
whiskerʳ {𝓕 = 𝓕} {𝓕′} 𝓖 α = record
  { component = 𝓖 ₁(α ⋆)
  ; natural = λ { {f = f} → begin
    𝓖 ₁(α ⋆) ∘ 𝓖 ₁(𝓕 ₁(f))  ≡⟨ sym $ resp-∘ 𝓖 ⟩
    𝓖 ₁(α ⋆ ∘ 𝓕 ₁(f))       ≡⟨ cong (𝓖 ₁_) $ natural α ⟩
    𝓖 ₁(𝓕′ ₁(f) ∘ α ⋆)       ≡⟨ resp-∘ 𝓖 ⟩
    𝓖 ₁(𝓕′ ₁(f)) ∘ 𝓖 ₁(α ⋆)  ∎ }
  }

horizontal : ∀ {𝓒 𝓓 𝓔} {𝓕 𝓕′ : 𝓒 ⟶ 𝓓} {𝓖 𝓖′ : 𝓓 ⟶ 𝓔}
  →     𝓕 ⟹      𝓕′
  → 𝓖     ⟹ 𝓖′
  → 𝓖 ∘ 𝓕 ⟹ 𝓖′ ∘ 𝓕′
horizontal {𝓕 = 𝓕} {𝓖′ = 𝓖′} α β = whiskerʳ 𝓖′ α ∘ whiskerˡ 𝓕 β

infixr 5 whiskerˡ whiskerʳ horizontal
syntax whiskerˡ 𝓕 β = β ∘ˡ 𝓕
syntax whiskerʳ 𝓖 α = 𝓖 ∘ʳ α
syntax horizontal α β = α * β
