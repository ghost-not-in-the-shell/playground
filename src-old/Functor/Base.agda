module Functor.Base where
open import Prelude
open import Category.Base
open import Category.Isomorphism

record Functor (𝓒 𝓓 : Category) : Set where
  field
    map₀ : Ob 𝓒 → Ob 𝓓
    map₁ : ∀ {A B} → 𝓒 ∣ A ⟶ B → 𝓓 ∣ map₀ A ⟶ map₀ B

  private
    𝓕₀ = map₀
    𝓕₁ = map₁

  field
    resp-id : ∀ {A} → 𝓕₁(id) ≡ id₍ 𝓕₀(A) ₎
    resp-∘  : ∀ {A B C} {f : 𝓒 ∣ A ⟶ B} {g : 𝓒 ∣ B ⟶ C}
      → 𝓕₁(g ∘ f) ≡ 𝓕₁(g) ∘ 𝓕₁(f)

  resp-≅ : ∀ {A B} → A ≅ B [ 𝓒 ] → 𝓕₀(A) ≅ 𝓕₀(B) [ 𝓓 ]
  resp-≅ (-, f) = 𝓕₁ ∣ f ∣ , record
    { inverse = 𝓕₁ ∣ f ⁻¹ ∣
    ; isoˡ = begin
      𝓕₁ ∣ f ⁻¹ ∣ ∘ 𝓕₁ ∣ f ∣  ≡⟨ sym resp-∘ ⟩
      𝓕₁(∣ f ⁻¹ ∣ ∘ ∣ f ∣)    ≡⟨ cong 𝓕₁ $ isoˡ f ⟩
      𝓕₁(id)                  ≡⟨ resp-id ⟩
      id                      ∎
    ; isoʳ = begin
      𝓕₁ ∣ f ∣ ∘ 𝓕₁ ∣ f ⁻¹ ∣  ≡⟨ sym resp-∘ ⟩
      𝓕₁(∣ f ∣ ∘ ∣ f ⁻¹ ∣)    ≡⟨ cong 𝓕₁ $ isoʳ f ⟩
      𝓕₁(id)                  ≡⟨ resp-id ⟩
      id                      ∎
    }

open Functor public

infix 4 _⟶_
_⟶_ = Functor
{-# DISPLAY Functor = _⟶_ #-}

infix 6 _₀_ _₁_
_₀_ = map₀
_₁_ = map₁
{-# DISPLAY map₀ 𝓕 A = 𝓕 ₀(A) #-}
{-# DISPLAY map₁ 𝓕 f = 𝓕 ₁(f) #-}

infix 4 _≡functor_
record _≡functor_ {𝓒 𝓓} (𝓕 𝓖 : 𝓒 ⟶ 𝓓) : Set where
  constructor _,_
  field
    map₀⁼ : 𝓕 ₀_ ≡ 𝓖 ₀_
    map₁⁼ : 𝓕 ₁_ ≡ 𝓖 ₁_ [ (λ map₀ → ∀ {A B} → 𝓒 ∣ A ⟶ B → 𝓓 ∣ map₀ A ⟶ map₀ B) ↓ map₀⁼ ]

functor⁼ : ∀ {𝓒 𝓓} {𝓕 𝓖 : 𝓒 ⟶ 𝓓} → 𝓕 ≡functor 𝓖 → 𝓕 ≡ 𝓖
functor⁼ {𝓒} {𝓓} {𝓕} {𝓖} (refl , refl) =
  lemma (ƛ⁼ $                     uip (resp-id 𝓕) (resp-id 𝓖))
        (ƛ⁼ $ ƛ⁼ $ ƛ⁼ $ ƛ⁼ $ ƛ⁼ $ uip (resp-∘  𝓕) (resp-∘  𝓖))
  where
    Resp-id = ∀ {A} → 𝓖 ₁(id) ≡ id₍ 𝓖 ₀(A) ₎
    Resp-∘  = ∀ {A B C} {f : Hom 𝓒 A B} {g : Hom 𝓒 B C} → 𝓖 ₁(g ∘ f) ≡ 𝓖 ₁(g) ∘ 𝓕 ₁(f)

    lemma : ∀ {𝓕-resp-id 𝓖-resp-id : Resp-id}
              {𝓕-resp-∘  𝓖-resp-∘  : Resp-∘ }
            → 𝓕-resp-id ≡ 𝓖-resp-id [ Resp-id ]
            → 𝓕-resp-∘  ≡ 𝓖-resp-∘  [ Resp-∘  ]
            → record { map₀ = 𝓖 ₀_; map₁ = 𝓖 ₁_; resp-id = 𝓕-resp-id; resp-∘ = 𝓕-resp-∘ }
            ≡ record { map₀ = 𝓖 ₀_; map₁ = 𝓖 ₁_; resp-id = 𝓖-resp-id; resp-∘ = 𝓖-resp-∘ }
            [ 𝓒 ⟶ 𝓓 ]
    lemma refl refl = refl

private
  id' : ∀ {𝓒} → 𝓒 ⟶ 𝓒
  id' = record
    { map₀ = id
    ; map₁ = id
    ; resp-id = refl
    ; resp-∘  = refl
    }

  _∘'_ : ∀ {𝓒 𝓓 𝓔} → 𝓓 ⟶ 𝓔 → 𝓒 ⟶ 𝓓 → 𝓒 ⟶ 𝓔
  𝓖 ∘' 𝓕 = record
    { map₀ = 𝓖 ₀_ ∘ 𝓕 ₀_
    ; map₁ = 𝓖 ₁_ ∘ 𝓕 ₁_
    ; resp-id = trans (cong (𝓖 ₁_) (resp-id 𝓕)) (resp-id 𝓖)
    ; resp-∘  = trans (cong (𝓖 ₁_) (resp-∘  𝓕)) (resp-∘  𝓖)
    }

instance
  𝓒𝓪𝓽-categorical : CategoricalOp Functor
  𝓒𝓪𝓽-categorical = record
    { id  = id'
    ; _∘_ = _∘'_
    }

_ᵒᵖ' : ∀ {𝓒 𝓓} → 𝓒 ⟶ 𝓓 → 𝓒 ᵒᵖ ⟶ 𝓓 ᵒᵖ
𝓕 ᵒᵖ' = record
  { map₀ = map₀ 𝓕
  ; map₁ = map₁ 𝓕
  ; resp-id = resp-id 𝓕
  ; resp-∘  = resp-∘  𝓕
  }
