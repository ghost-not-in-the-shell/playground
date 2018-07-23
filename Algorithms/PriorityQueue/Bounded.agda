open import Algorithms.TotalOrder
module Algorithms.PriorityQueue.Bounded {𝑎 ℓ} (⟨A,≤⟩ : TotalOrder 𝑎 ℓ) where
open TotalOrder ⟨A,≤⟩ renaming (Carrier to A)
open import Algorithms.Equality
open import Algorithms.Miscellaneous

infix 4 _≤⁺_
infix 4 _≥⁺_

data A⁺ : Set 𝑎 where
  ∞  : A⁺
  _⁺ : A → A⁺

data _≤⁺_ : A⁺ → A⁺ → Set ℓ where
  ∞  : ∀ {x⁺}          → x⁺  ≤⁺ ∞
  _⁺ : ∀ {x y} → x ≤ y → x ⁺ ≤⁺ y ⁺

pattern ∞̸ = _ ⁺

_≥⁺_ = flip _≤⁺_

reflexive⁺ : ∀ {x⁺} → x⁺ ≤⁺ x⁺
reflexive⁺ {∞} = ∞
reflexive⁺ {∞̸} = reflexive ⁺

antisym⁺ : ∀ {x⁺ y⁺} → x⁺ ≤⁺ y⁺ → x⁺ ≥⁺ y⁺ → x⁺ ≡ y⁺
antisym⁺ ∞ ∞ = refl
antisym⁺ (x<y ⁺) (x>y ⁺) = _⁺ ⟨$⟩ antisym x<y x>y

trans⁺ : ∀ {x⁺ y⁺ z⁺} → x⁺ ≤⁺ y⁺ → y⁺ ≤⁺ z⁺ → x⁺ ≤⁺ z⁺
trans⁺ ∞ ∞ = ∞
trans⁺ ∞̸ ∞ = ∞
trans⁺ (x<y ⁺) (y<z ⁺) = (trans x<y y<z)⁺

total⁺ : ∀ x⁺ y⁺ → x⁺ ≤⁺ y⁺ ⊎ x⁺ ≥⁺ y⁺
total⁺ ∞ ∞ = inj₁ ∞
total⁺ ∞ ∞̸ = inj₂ ∞
total⁺ ∞̸ ∞ = inj₁ ∞
total⁺ (x ⁺) (y ⁺) with total x y
... | inj₁ x≤y = inj₁ (x≤y ⁺)
... | inj₂ x≥y = inj₂ (x≥y ⁺)

⟨A⁺,≤⁺⟩ : TotalOrder 𝑎 ℓ
⟨A⁺,≤⁺⟩ = record
  { Carrier   = A⁺
  ; _≤_       = _≤⁺_
  ; reflexive = reflexive⁺
  ; antisym   = antisym⁺
  ; trans     = trans⁺
  ; total     = total⁺
  }

open TotalOrder ⟨A⁺,≤⁺⟩ using () public renaming
  ( min   to min⁺
  ; ⟨_,_⟩ to ⟨_,_⟩⁺
  )
