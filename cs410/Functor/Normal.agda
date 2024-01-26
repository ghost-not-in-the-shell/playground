{-# OPTIONS --type-in-type #-}
module Functor.Normal where
open import Prelude
open import Category.Base
open import Category.Set
open import Functor.Base

infix 4 _►_
record Normal : Set where
  constructor _►_
  field
    Sh   : Set
    size : Sh → ℕ

-- functorial
⟦_⟧ᴺ : Normal → Set → Set
⟦ Sh ► size ⟧ᴺ X = Σ Sh (Vec X ∘ size)

normal : ∀ {𝓕 A B} → (A → B) → (⟦ 𝓕 ⟧ᴺ A → ⟦ 𝓕 ⟧ᴺ B)
normal f (coeff , xs) = coeff , vec f xs

⟦_⟧ : Normal → 𝓢𝓮𝓽 ⟶ 𝓢𝓮𝓽
⟦ 𝓕 ⟧ = record
  { map₀ = ⟦ 𝓕 ⟧ᴺ
  ; map₁ = normal
  ; resp-id = λ⁼ λ (s , xs) → cong (s ,_) $ vec-id xs
  ; resp-∘  = λ⁼ λ (s , xs) → cong (s ,_) $ vec-∘  xs
  }

-- polynomial
varᴺ : Normal
varᴺ = ⊤ ► const 1

κᴺ : Set → Normal
κᴺ A = A ► const 0

infixr 5 _+ᴺ_
_+ᴺ_ : Normal → Normal → Normal
(Sh ► size) +ᴺ (Sh′ ► size′) = Sh + Sh′ ► [ size , size′ ]

infixr 6 _×ᴺ_
_×ᴺ_ : Normal → Normal → Normal
(Sh ► size) ×ᴺ (Sh′ ► size′) = Sh × Sh′ ► λ (s , s′) → plus (size s) (size′ s′)

infixr 5 _∘ᴺ_
_∘ᴺ_ : Normal → Normal → Normal
𝓕 ∘ᴺ (𝓖Sh ► 𝓖pow) = ⟦ 𝓕 ⟧ᴺ 𝓖Sh ► {!!}

-- categorical
_→ᴺ_ : Normal → Normal → Set
(𝓕Sh ► 𝓕size) →ᴺ 𝓖 = ∀ (s : 𝓕Sh) → ⟦ 𝓖 ⟧ᴺ (Fin (𝓕size s))

𝓝𝓸𝓻𝓶𝓪𝓵 : Category
𝓝𝓸𝓻𝓶𝓪𝓵 = record
  { Ob  = Normal
  ; Hom = _→ᴺ_
  ; op  = {!!}
  ; ∘-identityˡ = {!!}
  ; ∘-identityʳ = {!!}
  ; ∘-assoc = {!!}
  }

data Poly : Set where
  var :               Poly
  κ   : Set         → Poly
  _⊕_ : Poly → Poly → Poly
  _⊗_ : Poly → Poly → Poly

⟦_⟧ᴰ : Poly → Set → Set
⟦ var ⟧ᴰ = id
⟦ κ A ⟧ᴰ = const A
⟦ 𝓕 ⊕ 𝓖 ⟧ᴰ X = ⟦ 𝓕 ⟧ᴰ X + ⟦ 𝓖 ⟧ᴰ X
⟦ 𝓕 ⊗ 𝓖 ⟧ᴰ X = ⟦ 𝓕 ⟧ᴰ X × ⟦ 𝓖 ⟧ᴰ X

