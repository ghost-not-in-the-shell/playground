{-# OPTIONS --type-in-type #-}
module Prelude.Function where
open import Prelude.Equality
open import Prelude.Op

Function : Set → Set → Set
Function A B = A → B

instance
  𝓢𝓮𝓽-categorical : CategoricalOp Function
  𝓢𝓮𝓽-categorical = record
    { id  = λ x → x
    ; _∘_ = λ g f x → g (f x)
    }

const : ∀ {A B : Set} → A → B → A
const x = λ _ → x

flip : ∀ {A₁ A₂ B : Set}
  → (A₁ → A₂ → B)
  → (A₂ → A₁ → B)
flip f = λ x₂ x₁ → f x₁ x₂

infixr -1 _$_
_$_ : ∀ {A : Set} {B : A → Set}
  → ((x : A) → B x)
  → ((x : A) → B x)
f $ x = f x

infixl 1 _⟨_⟩_
_⟨_⟩_ : ∀ {A B C : Set} → A → (A → B → C) → B → C
x ⟨ f ⟩ y = f x y

infixr 0 _-⟨_⟩-_
_-⟨_⟩-_ : ∀ {A₁ A₂ B₁ B₂ C : Set} → (A₁ → A₂) → (A₂ → B₂ → C) → (B₁ → B₂) → (A₁ → B₁ → C)
f -⟨ _*_ ⟩- g = λ x y → f x * g y
