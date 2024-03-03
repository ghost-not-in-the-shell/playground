{-# OPTIONS --type-in-type #-}
module Prelude.Function where
open import Prelude.Idiom.Category

Function : Set → Set → Set
Function A B = A → B

instance
  𝐒𝐞𝐭-categorical : Categorical Function
  𝐒𝐞𝐭-categorical = record
    { id  = λ x → x
    ; _∘_ = λ g f x → g (f x)
    }

private
  variable
    A B C : Set

const : A → B → A
const x = λ _ → x

flip : (A → B → C) → (B → A → C)
flip f = λ y x → f x y

infixr -1 _$_
_$_ : ∀ {P : A → Set}
  → ((x : A) → P x)
  → ((x : A) → P x)
f $ x = f x

infixl 1 _⟨_⟩_
_⟨_⟩_ : A → (A → B → C) → B → C
x ⟨ f ⟩ y = f x y
