module Prelude where

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

data ⊥ : Set where

record ⊤ : Set where
  constructor tt

data Bool : Set where
  false true : Bool

data Maybe (A : Set) : Set where
  nothing :     Maybe A
  just    : A → Maybe A

infixr 5 _∷_
data List (A : Set) : Set where
  []  :              List A
  _∷_ : A → List A → List A

open import Equality public
