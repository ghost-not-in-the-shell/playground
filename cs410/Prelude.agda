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

infixl 4 _◅_
data Star {A : Set} (_≤_ : A → A → Set) : A → A → Set where
  ε   : let _≤⁺_ = Star _≤_ in ∀ {x} → x ≤⁺ x
  _◅_ : let _≤⁺_ = Star _≤_ in ∀ {x y z} → x ≤ y → y ≤⁺ z → x ≤⁺ z

infixl 4 _◅◅_
_◅◅_ : ∀ {A _≤_} {x y z : A} → Star _≤_ x y → Star _≤_ y z → Star _≤_ x z
ε      ◅◅ qs = qs
p ◅ ps ◅◅ qs = p ◅ (ps ◅◅ qs)

infixr 4 _▻_
pattern _▻_ ps p = p ◅ ps

infixr 4 _▻▻_
_▻▻_ : ∀ {A _≤_} {x y z : A} → Star _≤_ y z → Star _≤_ x y → Star _≤_ x z
_▻▻_ = flip _◅◅_

gmap : ∀ {A B} {_≤_ : A → A → Set} {_⊆_ : B → B → Set} {f : A → B} →
  let _≤⁺_ = Star _≤_
      _⊆⁺_ = Star _⊆_
  in (∀ {x y} → x ≤  y → f x ⊆  f y)
   → (∀ {x y} → x ≤⁺ y → f x ⊆⁺ f y)
gmap g ε        = ε
gmap g (p ◅ ps) = g p ◅ gmap g ps

open import Equality public
