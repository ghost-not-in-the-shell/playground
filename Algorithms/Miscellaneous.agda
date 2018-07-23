module Algorithms.Miscellaneous where
open import Agda.Primitive     public
open import Agda.Builtin.Nat   public renaming (Nat to ℕ) hiding (_<_)
open import Agda.Builtin.Sigma public

infixr 1 _⊎_
infixr 2 _×_
infix  3 ¬_
infix  3 _↯_
infix  4 _≤ℕ_
infix  4 _≥ℕ_

flip : ∀ {𝑎 𝑏 𝑐} {A : Set 𝑎} {B : Set 𝑏} {C : A → B → Set 𝑐}
  → (∀ x y → C x y)
  → (∀ y x → C x y)
flip f = λ y x → f x y

const : ∀ {𝑎 𝑏} {A : Set 𝑎} {B : Set 𝑏}
  → B → A → B
const x = λ _ → x

data ⊥ : Set where

magic : ∀ {𝑎} {A : Set 𝑎} → ⊥ → A
magic ()

¬_ : ∀ {𝑎} → Set 𝑎 → Set 𝑎
¬ A = A → ⊥

_↯_ : ∀ {𝑎} {A : Set 𝑎} → A → ¬ A → ⊥
a ↯ ¬a = ¬a a

data _⊎_ {𝑎 𝑏} (A : Set 𝑎) (B : Set 𝑏) : Set (𝑎 ⊔ 𝑏) where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

_×_ : ∀ {𝑎 𝑏} → Set 𝑎 → Set 𝑏 → Set _
A × B = Σ A (const B)

∃ : ∀ {𝑎 𝑏} {A : Set 𝑎} (B : A → Set 𝑏) → Set (𝑎 ⊔ 𝑏)
∃ B = Σ _ B

data Maybe {𝑎} (A : Set 𝑎) : Set 𝑎 where
  nothing : Maybe A
  just    : A → Maybe A

data _≤ℕ_ : ℕ → ℕ → Set where
  zero : ∀ {n} → zero ≤ℕ n
  suc  : ∀ {m n} → m ≤ℕ n → suc m ≤ℕ suc n

_≥ℕ_ = flip _≤ℕ_

≤ℕ-total : ∀ x y → x ≤ℕ y ⊎ x ≥ℕ y
≤ℕ-total zero _       = inj₁ zero
≤ℕ-total (suc x) zero = inj₂ zero
≤ℕ-total (suc x) (suc y) with ≤ℕ-total x y
... | inj₁ x≤y = inj₁ (suc x≤y)
... | inj₂ x≥y = inj₂ (suc x≥y)

≥ℕ-total = flip ≤ℕ-total

data Dec {𝑝} (P : Set 𝑝) : Set 𝑝 where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P
