module Jellyfish.Prelude.List where
open import Agda.Primitive
open import Jellyfish.Prelude.Dec
open import Jellyfish.Prelude.Fin
open import Jellyfish.Prelude.Function
open import Jellyfish.Prelude.Equality
open import Jellyfish.Prelude.Maybe
open import Jellyfish.Prelude.Monad
open import Jellyfish.Prelude.Nat

infixl 5 _▻_
data List {𝔞} (A : Set 𝔞) : Set 𝔞 where
  ε   : List A
  _▻_ : List A → A → List A

_▻▻_ : ∀ {𝔞} {A : Set 𝔞} → List A → List A → List A
xs ▻▻ ε        = xs
xs ▻▻ (ys ▻ y) = xs ▻▻ ys ▻ y

▻▻-assoc : ∀ {𝔞} {A : Set 𝔞} (xs ys zs : List A) → (xs ▻▻ ys) ▻▻ zs ≡ xs ▻▻ (ys ▻▻ zs)
▻▻-assoc xs ys ε = refl
▻▻-assoc xs ys (zs ▻ z) = _▻ z ⟨$⟩ ▻▻-assoc xs ys zs

infix 4 _∋_
data _∋_ {𝔞} {A : Set 𝔞} : List A → A → Set where
  ze : ∀ {xs x}            → xs ▻ x ∋ x
  su : ∀ {xs x y} → xs ∋ x → xs ▻ y ∋ x

length : ∀ {𝔞} {A : Set 𝔞} → List A → Nat
length ε        = 0
length (xs ▻ x) = suc (length xs)

lookup : ∀ {𝔞} {A : Set 𝔞} (xs : List A) → Fin (length xs) → A
lookup ε ()
lookup (xs ▻ x) zero    = x
lookup (xs ▻ x) (suc i) = lookup xs i

Fin→∋ : ∀ {𝔞} {A : Set 𝔞} {xs : List A} (i : Fin (length xs))
  → let x = lookup xs i
    in xs ∋ x
Fin→∋ {xs = ε} ()
Fin→∋ {xs = xs ▻ x} zero    = ze
Fin→∋ {xs = xs ▻ y} (suc i) = su (Fin→∋ i)

index : ∀ {𝔞} {A : Set 𝔞} ⦃ _ : Eq A ⦄ (x : A) (xs : List A) → Maybe (Fin (length xs))
index x ε = nothing
index x (xs ▻ y) with x ≟ y
... | yes _ = pure zero
... | no  _ = suc <$> index x xs

data All {𝔞 𝔭} {A : Set 𝔞} (P : A → Set 𝔭) : List A → Set 𝔭 where
  ε   : All P ε
  _▻_ : ∀ {xs x} → All P xs → P x → All P (xs ▻ x)

_▻▻▻_ : ∀ {𝔞 𝔭} {A : Set 𝔞} {P : A → Set 𝔭} {xs ys : List A}
  → All P xs → All P ys → All P (xs ▻▻ ys)
pxs ▻▻▻ ε          = pxs
pxs ▻▻▻ (pys ▻ py) = pxs ▻▻▻ pys ▻ py

find : ∀ {𝔞 𝔭} {A : Set 𝔞} {P : A → Set 𝔭} {xs} → All P xs → ∀ {x} → xs ∋ x → P x
find ε ()
find (pxs ▻ px) ze     = px
find (pxs ▻ px) (su i) = find pxs i

map : ∀ {𝔞 𝔭 𝔮} {A : Set 𝔞} {P : A → Set 𝔭} {Q : A → Set 𝔮}
  → (∀ {x}  →     P x  →     Q x )
  → (∀ {xs} → All P xs → All Q xs)
map f ε          = ε
map f (pxs ▻ px) = map f pxs ▻ f px

find-map : ∀ {𝔞 𝔭 𝔮} {A : Set 𝔞} {P : A → Set 𝔭} {Q : A → Set 𝔮} {xs x}
  → (i   : xs ∋ x)
  → (f   : ∀ {x} → P x → Q x)
  → (pxs : All P xs)
  → find (map f pxs) i ≡ f (find pxs i)
find-map ze     f (pxs ▻ px) = refl
find-map (su i) f (pxs ▻ px) = find-map i f pxs

map-resp-∘₂ : ∀ {𝔞 𝔭 𝔮 𝔯} {A : Set 𝔞} {P : A → Set 𝔭} {Q : A → Set 𝔮} {R : A → Set 𝔯} {xs}
  → {f : ∀ {x} → P x → Q x}
  → {g : ∀ {x} → Q x → R x}
  → ∀ (pxs : All P xs) → map (g ∘ f) pxs ≡ map g (map f pxs)
map-resp-∘₂ ε          = refl
map-resp-∘₂ (pxs ▻ px) = _▻ _ ⟨$⟩ map-resp-∘₂ pxs
