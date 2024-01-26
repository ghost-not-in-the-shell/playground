{-# OPTIONS --type-in-type #-}
module Monad.Lift where
open import Prelude renaming (refl to ≡-refl; trans to ≡-trans)
open import Preorder
open import Category
open import Category.Preorder
open import Functor.Maybe
open import Monad

data BoundedBelow {A : Set} (≤ : A → A → Set) : Maybe A → Maybe A → Set where
  bottom : ∀ {x : Maybe A}     → nothing ⟨ BoundedBelow ≤ ⟩ x
  embed  : ∀ {x y} → x ⟨ ≤ ⟩ y → just x  ⟨ BoundedBelow ≤ ⟩ just y

refl : ∀ {A : Set} {≤ : A → A → Set} → Refl ≤ → Refl (BoundedBelow ≤)
refl ≤-refl {x = nothing} = bottom
refl ≤-refl {x = just x } = embed ≤-refl

trans : ∀ {A : Set} {≤ : A → A → Set} → Trans ≤ → Trans (BoundedBelow ≤)
trans ≤-trans bottom    q         = bottom
trans ≤-trans (embed p) (embed q) = embed (≤-trans p q)

antisym : ∀ {A : Set} {≤ : A → A → Set} → Antisym ≤ → Antisym (BoundedBelow ≤)
antisym ≤-antisym {p = bottom } {bottom } = ≡-refl
antisym ≤-antisym {p = embed p} {embed q} = cong embed ≤-antisym

Lift : Preorder → Preorder
Lift 𝑷 = record
  { carrier = Maybe carrier
  ; _≤_ = BoundedBelow _≤_
  ; ≤-refl = refl ≤-refl
  ; ≤-trans = trans ≤-trans
  ; ≤-antisym = antisym ≤-antisym
  } where open Preorder.Preorder 𝑷

bounded : ∀ {A B : Set} {≤ : A → A → Set} {⊆ : B → B → Set} {f : A → B}
  → (∀ {x y} → x ⟨              ≤ ⟩ y →       f x ⟨              ⊆ ⟩       f y)
  → (∀ {x y} → x ⟨ BoundedBelow ≤ ⟩ y → maybe f x ⟨ BoundedBelow ⊆ ⟩ maybe f y)
bounded g bottom    = bottom
bounded g (embed p) = embed (g p)

lift : ∀ {𝑷 𝑸 : Preorder} → 𝓞𝓻𝓭 ∣ 𝑷 ⟶ 𝑸 → 𝓞𝓻𝓭 ∣ Lift 𝑷 ⟶ Lift 𝑸
lift 𝒇 = record
  { map      = maybe   (map      𝒇)
  ; monotone = bounded (monotone 𝒇)
  }



𝓛𝓲𝓯𝓽 : 𝓞𝓻𝓭 ⟶ 𝓞𝓻𝓭
𝓛𝓲𝓯𝓽 = record
  { map₀ = Lift
  ; map₁ = lift
  ; resp-id = {!!}
  ; resp-∘  = {!!}
  }

