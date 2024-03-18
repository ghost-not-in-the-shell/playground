{-# OPTIONS --type-in-type #-}
module Prelude.Monoid where
open import Prelude.Equality
open import Prelude.Function
open import Prelude.Op

record Monoid : Set where
  infixl 5 _*_
  field
    Carrier : Set
    ε   : Carrier
    _*_ : Carrier → Carrier → Carrier

    *-identityˡ : ∀ {x} → ε * x ≡ x
    *-identityʳ : ∀ {x} → x * ε ≡ x
    *-assoc : ∀ {x y z} → (x * y) * z ≡ x * (y * z)

record Homomorphism (𝑴 𝑵 : Monoid) : Set where
  private
    module 𝑴 = Monoid 𝑴
    module 𝑵 = Monoid 𝑵
  field
    map : 𝑴.Carrier → 𝑵.Carrier
    resp-ε : map 𝑴.ε ≡ 𝑵.ε
    resp-* : ∀ {x y} → map (x 𝑴.* y) ≡ map x 𝑵.* map y

open Homomorphism public

homomorphism⁼ : ∀ {𝑴 𝑵} {𝒇 𝒈 : Homomorphism 𝑴 𝑵}
  → map 𝒇 ≡ map 𝒈
  →     𝒇 ≡     𝒈
homomorphism⁼ {𝑴} {𝑵} {𝒇} {𝒈} refl =
  lemma (          uip (resp-ε 𝒇) (resp-ε 𝒈))
        (ƛ⁼ $ ƛ⁼ $ uip (resp-* 𝒇) (resp-* 𝒈))
    where module 𝑴 = Monoid 𝑴
          module 𝑵 = Monoid 𝑵
          Resp-ε = map 𝒈 𝑴.ε ≡ 𝑵.ε
          Resp-* = ∀ {x y} → map 𝒈 (x 𝑴.* y) ≡ map 𝒈 x 𝑵.* map 𝒈 y

          lemma : ∀ {𝒇-resp-ε 𝒈-resp-ε : Resp-ε}
                    {𝒇-resp-* 𝒈-resp-* : Resp-*}
                  → 𝒇-resp-ε ≡ 𝒈-resp-ε
                  → 𝒇-resp-* ≡ 𝒈-resp-* [ Resp-* ]
                  → record { map = map 𝒈; resp-ε = 𝒇-resp-ε; resp-* = 𝒇-resp-* }
                  ≡ record { map = map 𝒈; resp-ε = 𝒈-resp-ε; resp-* = 𝒈-resp-* }
                  [ Homomorphism 𝑴 𝑵 ]
          lemma refl refl = refl

𝓜𝓸𝓷-categorical : CategoricalOp Homomorphism
𝓜𝓸𝓷-categorical = record
  { id = record
    { map = id
    ; resp-ε = refl
    ; resp-* = refl
    }
  ; _∘_ = λ 𝒈 𝒇 → record
    { map = map 𝒈 ∘ map 𝒇
    ; resp-ε = trans (cong (map 𝒈) (resp-ε 𝒇)) (resp-ε 𝒈)
    ; resp-* = trans (cong (map 𝒈) (resp-* 𝒇)) (resp-* 𝒈)        }
  }

{-
record Action (𝑴 : Monoid) : Set where
  open Monoid 𝑴 renaming (Carrier to M)
  field
    Carrier : Set

  private
    X = Carrier

  field
    transform : M → X → X

    resp-ε : ∀ {x} → transform ε x ≡ x
    resp-* : ∀ {s t x} → transform s (transform t x) ≡ transform (s * t) x

open Action public hiding (Carrier)

_-Act = Action

_₍_₎_ : ∀ {𝑴} (𝑻 : 𝑴 -Act) → Monoid.Carrier 𝑴 → Action.Carrier 𝑻 → Action.Carrier 𝑻
𝑻 ₍ m ₎ x = transform 𝑻 m x

record -Hom 𝑴 (𝑭 𝑮 : 𝑴 -Act) : Set where
  private
    module 𝑴 = Monoid 𝑴
    module 𝑭 = Action 𝑭
    module 𝑮 = Action 𝑮
  field
    map : 𝑭.Carrier → 𝑮.Carrier

    resp-transform : ∀ {m x} → map (𝑭 ₍ m ₎ x) ≡ 𝑮 ₍ m ₎ (map x)
-}
