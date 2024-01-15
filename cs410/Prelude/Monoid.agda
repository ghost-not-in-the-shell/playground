{-# OPTIONS --type-in-type #-}
module Prelude.Monoid where
open import Prelude.Equality
open import Prelude.Function

record Monoid : Set where
  infixl 5 _∙_
  field
    carrier : Set
    ε   : carrier
    _∙_ : carrier → carrier → carrier

    ∙-identityˡ : ∀ {x} → ε ∙ x ≡ x
    ∙-identityʳ : ∀ {x} → x ∙ ε ≡ x
    ∙-assoc : ∀ {x y z} → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

record Homomorphism (𝑴 𝑵 : Monoid) : Set where
  private
    module 𝑴 = Monoid 𝑴
    module 𝑵 = Monoid 𝑵
  field
    map : 𝑴.carrier → 𝑵.carrier
    resp-ε : map 𝑴.ε ≡ 𝑵.ε
    resp-∙ : ∀ {x y} → map (x 𝑴.∙ y) ≡ map x 𝑵.∙ map y

open Homomorphism public

homomorphism⁼ : ∀ {𝑴 𝑵} {𝒇 𝒈 : Homomorphism 𝑴 𝑵}
  → map 𝒇 ≡ map 𝒈
  →     𝒇 ≡     𝒈
homomorphism⁼ {𝑴} {𝑵} {𝒇} {𝒈} refl =
  lemma (          uip (resp-ε 𝒇) (resp-ε 𝒈))
        (ƛ⁼ $ ƛ⁼ $ uip (resp-∙ 𝒇) (resp-∙ 𝒈))
    where module 𝑴 = Monoid 𝑴
          module 𝑵 = Monoid 𝑵
          Resp-ε = map 𝒈 𝑴.ε ≡ 𝑵.ε
          Resp-∙ = ∀ {x y} → map 𝒈 (x 𝑴.∙ y) ≡ map 𝒈 x 𝑵.∙ map 𝒈 y

          lemma : ∀ {𝒇-resp-ε 𝒈-resp-ε : Resp-ε}
                    {𝒇-resp-∙ 𝒈-resp-∙ : Resp-∙}
                  → 𝒇-resp-ε ≡ 𝒈-resp-ε
                  → 𝒇-resp-∙ ≡ 𝒈-resp-∙ [ Resp-∙ ]
                  → record { map = map 𝒈; resp-ε = 𝒇-resp-ε; resp-∙ = 𝒇-resp-∙ }
                  ≡ record { map = map 𝒈; resp-ε = 𝒈-resp-ε; resp-∙ = 𝒈-resp-∙ }
                  [ Homomorphism 𝑴 𝑵 ]
          lemma refl refl = refl
