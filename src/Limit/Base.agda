module Limit.Base {𝓙 𝓒} where
open import Prelude
open import Category.Base
open import Category.Instances.Functors
open import Functor.Base
open import Functor.Instances.Diagonal
open import Functor.Instances.Hom
open import Natural.Base
open import Universal.Morphism

Cone : (N : Ob 𝓒) (𝐷 : 𝓙 ⟶ 𝓒) → Type
Cone N 𝐷 = Δ ₀(N) ⟹ 𝐷

record Limit (𝐷 : 𝓙 ⟶ 𝓒) : Type where
  field
    apex : Ob 𝓒
  private lim = apex
  field
    proj : Cone lim 𝐷
  private π = proj
  field
    mediate : ∀ {X} (f : Cone X 𝐷) → 𝓒 ⦅ X , lim ⦆
  private <_> = mediate
  field
    commute : ∀ {X} {f : Cone X 𝐷}
      → {I : Ob 𝓙} → π ₍ I ₎ ∘ < f > ≡ f ₍ I ₎

    unique : ∀ {X} {f : Cone X 𝐷}
      → {⁇ : 𝓒 ⦅ X , lim ⦆}
      → (⁇-commute : {I : Ob 𝓙} → π ₍ I ₎ ∘ ⁇ ≡ f ₍ I ₎)
      → ⁇ ≡ < f >

lim₀ : (𝐷 : 𝓙 ⟶ 𝓒) ⦃ _ : Limit 𝐷 ⦄ → Ob 𝓒
lim₀ 𝐷 ⦃ limit ⦄ = Limit.apex limit

{-# DISPLAY Limit.apex {𝐷 = 𝐷} _ = lim₀ 𝐷 #-}

Cone₍-,_₎ : (𝐷 : 𝓙 ⟶ 𝓒) → 𝓒 ᵒᵖ ⟶ 𝓢𝓮𝓽
Cone₍-, 𝐷 ₎ = [ 𝓙 , 𝓒 ] ⦅-, 𝐷 ⦆ ∘ Δ ᵒᵖ

limit→terminal : {𝐷 : 𝓙 ⟶ 𝓒} → Limit 𝐷 → Terminal Δ 𝐷
limit→terminal limit = record
  { object   = A
  ; morphism = u
  ; mediate = mediate
  ; commute = λ {X} {f} → ext λ {I} → commute {X} {f} {I}
  ; unique  = λ {X} {f} {⁇} ⁇-commute →
                unique λ {I} → cong (_₍ I ₎) ⁇-commute
  } where open Limit limit renaming (apex to A; proj to u)

lim-iso : {𝐷 : 𝓙 ⟶ 𝓒} ⦃ _ : Limit 𝐷 ⦄ → [ 𝓒 ᵒᵖ , 𝓢𝓮𝓽 ] ⦅ 𝓒 ⦅-, lim₀ 𝐷 ⦆ ≅ Cone₍-, 𝐷 ₎ ⦆
lim-iso ⦃ limit ⦄ =
  let representable@(_ , α) = element→representable
                            $ terminal→element
                            $ limit→terminal limit
  in fwd α
  where open import Universal.Element
        open import Representable.Base
