module Yoneda.Embedding where
open import Prelude
open import Category.Base
open import Category.Instances.Functors
open import Functor.Base
open import Functor.Embedding
open import Functor.Instances.Hom
import Yoneda.Base

module Covariant 𝓒 where
  module _ {A B} where
    open Yoneda.Base.Covariant 𝓒 {ℎ⁻ ₀(B)} {A} public

  private
    _ : ∀ {A B} {f : 𝓒 ⦅ A , B ⦆} → ℎ⁻ ₁ f ≡ f ↑
    _ = refl

  instance
    yoneda-embedding : is-embedding (ℎ⁻ {𝓒})
    yoneda-embedding = ↑-iso

  yoneda-principle : ∀ {A B}
    → [ 𝓒 , 𝓢𝓮𝓽 ] ⦅ ℎ⁻ ₀(A) ≅ ℎ⁻ ₀(B) ⦆
    → 𝓒 ᵒᵖ ⦅ A ≅ B ⦆
  yoneda-principle = reflect-≅ ℎ⁻
