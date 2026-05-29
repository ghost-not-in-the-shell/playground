module Functor.Equiv {𝓒 𝓓} where
open import Prelude
open import Category.Base
open import Category.Instances.Functors
open import Functor.Base
open import Natural.Base
open import Adjoint.UnitCounit

record is-equiv (𝐹 : 𝓒 ⟶ 𝓓) : Type where
  field
    bwd : 𝓓 ⟶ 𝓒
  private 𝐹⁻¹ = bwd
  field
    unit≅   : [ 𝓒 , 𝓒 ] ⦅ id ≅ 𝐹⁻¹ ∘ 𝐹 ⦆
    counit≅ : [ 𝓓 , 𝓓 ] ⦅ 𝐹 ∘ 𝐹⁻¹ ≅ id ⦆
