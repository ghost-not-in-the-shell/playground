module Category.CartesianClosed 𝓒 where
open import Prelude
open import Category.Base
open import Limit.Instances.Exponential
open import Limit.Instances.Product
open import Limit.Instances.Terminal

record CartesianClosed : Type where
  field
    ⦃ terminal     ⦄ : Terminal      𝓒
    ⦃ products     ⦄ : BinaryProduct 𝓒
    ⦃ exponentials ⦄ : Exponentials  𝓒
