module Natural.Base where
open import Prelude
open import Category.Base
open import Functor.Base

record NaturalTransformation {𝓒 𝓓} (𝐹 𝐺 : 𝓒 ⟶ 𝓓) : Type where
  field
    component : ∀ {A} → 𝓓 ⦅ 𝐹 ₀(A) , 𝐺 ₀(A) ⦆
  private η = component
  field
    natural : ∀ {A B} {f : 𝓒 ⦅ A , B ⦆} → η ∘ 𝐹 ₁(f) ≡ 𝐺 ₁(f) ∘ η

open NaturalTransformation public

infix 4 _⟹_
_⟹_ = NaturalTransformation

private variable
  𝓒 𝓓 : Category
  𝐹 𝐺 : 𝓒 ⟶ 𝓓

instance
  natural-funlike : {𝐹 𝐺 : 𝓒 ⟶ 𝓓} → Funlike (𝐹 ⟹ 𝐺) (Ob 𝓒) λ A → 𝓓 ⦅ 𝐹 ₀(A) , 𝐺 ₀(A) ⦆
  natural-funlike = funlike-instance λ η A → η .component
