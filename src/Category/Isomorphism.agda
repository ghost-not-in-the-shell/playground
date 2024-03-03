open import Category.Base
module Category.Isomorphism (𝐂 : Category) where
open import Prelude
open import Category.Solver

variable
  A B C D : Ob 𝐂
  f : Hom 𝐂 A B
  g : Hom 𝐂 B C

test1 : ∀ {A B C : Ob 𝐂} {f : Hom 𝐂 A B} {g : Hom 𝐂 B C} → (g ∘ id) ∘ f ≡ g ∘ f
test1 {f = f} {g} = begin
  (g ∘ id) ∘ f ≡⟨ unquote (∘-assoc! 𝐂) ⟩
  g ∘ f ∎

