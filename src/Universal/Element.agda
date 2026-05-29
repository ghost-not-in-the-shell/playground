module Universal.Element where
open import Prelude
open import Category.Base
open import Functor.Base
open import Functor.Instances.Hom
open import Universal.Morphism

record Element {𝓒} (𝐹 : 𝓒 ⟶ 𝓢𝓮𝓽) : Type where
  constructor _,_
  field
    object : Ob 𝓒
  private A = object
  field
    element : ⌞ 𝐹 ₀(A) ⌟
  private u = element
  field
    {mediate} : ∀ {B} (x : ⌞ 𝐹 ₀(B) ⌟) → 𝓒 ⦅ A , B ⦆

    {commute} : ∀ {B} {x : ⌞ 𝐹 ₀(B) ⌟}
      → let x̅ = mediate x in
        (𝐹 ₁(x̅) $ u) ≡ x

    {unique} : ∀ {B} {x : ⌞ 𝐹 ₀(B) ⌟}
      → let x̅ = mediate x in
        {⁇ : 𝓒 ⦅ A , B ⦆}
      → (⁇-commute : (𝐹 ₁(⁇) $ u) ≡ x)
      → ⁇ ≡ x̅

initial→element : ∀ {𝓒 𝓓} {A : Ob 𝓒} {𝑅 : 𝓓 ⟶ 𝓒}
  → Initial A 𝑅
  → Element (𝓒 ⦅ A ,-⦆ ∘ 𝑅)
initial→element A,u = record
  { object  = object
  ; element = morphism
  ; mediate = mediate
  ; commute = commute
  ; unique  = unique
  } where open Morphism A,u

terminal→element : ∀ {𝓒 𝓓} {S : Ob 𝓓} {𝐿 : 𝓒 ⟶ 𝓓}
  → Terminal 𝐿 S
  → Element (𝓓 ⦅-, S ⦆ ∘ 𝐿 ᵒᵖ)
terminal→element = initial→element
