module Equivalence where
open import Agda.Primitive
open import Identity

id : ∀ {𝔞} {A : Set 𝔞} → A → A
id = λ x → x

infixl 5 _∘_
_∘_ : ∀ {𝔞 𝔟 𝔠} {A : Set 𝔞} {B : A → Set 𝔟} {C : ∀ {x} → B x → Set 𝔠}
  → (g : ∀ {x} (y : B x) → C y)
  → (f : ∀ x → B x)
  → ∀ x → C (f x)
g ∘ f = λ x → g (f x)

infix 4 _∼_
_∼_ : ∀ {𝔞 𝔟} {A : Set 𝔞} {B : A → Set 𝔟} → (∀ x → B x) → (∀ x → B x) → Set (𝔞 ⊔ 𝔟)
f ∼ g = ∀ x → f x ≡ g x

record Qinv {𝔞 𝔟} {A : Set 𝔞} {B : Set 𝔟} (f : A → B) : Set (𝔞 ⊔ 𝔟) where
  constructor [_,_,_]
  field
    g : B → A
    inverseʳ : f ∘ g ∼ id
    inverseˡ : g ∘ f ∼ id

record IsEquiv {𝔞 𝔟} {A : Set 𝔞} {B : Set 𝔟} (f : A → B) : Set (𝔞 ⊔ 𝔟) where
  constructor [_,_,_,_]
  field
    g : B → A
    h : B → A
    inverseʳ : f ∘ g ∼ id
    inverseˡ : h ∘ f ∼ id

Qinv→IsEquiv : ∀ {𝔞 𝔟} {A : Set 𝔞} {B : Set 𝔟} {f : A → B} → Qinv f → IsEquiv f
Qinv→IsEquiv [ g , α , β ] = [ g , g , α , β ]

IsEquiv→Qinv : ∀ {𝔞 𝔟} {A : Set 𝔞} {B : Set 𝔟} {f : A → B} → IsEquiv f → Qinv f
IsEquiv→Qinv {f = f} [ g , h , α , β ] = [ g , α , (λ x → γ (f x) ∙ β x) ]
  where γ : g ∼ h
        γ x = β (g x) ⁻¹ ∙ ap h (α x)

infix 4 _≃_
record _≃_ {𝔞 𝔟} (A : Set 𝔞) (B : Set 𝔟) : Set (𝔞 ⊔ 𝔟) where
  field
    f : A → B
    isequiv : IsEquiv f
