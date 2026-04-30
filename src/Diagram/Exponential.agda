open import Diagram.Product
module Diagram.Exponential 𝓒 ⦃ _ : BinaryProduct 𝓒 ⦄ where
open import Prelude
open import Category.Base
open import Diagram.Product.Properties
open import Functor.Base
open ApplicativeReasoning

private instance
  _ = ×.productOp 𝓒

record is-exponential {A B A⇒B} (ev : 𝓒 ⦅ A⇒B × A , B ⦆) : Type where
  field
    mediate : ∀ {Γ} (f : 𝓒 ⦅ Γ × A , B ⦆) → 𝓒 ⦅ Γ , A⇒B ⦆
  syntax mediate f = ƛ′ f
  field
    commute : ∀ {Γ} {f : 𝓒 ⦅ Γ × A , B ⦆} → ev ∘ (ƛ′ f ×₁ id) ≡ f
    unique  : ∀ {Γ} {f : 𝓒 ⦅ Γ × A , B ⦆}
      → {⁇ : 𝓒 ⦅ Γ , A⇒B ⦆}
      → (⁇-commute : ev ∘ (⁇ ×₁ id) ≡ f)
      → ⁇ ≡ ƛ′ f

  private
    app′ : ∀ {Γ} (f : 𝓒 ⦅ Γ , A⇒B ⦆) (a : 𝓒 ⦅ Γ , A ⦆) → 𝓒 ⦅ Γ , B ⦆
    app′ f a = ev ∘ < f , a >

    uncurry′ : ∀ {Γ} (f : 𝓒 ⦅ Γ , A⇒B ⦆) → 𝓒 ⦅ Γ × A , B ⦆
    uncurry′ f = ev ∘ f ×₁ id

  beta : ∀ {Γ} {f : 𝓒 ⦅ Γ × A , B ⦆} {a : 𝓒 ⦅ Γ , A ⦆}
    → app′ (ƛ′ f) a ≡ f ∘ < id , a >
  beta {f = f} {a} = begin
    ev ∘ < ƛ′ f      ,      a >   ≡⟨ - ○ ⦇ < ∘-idʳ 𝓒 , ∘-idˡ 𝓒 > ⦈ ⟨
    ev ∘ < ƛ′ f ∘ id , id ∘ a >   ≡⟨ - ○ ×.×<> 𝓒 ⟨
    ev ∘(ƛ′ f ×₁ id ∘ < id , a >) ≡⟨ ∘-assoc 𝓒 ⟨
   (ev ∘ ƛ′ f ×₁ id)∘ < id , a >  ≡⟨ commute ○ - ⟩
            f       ∘ < id , a >  ∎

  eta : ƛ′ ev ≡ id
  eta = sym $ unique $ begin
    ev ∘ id ×₁ id ≡⟨ - ○ resp-id -×- ⟩
    ev ∘    id    ≡⟨ ∘-idʳ 𝓒 ⟩
    ev            ∎

record Exponential (A B : Ob 𝓒) : Type where
  field
    apex : Ob 𝓒
  private A⇒B = apex
  field
    ev : 𝓒 ⦅ A⇒B × A , B ⦆
    exponential : is-exponential ev

  open is-exponential exponential public

record Exponentials : Type where
  constructor exponential-instance
  field
    has-all-exponentials : ∀ A B → Exponential A B

module ⇒ ⦃ (exponential-instance exp) : Exponentials ⦄ where
  module _ {A B} where
    open Exponential (exp A B) public hiding (apex; ev)

  instance
    exponentialOp : ExponentialOp (Hom 𝓒)
    exponentialOp = record
      { _⇒_ = λ  A       B  → apex    (exp A B)
      ; ev  = λ {A = A} {B} → ev      (exp A B)
      ; ƛ   = λ {A = A} {B} → mediate (exp A B)
      } where open Exponential
