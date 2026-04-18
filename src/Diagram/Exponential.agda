open import Diagram.Product
module Diagram.Exponential 𝓒 ⦃ _ : BinaryProduct 𝓒 ⦄ where
open import Prelude
open import Category.Base
open import Functor.Base

private instance
  _ = productOp 𝓒

record is-exponential {A B A⇒B} (ev : 𝓒 ⦅ A⇒B × A , B ⦆) : Type where
  field
    mediate : ∀ {Γ} (f : 𝓒 ⦅ Γ × A , B ⦆) → 𝓒 ⦅ Γ , A⇒B ⦆
  syntax mediate f = lam′ f
  field
    commute : ∀ {Γ} {f : 𝓒 ⦅ Γ × A , B ⦆} → ev ∘ (lam′ f ×₁ id) ≡ f
    unique  : ∀ {Γ} {f : 𝓒 ⦅ Γ × A , B ⦆}
      → {⁇ : 𝓒 ⦅ Γ , A⇒B ⦆}
      → (⁇-commute : ev ∘ (⁇ ×₁ id) ≡ f)
      → ⁇ ≡ lam′ f

  private
    app′ : ∀ {Γ} (f : 𝓒 ⦅ Γ , A⇒B ⦆) (a : 𝓒 ⦅ Γ , A ⦆) → 𝓒 ⦅ Γ , B ⦆
    app′ f a = ev ∘ < f , a >

    uncurry′ : ∀ {Γ} (f : 𝓒 ⦅ Γ , A⇒B ⦆) → 𝓒 ⦅ Γ × A , B ⦆
    uncurry′ f = ev ∘ f ×₁ id

  beta : ∀ {Γ} {f : 𝓒 ⦅ Γ × A , B ⦆} {a : 𝓒 ⦅ Γ , A ⦆}
    → app′ (lam′ f) a ≡ f ∘ < id , a >
  beta {f = f} {a} = begin
    ev ∘ < lam′ f      ,      a >   ≡⟨ - ○ cong₂ <_,_> (∘-idʳ 𝓒) (∘-idˡ 𝓒) ⟨
    ev ∘ < lam′ f ∘ id , id ∘ a >   ≡⟨ - ○ ×.×<> 𝓒 ⟨
    ev ∘(lam′ f ×₁ id ∘ < id , a >) ≡⟨ ∘-assoc 𝓒 ⟨
   (ev ∘ lam′ f ×₁ id)∘ < id , a >  ≡⟨ commute ○ - ⟩
              f       ∘ < id , a >  ∎

  eta : lam′ ev ≡ id
  eta = sym $ unique $ begin
    ev ∘ id ×₁ id ≡⟨ - ○ resp-id (×.functorial 𝓒) ⟩
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

instance
  exponentialOp : ⦃ _ : Exponentials ⦄ → ExponentialOp (Hom 𝓒)
  exponentialOp ⦃ exponential-instance exp ⦄ = record
    { _⇒_ = λ  A       B  → apex    (exp A B)
    ; ev  = λ {A = A} {B} → ev      (exp A B)
    ; lam = λ {A = A} {B} → mediate (exp A B)
    } where open Exponential

module ⇒ ⦃ (exponential-instance exp) : Exponentials ⦄ where
  module _ {A B} where
    open Exponential (exp A B) public hiding (apex; ev)

{-
  functorial : (𝓒 ᵒᵖ) × 𝓒 ⟶ 𝓒
  functorial = record
    { map₀ = λ (A , B) → A ⇒  B
    ; map₁ = λ (f , g) → f ⇒₁ g
    ; resp-id = begin
      id ⇒₁ id                  ≡⟨ refl ⟩
      lam (id ∘(ev ∘ id ×₁ id)) ≡⟨ cong lam (∘-idˡ 𝓒) ⟩
      lam (     ev ∘ id ×₁ id ) ≡⟨ unique refl ⟨
      id                        ∎
    ; resp-∘ = λ { {f = f₁ , f₂} {g₁ , g₂} → sym $ unique $ begin
      ev ∘ (g₁ ⇒₁ g₂ ∘ f₁ ⇒₁ f₂) ×₁ id ≡⟨ refl ⟩
      ev ∘(lam (g₂ ∘ ev ∘ id ×₁ g₁) ∘ f₁ ⇒₁ f₂) ×₁ id ≡⟨ refl ⟩
      ev ∘(lam (g₂ ∘ ev ∘ id ×₁ g₁) ∘ lam(f₂ ∘ ev ∘ id ×₁ f₁)) ×₁ id ≡⟨ refl ⟩
      ev ∘(lam _ ∘ lam _)×₁ id ≡⟨ - ○ cong₂ _×₁_ - (∘-idʳ 𝓒) ⟨
      ev ∘(lam _ ∘ lam _)×₁(id ∘ id) ≡⟨ - ○ resp-∘ (×.functorial 𝓒) ⟩
      ev ∘ lam _ ×₁ id ∘ lam _ ×₁ id ≡⟨ ∘-assoc 𝓒 ⟨
     (ev ∘ lam _ ×₁ id)∘ lam _ ×₁ id ≡⟨ commute ○ - ⟩
     (g₂ ∘ ev ∘ id ×₁ g₁)∘ lam(f₂ ∘ ev ∘ id ×₁ f₁) ×₁ id  ≡⟨ {!!} ⟩
      g₂ ∘ ev ∘(id ×₁ g₁ ∘ lam(f₂ ∘ ev ∘ id ×₁ f₁) ×₁ id) ≡⟨ - ○ - ○ resp-∘ (×.functorial 𝓒) ⟨
      g₂ ∘ ev ∘((id ∘ lam(f₂ ∘ ev ∘ id ×₁ f₁)) ×₁ (g₁ ∘ id)) ≡⟨ - ○ - ○ cong₂ _×₁_ (∘-idˡʳ 𝓒) (sym (∘-idˡʳ 𝓒)) ⟩
      g₂ ∘ ev ∘((lam(f₂ ∘ ev ∘ id ×₁ f₁)∘ id) ×₁ (id ∘ g₁)) ≡⟨ - ○ - ○ resp-∘ (×.functorial 𝓒) ⟩
      g₂ ∘ ev ∘(lam(f₂ ∘ ev ∘ id ×₁ f₁) ×₁ id ∘ id ×₁ g₁) ≡⟨ {!!} ⟩
      g₂ ∘(ev ∘ lam(f₂ ∘ ev ∘ id ×₁ f₁) ×₁ id)∘ id ×₁ g₁  ≡⟨ - ○ commute ○ - ⟩
      g₂ ∘         (f₂ ∘ ev ∘ id ×₁ f₁)       ∘ id ×₁ g₁ ≡⟨ {!!} ⟩
      g₂ ∘ f₂ ∘ ev ∘ (id ×₁ f₁ ∘ id ×₁ g₁) ≡⟨ {!!} ⟩
      (g₂ ∘ f₂) ∘ ev ∘ id ×₁ (f₁ ∘ g₁) ∎ }
    }
-}
