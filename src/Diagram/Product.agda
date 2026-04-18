module Diagram.Product 𝓒 where
open import Prelude
open import Category.Base
open import Functor.Base

record is-product {A B A×B} (π₁ : 𝓒 ⦅ A×B , A ⦆) (π₂ : 𝓒 ⦅ A×B , B ⦆) : Type where
  field
    mediate : ∀ {X} (f : 𝓒 ⦅ X , A ⦆) (g : 𝓒 ⦅ X , B ⦆) → 𝓒 ⦅ X , A×B ⦆
  syntax mediate f g = < f , g >′
  field
    commute₁ : ∀ {X} {f : 𝓒 ⦅ X , A ⦆} {g : 𝓒 ⦅ X , B ⦆}
      → π₁ ∘ < f , g >′ ≡ f
    commute₂ : ∀ {X} {f : 𝓒 ⦅ X , A ⦆} {g : 𝓒 ⦅ X , B ⦆}
      → π₂ ∘ < f , g >′ ≡ g
    unique : ∀ {X} {f : 𝓒 ⦅ X , A ⦆} {g : 𝓒 ⦅ X , B ⦆}
      → {⁇ : 𝓒 ⦅ X , A×B ⦆}
      → (⁇-commute₁ : π₁ ∘ ⁇ ≡ f)
      → (⁇-commute₂ : π₂ ∘ ⁇ ≡ g)
      → ⁇ ≡ < f , g >′

  <>∘ : ∀ {X Y} {g₁ : 𝓒 ⦅ Y , A ⦆} {g₂ : 𝓒 ⦅ Y , B ⦆} {f : 𝓒 ⦅ X , Y ⦆}
    → < g₁ , g₂ >′ ∘ f ≡ < g₁ ∘ f , g₂ ∘ f >′
  <>∘ {g₁ = g₁} {g₂} {f} = unique
    (begin
      π₁ ∘(< g₁ , g₂ >′ ∘ f) ≡⟨ ∘-assoc 𝓒 ⟨
     (π₁ ∘ < g₁ , g₂ >′)∘ f  ≡⟨ commute₁ ○ - ⟩
             g₁         ∘ f  ∎)
    (begin
      π₂ ∘(< g₁ , g₂ >′ ∘ f) ≡⟨ ∘-assoc 𝓒 ⟨
     (π₂ ∘ < g₁ , g₂ >′)∘ f  ≡⟨ commute₂ ○ - ⟩
                  g₂    ∘ f  ∎)

  eta : < π₁ , π₂ >′ ≡ id
  eta = sym $ unique (∘-idʳ 𝓒) (∘-idʳ 𝓒)

record Product (A B : Ob 𝓒) : Type where
  field
    apex : Ob 𝓒
    π₁ : 𝓒 ⦅ apex , A ⦆
    π₂ : 𝓒 ⦅ apex , B ⦆
    product : is-product π₁ π₂

  open is-product product public

record BinaryProduct : Type where
  constructor product-instance
  field
    has-all-products : ∀ A B → Product A B

productOp : ⦃ _ : BinaryProduct ⦄ → ProductOp (Hom 𝓒)
productOp ⦃ product-instance prod ⦄ = record
  { _×_   = λ  A   B  → apex    (prod A B)
  ; π₁    = λ {A} {B} → π₁      (prod A B)
  ; π₂    = λ {A} {B} → π₂      (prod A B)
  ; <_,_> = λ {A} {B} → mediate (prod A B)
  } where open Product

module × ⦃ (product-instance prod) : BinaryProduct ⦄ where
  module _ {A B} where
    open Product (prod A B) public hiding (apex; π₁; π₂)

  private instance
    _ = productOp

  ×<> : ∀ {A B₁ B₂ C₁ C₂}
    → {f₁ : 𝓒 ⦅ A , B₁ ⦆} {g₁ : 𝓒 ⦅ B₁ , C₁ ⦆}
    → {f₂ : 𝓒 ⦅ A , B₂ ⦆} {g₂ : 𝓒 ⦅ B₂ , C₂ ⦆}
    → (g₁ ×₁ g₂) ∘ < f₁ , f₂ > ≡ < g₁ ∘ f₁ , g₂ ∘ f₂ >
  ×<> {f₁ = f₁} {g₁} {f₂} {g₂} = unique
    (begin
      π₁ ∘(g₁ ×₁ g₂ ∘ < f₁ , f₂ >) ≡⟨ ∘-assoc 𝓒 ⟨
     (π₁ ∘ g₁ ×₁ g₂)∘ < f₁ , f₂ >  ≡⟨ commute₁ ○ - ⟩
          (g₁ ∘  π₁)∘ < f₁ , f₂ >  ≡⟨ ∘-assoc 𝓒 ⟩
           g₁ ∘ (π₁ ∘ < f₁ , f₂ >) ≡⟨ - ○ commute₁ ⟩
           g₁       ∘   f₁         ∎)
    (begin
      π₂ ∘(g₁ ×₁ g₂ ∘ < f₁ , f₂ >) ≡⟨ ∘-assoc 𝓒 ⟨
     (π₂ ∘ g₁ ×₁ g₂)∘ < f₁ , f₂ >  ≡⟨ commute₂ ○ - ⟩
          (g₂ ∘  π₂)∘ < f₁ , f₂ >  ≡⟨ ∘-assoc 𝓒 ⟩
           g₂ ∘ (π₂ ∘ < f₁ , f₂ >) ≡⟨ - ○ commute₂ ⟩
           g₂       ∘        f₂    ∎)

  swap<> : ∀ {A B X} {f : 𝓒 ⦅ X , A ⦆} {g : 𝓒 ⦅ X , B ⦆} → swap ∘ < f , g > ≡ < g , f >
  swap<> {f = f} {g} = unique
    (begin
      π₁ ∘(< π₂ , π₁ > ∘ < f , g >) ≡⟨ ∘-assoc 𝓒 ⟨
     (π₁ ∘ < π₂ , π₁ >)∘ < f , g >  ≡⟨ commute₁ ○ - ⟩
             π₂        ∘ < f , g >  ≡⟨ commute₂ ⟩
                               g    ∎)
    (begin
      π₂ ∘(< π₂ , π₁ > ∘ < f , g >) ≡⟨ ∘-assoc 𝓒 ⟨
     (π₂ ∘ < π₂ , π₁ >)∘ < f , g >  ≡⟨ commute₂ ○ - ⟩
                  π₁   ∘ < f , g >  ≡⟨ commute₁ ⟩
                           f        ∎)

  functorial : 𝓒 × 𝓒 ⟶ 𝓒
  functorial = record
    { map₀ = λ (A , B) → A ×  B
    ; map₁ = λ (f , g) → f ×₁ g
    ; resp-id = begin
      < id ∘ π₁ , id ∘ π₂ > ≡⟨ cong₂ <_,_> (∘-idˡ 𝓒) (∘-idˡ 𝓒) ⟩
      <      π₁ ,      π₂ > ≡⟨ eta ⟩
                id          ∎
    ; resp-∘  = λ { {f = (f₁ , f₂)} {(g₁ , g₂)} → begin
      (g₁ ∘  f₁) ×₁(g₂ ∘  f₂)         ≡⟨ refl ⟩
      <(g₁ ∘ f₁)∘ π₁ ,(g₂ ∘ f₂)∘ π₂ > ≡⟨ cong₂ <_,_> (∘-assoc 𝓒) (∘-assoc 𝓒) ⟩
      < g₁ ∘(f₁ ∘ π₁), g₂ ∘(f₂ ∘ π₂)> ≡⟨ ×<> ⟨
      (g₁ ×₁ g₂) ∘ (f₁ ×₁ f₂)         ∎ }
    }
