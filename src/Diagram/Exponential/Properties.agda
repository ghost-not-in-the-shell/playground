open import Diagram.Product
module Diagram.Exponential.Properties {𝓒} ⦃ _ : BinaryProduct 𝓒 ⦄ where
open import Prelude
open import Category.Base
open import Diagram.Product.Properties
open import Diagram.Exponential
open ApplicativeReasoning

module _ ⦃ _ : Exponentials 𝓒 ⦄ where
  open import Functor.Base

  private instance _ = ×.productOp     𝓒
  private instance _ = ⇒.exponentialOp 𝓒

  _⇒- : Ob (𝓒 ᵒᵖ) → 𝓒 ⟶ 𝓒
  X ⇒- = record
    { map₀ = λ A → X ⇒ A
    ; map₁ = λ g → ƛ (g ∘ ev)
    ; resp-id = sym $ ⇒.unique 𝓒 $
      begin
        ev ∘ id ×₁ id ≡⟨ - ○ resp-id -×- ⟩
        ev ∘ id       ≡⟨ ∘-idˡʳ 𝓒 ⟨
        id ∘ ev ∎
    ; resp-∘ = λ {f = f} {g} → sym $ ⇒.unique 𝓒 $
      begin
        ev ∘(ƛ(g ∘ ev)∘ ƛ(f ∘ ev))×₁ id       ≡⟨ - ○ ⦇ - ×₁ ∘-idʳ 𝓒 ⦈ ⟨
        ev ∘(ƛ(g ∘ ev)∘ ƛ(f ∘ ev))×₁(id ∘ id) ≡⟨ - ○ resp-∘ -×- ⟩
        ev ∘(ƛ(g ∘ ev)×₁ id ∘ ƛ(f ∘ ev)×₁ id) ≡⟨ ∘-assoc 𝓒 ⟨
       (ev ∘ ƛ(g ∘ ev)×₁ id)∘ ƛ(f ∘ ev)×₁ id  ≡⟨ ⇒.commute 𝓒 ○ - ⟩
              (g ∘ ev)      ∘ ƛ(f ∘ ev)×₁ id  ≡⟨ ∘-assoc 𝓒 ⟩
               g ∘(ev       ∘ ƛ(f ∘ ev)×₁ id) ≡⟨ - ○ ⇒.commute 𝓒 ⟩
               g ∘             (f ∘ ev)       ≡⟨ ∘-assoc 𝓒 ⟨
              (g ∘              f)∘ ev        ∎
    }

  -⇒_ : Ob 𝓒 → 𝓒 ᵒᵖ ⟶ 𝓒
  -⇒ X = record
    { map₀ = λ A → A ⇒ X
    ; map₁ = λ f → ƛ (ev ∘ id ×₁ f)
    ; resp-id = sym $ ⇒.unique 𝓒 refl
    ; resp-∘ = λ {f = f} {g} → sym $ ⇒.unique 𝓒 $
      begin
        ev ∘(ƛ(ev ∘ id ×₁ g) ∘ ƛ(ev ∘ id ×₁ f)) ×₁ id       ≡⟨ - ○ ⦇ - ×₁ ∘-idʳ 𝓒 ⦈ ⟨
        ev ∘(ƛ(ev ∘ id ×₁ g) ∘ ƛ(ev ∘ id ×₁ f)) ×₁(id ∘ id) ≡⟨ - ○ resp-∘ -×- ⟩
        ev ∘ ƛ(ev ∘ id ×₁ g) ×₁ id ∘ ƛ(ev ∘ id ×₁ f) ×₁ id  ≡⟨ ∘-assoc 𝓒 ⟨
       (ev ∘ ƛ(ev ∘ id ×₁ g) ×₁ id)∘ ƛ(ev ∘ id ×₁ f) ×₁ id  ≡⟨ ⇒.commute 𝓒 ○ - ⟩
              (ev ∘ id ×₁ g)       ∘ ƛ(ev ∘ id ×₁ f) ×₁ id  ≡⟨ ∘-assoc 𝓒 ⟩
               ev ∘ id ×₁ g        ∘ ƛ(ev ∘ id ×₁ f) ×₁ id  ≡⟨ - ○ ×-comm ⟨
               ev ∘ ƛ(ev ∘ id ×₁ f) ×₁ id  ∘ id ×₁ g        ≡⟨ ∘-assoc 𝓒 ⟨
              (ev ∘ ƛ(ev ∘ id ×₁ f) ×₁ id) ∘ id ×₁ g        ≡⟨ ⇒.commute 𝓒 ○ - ⟩
                     (ev ∘ id ×₁ f)        ∘ id ×₁ g        ≡⟨ ∘-assoc 𝓒 ⟩
                      ev ∘ id ×₁ f         ∘ id ×₁ g        ≡⟨ - ○ resp-∘ -×- ⟨
                      ev ∘ (id ∘ id) ×₁ (f ∘ g)             ≡⟨ - ○ ⦇ ∘-idʳ 𝓒 ×₁ - ⦈ ⟩
                      ev ∘  id       ×₁ (f ∘ g)             ∎
    } where
      ×-comm : ∀ {A₁ A₂ B₁ B₂} {f₁ : 𝓒 ⦅ A₁ , B₁ ⦆} {f₂ : 𝓒 ⦅ A₂ , B₂ ⦆}
        → f₁ ×₁ id ∘ id ×₁ f₂ ≡ id ×₁ f₂ ∘ f₁ ×₁ id
      ×-comm {f₁ = f₁} {f₂} = begin
        f₁ ×₁ id ∘  id ×₁ f₂  ≡⟨ resp-∘ -×- ⟨
       (f₁ ∘  id)×₁(id ∘  f₂) ≡⟨ ⦇ sym (∘-idˡʳ 𝓒) ×₁ ∘-idˡʳ 𝓒 ⦈ ⟩
       (id ∘  f₁)×₁(f₂ ∘  id) ≡⟨ resp-∘ -×- ⟩
        id ×₁ f₂ ∘  f₁ ×₁ id ∎

  open import Category.Slice
  open import Diagram.Pullback
  open import Diagram.Terminal

  ∏ : ⦃ _ : Terminal 𝓒 ⦄ ⦃ _ : Pullbacks 𝓒 ⦄ (A : Ob 𝓒) → 𝓒 / A ⟶ 𝓒
  ∏ A =
    let instance
          _ = 𝟙.terminalOp 𝓒
          _ = ⊗.pullbackOp 𝓒
    in record
    { map₀ = λ (A⨾B , πB) → 𝟙 ⊗₍ ƛ π₂ , ƛ (πB ∘ ev) ₎ (A ⇒ A⨾B)
    ; map₁ = λ {(A⨾B , πB)} {(A⨾B⨾C , πB∘πC)} (c , c-section) →
      let □ : ƛ π₂ ∘ p ≡ ƛ (πB∘πC ∘ ev) ∘ (ƛ (c ∘ ev) ∘ q)
          □ = begin
            ƛ  π₂                     ∘ p ≡⟨ ⊗.square 𝓒 ⟩
            ƛ( πB        ∘ ev)        ∘ q ≡⟨ ⦇ ƛ (c-section ○ -) ⦈ ○ - ⟩
            ƛ((πB∘πC ∘ c)∘ ev)        ∘ q ≡⟨ resp-∘ (A ⇒-) ○ - ⟩
           (ƛ(πB∘πC ∘ ev) ∘ ƛ(c ∘ ev))∘ q ≡⟨ ∘-assoc 𝓒 ⟩
            ƛ(πB∘πC ∘ ev) ∘ ƛ(c ∘ ev) ∘ q ∎
      in < p [ □ ] ƛ (c ∘ ev) ∘ q >
    ; resp-id = sym $ ⊗.unique 𝓒 (𝟙.unique₂ 𝓒) $
      begin
          q        ∘ id ≡⟨ ∘-idˡʳ 𝓒 ⟨
          id       ∘ q  ≡⟨ resp-id (A ⇒-) ○ - ⟨
        ƛ(id ∘ ev) ∘ q  ∎
    ; resp-∘ = λ { {f = c , _} {d , _} → sym $ ⊗.unique 𝓒 (𝟙.unique₂ 𝓒) $
      begin
        q ∘ < p [] ƛ(d ∘ ev)∘ q > ∘ < p [] ƛ(c ∘ ev) ∘ q > ≡⟨ ∘-assoc 𝓒 ⟨
       (q ∘ < p [] ƛ(d ∘ ev)∘ q >)∘ < p [] ƛ(c ∘ ev) ∘ q > ≡⟨ ⊗.commute₂ 𝓒 ○ - ⟩
                  (ƛ(d ∘ ev)∘ q)  ∘ < p [] ƛ(c ∘ ev) ∘ q > ≡⟨ ∘-assoc 𝓒 ⟩
                   ƛ(d ∘ ev)∘ q   ∘ < p [] ƛ(c ∘ ev) ∘ q > ≡⟨ - ○ ⊗.commute₂ 𝓒 ⟩
                   ƛ(d ∘ ev)∘              ƛ(c ∘ ev) ∘ q   ≡⟨ ∘-assoc 𝓒 ⟨
                  (ƛ(d ∘ ev)∘              ƛ(c ∘ ev))∘ q   ≡⟨ resp-∘ (A ⇒-) ○ - ⟨
                   ƛ((d ∘ c)∘ ev)                    ∘ q   ∎ }
    }
