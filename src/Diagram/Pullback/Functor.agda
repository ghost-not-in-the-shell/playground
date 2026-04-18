open import Diagram.Pullback
module Diagram.Pullback.Functor 𝓒 ⦃ _ : Pullbacks 𝓒 ⦄ where
open import Prelude
open import Category.Base
open import Category.Slice
open import Functor.Base

private instance
  _ = pullbackOp 𝓒

_* : ∀ {I J} → 𝓒 ᵒᵖ ⦅ I , J ⦆ → 𝓒 / I ⟶ 𝓒 / J
_* {I} {J} u = record
  { map₀ = λ (A , a) → J ⊗₍ u , a ₎ A , p
  ; map₁ = λ {(A , a)} {(B , b)} (f , f-vertical) →
    let □ : u ∘ p ≡ b ∘ (f ∘ q)
        □ = begin
          u     ∘ p  ≡⟨ ⊗.square 𝓒 ⟩
          a     ∘ q  ≡⟨ f-vertical ○ - ⟩
         (b ∘ f)∘ q  ≡⟨ ∘-assoc 𝓒 ⟩
          b ∘(f ∘ q) ∎
    in record
      { morphism = < p [ □ ] f ∘ q >
      ; vertical = sym (⊗.commute₁ 𝓒)
      }
  ; resp-id = ext $ sym $ ⊗.unique 𝓒 (∘-idʳ 𝓒) (sym (∘-idˡʳ 𝓒))
  ; resp-∘ = λ {(A , a)} {(B , b)} {(C , c)} {(f , f-vertical)} {(g , g-vertical)} →
    ext $ sym $ ⊗.unique 𝓒
      (begin
        p ∘(< p [] g ∘ q > ∘ < p [] f ∘ q >) ≡⟨ ∘-assoc 𝓒 ⟨
       (p ∘ < p [] g ∘ q >)∘ < p [] f ∘ q >  ≡⟨ ⊗.commute₁ 𝓒 ○ - ⟩
              p            ∘ < p [] f ∘ q >  ≡⟨ ⊗.commute₁ 𝓒 ⟩
                               p             ∎)
      (begin
        q ∘(< p [] g ∘ q > ∘ < p [] f ∘ q >) ≡⟨ ∘-assoc 𝓒 ⟨
       (q ∘ < p [] g ∘ q >)∘ < p [] f ∘ q >  ≡⟨ ⊗.commute₂ 𝓒 ○ - ⟩
                  (g ∘ q)  ∘ < p [] f ∘ q >  ≡⟨ ∘-assoc 𝓒 ⟩
                   g ∘(q   ∘ < p [] f ∘ q >) ≡⟨ - ○ ⊗.commute₂ 𝓒 ⟩
                   g ∘             (f ∘ q)   ≡⟨ ∘-assoc 𝓒 ⟨
                  (g ∘              f)∘ q    ∎)
  }
