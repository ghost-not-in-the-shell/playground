module Category.CartesianClosed.Locally 𝓒 where
open import Prelude
open import Adjoint.UnitCounit
open import Category.Base
open import Category.CartesianClosed
open import Category.Instances.Slice
open import Category.Instances.Slice.FiniteLimits 𝓒
open import Category.Instances.Slice.Iterated
open import Functor.Base
open import Limit.Instances.Exponential
open import Limit.Instances.Product
open import Limit.Instances.Pullback
open import Limit.Instances.Terminal
open import Natural.Base
open DependentSum 𝓒

record LocallyCartesianClosed : Type where
  field
    ⦃ terminal ⦄ : Terminal 𝓒

    ⦃ /cartesian-closed ⦄ : ∀ {I} → CartesianClosed (𝓒 / I)

  private instance
    /products : ∀ {I} → BinaryProduct (𝓒 / I)
    /products = CartesianClosed.products /cartesian-closed

    /exponentials : ∀ {I} → Exponentials (𝓒 / I)
    /exponentials = CartesianClosed.exponentials /cartesian-closed

    pullbacks : Pullbacks 𝓒
    pullbacks = /products→pullbacks

    /pullbacks : ∀ {I} → Pullbacks (𝓒 / I)
    /pullbacks = pullbacks→/pullbacks

    _ = ⊗.pullbackOp 𝓒

  ∑⊣* : ∀ {I J} {u : 𝓒 ⦅ I , J ⦆} → u ! ⊣ u *
  ∑⊣* {I} {J} {u} = record
    { unit = record
      { component = λ {(A , a)} → record
        { morphism = < a [ sym (∘-idʳ 𝓒) ] id >
        ; vertical = sym (⊗.commute₁ 𝓒)
        }
      ; natural = λ {(A , a) (B , b) (f , f-vertical)} → ext $ ⊗.unique₂ 𝓒
        {□ = sym (∘-assoc 𝓒)}
        (begin
          p ∘ < b □ id > ∘ f ≡⟨ ∘-assoc 𝓒 ⟨
         (p ∘ < b □ id >)∘ f ≡⟨ ⊗.commute₁ 𝓒 ○ - ⟩
                b        ∘ f ∎)
        (begin
          q ∘ < b □ id > ∘ f ≡⟨ ∘-assoc 𝓒 ⟨
         (q ∘ < b □ id >)∘ f ≡⟨ ⊗.commute₂ 𝓒 ○ - ⟩
                    id   ∘ f ≡⟨ ∘-idˡ 𝓒 ⟩
                           f ∎)
        (begin
          p ∘ < p □ f ∘ q > ∘ < a □ id > ≡⟨ ∘-assoc 𝓒 ⟨
         (p ∘ < p □ f ∘ q >)∘ < a □ id > ≡⟨ ⊗.commute₁ 𝓒 ○ - ⟩
                p           ∘ < a □ id > ≡⟨ ⊗.commute₁ 𝓒 ⟩
                                a        ≡⟨ f-vertical ⟩
                                b ∘ f    ∎)
        (begin
          q ∘ < p □ f ∘ q > ∘ < a □ id >  ≡⟨ ∘-assoc 𝓒 ⟨
         (q ∘ < p □ f ∘ q >)∘ < a □ id >  ≡⟨ ⊗.commute₂ 𝓒 ○ - ⟩
                   (f ∘ q)  ∘ < a □ id >  ≡⟨ ∘-assoc 𝓒 ⟩
                    f ∘(q   ∘ < a □ id >) ≡⟨ - ○ ⊗.commute₂ 𝓒 ⟩
                    f ∘             id    ≡⟨ ∘-idʳ 𝓒 ⟩
                    f                     ∎)
      }
    ; counit = record
      { component = λ {(A , a)} → record
        { morphism = q
        ; vertical = ⊗.square 𝓒
        }
      ; natural = λ {(A , a) (B , b) (f , f-vertical)} → ext (⊗.commute₂ 𝓒)
      }
    ; zig = λ {(A , a)} → ext (⊗.commute₂ 𝓒)
    ; zag = λ {(A , a)} → ext $ ⊗.unique₂ 𝓒
      {□ = ⊗.square 𝓒}
      (begin
        p ∘ < p □ q ∘ q > ∘ < p □ id > ≡⟨ ∘-assoc 𝓒 ⟨
       (p ∘ < p □ q ∘ q >)∘ < p □ id > ≡⟨ ⊗.commute₁ 𝓒 ○ - ⟩
              p           ∘ < p □ id > ≡⟨ ⊗.commute₁ 𝓒 ⟩
                              p        ∎)
      (begin
        q ∘ < p □ q ∘ q > ∘ < p □ id >  ≡⟨ ∘-assoc 𝓒 ⟨
       (q ∘ < p □ q ∘ q >)∘ < p □ id >  ≡⟨ ⊗.commute₂ 𝓒 ○ - ⟩
                 (q ∘ q)  ∘ < p □ id >  ≡⟨ ∘-assoc 𝓒 ⟩
                  q ∘(q   ∘ < p □ id >) ≡⟨ - ○ ⊗.commute₂ 𝓒 ⟩
                  q ∘             id    ≡⟨ ∘-idʳ 𝓒 ⟩
                  q                     ∎)
      (∘-idʳ 𝓒)
      (∘-idʳ 𝓒)
    }

  _⁎ : ∀ {I J} (u : 𝓒 ⦅ I , J ⦆) → 𝓒 / I ⟶ 𝓒 / J
  _⁎ {I} {J} u = ∏ (I , u) ∘ to-iterated (I , u)
    where open DependentProduct (𝓒 / J)

  *⊣∏ : ∀ {I J} (u : 𝓒 ⦅ I , J ⦆) → u * ⊣ u ⁎
  *⊣∏ = {!!}
