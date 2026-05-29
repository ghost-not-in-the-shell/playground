module Category.Instances.Slice.Iterated {𝓒} where
open import Prelude
open import Adjoint.UnitCounit
open import Category.Base
open import Category.Instances.Slice
open import Functor.Base

to-iterated : {Γ : Ob 𝓒} (A@(Γ⨾A , π) : 𝓒 / Γ -Ob) → 𝓒 / Γ⨾A ⟶ (𝓒 / Γ) / A
to-iterated {Γ} A@(Γ⨾A , πA) =
  let ∑A : (B : 𝓒 / Γ⨾A -Ob) → (𝓒 / Γ) / A -Ob
      ∑A (Γ⨾A⨾B , πB) = (Γ⨾A⨾B , πA ∘ πB) , (πB , refl)

      map∑ : ∀ {X Y} → 𝓒 / Γ⨾A -⦅ X , Y ⦆ → (𝓒 / Γ) / A -⦅ ∑A X , ∑A Y ⦆
      map∑ {(Γ⨾A⨾X , πX)} {(Γ⨾A⨾Y , πY)} (f , f-vertical) = record
        { morphism = record
          { morphism = f
          ; vertical = begin
              πA ∘ πX      ≡⟨ - ○ f-vertical ⟩
              πA ∘(πY ∘ f) ≡⟨ ∘-assoc 𝓒 ⟨
             (πA ∘ πY)∘ f  ∎
          }
        ; vertical = ext f-vertical
        }
  in record
  { map₀ = ∑A
  ; map₁ = map∑
  ; resp-id = ext refl
  ; resp-∘  = ext refl
  }

from-iterated : {Γ : Ob 𝓒} (A@(Γ⨾A , π) : 𝓒 / Γ -Ob) → (𝓒 / Γ) / A ⟶ 𝓒 / Γ⨾A
from-iterated (Γ⨾A , πA) = record
  { map₀ = λ ((Γ⨾A⨾B , πA∘πB) , (πB , vertical)) → (Γ⨾A⨾B , πB)
  ; map₁ = λ (f , f-vertical) → record
    { morphism =      fst f
    ; vertical = cong fst f-vertical
    }
  ; resp-id = ext refl
  ; resp-∘  = ext refl
  }

from⊣to : ∀ {Γ} (A : 𝓒 / Γ -Ob) → from-iterated A ⊣ to-iterated A
from⊣to (Γ⨾A , πA) = record
  { unit = record
    { component = λ {((Γ⨾A⨾B , πA∘πB) , (πB , vertical))} → record
      { morphism = record
        { morphism = id
        ; vertical = begin
            πA∘πB        ≡⟨ vertical ⟩
            πA ∘ πB      ≡⟨ ∘-idʳ 𝓒 ⟨
           (πA ∘ πB)∘ id ∎
        }
      ; vertical = ext (sym (∘-idʳ 𝓒))
      }
    ; natural = ext (∘-idˡʳ 𝓒)
    }
  ; counit = record
    { component = λ {(Γ⨾A⨾B , πA∘πB)} → record
      { morphism = id
      ; vertical = sym (∘-idʳ 𝓒)
      }
    ; natural = ext (∘-idˡʳ 𝓒)
    }
  ; zig = ext (∘-idˡ 𝓒)
  ; zag = ext (∘-idˡ 𝓒)
  }
