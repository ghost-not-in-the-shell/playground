module Category.Instances.Slice.Iterated {𝓒} where
open import Prelude
open import Category.Base
open import Category.Instances.Slice
open import Functor.Base

to-iterated : {Γ : Ob 𝓒} (A@(Γ⨾A , π) : 𝓒 / Γ -Ob) → 𝓒 / Γ⨾A ⟶ (𝓒 / Γ) / A
to-iterated (Γ⨾A , πA) = record
  { map₀ = λ  B@(Γ⨾A⨾B , πB) → (Γ⨾A⨾B , πA ∘ πB) , (πB , refl)
  ; map₁ = λ {B@(Γ⨾A⨾B , πB)} {B′@(Γ⨾A⨾B′ , πB′)} (f , f-vertical) → record
    { morphism = record
      { morphism = f
      ; vertical = begin
        πA ∘ πB       ≡⟨ - ○ f-vertical ⟩
        πA ∘(πB′ ∘ f) ≡⟨ ∘-assoc 𝓒 ⟨
       (πA ∘ πB′)∘ f  ∎
      }
    ; vertical = ext f-vertical
    }
  ; resp-id = ext refl
  ; resp-∘  = ext refl
  }

from-iterated : {Γ : Ob 𝓒} (A@(Γ⨾A , π) : 𝓒 / Γ -Ob) → (𝓒 / Γ) / A ⟶ 𝓒 / Γ⨾A
from-iterated (Γ⨾A , πA) = record
  { map₀ = λ (B , πB) → fst B , fst πB
  ; map₁ = λ (f , f-vertical) → record
    { morphism =      fst f
    ; vertical = cong fst f-vertical
    }
  ; resp-id = ext refl
  ; resp-∘  = ext refl
  }
