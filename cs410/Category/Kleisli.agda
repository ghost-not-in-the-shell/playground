open import Category
open import Monad
module Category.Kleisli {𝓒 : Category} {𝓜 : 𝓒 ⟶ 𝓒} (ℳ : Monad 𝓜) where
open import Prelude
open import Solver
open import Category.Category

private instance
  𝓜-monadic = monadic ℳ

𝓚𝓵𝓮𝓲𝓼𝓵𝓲 : Category
𝓚𝓵𝓮𝓲𝓼𝓵𝓲 = record
  { ob = ob 𝓒
  ; hom = λ A B → 𝓒 ∣ A ⟶ 𝓜 ₀(B)
  ; op = record
    { id = return
    ; _∘_ = _<=<_
    }
  ; ∘-identityˡ = λ { {f = f} → ⊨begin
    ` (return <=< f)                    ≡⟦ refl ⟧
    ` join ○ `map 𝓜 (` return) ○ ` f    ≡[ refl ]
    (` join ○ `map 𝓜 (` return)) ○ ` f  ≡⟦ ⦇ identityˡ ℳ ∘ refl ⦈ ⟧
    `id ○ ` f                           ≡[ refl ]
    ` f                                 ⟦∎⟧ }
  ; ∘-identityʳ = λ { {f = f} → ⊨begin
    ` (f <=< return)                  ≡⟦ refl ⟧
    ` join ○ `map 𝓜 (` f) ○ ` return  ≡⟦ ⦇ refl ∘ sym (natural (unit ℳ)) ⦈ ⟧
    ` join ○ ` return ○ ` f           ≡[ refl ]
    (` join ○ ` return) ○ ` f         ≡⟦ ⦇ identityʳ ℳ ∘ refl ⦈ ⟧
    `id ○ ` f                         ≡[ refl ]
    ` f                               ⟦∎⟧ }
  ; ∘-assoc = λ { {f = f} {g} {h} → ⊨begin
    ` ((h <=< g) <=< f)                                                   ≡⟦ refl ⟧
    ` join ○ `map 𝓜 (` join ○ `map 𝓜 (` h) ○ ` g) ○ ` f                   ≡[ refl ]
    (` join ○ `map 𝓜 (` join)) ○ `map (𝓜 ∘ 𝓜) (` h) ○ `map 𝓜 (` g) ○ ` f  ≡⟦ ⦇ assoc ℳ ∘ refl ⦈  ⟧
    (` join ○ ` join) ○ `map (𝓜 ∘ 𝓜) (` h) ○ `map 𝓜 (` g) ○ ` f           ≡[ refl ]
    ` join ○ (` join ○ `map (𝓜 ∘ 𝓜) (` h)) ○ `map 𝓜 (` g) ○ ` f           ≡⟦ ⦇ refl ∘ ⦇ natural (mult ℳ) ∘ refl ⦈ ⦈ ⟧
    ` join ○ (`map 𝓜 (` h) ○ ` join) ○ `map 𝓜 (` g) ○ ` f                 ≡[ refl ]
    ` join ○ `map 𝓜 (` h) ○ ` join ○ `map 𝓜 (` g) ○ ` f                   ≡⟦ refl ⟧
    ` (h <=< (g <=< f))                                                   ⟦∎⟧ }
  }
