module Yoneda.Lemma where
open import Prelude
open import Category.Base
open import Category.Instances.Functors
open import Functor.Base
open import Functor.Bifunctor.Curry
open import Functor.Instances.Hom
open import Natural.Base
import Yoneda.Base

module Covariant 𝓒 where
  open Yoneda.Base.Covariant 𝓒 public

  private
    [𝓒,𝓢𝓮𝓽]⦅ℎ-,-⦆ : [ 𝓒 , 𝓢𝓮𝓽 ] ×̅ 𝓒 ⟶ 𝓢𝓮𝓽
    [𝓒,𝓢𝓮𝓽]⦅ℎ-,-⦆ = Flip ([ 𝓒 , 𝓢𝓮𝓽 ] ⦅-,-⦆ ∘ˡ ℎ⁻ ᵒᵖ)

  ↑₍-,_₎ : (A : Ob 𝓒) → -$ A ⟹ [ 𝓒 , 𝓢𝓮𝓽 ] ⦅ ℎ⁻ ₀(A) ,-⦆
  ↑₍-, A ₎ = record
    { component = _↑
    ; natural = λ {𝐹 𝐺 : 𝓒 ⟶ 𝓢𝓮𝓽}
                  {α : 𝐹 ⟹ 𝐺} →
            ext λ (u : ⌞ 𝐹 ₀(A) ⌟)
                  {B : Ob 𝓒}
                  (f : 𝓒 ⦅ A , B ⦆) → begin
        (𝐺 ₁(f) $ α ₋ $ u) ≡⟨ refl ⟩
        (𝐺 ₁(f) ∘ α ₋ $ u) ≡⟨ cong (_$ u) (natural α) ⟨
        (α ₋ ∘ 𝐹 ₁(f) $ u) ≡⟨ refl ⟩
        (α ₋ $ 𝐹 ₁(f) $ u) ∎
    }

  ↑₍_,-₎ : (𝐹 : 𝓒 ⟶ 𝓢𝓮𝓽) → 𝐹 ⟹ [ 𝓒 , 𝓢𝓮𝓽 ] ⦅-, 𝐹 ⦆ ∘ ℎ⁻ ᵒᵖ
  ↑₍ 𝐹 ,-₎ = record
    { component = _↑
    ; natural = λ {A B : Ob 𝓒} {f : 𝓒 ⦅ A , B ⦆} →
            ext λ (u : ⌞ 𝐹 ₀(A) ⌟)
                  {C : Ob 𝓒}
                  (g : 𝓒 ⦅ B , C ⦆) → begin
        (𝐹 ₁(g)$ 𝐹 ₁(f)$ u) ≡⟨ refl ⟩
        (𝐹 ₁(g)∘ 𝐹 ₁(f)$ u) ≡⟨ cong (_$ u) (resp-∘ 𝐹) ⟨
        (𝐹 ₁(g ∘     f)$ u) ∎
    }

  yon : Flat Eval ⟹ Flat [𝓒,𝓢𝓮𝓽]⦅ℎ-,-⦆
  yon = binatural {𝐹 = Eval} {[𝓒,𝓢𝓮𝓽]⦅ℎ-,-⦆} _↑
    (λ {A 𝐹 𝐺 α} → natural ↑₍-, A ₎ {𝐹} {𝐺} {α})
    (λ {𝐹 A B f} → natural ↑₍ 𝐹 ,-₎ {A} {B} {f})

  open import Natural.Iso

  instance
    yon-iso : is-iso (Hom [ [ 𝓒 , 𝓢𝓮𝓽 ] × 𝓒 , 𝓢𝓮𝓽 ]) yon
    yon-iso = from-component yon
