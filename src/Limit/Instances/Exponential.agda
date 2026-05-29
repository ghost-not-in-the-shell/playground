module Limit.Instances.Exponential where
open import Prelude
open import Category.Base
open import Functor.Base
open import Limit.Instances.Product
open ApplicativeReasoning

module _ 𝓒 ⦃ _ : BinaryProduct 𝓒 ⦄ where
  private instance
    _ = ×.productOp 𝓒

  record is-exponential {A B A⇒B} (ev : 𝓒 ⦅ A⇒B × A , B ⦆) : Type where
    field
      mediate : ∀ {Γ} (f : 𝓒 ⦅ Γ × A , B ⦆) → 𝓒 ⦅ Γ , A⇒B ⦆
    private ƛ′ = mediate
    field
      commute : ∀ {Γ} {f : 𝓒 ⦅ Γ × A , B ⦆} → ev ∘ (ƛ′ f ×₁ id) ≡ f
      unique  : ∀ {Γ} {f : 𝓒 ⦅ Γ × A , B ⦆}
        → {⁇ : 𝓒 ⦅ Γ , A⇒B ⦆}
        → (⁇-commute : ev ∘ (⁇ ×₁ id) ≡ f)
        → ⁇ ≡ ƛ′ f

    unique₂ : ∀ {Γ} {f : 𝓒 ⦅ Γ × A , B ⦆}
      → {⁇₁ ⁇₂ : 𝓒 ⦅ Γ , A⇒B ⦆}
      → (⁇₁-commute : ev ∘ (⁇₁ ×₁ id) ≡ f)
      → (⁇₂-commute : ev ∘ (⁇₂ ×₁ id) ≡ f)
      → ⁇₁ ≡ ⁇₂
    unique₂ ⁇₁-commute ⁇₂-commute =
      trans (unique ⁇₁-commute)
      $ sym (unique ⁇₂-commute)

    eta : ƛ′ ev ≡ id
    eta = sym $ unique $ begin
      ev ∘ id ×₁ id ≡⟨ - ○ ×.resp-id 𝓒 ⟩
      ev ∘ id       ≡⟨ ∘-idʳ 𝓒 ⟩
      ev            ∎

  record Exponential (A B : Ob 𝓒) : Type where
    field
      apex : Ob 𝓒
      ev : 𝓒 ⦅ apex × A , B ⦆
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
        { _⇒_ = λ    A B  → exp A B .apex
        ; ev  = λ {  A B} → exp A B .ev
        ; ƛ   = λ {Γ A B} → exp A B .mediate
        } where open Exponential

    ƛ∘ : ∀ {Γ A B C} {g : 𝓒 ⦅ B , C ⦆} {f : 𝓒 ⦅ Γ , A ⇒ B ⦆}
      → ƛ(g ∘ ev)∘ f ≡ ƛ(g ∘ unƛ f)
    ƛ∘ {Γ} {A} {B} {C} {g} {f} = unique $ begin
      ev ∘(ƛ(g ∘ ev)      ∘ f)×₁ id  ≡⟨ - ○ resp-∘ (-× A) ⟩
      ev ∘(ƛ(g ∘ ev)×₁ id ∘ f ×₁ id) ≡⟨ ∘-assoc 𝓒 ⟨
     (ev ∘ ƛ(g ∘ ev)×₁ id)∘ f ×₁ id  ≡⟨ commute ○ - ⟩
            (g ∘ ev)      ∘ f ×₁ id  ≡⟨ ∘-assoc 𝓒 ⟩
             g ∘(ev       ∘ f ×₁ id) ∎

{-# DISPLAY Exponentials.has-all-exponentials _ A B .Exponential.apex = A ⇒ B #-}
{-# DISPLAY Exponential.ev _ = ev #-}
{-# DISPLAY is-exponential.mediate _ = ƛ #-}

module _ {𝓒} ⦃ _ : BinaryProduct 𝓒 ⦄ ⦃ _ : Exponentials 𝓒 ⦄ where
  private instance
    _ = ×.productOp     𝓒
    _ = ⇒.exponentialOp 𝓒

  instance
    ƛ-iso : {Γ A B : Ob 𝓒} → is-iso Function (ƛ {Γ = Γ} {A} {B})
    ƛ-iso = record
      { bwd = unƛ
      ; ∘-invˡ = ext λ _ → ⇒.commute 𝓒
      ; ∘-invʳ = ext λ _ → sym (⇒.unique 𝓒 refl)
      }

  -⇒_ : Ob 𝓒 → 𝓒 ᵒᵖ ⟶ 𝓒
  -⇒ X = record
    { map₀ = λ A → A ⇒ X
    ; map₁ = λ f → ƛ(ev ∘ id ×₁ f)
    ; resp-id = sym (⇒.unique 𝓒 refl)
    ; resp-∘ = λ {A B C f g} → sym $ ⇒.unique 𝓒 $ begin
        ev ∘(ƛ(ev ∘ id ×₁ g)      ∘ ƛ(ev ∘ id ×₁ f))×₁ id  ≡⟨ - ○ resp-∘ (-× C) ⟩
        ev ∘(ƛ(ev ∘ id ×₁ g)×₁ id ∘ ƛ(ev ∘ id ×₁ f) ×₁ id) ≡⟨ ∘-assoc 𝓒 ⟨
       (ev ∘ ƛ(ev ∘ id ×₁ g)×₁ id)∘ ƛ(ev ∘ id ×₁ f) ×₁ id  ≡⟨ ⇒.commute 𝓒 ○ - ⟩
              (ev ∘ id ×₁ g)      ∘ ƛ(ev ∘ id ×₁ f) ×₁ id  ≡⟨ ∘-assoc 𝓒 ⟩
               ev ∘(id ×₁ g       ∘ ƛ(ev ∘ id ×₁ f) ×₁ id) ≡⟨ - ○ ×.lrmap 𝓒 ⟨
               ev ∘(ƛ(ev ∘ id ×₁ f)×₁ id ∘ id ×₁ g)        ≡⟨ ∘-assoc 𝓒 ⟨
              (ev ∘ ƛ(ev ∘ id ×₁ f)×₁ id)∘ id ×₁ g         ≡⟨ ⇒.commute 𝓒 ○ - ⟩
                     (ev ∘ id ×₁ f)      ∘ id ×₁ g         ≡⟨ ∘-assoc 𝓒 ⟩
                      ev ∘(id ×₁ f       ∘ id ×₁ g)        ≡⟨ - ○ resp-∘ ((A ⇒ X) ×-) ⟨
                      ev ∘ id ×₁(f       ∘       g)        ∎
    }

  _⇒- : Ob (𝓒 ᵒᵖ) → 𝓒 ⟶ 𝓒
  X ⇒- = record
    { map₀ = λ A → X ⇒ A
    ; map₁ = λ g → ƛ(g ∘ ev)
    ; resp-id = begin
        ƛ(id ∘ ev) ≡⟨ ⦇ ƛ(∘-idˡ 𝓒) ⦈ ⟩
        ƛ      ev  ≡⟨ ⇒.eta 𝓒 ⟩
        id         ∎
    ; resp-∘ = λ {A B C f g} → sym $ ⇒.unique 𝓒 $ begin
        ev ∘(ƛ(g ∘ ev)      ∘ ƛ(f ∘ ev))×₁ id  ≡⟨ - ○ resp-∘ (-× X) ⟩
        ev ∘(ƛ(g ∘ ev)×₁ id ∘ ƛ(f ∘ ev) ×₁ id) ≡⟨ ∘-assoc 𝓒 ⟨
       (ev ∘ ƛ(g ∘ ev)×₁ id)∘ ƛ(f ∘ ev) ×₁ id  ≡⟨ ⇒.commute 𝓒 ○ - ⟩
              (g ∘ ev)      ∘ ƛ(f ∘ ev) ×₁ id  ≡⟨ ∘-assoc 𝓒 ⟩
               g ∘(ev       ∘ ƛ(f ∘ ev) ×₁ id) ≡⟨ - ○ ⇒.commute 𝓒 ⟩
               g ∘             (f ∘ ev)        ≡⟨ ∘-assoc 𝓒 ⟨
              (g ∘              f)∘ ev         ∎
    }

open import Limit.Instances.Pullback
open import Limit.Instances.Terminal
module DependentProduct 𝓒
    ⦃ _ : Terminal      𝓒 ⦄
    ⦃ _ : BinaryProduct 𝓒 ⦄
    ⦃ _ : Exponentials  𝓒 ⦄
    ⦃ _ : Pullbacks     𝓒 ⦄ where
  open import Category.Instances.Slice renaming (constant-family to Δ)

  private instance
    _ = 𝟙.terminalOp    𝓒
    _ = ×.productOp     𝓒
    _ = ⇒.exponentialOp 𝓒
    _ = ⊗.pullbackOp    𝓒

  ∏ : (A : Ob 𝓒) → 𝓒 / A ⟶ 𝓒
  ∏ A =
    let ∏A : 𝓒 / A -Ob → Ob 𝓒
        ∏A (A⨾B , πB) = ƛ π₂ ⊗ ƛ(πB ∘ ev)

        map : ∀ {X Y} → 𝓒 / A -⦅ X , Y ⦆ → 𝓒 ⦅ ∏A X , ∏A Y ⦆
        map {(A⨾X , πX)} {(A⨾Y , πY)} (f , f-vertical) =
          let □ : ƛ π₂ ∘ <> ≡ ƛ(πY ∘ ev) ∘ (ƛ(f ∘ ev) ∘ q)
              □ = begin
                ƛ π₂                  ∘ <> ≡⟨ - ○ 𝟙.unique 𝓒 ⟨
                ƛ π₂                  ∘ p  ≡⟨ ⊗.square 𝓒 ⟩
                ƛ( πX     ∘ ev)       ∘ q  ≡⟨ ⦇ ƛ(f-vertical ○ -) ⦈ ○ - ⟩
                ƛ((πY ∘ f)∘ ev)       ∘ q  ≡⟨ resp-∘ (A ⇒-) ○ - ⟩
               (ƛ(πY ∘ ev)∘ ƛ(f ∘ ev))∘ q  ≡⟨ ∘-assoc 𝓒 ⟩
                ƛ(πY ∘ ev)∘(ƛ(f ∘ ev) ∘ q) ∎
          in < <> [ □ ] ƛ(f ∘ ev) ∘ q >
    in record
    { map₀ = ∏A
    ; map₁ = map
    ; resp-id = sym $ ⊗.unique 𝓒 (𝟙.unique₂ 𝓒) $ begin
          q       ∘ id ≡⟨ ∘-idˡʳ 𝓒 ⟨
          id      ∘ q  ≡⟨ resp-id (A ⇒-) ○ - ⟨
        ƛ(id ∘ ev)∘ q  ∎
    ; resp-∘ =  λ {(A⨾X , πX) (A⨾Y , πY) (A⨾Z , πZ)
                   (f , f-vertical)
                   (g , g-vertical)} → sym $ ⊗.unique 𝓒 (𝟙.unique₂ 𝓒) $
       begin
         q ∘ < <> □ ƛ(g ∘ ev)∘ q > ∘ < <> □ ƛ(f ∘ ev) ∘ q >  ≡⟨ ∘-assoc 𝓒 ⟨
        (q ∘ < <> □ ƛ(g ∘ ev)∘ q >)∘ < <> □ ƛ(f ∘ ev) ∘ q >  ≡⟨ ⊗.commute₂ 𝓒 ○ - ⟩
                   (ƛ(g ∘ ev)∘ q)  ∘ < <> □ ƛ(f ∘ ev) ∘ q >  ≡⟨ ∘-assoc 𝓒 ⟩
                    ƛ(g ∘ ev)∘(q   ∘ < <> □ ƛ(f ∘ ev) ∘ q >) ≡⟨ - ○ ⊗.commute₂ 𝓒 ⟩
                    ƛ(g ∘ ev)∘             (ƛ(f ∘ ev) ∘ q)   ≡⟨ ∘-assoc 𝓒 ⟨
                   (ƛ(g ∘ ev)∘              ƛ(f ∘ ev))∘ q    ≡⟨ resp-∘ (A ⇒-) ○ - ⟨
                    ƛ((g ∘ f)∘ ev)                    ∘ q    ∎
    }

  ƛπ₂∘<> : ∀ {Γ A} → Path (𝓒 ⦅ Γ , A ⇒ A ⦆) (ƛ π₂ ∘ <>) (ƛ π₂)
  ƛπ₂∘<> {Γ} {A} = ⇒.unique 𝓒 $ begin
    ev ∘(ƛ π₂       ∘ <>)×₁ id  ≡⟨ - ○ resp-∘ (-× A) ⟩
    ev ∘(ƛ π₂ ×₁ id ∘ <> ×₁ id) ≡⟨ ∘-assoc 𝓒 ⟨
   (ev ∘ ƛ π₂ ×₁ id)∘ <> ×₁ id  ≡⟨ ⇒.commute 𝓒 ○ - ⟩
           π₂       ∘ <> ×₁ id  ≡⟨ ×.commute₂ 𝓒 ⟩
                      id ∘ π₂   ≡⟨ ∘-idˡ 𝓒 ⟩
                           π₂   ∎


  -- Γ , A ⊢ B
  -- =========
  -- Γ ⊢ ∏ A B
  𝓒/A⦅ΔΓ,B⦆≅𝓒⦅Γ,∏AB⦆ : ∀ {Γ A B} → 𝓒 / A -⦅ Δ(A)₀ Γ , B ⦆ ≅ 𝓒 ⦅ Γ , ∏ A ₀ B ⦆
  𝓒/A⦅ΔΓ,B⦆≅𝓒⦅Γ,∏AB⦆ {Γ} {A} {(Γ⨾A⨾B , πB)} = record
    { fwd = λ (t , t-vertical) →
        let □ : ƛ π₂ ∘ <> ≡ ƛ(πB ∘ ev) ∘ ƛ t
            □ = trans ƛπ₂∘<> $ sym $ ⇒.unique 𝓒 $ begin
              ev ∘(ƛ(πB ∘ ev)      ∘ ƛ t)×₁ id  ≡⟨ - ○ resp-∘ (-× A) ⟩
              ev ∘(ƛ(πB ∘ ev)×₁ id ∘ ƛ t ×₁ id) ≡⟨ ∘-assoc 𝓒 ⟨
             (ev ∘ ƛ(πB ∘ ev)×₁ id)∘ ƛ t ×₁ id  ≡⟨ ⇒.commute 𝓒 ○ - ⟩
                    (πB ∘ ev)      ∘ ƛ t ×₁ id  ≡⟨ ∘-assoc 𝓒 ⟩
                     πB ∘(ev       ∘ ƛ t ×₁ id) ≡⟨ - ○ ⇒.commute 𝓒 ⟩
                     πB ∘              t        ≡⟨ t-vertical ⟨
                     π₂                         ∎
        in < <> [ □ ] ƛ t >
    ; iso = record
      { bwd = λ t → record
        { morphism = unƛ(q ∘ t)
        ; vertical = iso→inj ƛ $ begin
            ƛ π₂                ≡⟨ ƛπ₂∘<> ⟨
            ƛ π₂ ∘     <>       ≡⟨ - ○ 𝟙.<>∘ 𝓒 ⟨
            ƛ π₂ ∘    (<> ∘ t)  ≡⟨ ∘-assoc 𝓒 ⟨
           (ƛ π₂ ∘     <>)∘ t   ≡⟨ (- ○ 𝟙.unique 𝓒) ○ - ⟨
           (ƛ π₂ ∘      p)∘ t   ≡⟨ ⊗.square 𝓒 ○ - ⟩
           (ƛ(πB ∘ ev)∘ q)∘ t   ≡⟨ ∘-assoc 𝓒 ⟩
            ƛ(πB ∘ ev)∘(q ∘ t)  ≡⟨ ⇒.ƛ∘ 𝓒 ⟩
            ƛ(πB ∘  unƛ(q ∘ t)) ∎
        }
      ; ∘-invˡ = ext λ (t , t-vertical) → begin
          ev ∘(q ∘ < <> □ ƛ t >)×₁ id ≡⟨ - ○ ⦇ ⊗.commute₂ 𝓒 ×₁ - ⦈ ⟩
          ev ∘            ƛ t   ×₁ id ≡⟨ ⇒.commute 𝓒 ⟩
                            t         ∎
      ; ∘-invʳ = ext λ t → sym (⊗.unique 𝓒 (𝟙.unique 𝓒) (sym (invʳ ƛ)))
      }
    }
