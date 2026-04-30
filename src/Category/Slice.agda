module Category.Slice where
open import Prelude
open import Category.Base

private module /Ob&/Hom 𝓒 I where
  /Ob : Type
  /Ob = Σ[ A ∈ Ob 𝓒 ] 𝓒 ⦅ A , I ⦆

  record /Hom (Aᵢ Bᵢ : /Ob) : Type where
    constructor _,_
    private
      A = fst Aᵢ
      B = fst Bᵢ
      a = snd Aᵢ
      b = snd Bᵢ
    field
      morphism : 𝓒 ⦅ A , B ⦆
    private f = morphism
    field
      vertical : a ≡ b ∘ f

  open /Hom public renaming (morphism to fst; vertical to snd)

  /Hom-set : ∀ {Aᵢ Bᵢ} → is-set (/Hom Aᵢ Bᵢ)
  /Hom-set {Aᵢ@(A , a)} {Bᵢ@(B , b)} = iso→is-set iso /Hom′-set
    where /Hom′ : /Ob → /Ob → Type
          /Hom′ (A , a) (B , b) = Σ[ f ∈ 𝓒 ⦅ A , B ⦆ ] a ≡ b ∘ f

          /Hom′-set : is-set (/Hom′ Aᵢ Bᵢ)
          /Hom′-set = Σ-is-set (Hom-set 𝓒)
                        λ f → is-prop→is-set (Hom-set 𝓒 a (b ∘ f))

          iso : /Hom′ Aᵢ Bᵢ ≅ /Hom Aᵢ Bᵢ
          iso = record
            { fwd = λ (f , f-vertical) → (f , f-vertical)
            ; iso = record
              { bwd = λ (f , f-vertical) → (f , f-vertical)
              ; ∘-invˡ = refl
              ; ∘-invʳ = refl
              }
            }

open /Ob&/Hom public
  renaming ( /Ob      to _/_-Ob
           ; /Hom     to _/_-⦅_,_⦆
           ; /Hom-set to _/_-Hom-set
           )

module _ {𝓒} {I} where
  private
    id′ : ∀ {Aᵢ} → 𝓒 / I -⦅ Aᵢ , Aᵢ ⦆
    id′ = id , sym (∘-idʳ 𝓒)

    _∘′_ : ∀ {Aᵢ Bᵢ Cᵢ} → 𝓒 / I -⦅ Bᵢ , Cᵢ ⦆ → 𝓒 / I -⦅ Aᵢ , Bᵢ ⦆ → 𝓒 / I -⦅ Aᵢ , Cᵢ ⦆
    _∘′_ {(-, a)} {(-, b)} {(-, c)} (g , g-vertical) (f , f-vertical) = record
      { morphism = g ∘ f
      ; vertical = begin
        a         ≡⟨ f-vertical ⟩
        b     ∘ f ≡⟨ g-vertical ○ - ⟩
       (c ∘ g)∘ f ≡⟨ ∘-assoc 𝓒 ⟩
        c ∘(g ∘ f) ∎
      }

  instance
    /-compositionalOp : CompositionalOp (𝓒 / I -⦅_,_⦆)
    /-compositionalOp = record
      { id  = id′
      ; _∘_ = _∘′_
      }

    /Hom-extensional : {Aᵢ@(A , a) Bᵢ@(B , b) : 𝓒 / I -Ob}
      → ⦃ _ : Extensional (𝓒 ⦅ A , B ⦆) ⦄
      → Extensional (𝓒 / I -⦅ Aᵢ , Bᵢ ⦆)
    /Hom-extensional {A , a} {B , b} = record
      { _≈_ = λ (f , _) (g , _) → f ≈ g
      ; ext = λ {(f , f-vertical)} {(g , g-vertical)} p i → record
        { morphism = ext p i
        ; vertical = is-prop→PathP (λ i → Hom-set 𝓒 a (b ∘ ext p i))
                       f-vertical g-vertical i
        }
      }

_/_ : ∀ 𝓒 I → Category
𝓒 / I = record
  { Ob      = 𝓒 / I -Ob
  ; Hom     = 𝓒 / I -⦅_,_⦆
  ; Hom-set = 𝓒 / I -Hom-set
  ; ∘-idˡ   = ext (∘-idˡ   𝓒)
  ; ∘-idʳ   = ext (∘-idʳ   𝓒)
  ; ∘-assoc = ext (∘-assoc 𝓒)
  }

module _ {𝓒} A where
  open import Diagram.Product
  open import Diagram.Product.Properties
  open import Functor.Base
  open import Functor.Bifunctor

  forget/ : 𝓒 / A ⟶ 𝓒
  forget/ = record
    { map₀ = λ (A , a) → A
    ; map₁ = λ (f , f-vertical) → f
    ; resp-id = refl
    ; resp-∘  = refl
    }

  constant-family : ⦃ BinaryProduct 𝓒 ⦄ → 𝓒 ⟶ 𝓒 / A
  constant-family =
    let instance _ = ×.productOp 𝓒
    in record
    { map₀ = λ B → A × B , π₁
    ; map₁ = λ f → record
      { morphism = id ×₁ f
      ; vertical = begin
                    π₁            ≡⟨ ∘-idˡ 𝓒 ⟨
               id ∘ π₁            ≡⟨ ×.commute₁ 𝓒 ⟨
        π₁ ∘ < id ∘ π₁ , f ∘ π₂ > ∎
      }
    ; resp-id = ext $ resp-id (A ×-)
    ; resp-∘  = ext $ resp-∘  (A ×-)
    }

module DependentSum 𝓒 where
  open import Functor.Base

  _! : ∀ {I J} (u : 𝓒 ⦅ I , J ⦆) → 𝓒 / I ⟶ 𝓒 / J
  _! u = record
    { map₀ = λ (A , a) → A , u ∘ a
    ; map₁ = λ {(-, a)} {(-, b)} (f , f-vertical) → record
      { morphism = f
      ; vertical = begin
        u ∘ a      ≡⟨ - ○ f-vertical ⟩
        u ∘(b ∘ f) ≡⟨ ∘-assoc 𝓒 ⟨
       (u ∘ b)∘ f  ∎
      }
    ; resp-id = ext refl
    ; resp-∘  = ext refl
    }
