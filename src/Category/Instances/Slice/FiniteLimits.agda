module Category.Instances.Slice.FiniteLimits 𝓒 where
open import Prelude
open import Category.Base
open import Category.Instances.Slice
open import Limit.Instances.Product
open import Limit.Instances.Pullback
open import Limit.Instances.Terminal

instance
  /terminal : ∀ {I} → Terminal (𝓒 / I)
  /terminal {I} =
    let 𝟙ᵢ : Ob (𝓒 / I)
        𝟙ᵢ = I , id

        <>ᵢ : ∀ {Xᵢ} → 𝓒 / I -⦅ Xᵢ , 𝟙ᵢ ⦆
        <>ᵢ {(-, x)} = record
          { morphism = x
          ; vertical = sym (∘-idˡ 𝓒)
          }
    in record
    { apex = 𝟙ᵢ
    ; terminal = record
      { mediate = <>ᵢ
      ; unique = λ {(X , x)} {(⁇ , ⁇-vertical)} → ext $ begin
               ⁇ ≡⟨ ∘-idˡ 𝓒 ⟨
          id ∘ ⁇ ≡⟨ ⁇-vertical ⟨
          x      ∎
      }
    }

module _ {I}
  {Aᵢ@(A , a) Bᵢ@(B , b) Aᵢ×Bᵢ@(A⊗B , diag) : Ob (𝓒 / I)}
  {πᵢ₁@(p , p-vertical) : 𝓒 / I ⦅ Aᵢ×Bᵢ , Aᵢ ⦆}
  {πᵢ₂@(q , q-vertical) : 𝓒 / I ⦅ Aᵢ×Bᵢ , Bᵢ ⦆} where

  is-pullback→is-fibre-product
    : is-pullback 𝓒 a b p q
    → is-product (𝓒 / I) πᵢ₁ πᵢ₂
  is-pullback→is-fibre-product pull = record
    { mediate = λ {(X , x)} (f , f-vertical) (g , g-vertical) →
      let □ : a ∘ f ≡ b ∘ g
          □ = begin
            a ∘ f ≡⟨ f-vertical ⟨
            x     ≡⟨ g-vertical ⟩
            b ∘ g ∎
      in record
      { morphism = < f [ □ ] g >′
      ; vertical = begin
        x                   ≡⟨ f-vertical ⟩
        a ∘       f         ≡⟨ - ○ commute₁ ⟨
        a ∘(p ∘ < f □ g >′) ≡⟨ ∘-assoc 𝓒 ⟨
       (a ∘ p)∘ < f □ g >′  ≡⟨ p-vertical ○ - ⟨
        diag  ∘ < f □ g >′  ∎
      }
    ; commute₁ = ext commute₁
    ; commute₂ = ext commute₂
    ; unique = λ ⁇ᵢ-commute₁ ⁇ᵢ-commute₂ →
      ext $ unique (ap fst ⁇ᵢ-commute₁)
                   (ap fst ⁇ᵢ-commute₂)
    } where open is-pullback pull

  is-fibre-product→is-pullback
    : is-product (𝓒 / I) πᵢ₁ πᵢ₂
    → is-pullback 𝓒 a b p q
  is-fibre-product→is-pullback prod = record
    { square = begin
      a ∘ p ≡⟨ p-vertical ⟨
      diag  ≡⟨ q-vertical ⟩
      b ∘ q ∎
    ; mediate = λ {X} f g □ →
      let Xᵢ : Ob (𝓒 / I)
          Xᵢ = X , a ∘ f

          fᵢ : 𝓒 / I ⦅ Xᵢ , Aᵢ ⦆
          fᵢ = record
            { morphism = f
            ; vertical = refl
            }

          gᵢ : 𝓒 / I ⦅ Xᵢ , Bᵢ ⦆
          gᵢ = record
            { morphism = g
            ; vertical = □
            }
      in fst < fᵢ , gᵢ >′
    ; commute₁ = ap fst commute₁
    ; commute₂ = ap fst commute₂
    ; unique = λ {X} {f} {g} {□} {⁇} ⁇-commute₁ ⁇-commute₂ →
      let Xᵢ : Ob (𝓒 / I)
          Xᵢ = X , a ∘ f

          ⁇ᵢ : 𝓒 / I ⦅ Xᵢ , Aᵢ×Bᵢ ⦆
          ⁇ᵢ = record
            { morphism = ⁇
            ; vertical = begin
              a ∘ f      ≡⟨ - ○ ⁇-commute₁ ⟨
              a ∘(p ∘ ⁇) ≡⟨ ∘-assoc 𝓒 ⟨
             (a ∘ p)∘ ⁇  ≡⟨ p-vertical ○ - ⟨
              diag  ∘ ⁇  ∎
            }
      in ap fst $ unique {⁇ = ⁇ᵢ}
                  (ext ⁇-commute₁)
                  (ext ⁇-commute₂)
    } where open is-product prod

module _ {I}
  {Jᵢ@(J , u) Aᵢ@(A , u∘a) Bᵢ@(B , u∘b) Aᵢ⊗Bᵢ@(A⊗B , diag) : Ob (𝓒 / I)}
  {aᵢ@(a , a-vertical) : 𝓒 / I ⦅ Aᵢ    , Jᵢ ⦆}
  {bᵢ@(b , b-vertical) : 𝓒 / I ⦅ Bᵢ    , Jᵢ ⦆}
  {pᵢ@(p , p-vertical) : 𝓒 / I ⦅ Aᵢ⊗Bᵢ , Aᵢ ⦆}
  {qᵢ@(q , q-vertical) : 𝓒 / I ⦅ Aᵢ⊗Bᵢ , Bᵢ ⦆} where

  is-pullback→is-fibre-pullback
    : is-pullback  𝓒      a  b  p  q
    → is-pullback (𝓒 / I) aᵢ bᵢ pᵢ qᵢ
  is-pullback→is-fibre-pullback pull = record
    { square = ext square
    ; mediate = λ {(X , x)} (f , f-vertical) (g , g-vertical) □ᵢ → record
      { morphism = < f [ ap fst □ᵢ ] g >′
      ; vertical = begin
        x                     ≡⟨ f-vertical ⟩
        u∘a ∘       f         ≡⟨ - ○ commute₁ ⟨
        u∘a ∘(p ∘ < f □ g >′) ≡⟨ ∘-assoc 𝓒 ⟨
       (u∘a ∘ p)∘ < f □ g >′  ≡⟨ p-vertical ○ - ⟨
        diag    ∘ < f □ g >′  ∎
      }
    ; commute₁ = ext commute₁
    ; commute₂ = ext commute₂
    ; unique = λ ⁇ᵢ-commute₁ ⁇ᵢ-commute₂ →
      ext $ unique (ap fst ⁇ᵢ-commute₁)
                   (ap fst ⁇ᵢ-commute₂)
    } where open is-pullback pull

  is-fibre-pullback→is-pullback
    : is-pullback (𝓒 / I) aᵢ bᵢ pᵢ qᵢ
    → is-pullback  𝓒      a  b  p  q
  is-fibre-pullback→is-pullback pull = record
    { square = ap fst square
    ; mediate = λ {X} f g □ →
      let Xᵢ : Ob (𝓒 / I)
          Xᵢ = X , u∘a ∘ f

          fᵢ : 𝓒 / I ⦅ Xᵢ , Aᵢ ⦆
          fᵢ = record
            { morphism = f
            ; vertical = refl
            }

          gᵢ : 𝓒 / I ⦅ Xᵢ , Bᵢ ⦆
          gᵢ = record
            { morphism = g
            ; vertical = begin
               u∘a  ∘ f  ≡⟨ a-vertical ○ - ⟩
             (u ∘ a)∘ f  ≡⟨ ∘-assoc 𝓒 ⟩
              u ∘(a ∘ f) ≡⟨ - ○ □ ⟩
              u ∘(b ∘ g) ≡⟨ ∘-assoc 𝓒 ⟨
             (u ∘ b)∘ g  ≡⟨ b-vertical ○ - ⟨
               u∘b  ∘ g  ∎
            }
      in fst < fᵢ [ ext □ ] gᵢ >′
    ; commute₁ = ap fst commute₁
    ; commute₂ = ap fst commute₂
    ; unique = λ {X} {f} {g} {□} {⁇} ⁇-commute₁ ⁇-commute₂ →
      let Xᵢ : Ob (𝓒 / I)
          Xᵢ = X , u∘a ∘ f

          ⁇ᵢ : 𝓒 / I ⦅ Xᵢ , Aᵢ⊗Bᵢ ⦆
          ⁇ᵢ = record
            { morphism = ⁇
            ; vertical = begin
              u∘a ∘ f      ≡⟨ - ○ ⁇-commute₁ ⟨
              u∘a ∘(p ∘ ⁇) ≡⟨ ∘-assoc 𝓒 ⟨
             (u∘a ∘ p)∘ ⁇  ≡⟨ p-vertical ○ - ⟨
              diag    ∘ ⁇  ∎
            }
      in ap fst $ unique {⁇ = ⁇ᵢ}
                   (ext ⁇-commute₁)
                   (ext ⁇-commute₂)
    } where open is-pullback pull

pullbacks→/products : ∀ {I} ⦃ _ : Pullbacks 𝓒 ⦄ → BinaryProduct (𝓒 / I)
pullbacks→/products {I} ⦃ pull ⦄ = product-instance
  λ Aᵢ@(A , a) Bᵢ@(B , b) →
    let instance _ = ⊗.pullbackOp 𝓒

        Aᵢ×Bᵢ : Ob (𝓒 / I)
        Aᵢ×Bᵢ = a ⊗ b , a ∘ p

        πᵢ₁ : 𝓒 / I ⦅ Aᵢ×Bᵢ , Aᵢ ⦆
        πᵢ₁ = record
          { morphism = p
          ; vertical = refl
          }

        πᵢ₂ : 𝓒 / I ⦅ Aᵢ×Bᵢ , Bᵢ ⦆
        πᵢ₂ = record
          { morphism = q
          ; vertical = begin
            a ∘ p ≡⟨ ⊗.square 𝓒 ⟩
            b ∘ q ∎
          }
    in record
      { apex = Aᵢ×Bᵢ
      ; π₁ = πᵢ₁
      ; π₂ = πᵢ₂
      ; product = is-pullback→is-fibre-product
                  $ Pullback.pullback
                  $ Pullbacks.has-all-pullbacks pull a b
      }

/products→pullbacks : ⦃ ∀ {I} → BinaryProduct (𝓒 / I) ⦄ → Pullbacks 𝓒
/products→pullbacks ⦃ prod ⦄ = pullback-instance
  λ {I A B} a b →
    let instance _ = ×.productOp (𝓒 / I)

        Aᵢ : 𝓒 / I -Ob
        Aᵢ = A , a

        Bᵢ : 𝓒 / I -Ob
        Bᵢ = B , b
    in record
      { apex = fst (Aᵢ × Bᵢ)
      ; p = fst π₁
      ; q = fst π₂
      ; pullback = is-fibre-product→is-pullback
                   $ Product.product
                   $ BinaryProduct.has-all-products prod Aᵢ Bᵢ
      }

pullbacks→/pullbacks : ∀ {I} ⦃ _ : Pullbacks 𝓒 ⦄ → Pullbacks (𝓒 / I)
pullbacks→/pullbacks {I} ⦃ pull ⦄ = pullback-instance
  λ {Jᵢ@(J , u) Aᵢ@(A , u∘a) Bᵢ@(B , u∘b)}
     aᵢ@(a , a-vertical) bᵢ@(b , b-vertical) →
    let instance _ = ⊗.pullbackOp 𝓒

        Aᵢ⊗Bᵢ : Ob (𝓒 / I)
        Aᵢ⊗Bᵢ = a ⊗ b , u∘a ∘ p

        pᵢ : 𝓒 / I ⦅ Aᵢ⊗Bᵢ , Aᵢ ⦆
        pᵢ = record
          { morphism = p
          ; vertical = refl
          }

        qᵢ : 𝓒 / I ⦅ Aᵢ⊗Bᵢ , Bᵢ ⦆
        qᵢ = record
          { morphism = q
          ; vertical = begin
             u∘a  ∘ p  ≡⟨ a-vertical ○ - ⟩
           (u ∘ a)∘ p  ≡⟨ ∘-assoc 𝓒 ⟩
            u ∘(a ∘ p) ≡⟨ - ○ ⊗.square 𝓒 ⟩
            u ∘(b ∘ q) ≡⟨ ∘-assoc 𝓒 ⟨
           (u ∘ b)∘ q  ≡⟨ b-vertical ○ - ⟨
             u∘b  ∘ q  ∎
          }
    in record
      { apex = Aᵢ⊗Bᵢ
      ; p = pᵢ
      ; q = qᵢ
      ; pullback = is-pullback→is-fibre-pullback
                   $ Pullback.pullback
                   $ Pullbacks.has-all-pullbacks pull a b
      }
