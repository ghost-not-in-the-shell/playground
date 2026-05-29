{-# OPTIONS --no-require-unique-meta-solutions #-}
module Limit.Instances.Product where
open import Prelude
open import Category.Base
open ApplicativeReasoning

module _ 𝓒 where
  record is-product {A B A×B} (π₁ : 𝓒 ⦅ A×B , A ⦆) (π₂ : 𝓒 ⦅ A×B , B ⦆) : Type where
    no-eta-equality
    field
      mediate : ∀ {X} (f : 𝓒 ⦅ X , A ⦆) (g : 𝓒 ⦅ X , B ⦆) → 𝓒 ⦅ X , A×B ⦆
    syntax mediate f g = < f , g >′
    field
      commute₁ : ∀ {X} {f : 𝓒 ⦅ X , A ⦆} {g : 𝓒 ⦅ X , B ⦆}
        → π₁ ∘ < f , g >′ ≡ f
      commute₂ : ∀ {X} {f : 𝓒 ⦅ X , A ⦆} {g : 𝓒 ⦅ X , B ⦆}
        → π₂ ∘ < f , g >′ ≡ g
      unique : ∀ {X} {f : 𝓒 ⦅ X , A ⦆} {g : 𝓒 ⦅ X , B ⦆}
        → {⁇ : 𝓒 ⦅ X , A×B ⦆}
        → (⁇-commute₁ : π₁ ∘ ⁇ ≡ f)
        → (⁇-commute₂ : π₂ ∘ ⁇ ≡ g)
        → ⁇ ≡ < f , g >′

    <>∘ : ∀ {X Y} {f : 𝓒 ⦅ X , Y ⦆} {g₁ : 𝓒 ⦅ Y , A ⦆} {g₂ : 𝓒 ⦅ Y , B ⦆}
      → < g₁ , g₂ >′ ∘ f ≡ < g₁ ∘ f , g₂ ∘ f >′
    <>∘ {f = f} {g₁} {g₂} = unique
      (begin
        π₁ ∘(< g₁ , g₂ >′ ∘ f) ≡⟨ ∘-assoc 𝓒 ⟨
       (π₁ ∘ < g₁ , g₂ >′)∘ f  ≡⟨ commute₁ ○ - ⟩
               g₁         ∘ f  ∎)
      (begin
        π₂ ∘(< g₁ , g₂ >′ ∘ f) ≡⟨ ∘-assoc 𝓒 ⟨
       (π₂ ∘ < g₁ , g₂ >′)∘ f  ≡⟨ commute₂ ○ - ⟩
                    g₂    ∘ f  ∎)

    eta : < π₁ , π₂ >′ ≡ id
    eta = sym $ unique (∘-idʳ 𝓒) (∘-idʳ 𝓒)

  record Product (A B : Ob 𝓒) : Type where
    no-eta-equality
    field
      apex : Ob 𝓒
      π₁ : 𝓒 ⦅ apex , A ⦆
      π₂ : 𝓒 ⦅ apex , B ⦆
      product : is-product π₁ π₂

    open is-product product public

  record BinaryProduct : Type where
    constructor product-instance
    field
      has-all-products : ∀ A B → Product A B

  module × ⦃ (product-instance prod) : BinaryProduct ⦄ where
    module _ {A B} where
      open Product (prod A B) public hiding (apex; π₁; π₂)

    instance
      productOp : ProductOp (Hom 𝓒)
      productOp = record
        { _×_   = λ  A B  → prod A B .apex
        ; π₁    = λ {A B} → prod A B .π₁
        ; π₂    = λ {A B} → prod A B .π₂
        ; <_,_> = λ {A B} → prod A B .mediate
        } where open Product

    ×<> : ∀ {A B₁ B₂ C₁ C₂}
      → {f₁ : 𝓒 ⦅ A , B₁ ⦆} {g₁ : 𝓒 ⦅ B₁ , C₁ ⦆}
      → {f₂ : 𝓒 ⦅ A , B₂ ⦆} {g₂ : 𝓒 ⦅ B₂ , C₂ ⦆}
      → (g₁ ×₁ g₂) ∘ < f₁ , f₂ > ≡ < g₁ ∘ f₁ , g₂ ∘ f₂ >
    ×<> {f₁ = f₁} {g₁} {f₂} {g₂} = unique
      (begin
        π₁ ∘(g₁ ×₁ g₂ ∘ < f₁ , f₂ >) ≡⟨ ∘-assoc 𝓒 ⟨
       (π₁ ∘ g₁ ×₁ g₂)∘ < f₁ , f₂ >  ≡⟨ commute₁ ○ - ⟩
            (g₁ ∘  π₁)∘ < f₁ , f₂ >  ≡⟨ ∘-assoc 𝓒 ⟩
             g₁ ∘ (π₁ ∘ < f₁ , f₂ >) ≡⟨ - ○ commute₁ ⟩
             g₁ ∘         f₁         ∎)
      (begin
        π₂ ∘(g₁ ×₁ g₂ ∘ < f₁ , f₂ >) ≡⟨ ∘-assoc 𝓒 ⟨
       (π₂ ∘ g₁ ×₁ g₂)∘ < f₁ , f₂ >  ≡⟨ commute₂ ○ - ⟩
            (g₂ ∘  π₂)∘ < f₁ , f₂ >  ≡⟨ ∘-assoc 𝓒 ⟩
             g₂ ∘ (π₂ ∘ < f₁ , f₂ >) ≡⟨ - ○ commute₂ ⟩
             g₂ ∘              f₂    ∎)

    swap<> : ∀ {A B X} {f : 𝓒 ⦅ X , A ⦆} {g : 𝓒 ⦅ X , B ⦆} → swap ∘ < f , g > ≡ < g , f >
    swap<> {f = f} {g} = unique
      (begin
        π₁ ∘(< π₂ , π₁ > ∘ < f , g >) ≡⟨ ∘-assoc 𝓒 ⟨
       (π₁ ∘ < π₂ , π₁ >)∘ < f , g >  ≡⟨ commute₁ ○ - ⟩
               π₂        ∘ < f , g >  ≡⟨ commute₂ ⟩
                                 g    ∎)
      (begin
        π₂ ∘(< π₂ , π₁ > ∘ < f , g >) ≡⟨ ∘-assoc 𝓒 ⟨
       (π₂ ∘ < π₂ , π₁ >)∘ < f , g >  ≡⟨ commute₂ ○ - ⟩
                    π₁   ∘ < f , g >  ≡⟨ commute₁ ⟩
                             f        ∎)

    resp-id : {A S : Ob 𝓒} → id₍ A ₎ ×₁ id₍ S ₎ ≡ id
    resp-id = begin
      < id ∘ π₁ , id ∘ π₂ > ≡⟨ ⦇ < ∘-idˡ 𝓒 , ∘-idˡ 𝓒 > ⦈ ⟩
      <      π₁ ,      π₂ > ≡⟨ eta ⟩
                id          ∎

    resp-∘ : ∀ {A B C S T U}
      → {f : 𝓒 ⦅ A , B ⦆} {p : 𝓒 ⦅ S , T ⦆}
      → {g : 𝓒 ⦅ B , C ⦆} {q : 𝓒 ⦅ T , U ⦆}
      → (g ∘ f) ×₁ (q ∘ p) ≡ g ×₁ q ∘ f ×₁ p
    resp-∘ {f = f} {p} {g} {q} = begin
      <(g ∘  f)∘ π₁ ,(q ∘  p)∘ π₂ > ≡⟨ ⦇ < ∘-assoc 𝓒 , ∘-assoc 𝓒 > ⦈ ⟩
      < g ∘ (f ∘ π₁), q ∘ (p ∘ π₂)> ≡⟨ ×<> ⟨
        g ×₁ q      ∘ f ×₁ p        ∎

    lrmap : ∀ {A B S T} {f : 𝓒 ⦅ A , B ⦆} {p : 𝓒 ⦅ S , T ⦆} →
      f ×₁ id ∘ id ×₁ p ≡ id ×₁ p ∘ f ×₁ id
    lrmap {f = f} {p} = begin
      f  ×₁ id ∘  id ×₁  p  ≡⟨ resp-∘ ⟨
     (f  ∘  id)×₁(id ∘   p) ≡⟨ ⦇ sym (∘-idˡʳ 𝓒) ×₁ ∘-idˡʳ 𝓒 ⦈ ⟩
     (id ∘   f)×₁(p  ∘  id) ≡⟨ resp-∘ ⟩
      id ×₁  p ∘  f  ×₁ id  ∎

{-# DISPLAY BinaryProduct.has-all-products _ A B .Product.apex = A × B #-}
{-# DISPLAY Product.π₁ _ = π₁ #-}
{-# DISPLAY Product.π₂ _ = π₂ #-}
{-# DISPLAY is-product.mediate _ = <_,_> #-}

module _ {𝓒} ⦃ _ : BinaryProduct 𝓒 ⦄ where
  open import Functor.Base
  open import Functor.Bifunctor

  private instance
    _ = ×.productOp 𝓒

  -×- : 𝓒 × 𝓒 ⟶ 𝓒
  -×- = record
    { map₀ = λ (A , S) → A ×  S
    ; map₁ = λ (f , p) → f ×₁ p
    ; resp-id = ×.resp-id 𝓒
    ; resp-∘  = ×.resp-∘  𝓒
    }

  _×- : Ob 𝓒 → 𝓒 ⟶ 𝓒
  A ×- = -×- ₀₍ A ,-₎

  -×_ : Ob 𝓒 → 𝓒 ⟶ 𝓒
  -× B = -×- ₀₍-, B ₎

  open import Natural.Base
  open import Category.Instances.Functors

  instance
    𝓕𝓾𝓷-products : ∀ {𝓑} → BinaryProduct [ 𝓑 , 𝓒 ]
    𝓕𝓾𝓷-products {𝓑} = product-instance λ 𝐹 𝐺 →
      let 𝐹×′𝐺 : 𝓑 ⟶ 𝓒
          𝐹×′𝐺 = record
            { map₀ = λ A → 𝐹 ₀(A) ×  𝐺 ₀(A)
            ; map₁ = λ f → 𝐹 ₁(f) ×₁ 𝐺 ₁(f)
            ; resp-id = trans (cong₂ _×₁_ (resp-id 𝐹) (resp-id 𝐺)) (resp-id -×-)
            ; resp-∘  = trans (cong₂ _×₁_ (resp-∘  𝐹) (resp-∘  𝐺)) (resp-∘  -×-)
            }

          π₁′ : 𝐹×′𝐺 ⟹ 𝐹
          π₁′ = record
            { component = π₁
            ; natural = ×.commute₁ 𝓒
            }

          π₂′ : 𝐹×′𝐺 ⟹ 𝐺
          π₂′ = record
            { component = π₂
            ; natural = ×.commute₂ 𝓒
            }

          <_,_>′ : {𝑋 : 𝓑 ⟶ 𝓒} → 𝑋 ⟹ 𝐹 → 𝑋 ⟹ 𝐺 → 𝑋 ⟹ 𝐹×′𝐺
          <_,_>′ {𝑋} α β = record
            { component = λ {A} → < α ₍ A ₎ , β ₍ A ₎ >
            ; natural = λ {A B f} → begin
                < α ₋ , β ₋ >  ∘ 𝑋 ₁(f)        ≡⟨ ×.<>∘ 𝓒 ⟩
                < α ₋ ∘ 𝑋 ₁(f) , β ₋ ∘ 𝑋 ₁(f)> ≡⟨ ⦇ < natural α , natural β > ⦈ ⟩
                < 𝐹 ₁(f)∘ α ₋  , 𝐺 ₁(f)∘ β ₋ > ≡⟨ ×.×<> 𝓒 ⟨
                𝐹 ₁(f)×₁ 𝐺 ₁(f)∘ < α ₋ , β ₋ > ∎
            }
      in record
      { apex = 𝐹×′𝐺
      ; π₁ = π₁′
      ; π₂ = π₂′
      ; product = record
        { mediate = <_,_>′
        ; commute₁ = ext λ {A} → ×.commute₁ 𝓒
        ; commute₂ = ext λ {A} → ×.commute₂ 𝓒
        ; unique = λ ⁇-commute₁ ⁇-commute₂ →
            ext λ {A} → ×.unique 𝓒 (cong _₍ A ₎ ⁇-commute₁)
                                   (cong _₍ A ₎ ⁇-commute₂)
        }
      }
