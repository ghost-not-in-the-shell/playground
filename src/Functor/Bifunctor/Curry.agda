{-# OPTIONS --no-require-unique-meta-solutions #-}
module Functor.Bifunctor.Curry where
open import Prelude
open import Category.Assoc
open import Category.Base
open import Category.Instances.Functors
open import Functor.Base
open import Natural.Base
open ApplicativeReasoning

record Bifunctor 𝓒 𝓓 𝓔 : Type where
  field
    map₀ : Ob 𝓒 → Ob 𝓓 → Ob 𝓔
  private
    𝐹₀ = map₀
  field
    lmap : ∀ {S A B} → 𝓒 ⦅ A , B ⦆ → 𝓔 ⦅ 𝐹₀ A S , 𝐹₀ B S ⦆
    rmap : ∀ {A S T} → 𝓓 ⦅ S , T ⦆ → 𝓔 ⦅ 𝐹₀ A S , 𝐹₀ A T ⦆
  private
    𝐹◂ = lmap
    𝐹▸ = rmap
  field
    lmap-id : {S : Ob 𝓓} {A : Ob 𝓒} → 𝐹◂ {S} id₍ A ₎ ≡ id
    rmap-id : {A : Ob 𝓒} {S : Ob 𝓓} → 𝐹▸ {A} id₍ S ₎ ≡ id
    lmap-∘ : ∀ {S A B C} {f : 𝓒 ⦅ A , B ⦆} {g : 𝓒 ⦅ B , C ⦆}
      → 𝐹◂ {S} (g ∘ f) ≡ 𝐹◂(g) ∘ 𝐹◂(f)
    rmap-∘ : ∀ {A S T U} {p : 𝓓 ⦅ S , T ⦆} {q : 𝓓 ⦅ T , U ⦆}
      → 𝐹▸ {A} (q ∘ p) ≡ 𝐹▸(q) ∘ 𝐹▸(p)
    lrmap : ∀ {A B S T} {f : 𝓒 ⦅ A , B ⦆} {p : 𝓓 ⦅ S , T ⦆}
      → 𝐹◂(f) ∘ 𝐹▸(p) ≡ 𝐹▸(p) ∘ 𝐹◂(f)

  infix 6 _₀₍_,_₎ _◂_ _▸_
  _₀₍_,_₎ = map₀
  _◂_     = lmap
  _▸_     = rmap

open Bifunctor public

infix 4 _×̅_⟶_
_×̅_⟶_ = Bifunctor

{-# DISPLAY Bifunctor = _×̅_⟶_ #-}
{-# DISPLAY map₀ = _₀₍_,_₎ #-}
{-# DISPLAY lmap = _◂_     #-}
{-# DISPLAY rmap = _▸_     #-}

private variable
  𝓒 𝓓 𝓔 𝓧 : Category

Left : 𝓒 ×̅ 𝓓 ⟶ 𝓔 → Ob 𝓓 → 𝓒 ⟶ 𝓔
Left 𝐹 S = record
  { map₀ = λ A → 𝐹 ₀₍ A , S ₎
  ; map₁ = λ f → 𝐹 ◂ f
  ; resp-id = lmap-id 𝐹
  ; resp-∘  = lmap-∘  𝐹
  }

Right : 𝓒 ×̅ 𝓓 ⟶ 𝓔 → Ob 𝓒 → 𝓓 ⟶ 𝓔
Right 𝐹 A = record
  { map₀ = λ S → 𝐹 ₀₍ A , S ₎
  ; map₁ = λ p → 𝐹 ▸ p
  ; resp-id = rmap-id 𝐹
  ; resp-∘  = rmap-∘  𝐹
  }

Flip : 𝓒 ×̅ 𝓓 ⟶ 𝓔 → 𝓓 ×̅ 𝓒 ⟶ 𝓔
Flip 𝐹 = record
  { map₀ = flip (map₀ 𝐹)
  ; lmap = rmap 𝐹
  ; rmap = lmap 𝐹
  ; lmap-id = rmap-id 𝐹
  ; rmap-id = lmap-id 𝐹
  ; lmap-∘  = rmap-∘  𝐹
  ; rmap-∘  = lmap-∘  𝐹
  ; lrmap = sym (lrmap 𝐹)
  }

Curry : 𝓒 ×̅ 𝓓 ⟶ 𝓔 → 𝓒 ⟶ [ 𝓓 , 𝓔 ]
Curry 𝐹 = record
  { map₀ = λ A → record
    { map₀ = λ S → 𝐹 ₀₍ A , S ₎ 
    ; map₁ = λ p → 𝐹 ▸ p
    ; resp-id = rmap-id 𝐹
    ; resp-∘  = rmap-∘  𝐹
    }
  ; map₁ = λ f → record
    { component = 𝐹 ◂ f
    ; natural   = lrmap 𝐹
    }
  ; resp-id = ext λ {_} → lmap-id 𝐹
  ; resp-∘  = ext λ {_} → lmap-∘  𝐹
  }

Uncurry : 𝓒 ⟶ [ 𝓓 , 𝓔 ] → 𝓒 ×̅ 𝓓 ⟶ 𝓔
Uncurry 𝐹 = record
  { map₀ = λ A S → 𝐹 ₀(A) ₀(S)
  ; lmap = λ {S} f → 𝐹 ₁(f) ₍ S ₎
  ; rmap = λ {A} p → 𝐹 ₀(A) ₁(p)
  ; lmap-id = λ {S} → cong _₍ S ₎ (resp-id 𝐹)
  ; rmap-id = λ {A} → resp-id (𝐹 ₀(A))
  ; lmap-∘  = λ {S} → cong _₍ S ₎ (resp-∘ 𝐹)
  ; rmap-∘  = λ {A} → resp-∘ (𝐹 ₀(A))
  ; lrmap   = natural (𝐹 ₁(_))
  }

Flat : 𝓒 ×̅ 𝓓 ⟶ 𝓔 → 𝓒 × 𝓓 ⟶ 𝓔
Flat {𝓔 = 𝓔} 𝐹 = record
  { map₀ = λ (A , S) → 𝐹 ₀₍ A , S ₎
  ; map₁ = λ (f , p) → 𝐹 ▸ p ∘ 𝐹 ◂ f
  ; resp-id = begin
      𝐹 ▸ id ∘ 𝐹 ◂ id ≡⟨ rmap-id 𝐹 ○ lmap-id 𝐹 ⟩
          id ∘     id ≡⟨ ∘-idˡ 𝓔 ⟩
                   id ∎
  ; resp-∘  = λ {_ _ _} {(f , p)} {(g , q)} → begin
      𝐹 ▸(q ∘     p)∘ 𝐹 ◂(g ∘     f) ≡⟨ rmap-∘ 𝐹 ○ lmap-∘ 𝐹 ⟩
     (𝐹 ▸ q ∘ 𝐹 ▸ p)∘(𝐹 ◂ g ∘ 𝐹 ◂ f) ≡⟨ ∘-assoc! 𝓔 ⟩
      𝐹 ▸ q ∘(𝐹 ▸ p ∘ 𝐹 ◂ g)∘ 𝐹 ◂ f  ≡⟨ - ○ lrmap 𝐹 ○ - ⟨
      𝐹 ▸ q ∘(𝐹 ◂ g ∘ 𝐹 ▸ p)∘ 𝐹 ◂ f  ≡⟨ ∘-assoc! 𝓔 ⟩
     (𝐹 ▸ q ∘ 𝐹 ◂ g)∘(𝐹 ▸ p ∘ 𝐹 ◂ f) ∎
  }

private
  _ : {𝐹 : 𝓒 ×̅ 𝓓 ⟶ 𝓔} → Uncurry (Curry 𝐹) ≡ 𝐹
  _ = refl

  _ : {𝐹 : 𝓒 ⟶ [ 𝓓 , 𝓔 ]} → Curry (Uncurry 𝐹) ≡ 𝐹
  _ = ext (refl , refl)

  _ : {𝐹 : 𝓒 ×̅ 𝓓 ⟶ 𝓔} → Flip (Flip 𝐹) ≡ 𝐹
  _ = refl

  _ : {𝐹 : 𝓒 ×̅ 𝓓 ⟶ 𝓔} → Right (Flip 𝐹) ≡ Left 𝐹
  _ = refl

  _ : {𝐹 : 𝓒 ×̅ 𝓓 ⟶ 𝓔} → Left (Flip 𝐹) ≡ Right 𝐹
  _ = refl

  _ : (𝐹 : 𝓒 ×̅ 𝓓 ⟶ 𝓔) → Flat (Flip 𝐹) ≡ Flat 𝐹 ∘ swap
  _ = λ 𝐹 → ext (refl , ext λ _ → lrmap 𝐹)

infix 5 _∘ˡ_ _∘ʳ_

_∘ˡ_ : (𝐺 : 𝓒 ×̅ 𝓓 ⟶ 𝓔)
     → (𝐹 : 𝓧 ⟶ 𝓒)
     →      𝓧 ×̅ 𝓓 ⟶ 𝓔
𝐺 ∘ˡ 𝐹 = record
  { map₀ = λ A S → 𝐺 ₀₍ 𝐹 ₀(A) , S ₎
  ; lmap = 𝐺 ◂_ ∘ 𝐹 ₁_
  ; lmap-id = trans (cong (𝐺 ◂_) (resp-id 𝐹)) (lmap-id 𝐺)
  ; lmap-∘  = trans (cong (𝐺 ◂_) (resp-∘  𝐹)) (lmap-∘  𝐺)
  ; rmap    = 𝐺 .rmap
  ; rmap-id = 𝐺 .rmap-id
  ; rmap-∘  = 𝐺 .rmap-∘
  ; lrmap   = 𝐺 .lrmap
  }

_∘ʳ_ : (𝐺 : 𝓒 ×̅ 𝓓 ⟶ 𝓔)
     → (𝐹 : 𝓧 ⟶ 𝓓)
     →      𝓒 ×̅ 𝓧 ⟶ 𝓔
𝐺 ∘ʳ 𝐹 = record
  { map₀ = λ A S → 𝐺 ₀₍ A , 𝐹 ₀(S) ₎
  ; rmap = 𝐺 ▸_ ∘ 𝐹 ₁_
  ; rmap-id = trans (cong (𝐺 ▸_) (resp-id 𝐹)) (rmap-id 𝐺)
  ; rmap-∘  = trans (cong (𝐺 ▸_) (resp-∘  𝐹)) (rmap-∘  𝐺)
  ; lmap    = 𝐺 .lmap
  ; lmap-id = 𝐺 .lmap-id
  ; lmap-∘  = 𝐺 .lmap-∘
  ; lrmap   = 𝐺 .lrmap
  }

private
  _ : {𝐺 : 𝓒 ×̅ 𝓓 ⟶ 𝓔} {𝐹 : 𝓧 ⟶ 𝓒}
    → Flat 𝐺 ∘ 𝐹 ×₁ id ≡ Flat (𝐺 ∘ˡ 𝐹)
  _ = ext (refl , refl)

  _ : {𝐺 : 𝓒 ×̅ 𝓓 ⟶ 𝓔} {𝐹 : 𝓧 ⟶ 𝓓}
    → Flat 𝐺 ∘ id ×₁ 𝐹 ≡ Flat (𝐺 ∘ʳ 𝐹)
  _ = ext (refl , refl)

  _ : {𝐺 : 𝓒 ×̅ 𝓓 ⟶ 𝓔} {𝐹 : 𝓧 ⟶ 𝓒} {S : Ob 𝓓}
    → Left (𝐺 ∘ˡ 𝐹) S ≡ Left 𝐺 S ∘ 𝐹
  _ = refl

  _ : {𝐺 : 𝓒 ×̅ 𝓓 ⟶ 𝓔} {𝐹 : 𝓧 ⟶ 𝓒} {A : Ob 𝓧}
    → Right (𝐺 ∘ˡ 𝐹) A ≡ Right 𝐺 (𝐹 ₀(A))
  _ = refl

  _ : {𝐺 : 𝓒 ×̅ 𝓓 ⟶ 𝓔} {𝐹 : 𝓧 ⟶ 𝓓} {A : Ob 𝓒}
    → Right (𝐺 ∘ʳ 𝐹) A ≡ Right 𝐺 A ∘ 𝐹
  _ = refl

  _ : {𝐺 : 𝓒 ×̅ 𝓓 ⟶ 𝓔} {𝐹 : 𝓧 ⟶ 𝓓} {S : Ob 𝓧}
    → Left (𝐺 ∘ʳ 𝐹) S ≡ Left 𝐺 (𝐹 ₀(S))
  _ = refl

Eval : [ 𝓒 , 𝓓 ] ×̅ 𝓒 ⟶ 𝓓
Eval {𝓒} {𝓓} = record
  { map₀ = λ  𝐹  A → 𝐹 ₀(A)
  ; rmap = λ {𝐹} f → 𝐹 ₁(f)
  ; rmap-id = λ {𝐹} → 𝐹 .resp-id
  ; rmap-∘  = λ {𝐹} → 𝐹 .resp-∘
  ; lmap = λ {A} α → α ₍ A ₎
  ; lmap-id = refl
  ; lmap-∘  = refl
  ; lrmap = λ { {f = α} → natural α }
  }

-$_ : (A : Ob 𝓒) → [ 𝓒 , 𝓓 ] ⟶ 𝓓
-$ A = record
  { map₀ = λ 𝐹 → 𝐹 ₀(A)
  ; map₁ = λ α → α ₍ A ₎
  ; resp-id = refl
  ; resp-∘  = refl
  }

private
  _ : Flat Eval ≡ ev [ i ↦ [ 𝓒 , 𝓓 ] × 𝓒 ⟶ 𝓓 ]
  _ = refl

  _ : {A : Ob 𝓒} → Left Eval A ≡ -$ A [ i ↦ [ 𝓒 , 𝓓 ] ⟶ 𝓓 ]
  _ = refl

  _ : {𝐹 : 𝓒 ⟶ 𝓓} → Right Eval 𝐹 ≡ 𝐹
  _ = refl

binatural : {𝐹 𝐺 : 𝓒 ×̅ 𝓓 ⟶ 𝓔}
  → (α : ∀ {A S} → 𝓔 ⦅ 𝐹 ₀₍ A , S ₎ , 𝐺 ₀₍ A , S ₎ ⦆)
  → (natural₁ : ∀ {S A B} {f : 𝓒 ⦅ A , B ⦆}
      → α{B}{S} ∘ 𝐹 ◂ f ≡ 𝐺 ◂ f ∘ α{A}{S})
  → (natural₂ : ∀ {A S T} {p : 𝓓 ⦅ S , T ⦆}
      → α{A}{T} ∘ 𝐹 ▸ p ≡ 𝐺 ▸ p ∘ α{A}{S})
  → Flat 𝐹 ⟹ Flat 𝐺
binatural {𝓔 = 𝓔} {𝐹} {𝐺} α natural₁ natural₂ = record
  { component = α
  ; natural = λ {(A , S)} {(B , T)} {(f , p)} → begin
      α ∘(𝐹 ▸ p ∘ 𝐹 ◂ f) ≡⟨ ∘-assoc 𝓔 ⟨
     (α ∘ 𝐹 ▸ p)∘ 𝐹 ◂ f  ≡⟨ natural₂ ○ - ⟩
     (𝐺 ▸ p ∘ α)∘ 𝐹 ◂ f  ≡⟨ ∘-assoc 𝓔 ⟩
      𝐺 ▸ p ∘(α ∘ 𝐹 ◂ f) ≡⟨ - ○ natural₁ ⟩
      𝐺 ▸ p ∘(𝐺 ◂ f ∘ α) ≡⟨ ∘-assoc 𝓔 ⟨
     (𝐺 ▸ p ∘ 𝐺 ◂ f)∘ α  ∎
  }
