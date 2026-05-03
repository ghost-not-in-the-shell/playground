module Functor.Bifunctor where
open import Prelude
open import Category.Assoc
open import Category.Base
open import Functor.Base
-- open import Natural.Base
open ApplicativeReasoning

record Bifunctor 𝓒 𝓓 𝓔 : Type where
  infix 6 map₀ lmap rmap
  field
    map₀ : Ob 𝓒 → Ob 𝓓 → Ob 𝓔
  private 𝐹₀₍_,_₎ = map₀
  field
    lmap : ∀ {S A B} → 𝓒 ⦅ A , B ⦆ → 𝓔 ⦅ 𝐹₀₍ A , S ₎ , 𝐹₀₍ B , S ₎ ⦆
    rmap : ∀ {A S T} → 𝓓 ⦅ S , T ⦆ → 𝓔 ⦅ 𝐹₀₍ A , S ₎ , 𝐹₀₍ A , T ₎ ⦆
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

  left : Ob 𝓓 → 𝓒 ⟶ 𝓔
  left S = record
    { map₀ = λ A → map₀ A S
    ; map₁ = λ f → lmap f
    ; resp-id = lmap-id
    ; resp-∘  = lmap-∘
    }

  right : Ob 𝓒 → 𝓓 ⟶ 𝓔
  right A = record
    { map₀ = λ S → map₀ A S
    ; map₁ = λ p → rmap p
    ; resp-id = rmap-id
    ; resp-∘  = rmap-∘
    }

open Bifunctor public renaming
  ( map₀ to _₀₍_,_₎
  ; lmap to _◂_
  ; rmap to _▸_
  )

module _ {𝓒 𝓓 𝓔 : Category} where
  from-bifunctor : Bifunctor 𝓒 𝓓 𝓔 → 𝓒 × 𝓓 ⟶ 𝓔
  from-bifunctor 𝐹 = record
    { map₀ = λ (A , S) → 𝐹 ₀₍ A , S ₎
    ; map₁ = λ (f , p) → 𝐹 ◂(f) ∘ 𝐹 ▸(p)
    ; resp-id = begin
        𝐹 ◂(id)∘ 𝐹 ▸(id) ≡⟨ lmap-id 𝐹 ○ rmap-id 𝐹 ⟩
            id ∘     id  ≡⟨ ∘-idʳ 𝓔 ⟩
            id           ∎
    ; resp-∘ = λ {(A , S)} {(B , T)} {(C , U)} {(f , p)} {(g , q)} → begin
        𝐹 ◂(g ∘     f )∘ 𝐹 ▸(q  ∘     p ) ≡⟨ lmap-∘ 𝐹 ○ rmap-∘ 𝐹 ⟩
       (𝐹 ◂(g)∘ 𝐹 ◂(f))∘(𝐹 ▸(q) ∘ 𝐹 ▸(p)) ≡⟨ ∘-assoc! 𝓔 ⟩
        𝐹 ◂(g)∘(𝐹 ◂(f) ∘ 𝐹 ▸(q))∘ 𝐹 ▸(p)  ≡⟨ - ○ lrmap 𝐹 ○ - ⟩
        𝐹 ◂(g)∘(𝐹 ▸(q) ∘ 𝐹 ◂(f))∘ 𝐹 ▸(p)  ≡⟨ ∘-assoc! 𝓔 ⟩
       (𝐹 ◂(g)∘ 𝐹 ▸(q))∘(𝐹 ◂(f) ∘ 𝐹 ▸(p)) ∎
    }

  _₀₍_,-₎ : (𝐹 : 𝓒 × 𝓓 ⟶ 𝓔) (A : Ob 𝓒) → 𝓓 ⟶ 𝓔
  𝐹 ₀₍ A ,-₎ = record
    { map₀ = λ S → 𝐹 ₀(A  , S)
    ; map₁ = λ p → 𝐹 ₁(id , p)
    ; resp-id = resp-id 𝐹
    ; resp-∘ = λ { {f = p} {q} → begin
        𝐹 ₁(id      , q ∘ p)      ≡⟨ ⦇ (𝐹 ₁_) ⦇ ∘-idʳ 𝓒 , - ⦈ ⦈ ⟨
        𝐹 ₁(id ∘ id , q ∘ p)      ≡⟨ resp-∘ 𝐹 ⟩
        𝐹 ₁(id , q) ∘ 𝐹 ₁(id , p) ∎ }
    }

  _₀₍-,_₎ : (𝐹 : 𝓒 × 𝓓 ⟶ 𝓔) (S : Ob 𝓓) → 𝓒 ⟶ 𝓔
  𝐹 ₀₍-, S ₎ = record
    { map₀ = λ A → 𝐹 ₀(A ,  S)
    ; map₁ = λ f → 𝐹 ₁(f , id)
    ; resp-id = resp-id 𝐹
    ; resp-∘ = λ { {f = f} {g} → begin
        𝐹 ₁(g ∘ f ,      id)      ≡⟨ ⦇ (𝐹 ₁_) ⦇ - , ∘-idˡ 𝓓 ⦈ ⦈ ⟨
        𝐹 ₁(g ∘ f , id ∘ id)      ≡⟨ resp-∘ 𝐹 ⟩
        𝐹 ₁(g , id) ∘ 𝐹 ₁(f , id) ∎ }
    }

  to-bifunctor : 𝓒 × 𝓓 ⟶ 𝓔 → Bifunctor 𝓒 𝓓 𝓔
  to-bifunctor 𝐹 = record
    { map₀ = λ A S → 𝐹 ₀(A , S)
    ; lmap = λ {S} f → 𝐹 ₀₍-, S ₎ ₁(f)
    ; rmap = λ {A} p → 𝐹 ₀₍ A ,-₎ ₁(p)
    ; lmap-id = λ {S} → resp-id (𝐹 ₀₍-, S ₎)
    ; rmap-id = λ {A} → resp-id (𝐹 ₀₍ A ,-₎)
    ; lmap-∘ = λ {S} → resp-∘ (𝐹 ₀₍-, S ₎)
    ; rmap-∘ = λ {A} → resp-∘ (𝐹 ₀₍ A ,-₎)
    ; lrmap = λ { {f = f} {p} → begin
        𝐹 ₁(f , id) ∘ 𝐹 ₁(id , p) ≡⟨ resp-∘ 𝐹 ⟨
        𝐹 ₁(f  ∘ id , id ∘  p)    ≡⟨ ⦇ (𝐹 ₁_) ⦇ sym (∘-idˡʳ 𝓒) , ∘-idˡʳ 𝓓 ⦈ ⦈ ⟩
        𝐹 ₁(id ∘  f , p  ∘ id)    ≡⟨ resp-∘ 𝐹 ⟩
        𝐹 ₁(id , p) ∘ 𝐹 ₁(f , id) ∎ }
    }

{-
  _₁₍_,-₎ : (𝐹 : 𝓒 × 𝓓 ⟶ 𝓔) {A B : Ob 𝓒} (f : 𝓒 ⦅ A , B ⦆) → 𝐹 ₀₍ A ,-₎ ⟹ 𝐹 ₀₍ B ,-₎
  𝐹 ₁₍ f ,-₎ = record
    { component = λ {S} → 𝐹 ₁(f , id)
    ; natural = λ { {f = g} → begin
        𝐹 ₁(f , id) ∘ 𝐹 ₁(id , g) ≡⟨ resp-∘ 𝐹 ⟨
        𝐹 ₁(f ∘ id , id ∘ g)      ≡⟨ ⦇ (𝐹 ₁_) ⦇ sym (∘-idˡʳ 𝓒) , ∘-idˡʳ 𝓓 ⦈ ⦈ ⟩
        𝐹 ₁(id ∘ f , g ∘ id)      ≡⟨ resp-∘ 𝐹 ⟩
        𝐹 ₁(id , g) ∘ 𝐹 ₁(f , id) ∎ }
    }

  _₁₍-,_₎ : (𝐹 : 𝓒 × 𝓓 ⟶ 𝓔) {S T : Ob 𝓓} (g : 𝓓 ⦅ S , T ⦆) → 𝐹 ₀₍-, S ₎ ⟹ 𝐹 ₀₍-, T ₎
  𝐹 ₁₍-, g ₎ = record
    { component = λ {A} → 𝐹 ₁(id , g)
    ; natural = λ { {f = f} → begin
        𝐹 ₁(id , g) ∘ 𝐹 ₁(f , id) ≡⟨ resp-∘ 𝐹 ⟨
        𝐹 ₁(id ∘ f , g ∘ id)      ≡⟨ ⦇ (𝐹 ₁_) ⦇ ∘-idˡʳ 𝓒 , sym (∘-idˡʳ 𝓓) ⦈ ⦈ ⟩
        𝐹 ₁(f ∘ id , id ∘ g)      ≡⟨ resp-∘ 𝐹 ⟩
        𝐹 ₁(f , id) ∘ 𝐹 ₁(id , g) ∎ }
    }

  module BinaturalTransformation {𝐹 𝐺 : 𝓒 × 𝓓 ⟶ 𝓔} where
    _₍_,-₎ : (α : 𝐹 ⟹ 𝐺) (A : Ob 𝓒) → 𝐹 ₀₍ A ,-₎ ⟹ 𝐺 ₀₍ A ,-₎
    α ₍ A ,-₎ = record
      { component = λ {S} → α ₍ A , S ₎
      ; natural = natural α
      }

    _₍-,_₎ : (α : 𝐹 ⟹ 𝐺) (S : Ob 𝓓) → 𝐹 ₀₍-, S ₎ ⟹ 𝐺 ₀₍-, S ₎
    α ₍-, S ₎ = record
      { component = λ {A} → α ₍ A , S ₎
      ; natural = natural α
      }

    binatural : (α : ∀ {A S} → 𝓔 ⦅ 𝐹 ₀(A , S) , 𝐺 ₀(A , S) ⦆)
      → (natural₁ : ∀ {S A B} {f : 𝓒 ⦅ A , B ⦆}
          → α{B}{S} ∘ 𝐹 ₁(f , id) ≡ 𝐺 ₁(f , id) ∘ α{A}{S})
      → (natural₂ : ∀ {A S T} {p : 𝓓 ⦅ S , T ⦆}
          → α{A}{T} ∘ 𝐹 ₁(id , p) ≡ 𝐺 ₁(id , p) ∘ α{A}{S})
      → 𝐹 ⟹ 𝐺
    binatural α natural₁ natural₂ = record
      { component = α
      ; natural = λ { {f = f , p} → begin
          α ∘ 𝐹 ₁(f       ,          p)  ≡⟨ - ○ decompose 𝐹 ⟩
          α ∘(𝐹 ₁(f , id) ∘ 𝐹 ₁(id , p)) ≡⟨ ∘-assoc 𝓔 ⟨
         (α ∘ 𝐹 ₁(f , id))∘ 𝐹 ₁(id , p)  ≡⟨ natural₁ ○ - ⟩
         (𝐺 ₁(f , id) ∘ α)∘ 𝐹 ₁(id , p)  ≡⟨ ∘-assoc 𝓔 ⟩
          𝐺 ₁(f , id) ∘(α ∘ 𝐹 ₁(id , p)) ≡⟨ - ○ natural₂ ⟩
          𝐺 ₁(f , id) ∘(𝐺 ₁(id , p) ∘ α) ≡⟨ ∘-assoc 𝓔 ⟨
         (𝐺 ₁(f , id) ∘ 𝐺 ₁(id , p))∘ α  ≡⟨ decompose 𝐺 ○ - ⟨
          𝐺 ₁(f       ,          p) ∘ α  ∎ }
      } where
        decompose : ∀ (𝐹 : 𝓒 × 𝓓 ⟶ 𝓔) {A B S T} {f : 𝓒 ⦅ A , B ⦆} {p : 𝓓 ⦅ S , T ⦆}
          → 𝐹 ₁(f , p) ≡ 𝐹 ₁(f , id) ∘ 𝐹 ₁(id , p)
        decompose 𝐹 {f = f} {p} = begin
          𝐹 ₁(f      ,      p)      ≡⟨ ⦇ (𝐹 ₁_) ⦇ ∘-idʳ 𝓒 , ∘-idˡ 𝓓 ⦈ ⦈ ⟨
          𝐹 ₁(f ∘ id , id ∘ p)      ≡⟨ resp-∘ 𝐹 ⟩
          𝐹 ₁(f , id) ∘ 𝐹 ₁(id , p) ∎

  open BinaturalTransformation public
-}
