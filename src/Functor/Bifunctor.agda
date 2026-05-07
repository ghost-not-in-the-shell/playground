module Functor.Bifunctor where
open import Prelude
open import Category.Assoc
open import Category.Base
open import Functor.Base
open import Natural.Base
open ApplicativeReasoning

module _ {𝓒 𝓓 𝓔 : Category} where
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

  _₁₍_,-₎ : (𝐹 : 𝓒 × 𝓓 ⟶ 𝓔) {A B : Ob 𝓒} (f : 𝓒 ⦅ A , B ⦆) → 𝐹 ₀₍ A ,-₎ ⟹ 𝐹 ₀₍ B ,-₎
  𝐹 ₁₍ f ,-₎ = record
    { component = 𝐹 ₁(f , id)
    ; natural = λ { {f = g} → begin
        𝐹 ₁(f , id) ∘ 𝐹 ₁(id , g) ≡⟨ resp-∘ 𝐹 ⟨
        𝐹 ₁(f ∘ id , id ∘ g)      ≡⟨ ⦇ (𝐹 ₁_) ⦇ sym (∘-idˡʳ 𝓒) , ∘-idˡʳ 𝓓 ⦈ ⦈ ⟩
        𝐹 ₁(id ∘ f , g ∘ id)      ≡⟨ resp-∘ 𝐹 ⟩
        𝐹 ₁(id , g) ∘ 𝐹 ₁(f , id) ∎ }
    }

  _₁₍-,_₎ : (𝐹 : 𝓒 × 𝓓 ⟶ 𝓔) {S T : Ob 𝓓} (g : 𝓓 ⦅ S , T ⦆) → 𝐹 ₀₍-, S ₎ ⟹ 𝐹 ₀₍-, T ₎
  𝐹 ₁₍-, g ₎ = record
    { component = 𝐹 ₁(id , g)
    ; natural = λ { {f = f} → begin
        𝐹 ₁(id , g) ∘ 𝐹 ₁(f , id) ≡⟨ resp-∘ 𝐹 ⟨
        𝐹 ₁(id ∘ f , g ∘ id)      ≡⟨ ⦇ (𝐹 ₁_) ⦇ ∘-idˡʳ 𝓒 , sym (∘-idˡʳ 𝓓) ⦈ ⦈ ⟩
        𝐹 ₁(f ∘ id , id ∘ g)      ≡⟨ resp-∘ 𝐹 ⟩
        𝐹 ₁(f , id) ∘ 𝐹 ₁(id , g) ∎ }
    }

  module _ {𝐹 𝐺 : 𝓒 × 𝓓 ⟶ 𝓔} where
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
          α ∘(𝐹 ₁(id , p) ∘ 𝐹 ₁(f , id)) ≡⟨ ∘-assoc 𝓔 ⟨
         (α ∘ 𝐹 ₁(id , p))∘ 𝐹 ₁(f , id)  ≡⟨ natural₂ ○ - ⟩
         (𝐺 ₁(id , p)∘ α) ∘ 𝐹 ₁(f , id)  ≡⟨ ∘-assoc 𝓔 ⟩
          𝐺 ₁(id , p)∘(α  ∘ 𝐹 ₁(f , id)) ≡⟨ - ○ natural₁ ⟩
          𝐺 ₁(id , p)∘(𝐺 ₁(f , id) ∘ α)  ≡⟨ ∘-assoc 𝓔 ⟨
         (𝐺 ₁(id , p)∘ 𝐺 ₁(f , id))∘ α   ≡⟨ decompose 𝐺 ○ - ⟨
          𝐺 ₁(f      ,          p) ∘ α   ∎ }
      } where
        decompose : ∀ (𝐹 : 𝓒 × 𝓓 ⟶ 𝓔) {A B S T} {f : 𝓒 ⦅ A , B ⦆} {p : 𝓓 ⦅ S , T ⦆}
          → 𝐹 ₁(f , p) ≡ 𝐹 ₁(id , p) ∘ 𝐹 ₁(f , id)
        decompose 𝐹 {f = f} {p} = begin
          𝐹 ₁(     f , p     )      ≡⟨ ⦇ (𝐹 ₁_) ⦇ ∘-idˡ 𝓒 , ∘-idʳ 𝓓 ⦈ ⦈ ⟨
          𝐹 ₁(id ∘ f , p ∘ id)      ≡⟨ resp-∘ 𝐹 ⟩
          𝐹 ₁(id , p) ∘ 𝐹 ₁(f , id) ∎
