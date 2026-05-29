module Universal.Morphism where
open import Prelude
open import Category.Base
open import Functor.Base
open import Natural.Base
open import Adjoint.UnitCounit

record Morphism {𝓒 𝓓} (X : Ob 𝓒) (𝐹 : 𝓓 ⟶ 𝓒) : Type where
  constructor _,_
  field
    object : Ob 𝓓
  private A = object
  field
    morphism : 𝓒 ⦅ X , 𝐹 ₀(A) ⦆
  private u = morphism
  field
    {mediate} : ∀ {B} (f : 𝓒 ⦅ X , 𝐹 ₀(B) ⦆) → 𝓓 ⦅ A , B ⦆

    {commute} : ∀ {B} {f : 𝓒 ⦅ X , 𝐹 ₀(B) ⦆}
      → let f̅ = mediate f in
        𝐹 ₁(f̅) ∘ u ≡ f

    {unique} : ∀ {B} {f : 𝓒 ⦅ X , 𝐹 ₀(B) ⦆}
      → let f̅ = mediate f in
        {⁇ : 𝓓 ⦅ A , B ⦆}
      → (⁇-commute : 𝐹 ₁(⁇) ∘ u ≡ f)
      → ⁇ ≡ f̅

Initial : ∀ {𝓒 𝓓} (A : Ob 𝓒) (𝑅 : 𝓓 ⟶ 𝓒) → Type
Initial A 𝑅 = Morphism A 𝑅

module LeftAdjoint {𝓒 𝓓} {𝑅 : 𝓓 ⟶ 𝓒} (universal-morphism : ∀ A → Initial A 𝑅) where
  open Morphism
  open ApplicativeReasoning

  private
    𝐿₀ : Ob 𝓒 → Ob 𝓓
    𝐿₀(A) = object (universal-morphism A)

    η : ∀ {A} → 𝓒 ⦅ A , 𝑅 ₀(𝐿₀(A)) ⦆
    η {A} = morphism (universal-morphism A)

    _♯ : ∀ {A S} (f : 𝓒 ⦅ A , 𝑅 ₀(S) ⦆) → 𝓓 ⦅ 𝐿₀(A) , S ⦆
    _♯ {A} = mediate (universal-morphism A)

    ♯-commute : ∀ {A S} {f : 𝓒 ⦅ A , 𝑅 ₀(S) ⦆}
      → 𝑅 ₁(f ♯) ∘ η ≡ f
    ♯-commute {A} = commute (universal-morphism A)

    ♯-unique : ∀ {A S} {f : 𝓒 ⦅ A , 𝑅 ₀(S) ⦆}
      → {⁇ : 𝓓 ⦅ 𝐿₀(A) , S ⦆}
      → (⁇-commute : 𝑅 ₁(⁇) ∘ η ≡ f)
      → ⁇ ≡ f ♯
    ♯-unique {A} = unique (universal-morphism A)

    ♯-unique₂ : ∀ {A S} {f : 𝓒 ⦅ A , 𝑅 ₀(S) ⦆}
      → {⁇₁ ⁇₂ : 𝓓 ⦅ 𝐿₀(A) , S ⦆}
      → (⁇₁-commute : 𝑅 ₁(⁇₁) ∘ η ≡ f)
      → (⁇₂-commute : 𝑅 ₁(⁇₂) ∘ η ≡ f)
      → ⁇₁ ≡ ⁇₂
    ♯-unique₂ ⁇₁-commute ⁇₂-commute =
      trans (♯-unique ⁇₁-commute)
      $ sym (♯-unique ⁇₂-commute)

    𝐿₁ : ∀ {A B} → 𝓒 ⦅ A , B ⦆ → 𝓓 ⦅ 𝐿₀(A) , 𝐿₀(B) ⦆
    𝐿₁(p) = (η ∘ p)♯

    𝐿 : 𝓒 ⟶ 𝓓
    𝐿 = record
      { map₀ = 𝐿₀
      ; map₁ = 𝐿₁
      ; resp-id = sym $ ♯-unique $ begin
          𝑅 ₁ id ∘ η      ≡⟨ resp-id 𝑅 ○ - ⟩
              id ∘ η      ≡⟨ ∘-idˡʳ 𝓒 ⟩
                   η ∘ id ∎
      ; resp-∘ = λ {A B C f g} → sym $ ♯-unique $ begin
          𝑅 ₁(𝐿₁ g ∘     𝐿₁ f) ∘ η  ≡⟨ resp-∘ 𝑅 ○ - ⟩
         (𝑅 ₁(𝐿₁ g)∘ 𝑅 ₁(𝐿₁ f))∘ η  ≡⟨ ∘-assoc 𝓒 ⟩
          𝑅 ₁(𝐿₁ g)∘(𝑅 ₁(𝐿₁ f) ∘ η) ≡⟨ - ○ ♯-commute ⟩
          𝑅 ₁(𝐿₁ g)∘   (η ∘ f)      ≡⟨ ∘-assoc 𝓒 ⟨
         (𝑅 ₁(𝐿₁ g)∘    η)∘ f       ≡⟨ ♯-commute ○ - ⟩
            (η ∘ g)       ∘ f       ≡⟨ ∘-assoc 𝓒 ⟩
             η ∘ g        ∘ f       ∎
      }

    unit : id ⟹ 𝑅 ∘ 𝐿
    unit = record
      { component = η
      ; natural = sym ♯-commute
      }

    ε : ∀ {S} → 𝓓 ⦅ 𝐿₀(𝑅 ₀(S)) , S ⦆
    ε = id ♯

    counit : 𝐿 ∘ 𝑅 ⟹ id
    counit = record
      { component = ε
      ; natural = λ {S T p} →
        let commute₁ : 𝑅 ₁(id ♯ ∘ 𝐿 ₁(𝑅 ₁ p)) ∘ η ≡ 𝑅 ₁ p
            commute₁ = begin
              𝑅 ₁(id ♯ ∘     𝐿 ₁(𝑅 ₁ p)) ∘ η  ≡⟨ resp-∘ 𝑅 ○ - ⟩
             (𝑅 ₁(id ♯)∘ 𝑅 ₁(𝐿 ₁(𝑅 ₁ p)))∘ η  ≡⟨ ∘-assoc 𝓒 ⟩
              𝑅 ₁(id ♯)∘(𝑅 ₁(𝐿 ₁(𝑅 ₁ p)) ∘ η) ≡⟨ - ○ ♯-commute ⟩
              𝑅 ₁(id ♯)∘    (η ∘ 𝑅 ₁ p)       ≡⟨ ∘-assoc 𝓒 ⟨
             (𝑅 ₁(id ♯)∘     η)∘ 𝑅 ₁ p        ≡⟨ ♯-commute ○ - ⟩
                  id           ∘ 𝑅 ₁ p        ≡⟨ ∘-idˡ 𝓒 ⟩
                                 𝑅 ₁ p        ∎

            commute₂ : 𝑅 ₁(p ∘ id ♯) ∘ η ≡ 𝑅 ₁ p
            commute₂ = begin
              𝑅 ₁(p ∘     id ♯) ∘ η  ≡⟨ resp-∘ 𝑅 ○ - ⟩
             (𝑅 ₁ p ∘ 𝑅 ₁(id ♯))∘ η  ≡⟨ ∘-assoc 𝓒 ⟩
              𝑅 ₁ p ∘(𝑅 ₁(id ♯) ∘ η) ≡⟨ - ○ ♯-commute ⟩
              𝑅 ₁ p ∘     id         ≡⟨ ∘-idʳ 𝓒 ⟩
              𝑅 ₁ p                  ∎
        in ♯-unique₂ commute₁ commute₂
      }

    zig : ∀ {A} → ε{𝐿₀(A)} ∘ 𝐿₁(η{A}) ≡ id
    zig = let commute₁ : 𝑅 ₁(id ♯ ∘ 𝐿₁ η) ∘ η ≡ η
              commute₁ = begin
                𝑅 ₁(id ♯ ∘     𝐿 ₁ η) ∘ η  ≡⟨ resp-∘ 𝑅 ○ - ⟩
               (𝑅 ₁(id ♯)∘ 𝑅 ₁(𝐿 ₁ η))∘ η  ≡⟨ ∘-assoc 𝓒 ⟩
                𝑅 ₁(id ♯)∘(𝑅 ₁(𝐿 ₁ η) ∘ η) ≡⟨ - ○ ♯-commute ⟩
                𝑅 ₁(id ♯)∘    (η ∘ η)      ≡⟨ ∘-assoc 𝓒 ⟨
               (𝑅 ₁(id ♯)∘     η)∘ η       ≡⟨ ♯-commute ○ - ⟩
                    id           ∘ η       ≡⟨ ∘-idˡ 𝓒 ⟩
                                   η       ∎

              commute₂ : 𝑅 ₁ id ∘ η ≡ η
              commute₂ = begin
                𝑅 ₁ id ∘ η ≡⟨ resp-id 𝑅 ○ - ⟩
                    id ∘ η ≡⟨ ∘-idˡ 𝓒 ⟩
                         η ∎
          in ♯-unique₂ commute₁ commute₂

    zag : ∀ {S} → 𝑅 ₁(ε{S}) ∘ η{𝑅 ₀(S)} ≡ id
    zag = ♯-commute

  functorial = 𝐿

  adjoint : 𝐿 ⊣ 𝑅
  adjoint = record
    { unit = unit
    ; counit = counit
    ; zig = zig
    ; zag = zag
    }

Terminal : ∀ {𝓒 𝓓} (𝐿 : 𝓒 ⟶ 𝓓) (S : Ob 𝓓) → Type
Terminal {𝓒} {𝓓} 𝐿 S = Morphism {𝓓 ᵒᵖ} {𝓒 ᵒᵖ} S (𝐿 ᵒᵖ)

module RightAdjoint {𝓒 𝓓} {𝐿 : 𝓒 ⟶ 𝓓} (universal-morphism : ∀ S → Terminal 𝐿 S) where
  open LeftAdjoint universal-morphism
    renaming ( functorial to functorial′
             ; adjoint    to adjoint′
             )

  functorial : 𝓓 ⟶ 𝓒
  adjoint    : 𝐿 ⊣ _
  functorial = functorial′ ᵒᵖ
  adjoint    = adjoint′    ᵒᵖ
