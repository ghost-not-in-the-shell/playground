module Category.Assoc where
open import Prelude
open import Category.Base

module NbE 𝓒 where
  private variable
    A B C : Ob 𝓒

  infixr 5 _‘∘’_
  data Syn : Ob 𝓒 → Ob 𝓒 → Type where
    ‘id’  : Syn A A
    _‘∘’_ : Syn B C → Syn A B → Syn A C
    ‘_’   : Hom 𝓒 A B → Syn A B

  embed : Syn A B → Hom 𝓒 A B
  embed ‘id’      = id
  embed (g ‘∘’ f) = embed g ∘ embed f
  embed ‘ f ’     = f

  eval : Syn B C → Hom 𝓒 A B → Hom 𝓒 A C
  eval ‘id’      f = f
  eval (h ‘∘’ g) f = eval h (eval g f)
  eval ‘ g ’     f = g ∘ f

  nf : Syn A B → Hom 𝓒 A B
  nf f = eval f id

  eval-sound : (g : Syn B C) {f : Hom 𝓒 A B} → eval g f ≡ embed g ∘ f
  eval-sound ‘id’ = sym (∘-idˡ 𝓒)
  eval-sound (h ‘∘’ g) {f} = begin
    eval  h  (eval  g   f) ≡⟨ eval-sound h ⟩
    embed h ∘(eval  g   f) ≡⟨ - ○ eval-sound g ⟩
    embed h ∘(embed g ∘ f) ≡⟨ ∘-assoc 𝓒 ⟨
   (embed h ∘ embed g)∘ f  ∎
  eval-sound ‘ g ’ = refl

  sound : (f : Syn A B) → nf f ≡ embed f
  sound f = begin
    eval  f   id ≡⟨ eval-sound f ⟩
    embed f ∘ id ≡⟨ ∘-idʳ 𝓒 ⟩
    embed f      ∎

  equate : (f g : Syn A B) → nf f ≡ nf g → embed f ≡ embed g
  equate f g hyp = begin
    embed f ≡⟨ sound f ⟨
    nf    f ≡⟨ hyp ⟩
    nf    g ≡⟨ sound g ⟩
    embed g ∎

module Tactic where
  open import Prelude.Reflection

  don't-reduce : List Name
  don't-reduce = quote CompositionalOp.id
               ∷ quote CompositionalOp._∘_
               ∷ []

  pattern comp-op-args xs = _ ∷ₕ _ ∷ₕ _ ∷ᵥ xs

  pattern “id” =
    def (quote CompositionalOp.id)  (comp-op-args (_ ∷ₕ []))

  pattern _“∘”_ g f =
    def (quote CompositionalOp._∘_) (comp-op-args (_ ∷ₕ _ ∷ₕ _ ∷ₕ g ∷ᵥ f ∷ᵥ []))

  pattern ‘id’      = con (quote NbE.‘id’ )            []
  pattern _‘∘’_ g f = con (quote NbE._‘∘’_) (g ∷ᵥ f ∷ᵥ [])
  pattern ‘_’     f = con (quote NbE.‘_’  ) (     f ∷ᵥ [])

  translate : Term → Term
  translate “id”      = ‘id’
  translate (g “∘” f) = translate g ‘∘’ translate f
  translate f         = ‘ f ’

  “equate” : Term → Term → Term → Term
  “equate” “𝓒” “lhs” “rhs” = def (quote NbE.equate) (“𝓒” ∷ᵥ unknown ∷ₕ unknown ∷ₕ “lhs” ∷ᵥ “rhs” ∷ᵥ “refl” ∷ᵥ [])

  module _ 𝓒 {A B : Ob 𝓒} {f g : 𝓒 ⦅ A , B ⦆} where
    worker : Term → TC ⊤
    worker goal = with-reconstructed true $ with-normalisation true $ with-reduce-defs (false , don't-reduce) do
      “f” ← quote-term f >>= wait-for-type
      “g” ← quote-term g
      “𝓒” ← quote-term 𝓒

      unify goal (“equate” “𝓒” (translate “f”) (translate “g”))

    wrapper : {@(tactic worker) p : f ≡ g} → f ≡ g
    wrapper {p = p} = p
      
  macro
    ∘-assoc! : Term → Term → TC ⊤
    ∘-assoc! 𝓒 hole = unify hole (def (quote wrapper) (𝓒 ∷ᵥ []))

open Tactic using (∘-assoc!) public

module _ 𝓒 where private
  test : {A : Ob 𝓒} {a b c d : 𝓒 ⦅ A , A ⦆} → (id ∘ a) ∘ (b ∘ c) ∘ d ∘ id ≡ a ∘ b ∘ c ∘ d
  test {a = a} {b} {c} {d} = begin
    (id ∘ a) ∘ (b ∘ c) ∘ d ∘ id ≡⟨ ∘-assoc! 𝓒 ⟩
    a ∘ b ∘ c ∘ d ∎
