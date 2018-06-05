module Jellyfish.Prelude.String where
open import Agda.Builtin.String     public
open import Agda.Builtin.FromString public
open import Agda.Builtin.List
open import Jellyfish.Prelude.Bool
open import Jellyfish.Prelude.Char
open import Jellyfish.Prelude.Dec
open import Jellyfish.Prelude.Equality
open import Jellyfish.Prelude.Function
open import Jellyfish.Prelude.List renaming (List to SnocList)

toSnoc : ∀ {𝔞} {A : Set 𝔞} → List A → SnocList A
toSnoc [] = ε
toSnoc (x ∷ xs) = (ε ▻ x) ▻▻ toSnoc xs

private
  record ⊤ : Set where
    constructor tt

instance
  triv : ⊤
  triv = tt

instance
  string-dec-eq : Eq String
  _≟_ ⦃ string-dec-eq ⦄ s₁ s₂ with primStringEquality s₁ s₂
  ... | true  = yes trust-me where postulate trust-me : _
  ... | false = no  trust-me where postulate trust-me : _

  List-Char-is-string : IsString (SnocList Char)
  List-Char-is-string = record
    { Constraint = λ _ → ⊤
    ; fromString = λ s → toSnoc (primStringToList s)
    }
