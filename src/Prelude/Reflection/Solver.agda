module Prelude.Reflection.Solver where
open import Prelude.Prim
open import Prelude.Idiom
open import Prelude.Reflection.Argument
open import Prelude.Reflection.Error
open import Prelude.Reflection.Name
open import Prelude.Reflection.Meta
open import Prelude.Reflection.Monad
open import Prelude.Reflection.Term

solver-failed : ∀ {ℓ} {A : Type ℓ} → Term → Term → TC A
solver-failed lhs rhs =
  error (str "Could not equate the following expressings:\n " ∷
          term lhs ∷
         str "\nAnd\n " ∷
          term rhs ∷ [])

record Equality : Type where
  constructor _,_
  field
    lhs : Term
    rhs : Term

get-boundary : Term → TC Equality
get-boundary (def (quote _≡_) (_ ∷ₕ lhs ∷ᵥ rhs ∷ᵥ [])) = return (lhs , rhs)
get-boundary (meta m ts) = block (meta m)
get-boundary t = error $ str "Expected _≡_, given " ∷ term t ∷ []

record SimpleSolver : Type where
  field
    don't-reduce : List Name
    translate    : Term → Term
    equate       : Term → Term → Term

  solve : Term → TC ⊤
  solve hole =
    with-normalisation false $
    with-reduce-defs (false , don't-reduce) $ do
      goal ← infer hole >>= reduce
      (lhs , rhs) ← get-boundary goal
      elhs ← normalise lhs >>= return ∘ translate
      erhs ← normalise rhs >>= return ∘ translate
      no-constraints (unify hole (equate elhs erhs))
        <|> solver-failed elhs erhs
      

