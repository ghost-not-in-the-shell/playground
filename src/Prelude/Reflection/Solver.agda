module Prelude.Reflection.Solver where
open import Prelude.Bool
open import Prelude.Function
open import Prelude.Idiom
open import Prelude.List
open import Prelude.Sigma
open import Prelude.Unit
open import Prelude.Reflection.Error
open import Prelude.Reflection.Name
open import Prelude.Reflection.Monad
open import Prelude.Reflection.Term

solver-failed : ∀ {A : Set} → Term → Term → TC A
solver-failed lhs rhs =
  error $ str "Could not equate the following expressions:\n"
        ∷ term lhs
        ∷ str "\nAnd\n"
        ∷ term rhs
        ∷ []

record Solver : Set where
  field
    don't-reduce : List Name
    translate    : Term → TC Term
    equate       : Term → Term → Term

  solve! : Term → TC ⊤
  solve! hole =
    with-normalisation false $
    with-reduce-defs (false , don't-reduce) $ do
      goal ← infer hole
      debug! goal
--      (lhs , rhs) ← get-boundary goal
--      elhs ← translate lhs
--      erhs ← translate rhs
--      no-constraints (unify hole (equate elhs erhs)) <|> solver-failed elhs erhs
