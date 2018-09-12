{-# LANGUAGE UnicodeSyntax #-}
module Pie.TypeChecking.Readback where
import Pie.Syntax.Variable
import Pie.Syntax.Weakening
import Pie.Syntax.Term
import Pie.Syntax.NeutralForm
import Pie.Syntax.WeakHeadNormalForm
import Pie.TypeChecking.Evaluation

quoteᵀʸ ∷ Val → Tm
quoteᵀʸ (Set_        ) = Set
quoteᵀʸ (Pi_    σ τ ρ) = Pi    (quoteᵀʸ σ) (quoteᵀʸ (eval τ (var_ σ Here : ρ)))
quoteᵀʸ (Sigma_ σ τ ρ) = Sigma (quoteᵀʸ σ) (quoteᵀʸ (eval τ (var_ σ Here : ρ)))
quoteᵀʸ (Unit_       ) = Unit
quoteᵀʸ (Sum_   σ τ  ) = Sum   (quoteᵀʸ σ) (quoteᵀʸ τ)

quote ∷ Val → Val→ Tm
quote (Set_        ) σ = quoteᵀʸ σ
quote (Pi_    σ τ ρ) t = Lam (quote (eval τ (var_ σ Here : ρ))
                                    (app_ (renⱽᵃˡ (wk (length ρ)) t) (var_ σ Here)))
quote (Sigma_ σ τ ρ) t = Cons (quote σ (car_ t))
                              (quote (eval τ (car_ t : ρ)) (cdr_ t))
quote (Unit_)        _ = Sole


