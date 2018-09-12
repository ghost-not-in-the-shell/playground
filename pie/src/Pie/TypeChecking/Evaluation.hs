{-# LANGUAGE NoImplicitPrelude, UnicodeSyntax #-}
module Pie.TypeChecking.Evaluation where
import Prelude hiding (lookup)
import Pie.Syntax.Variable
import Pie.Syntax.Term
import Pie.Syntax.NeutralForm
import Pie.Syntax.WeakHeadNormalForm

app_ ∷ Val → Val → Val
app_ (Ne_ (Pi_ σ τ ρ) t) u = Ne_ (eval τ (u : ρ)) (App_ t u)
app_ (Lam_ t ρ)          u = eval t (u : ρ)

car_ ∷ Val → Val
car_ (Ne_ (Sigma_ σ τ ρ) t) = Ne_ σ (Car_ t)
car_ (Cons_ t u)            = t

cdr_ ∷ Val → Val
cdr_ p@(Ne_ (Sigma_ σ τ ρ) t) = Ne_ (eval τ (car_ p : ρ)) (Cdr_ t)
cdr_ (Cons_ t u)              = u

case_ ∷ Val → Val → Val → Val → Val
case_ μ i₁ i₂ s@(Ne_ (Sum_ σ τ) t) = Ne_ (app_ μ s) (Case_ μ i₁ i₂ t)
case_ μ i₁ i₂ (Inj₁_ t)            = app_ i₁ t
case_ μ i₁ i₂ (Inj₂_ t)            = app_ i₂ t

lookup ∷ Env → Var → Val
lookup (t:ρ) Here      = t
lookup (t:ρ) (There x) = lookup ρ x

eval ∷ Tm → Env → Val
eval (Set            ) ρ = Set_
eval (Pi    σ τ      ) ρ = Pi_    (eval σ ρ) τ ρ
eval (Sigma σ τ      ) ρ = Sigma_ (eval σ ρ) τ ρ
eval (Unit           ) ρ = Unit_
eval (Sum   σ τ      ) ρ = Sum_   (eval σ ρ) (eval τ ρ)
eval (Var   x        ) ρ = lookup ρ x
eval (App   t u      ) ρ = app_   (eval t ρ) (eval u ρ)
eval (Cons  t u      ) ρ = Cons_  (eval t ρ) (eval u ρ)
eval (Car   t        ) ρ = car_   (eval t ρ)
eval (Cdr   t        ) ρ = cdr_   (eval t ρ)
eval (Sole           ) ρ = Sole_
eval (Inj₁  t        ) ρ = Inj₁_  (eval t ρ)
eval (Inj₂  t        ) ρ = Inj₂_  (eval t ρ)
eval (Case  μ i₁ i₂ t) ρ = case_  (eval μ ρ) (eval i₁ ρ) (eval i₂ ρ) (eval t ρ)
