{-# LANGUAGE GADTs, UnicodeSyntax #-}
module Pie.Syntax.Term where
import Pie.Syntax.Weakening
import Pie.Syntax.Variable

data Tm where
  Set   ∷           Tm
  Pi    ∷ Tm → Tm → Tm
  Sigma ∷ Tm → Tm → Tm
  Unit  ∷           Tm
  Sum   ∷ Tm → Tm → Tm

  Var ∷ Var     → Tm
  Lam ∷ Tm      → Tm
  App ∷ Tm → Tm → Tm

  Cons ∷ Tm → Tm → Tm
  Car  ∷ Tm      → Tm
  Cdr  ∷ Tm      → Tm

  Sole ∷ Tm

  Inj₁ ∷ Tm                → Tm
  Inj₂ ∷ Tm                → Tm
  Case ∷ Tm → Tm → Tm → Tm → Tm
  deriving (Show)

renᵀᵐ ∷ Ren → Tm → Tm
renᵀᵐ w (Set            ) = Set
renᵀᵐ w (Pi    σ τ      ) = Pi    (renᵀᵐ  w σ) (renᵀᵐ (Keep w) τ)
renᵀᵐ w (Sigma σ τ      ) = Sigma (renᵀᵐ  w σ) (renᵀᵐ (Keep w) τ)
renᵀᵐ w (Unit           ) = Unit
renᵀᵐ w (Sum   σ τ      ) = Sum   (renᵀᵐ  w σ) (renᵀᵐ w τ)
renᵀᵐ w (Var   x        ) = Var   (renⱽᵃʳ w x)
renᵀᵐ w (Lam   t        ) = Lam   (renᵀᵐ  (Keep w) t)
renᵀᵐ w (App   t u      ) = App   (renᵀᵐ  w t) (renᵀᵐ w u)
renᵀᵐ w (Cons  t u      ) = Cons  (renᵀᵐ  w t) (renᵀᵐ w u)
renᵀᵐ w (Car   t        ) = Car   (renᵀᵐ  w t)
renᵀᵐ w (Cdr   t        ) = Cdr   (renᵀᵐ  w t)
renᵀᵐ w (Inj₁  t        ) = Inj₁  (renᵀᵐ  w t)
renᵀᵐ w (Inj₂  t        ) = Inj₂  (renᵀᵐ  w t)
renᵀᵐ w (Case  σ i₁ i₂ t) = Case  (renᵀᵐ  w σ)
                                  (renᵀᵐ  (Keep w) i₁)
                                  (renᵀᵐ  (Keep w) i₂)
                                  (renᵀᵐ  w t)
