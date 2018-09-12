{-# LANGUAGE GADTs, UnicodeSyntax #-}
module Pie.Syntax.WeakHeadNormalForm where
import Pie.Syntax.Weakening
import Pie.Syntax.Variable
import Pie.Syntax.Term
import Pie.Syntax.NeutralForm

type Env = [Val]

data Val where
  Ne_ ∷ Val → Ne Val → Val

  Set_   ∷                  Val
  Pi_    ∷ Val → Tm → Env → Val
  Sigma_ ∷ Val → Tm → Env → Val
  Unit_  ∷                  Val
  Sum_   ∷ Val → Val      → Val

  Lam_ ∷ Tm → Env → Val

  Cons_ ∷ Val → Val → Val

  Sole_ ∷ Val

  Inj₁_ ∷ Val → Val
  Inj₂_ ∷ Val → Val
  deriving (Show)

renᴱⁿᵛ ∷ Ren → Env → Env
renᴱⁿᵛ w = map (renⱽᵃˡ w)

renⱽᵃˡ ∷ Ren → Val → Val
renⱽᵃˡ w (Ne_    σ t  ) = Ne_    (renⱽᵃˡ w σ) (renᴺᵉ  w t)
renⱽᵃˡ w (Set_        ) = Set_
renⱽᵃˡ w (Pi_    σ τ ρ) = Pi_    (renⱽᵃˡ w σ)           τ (renᴱⁿᵛ w ρ)
renⱽᵃˡ w (Sigma_ σ τ ρ) = Sigma_ (renⱽᵃˡ w σ)           τ (renᴱⁿᵛ w ρ)
renⱽᵃˡ w (Unit_       ) = Unit_
renⱽᵃˡ w (Sum_   σ τ  ) = Sum_   (renⱽᵃˡ w σ) (renⱽᵃˡ w τ)
renⱽᵃˡ w (Lam_   t ρ  ) = Lam_             t  (renᴱⁿᵛ w ρ)
renⱽᵃˡ w (Cons_  t u  ) = Cons_  (renⱽᵃˡ w t) (renⱽᵃˡ w u)
renⱽᵃˡ w (Sole_       ) = Sole_
renⱽᵃˡ w (Inj₁_  t    ) = Inj₁_  (renⱽᵃˡ w t)
renⱽᵃˡ w (Inj₂_  t    ) = Inj₂_  (renⱽᵃˡ w t)

renᴺᵉ ∷ Ren → Ne Val → Ne Val
renᴺᵉ = mkRenᴺᵉ renⱽᵃˡ

var_ ∷ Val → Var → Val
var_ σ x = Ne_ σ (Var_ x)
