{-# LANGUAGE GADTs, UnicodeSyntax #-}
module Pie.Syntax.NeutralForm where
import Pie.Syntax.Weakening
import Pie.Syntax.Variable

data Ne nf where
  Var_ ∷ Var        → Ne nf
  App_ ∷ Ne nf → nf → Ne nf

  Car_ ∷ Ne nf → Ne nf
  Cdr_ ∷ Ne nf → Ne nf

  Case_ ∷ nf → nf → nf → Ne nf → Ne nf
  deriving (Show)

mkRenᴺᵉ ∷ (Ren → nf → nf) → Ren → Ne nf → Ne nf
mkRenᴺᵉ renᴺᶠ w t = renᴺᵉ w t
  where renᴺᵉ w (Var_  x        ) = Var_  (renⱽᵃʳ w x)
        renᴺᵉ w (App_  t₁ t₂    ) = App_  (renᴺᵉ  w t₁) (renᴺᶠ w t₂)
        renᴺᵉ w (Car_  t        ) = Car_  (renᴺᵉ  w t)
        renᴺᵉ w (Cdr_  t        ) = Cdr_  (renᴺᵉ  w t)
        renᴺᵉ w (Case_ σ i₁ i₂ t) = Case_ (renᴺᶠ  w σ)
                                          (renᴺᶠ (Keep w) i₁)
                                          (renᴺᶠ (Keep w) i₂)
                                          (renᴺᵉ w t)
