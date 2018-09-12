{-# LANGUAGE GADTs, UnicodeSyntax #-}
module Pie.Syntax.Variable where
import Pie.Syntax.Weakening

data Var where
  Here  ∷       Var
  There ∷ Var → Var
  deriving (Show)

renⱽᵃʳ ∷ Ren → Var → Var
renⱽᵃʳ (Skip w) x         = There (renⱽᵃʳ w x)
renⱽᵃʳ (Keep w) Here      = Here
renⱽᵃʳ (Keep w) (There x) = There (renⱽᵃʳ w x)
