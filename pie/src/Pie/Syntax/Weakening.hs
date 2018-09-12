{-# LANGUAGE GADTs, NoImplicitPrelude, UnicodeSyntax #-}
module Pie.Syntax.Weakening where
import Prelude hiding (id)

data Ren where
  Done ∷       Ren
  Skip ∷ Ren → Ren
  Keep ∷ Ren → Ren

id ∷ Int → Ren
id 0 = Done
id n = Keep $ id (n-1)

wk :: Int → Ren
wk n = Skip (id n)
