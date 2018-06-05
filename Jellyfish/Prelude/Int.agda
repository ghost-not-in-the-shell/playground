module Jellyfish.Prelude.Int where
open import Jellyfish.Prelude.Nat hiding (_+_)

infix 8 +_
data Int : Set where
  +_     : (n : Nat) → Int
  -[1+_] : (n : Nat) → Int

postulate
  _+′_ : Int → Int → Int
  _-′_ : Int → Int → Int
  _*′_ : Int → Int → Int

{-# BUILTIN INTEGER Int #-}
{-# BUILTIN INTEGERPOS +_ #-}
{-# BUILTIN INTEGERNEGSUC -[1+_] #-}
{-# COMPILE GHC Int = type Int #-}
{-# COMPILE GHC _+′_ = (+) #-}
