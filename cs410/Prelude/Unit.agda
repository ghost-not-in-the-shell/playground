{-# OPTIONS --type-in-type #-}
module Prelude.Unit where
open import Prelude.Function
open import Prelude.Op

record ⊤ : Set where
  constructor tt

instance
  𝓢𝓮𝓽-terminal : TerminalOp Function
  𝓢𝓮𝓽-terminal = record
    { 𝟙 = ⊤
    ; ! = const tt
    }
