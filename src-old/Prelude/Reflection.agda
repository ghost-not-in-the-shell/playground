module Prelude.Reflection where
open import Agda.Primitive
open import Prelude.Reflection.Meta public
open import Prelude.Reflection.Term public

variable
  a b : Level
  A : Set a
  B : Set b

postulate
  TC       : Set a → Set a
  returnTC : A → TC A
  bindTC   : TC A → (A → TC B) → TC B
  
  infer : Term → TC Term
  quoteTC : A → TC Term
  blockTC : Blocker → TC A

{-# BUILTIN AGDATCM       TC       #-}
{-# BUILTIN AGDATCMRETURN returnTC #-}
{-# BUILTIN AGDATCMBIND   bindTC   #-}
{-# BUILTIN AGDATCMINFERTYPE infer #-}
{-# BUILTIN AGDATCMQUOTETERM quoteTC #-}
{-# BUILTIN AGDATCMBLOCK     blockTC #-}

block-on-meta : Meta → TC A
block-on-meta m = blockTC (meta m)
