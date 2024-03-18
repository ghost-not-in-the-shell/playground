module Prelude.Reflection.Error where
open import Prelude.String
open import Prelude.Reflection.Name
open import Prelude.Reflection.Term

data Error : Set where
  str  : String  → Error
  term : Term    → Error
  patt : Pattern → Error
  name : Name    → Error

{-# BUILTIN AGDAERRORPART Error #-}
