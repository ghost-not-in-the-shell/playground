module Prelude.Bool where

data Bool : Set where
  false : Bool
  true  : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN FALSE false #-}
{-# BUILTIN TRUE  true  #-}
