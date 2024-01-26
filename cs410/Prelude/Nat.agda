module Prelude.Nat where

data ℕ : Set where
  zero :     ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

plus : ℕ → ℕ → ℕ
plus zero    n = n
plus (suc m) n = suc (plus m n)
