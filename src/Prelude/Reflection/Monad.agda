module Prelude.Reflection.Monad where
open import Agda.Primitive
open import Prelude.Bool
open import Prelude.Equality
open import Prelude.Idiom
open import Prelude.List
open import Prelude.Maybe
open import Prelude.Nat
open import Prelude.Sigma
open import Prelude.String
open import Prelude.Unit
open import Prelude.Reflection.Argument
open import Prelude.Reflection.Error
open import Prelude.Reflection.Meta
open import Prelude.Reflection.Name
open import Prelude.Reflection.Term

private
  variable
    a b : Level
    A : Set a
    B : Set b

postulate
  TC : Set a → Set a

  return' : A → TC A
  bind    : TC A → (A → TC B) → TC B
  error   : List Error → TC A
  catch   : TC A → TC A → TC A

  quote'   : A → TC Term
  unquote' : Term → TC A

  infer     : Term → TC Term
  check     : Term → Term → TC Term
  reduce    : Term → TC Term
  normalise : Term → TC Term
  unify     : Term → Term → TC ⊤
  block     : Blocker → TC A

  with-normalisation : Bool → TC A → TC A
  with-reconstructed : Bool → TC A → TC A
  with-expand-last   : Bool → TC A → TC A
  with-reduce-defs   : (Σ Bool λ _ → List Name) → TC A → TC A
  no-constraints     : TC A → TC A

  debug-print : String → Nat → List Error → TC ⊤

{-# BUILTIN AGDATCM            TC          #-}
{-# BUILTIN AGDATCMRETURN      return'     #-}
{-# BUILTIN AGDATCMBIND        bind        #-}
{-# BUILTIN AGDATCMTYPEERROR   error       #-}
{-# BUILTIN AGDATCMCATCHERROR  catch       #-}
{-# BUILTIN AGDATCMQUOTETERM   quote'      #-}
{-# BUILTIN AGDATCMUNQUOTETERM unquote'    #-}
{-# BUILTIN AGDATCMINFERTYPE   infer       #-}
{-# BUILTIN AGDATCMCHECKTYPE   check       #-}
{-# BUILTIN AGDATCMNORMALISE   normalise   #-}
{-# BUILTIN AGDATCMREDUCE      reduce      #-}
{-# BUILTIN AGDATCMUNIFY       unify       #-}
{-# BUILTIN AGDATCMBLOCK       block       #-}
{-# BUILTIN AGDATCMWITHNORMALISATION with-normalisation #-}
{-# BUILTIN AGDATCMWITHRECONSTRUCTED with-reconstructed #-}
{-# BUILTIN AGDATCMWITHEXPANDLAST    with-expand-last   #-}
{-# BUILTIN AGDATCMWITHREDUCEDEFS    with-reduce-defs   #-}
{-# BUILTIN AGDATCMNOCONSTRAINTS     no-constraints     #-}
{-# BUILTIN AGDATCMDEBUGPRINT        debug-print        #-}

instance
  TC-bind : Bind TC
  TC-bind = record { return = return'; _>>=_  = bind }

  TC-alt : Alt TC
  TC-alt = record { fail = error []; _<|>_ = catch }

debug! : Term → TC A
debug! t = error (str "[DEBUG]: " ∷ term t ∷ [])

record Equality : Set where
  constructor _,_
  field
    lhs : Term
    rhs : Term

get-boundary : Term → TC Equality
get-boundary (def (quote _≡_) (_ h∷ lhs v∷ rhs v∷ [])) = return (lhs , rhs)
get-boundary (meta m ts) = block (meta m)
get-boundary t = error (str "Expected _≡_, given " ∷ term t ∷ [])
