module Prelude.Reflection.Argument where
open import Prelude.Prim

data Visibility : Type where
  expl impl inst : Visibility

{-# BUILTIN HIDING Visibility #-}
{-# BUILTIN VISIBLE  expl #-}
{-# BUILTIN HIDDEN   impl #-}
{-# BUILTIN INSTANCE inst #-}

data Relevance : Type where
  relevant irrelevant : Relevance

{-# BUILTIN RELEVANCE  Relevance  #-}
{-# BUILTIN RELEVANT   relevant   #-}
{-# BUILTIN IRRELEVANT irrelevant #-}

data Quantity : Type where
  quantity-0 quantity-ω : Quantity

{-# BUILTIN QUANTITY   Quantity   #-}
{-# BUILTIN QUANTITY-0 quantity-0 #-}
{-# BUILTIN QUANTITY-ω quantity-ω #-}

data Modality : Type where
  modality : Relevance → Quantity → Modality

{-# BUILTIN MODALITY             Modality #-}
{-# BUILTIN MODALITY-CONSTRUCTOR modality #-}

pattern default-modality = modality relevant quantity-ω

data ArgInfo : Type where
  arg-info : Visibility → Modality → ArgInfo

{-# BUILTIN ARGINFO    ArgInfo  #-}
{-# BUILTIN ARGARGINFO arg-info #-}

data Arg {ℓ} (A : Type ℓ) : Type ℓ where
  arg : ArgInfo → A → Arg A

{-# BUILTIN ARG    Arg #-}
{-# BUILTIN ARGARG arg #-}

pattern argᵥ x = arg (arg-info expl default-modality) x
pattern argₕ x = arg (arg-info impl default-modality) x
pattern argᵢ x = arg (arg-info inst default-modality) x

infixr 5 _∷ᵥ_ _∷ₕ_ _∷ᵢ_
pattern _∷ᵥ_ x xs = argᵥ x ∷ xs
pattern _∷ₕ_ x xs = argₕ x ∷ xs
pattern _∷ᵢ_ x xs = argᵢ x ∷ xs
