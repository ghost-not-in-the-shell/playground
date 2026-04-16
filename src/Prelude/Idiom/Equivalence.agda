module Prelude.Idiom.Equivalence where
open import Prelude.Prim

record EquivRel {I : Type} (A : I → Type) (_≈_ : ∀ {i j} → A i → A j → Type) : Type where
  field
    refl  : ∀ {i} {x : A i} → x ≈ x
    sym   : ∀ {i j} {x : A i} {y : A j} → x ≈ y → y ≈ x
    trans : ∀ {i j k} {x : A i} {y : A j} {z : A k} → x ≈ y → y ≈ z → x ≈ z

  refl₍_₎ : ∀ {i} (x : A i) → x ≈ x
  refl₍ x ₎ = refl

  module EquivReasoning where
    private variable
      i j k : I
      x : A i
      y : A j
      z : A k

    infix  1 begin_
    infixr 2 ≈⟨⟩ ≈⟨⟨
    infix  3 _∎

    begin_ : x ≈ y → x ≈ y
    begin p = p

    ≈⟨⟩ : (x : A i) → y ≈ z → x ≈ y → x ≈ z
    ≈⟨⟩ x q p = trans p q

    ≈⟨⟨ : (x : A i) → y ≈ z → y ≈ x → x ≈ z
    ≈⟨⟨ x q p = trans (sym p) q

    _∎ : (x : A i) → x ≈ x
    x ∎ = refl

    syntax ≈⟨⟩ x y≈z x≈y = x ≈⟨ x≈y ⟩ y≈z
    syntax ≈⟨⟨ x y≈z y≈x = x ≈⟨ y≈x ⟨ y≈z

    - = refl

  open EquivReasoning public

open EquivRel ⦃...⦄ public

{-# DISPLAY EquivRel.refl  _ = refl  #-}
{-# DISPLAY EquivRel.sym   _ = sym   #-}
{-# DISPLAY EquivRel.trans _ = trans #-}

