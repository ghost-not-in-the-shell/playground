module Category.Iso where
open import Prelude hiding (fwd)
open import Category.Base

record _⦅_≅_⦆ 𝓒 (A B : Ob 𝓒) : Type where
  constructor fwd
  field
    fwd : 𝓒 ⦅ A , B ⦆
    ⦃ iso ⦄ : is-iso (Hom 𝓒) fwd

open _⦅_≅_⦆ renaming (fwd to fwd≅) public
