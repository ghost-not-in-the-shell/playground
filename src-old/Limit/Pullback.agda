open import Category.Base using (Category)
module Limit.Pullback (𝓒 : Category) where
open Category 𝓒
open import Prelude

record Pullback {A B C} (f : Hom A C) (g : Hom B C) : Set where
  field
    pullback : Ob
    p₁ : Hom pullback A
    p₂ : Hom pullback B
    
