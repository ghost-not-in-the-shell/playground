module Category.Slice 𝓒 where
open import Category.Base hiding (Ob; Hom; ∘-identityˡ; ∘-identityʳ; ∘-assoc; dom)
open import Prelude
open import Functor.Base

open Category 𝓒

module _ X where
  record /-Ob : Set where
    constructor cut
    field
      {dom}  : Ob
      bundle : Hom dom X

  open /-Ob public

  SliceOb = ∃ λ A → Hom A X

  record /-Hom (A B : /-Ob) : Set where
    open /-Ob A renaming (dom to A₀ ; bundle to i)
    open /-Ob B renaming (dom to B₀ ; bundle to j)
    field
      map      : Hom A₀ B₀
      commutes : j ∘ map ≡ i

  open /-Hom public

  SliceHom : SliceOb → SliceOb → Set
  SliceHom (A , π) (A′ , π′) = ∃ λ (f : Hom A A′) → π′ ∘ f ≡ π

  hom⁼ : ∀ {A B} {f g : SliceHom A B}
    → fst f ≡ fst g
    →     f ≡     g
  hom⁼ {_ , π} {_ , π′} {f , f-commute} {.f , g-commute} refl = lemma (uip f-commute g-commute)
    where lemma : f-commute ≡ g-commute → (f , f-commute) ≡ (f , g-commute)
          lemma refl = refl

  Slice : Category
  Slice = record
    { Ob  = SliceOb
    ; Hom = SliceHom
    ; op  = record
      { id  = id , ∘-identityʳ
      ; _∘_ = λ { {_ , π} {_ , π′} {_ , π″} (g , g-commute) (f , f-commute) → g ∘ f , (begin
        π″ ∘ g ∘ f    ≡⟨ sym $ ∘-assoc ⟩
        (π″ ∘ g) ∘ f  ≡⟨ cong (_∘ f) $ g-commute ⟩
        π′ ∘ f        ≡⟨ f-commute ⟩
        π             ∎) }
      }
    ; ∘-identityˡ = hom⁼ ∘-identityˡ
    ; ∘-identityʳ = hom⁼ ∘-identityʳ
    ; ∘-assoc     = hom⁼ ∘-assoc
    }

_! : ∀ {X Y} → Hom X Y → Slice X ⟶ Slice Y
f ! = record
  { map₀ = λ (_ , π) → _ , f ∘ π
  ; map₁ = λ (_ , p) → _ , trans ∘-assoc (cong (f ∘_) p)
  ; resp-id = {!!}
  ; resp-∘  = {!!}
  }
