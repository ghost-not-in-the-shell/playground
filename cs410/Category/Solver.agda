module Category.Solver where
open import Prelude
open import Category.Base
open import Functor.Base

infixr 5 _○_
infix  6 `_
data Syn (𝓒 : Category) : Ob 𝓒 → Ob 𝓒 → Set where
  `_ : ∀ {A B} → Hom 𝓒 A B → Syn 𝓒 A B
  `id : ∀ {A} → Syn 𝓒 A A
  _○_ : ∀ {A B C} → Syn 𝓒 B C → Syn 𝓒 A B → Syn 𝓒 A C
  `map : ∀ {𝓧 A B} (𝓕 : 𝓧 ⟶ 𝓒) → Syn 𝓧 A B → Syn 𝓒 (𝓕 ₀(A)) (𝓕 ₀(B))

⟦_⟧ : ∀ {𝓒 A B} → Syn 𝓒 A B → Hom 𝓒 A B
⟦ ` f       ⟧ = f
⟦ `id       ⟧ = id
⟦ `g ○ `f   ⟧ = ⟦ `g ⟧ ∘ ⟦ `f ⟧
⟦ `map 𝓕 `f ⟧ = 𝓕 ₁ ⟦ `f ⟧

data Norm (𝓒 : Category) : Ob 𝓒 → Ob 𝓒 → Set where
  `_ : ∀ {A B} → Hom 𝓒 A B → Norm 𝓒 A B
  `map : ∀ {𝓧 A B} (𝓕 : 𝓧 ⟶ 𝓒) → Norm 𝓧 A B → Norm 𝓒 (𝓕 ₀(A)) (𝓕 ₀(B))

Sp : ∀ 𝓒 → Ob 𝓒 → Ob 𝓒 → Set
Sp 𝓒 A B = Star (Norm 𝓒) A B

⟦_↓⟧ : ∀ {𝓒 A B} → Norm 𝓒 A B → Hom 𝓒 A B
⟦ ` f       ↓⟧ = f
⟦ `map 𝓕 `f ↓⟧ = 𝓕 ₁ ⟦ `f ↓⟧

⟦_⇓⟧ : ∀ {𝓒 A B} → Sp 𝓒 A B → Hom 𝓒 A B
⟦ ε        ⇓⟧ = id
⟦ `f ◅ `fs ⇓⟧ = ⟦ `fs ⇓⟧ ∘ ⟦ `f ↓⟧

norm : ∀ {𝓒 A B} → Syn 𝓒 A B → Sp 𝓒 A B
norm (` f      ) = ε ▻ ` f
norm (`id      ) = ε
norm (`g ○ `f  ) = norm `g ▻▻ norm `f
norm (`map 𝓕 `f) = gmap (`map 𝓕) (norm `f)

module _ {𝓒 : Category} where
  ⟦⟧-commutes-∘ : ∀ {A B C} (`fs : Sp 𝓒 A B) {`gs : Sp 𝓒 B C}
    → ⟦ `gs ▻▻ `fs ⇓⟧ ≡ ⟦ `gs ⇓⟧ ∘ ⟦ `fs ⇓⟧
  ⟦⟧-commutes-∘ ε = sym (∘-identityʳ 𝓒)
  ⟦⟧-commutes-∘ (`fs ▻ `f) {`gs} = begin
    ⟦ `gs ▻▻ `fs ⇓⟧ ∘ ⟦ `f ↓⟧        ≡⟨ ⦇ ⟦⟧-commutes-∘ `fs ∘ refl ⦈ ⟩
    (⟦ `gs ⇓⟧ ∘ ⟦ `fs ⇓⟧) ∘ ⟦ `f ↓⟧  ≡⟨ ∘-assoc 𝓒 ⟩
    ⟦ `gs ⇓⟧ ∘ (⟦ `fs ⇓⟧ ∘ ⟦ `f ↓⟧)  ∎

  ⟦⟧-commutes-map : ∀ {𝓧 A B} {𝓕 : 𝓧 ⟶ 𝓒} (`fs : Sp 𝓧 A B)
    → ⟦ gmap (`map 𝓕) `fs ⇓⟧ ≡ 𝓕 ₁ ⟦ `fs ⇓⟧
  ⟦⟧-commutes-map {𝓕 = 𝓕} ε = sym (resp-id 𝓕)
  ⟦⟧-commutes-map {𝓕 = 𝓕} (`fs ▻ `f) = begin
    ⟦ gmap (`map 𝓕) `fs ⇓⟧ ∘ 𝓕 ₁ ⟦ `f ↓⟧  ≡⟨ ⦇ ⟦⟧-commutes-map `fs ∘ refl ⦈ ⟩
    𝓕 ₁ ⟦ `fs ⇓⟧ ∘ 𝓕 ₁ ⟦ `f ↓⟧            ≡⟨ sym (resp-∘ 𝓕) ⟩
    𝓕 ₁ (⟦ `fs ⇓⟧ ∘ ⟦ `f ↓⟧)              ∎

sound : ∀ {𝓒 A B} (`f : Syn 𝓒 A B) → ⟦ norm `f ⇓⟧ ≡ ⟦ `f ⟧
sound {𝓒} (` f) = ∘-identityˡ 𝓒
sound `id = refl
sound (`g ○ `f) = begin
  ⟦ norm `g ▻▻ norm `f ⇓⟧      ≡⟨ ⟦⟧-commutes-∘ (norm `f) ⟩
  ⟦ norm `g ⇓⟧ ∘ ⟦ norm `f ⇓⟧  ≡⟨ ⦇ sound `g ∘ sound `f ⦈ ⟩
  ⟦ `g ⟧ ∘ ⟦ `f ⟧              ∎
sound (`map 𝓕 `f) = begin
  ⟦ gmap (`map 𝓕) (norm `f) ⇓⟧  ≡⟨ ⟦⟧-commutes-map (norm `f) ⟩
  𝓕 ₁ ⟦ norm `f ⇓⟧              ≡⟨ cong (𝓕 ₁_) (sound `f) ⟩
  𝓕 ₁ ⟦ `f ⟧                    ∎

solve : ∀ 𝓒 {A B} (`f `g : Syn 𝓒 A B) → ⟦ norm `f ⇓⟧ ≡ ⟦ norm `g ⇓⟧ → ⟦ `f ⟧ ≡ ⟦ `g ⟧
solve 𝓒 `f `g hyp = begin
  ⟦      `f  ⟧  ≡⟨ sym (sound `f) ⟩
  ⟦ norm `f ⇓⟧  ≡⟨ hyp ⟩
  ⟦ norm `g ⇓⟧  ≡⟨ sound `g ⟩
  ⟦      `g  ⟧  ∎

module CategoricalReasoning where
  infix 4 ⟦_⟧≡⟦_⟧
  record ⟦_⟧≡⟦_⟧ {𝓒 A B} (`f `g : Syn 𝓒 A B) : Set where
    field
      because : ⟦ `f ⟧ ≡ ⟦ `g ⟧

  open ⟦_⟧≡⟦_⟧ public

  infix  1 _⊨begin_
  infixr 2 _≡[_]_ _≡⟦_⟧_
  infix  3 _⟦∎⟧

  _⊨begin_ : ∀ 𝓒 {A B} {`f `g : Syn 𝓒 A B} → ⟦ `f ⟧≡⟦ `g ⟧ → ⟦ `f ⟧ ≡ ⟦ `g ⟧
  𝓒 ⊨begin p = because p

  _≡[_]_ : ∀ {𝓒 A B} (`f : Syn 𝓒 A B) {`g `h} → ⟦ norm `f ⇓⟧ ≡ ⟦ norm `g ⇓⟧ → ⟦ `g ⟧≡⟦ `h ⟧ → ⟦ `f ⟧≡⟦ `h ⟧
  because (_≡[_]_ `f {`g} p q) = ⟦ `f ⟧ ≡⟨ solve _ `f `g p ⟩ because q

  _≡⟦_⟧_ : ∀ {𝓒 A B} (`f : Syn 𝓒 A B) {`g `h} → ⟦ `f ⟧ ≡ ⟦ `g ⟧ → ⟦ `g ⟧≡⟦ `h ⟧ → ⟦ `f ⟧≡⟦ `h ⟧
  because (`f ≡⟦ p ⟧ q) = ⟦ `f ⟧ ≡⟨ p ⟩ because q

  _⟦∎⟧ : ∀ {𝓒 A B} (`f : Syn 𝓒 A B) → ⟦ `f ⟧≡⟦ `f ⟧
  because (`f ⟦∎⟧) = refl

open CategoricalReasoning public
