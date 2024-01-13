{-# OPTIONS --type-in-type #-}
module Category where
open import Prelude

record CategoricalOp {ob : Set} (hom : ob → ob → Set) : Set where
  infixr 5 _∘_
  field
    id  : ∀ {A} → hom A A
    _∘_ : ∀ {A B C} → hom B C → hom A B → hom A C

  id₍_₎ : ∀ A → hom A A
  id₍ A ₎ = id

open CategoricalOp ⦃...⦄ public

{-# DISPLAY CategoricalOp.id    _ = id    #-}
{-# DISPLAY CategoricalOp.id₍_₎ _ = id₍_₎ #-}
{-# DISPLAY CategoricalOp._∘_   _ = _∘_   #-}

record Category : Set where
  field
    ob : Set
    hom : ob → ob → Set
    ⦃ op ⦄ : CategoricalOp hom

    ∘-identityˡ : ∀ {A B} {f : hom A B} → id ∘ f ≡ f
    ∘-identityʳ : ∀ {A B} {f : hom A B} → f ∘ id ≡ f
    ∘-assoc : ∀ {A B C D} {f : hom A B} {g : hom B C} {h : hom C D}
      → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)

open Category public hiding (op)

infix 4 _∣_⟶_
_∣_⟶_ = hom
{-# DISPLAY hom 𝓒 A B = 𝓒 ∣ A ⟶ B #-}

record Functor (𝓒 𝓓 : Category) : Set where
  field
    map₀ : ob 𝓒 → ob 𝓓
    map₁ : ∀ {A B} → 𝓒 ∣ A ⟶ B → 𝓓 ∣ map₀ A ⟶ map₀ B

  private
    𝓕₀ = map₀
    𝓕₁ = map₁

  field
    resp-id : ∀ {A} → 𝓕₁(id) ≡ id₍ 𝓕₀(A) ₎
    resp-∘  : ∀ {A B C} {f : 𝓒 ∣ A ⟶ B} {g : 𝓒 ∣ B ⟶ C}
      → 𝓕₁(g ∘ f) ≡ 𝓕₁(g) ∘ 𝓕₁(f)

open Functor public

infix 4 _⟶_
_⟶_ = Functor
{-# DISPLAY Functor = _⟶_ #-}

infix 6 _₀_ _₁_
_₀_ = map₀
_₁_ = map₁
{-# DISPLAY map₀ 𝓕 A = 𝓕 ₀(A) #-}
{-# DISPLAY map₁ 𝓕 f = 𝓕 ₁(f) #-}

record _≡functor_ {𝓒 𝓓} (𝓕 𝓖 : 𝓒 ⟶ 𝓓) : Set where
  constructor _,_
  field
    map₀⁼ : 𝓕 ₀_ ≡ 𝓖 ₀_
    map₁⁼ : 𝓕 ₁_ ≡ 𝓖 ₁_ [ (λ map₀ → ∀ {A B} → 𝓒 ∣ A ⟶ B → 𝓓 ∣ map₀ A ⟶ map₀ B) ↓ map₀⁼ ]

functor⁼ : ∀ {𝓒 𝓓} {𝓕 𝓖 : 𝓒 ⟶ 𝓓} → 𝓕 ≡functor 𝓖 → 𝓕 ≡ 𝓖
functor⁼ {𝓒} {𝓓} {𝓕} {𝓖} (refl , refl) =
  irrelevance (ƛ⁼ $                     uip (resp-id 𝓕) (resp-id 𝓖))
              (ƛ⁼ $ ƛ⁼ $ ƛ⁼ $ ƛ⁼ $ ƛ⁼ $ uip (resp-∘  𝓕) (resp-∘  𝓖))
  where
    Resp-id = ∀ {A} → 𝓖 ₁(id) ≡ id₍ 𝓖 ₀(A) ₎
    Resp-∘  = ∀ {A B C} {f : hom 𝓒 A B} {g : hom 𝓒 B C} → 𝓖 ₁(g ∘ f) ≡ 𝓖 ₁(g) ∘ 𝓕 ₁(f)
    
    irrelevance : ∀ {𝓕-resp-id 𝓖-resp-id : Resp-id}
                    {𝓕-resp-∘  𝓖-resp-∘  : Resp-∘ }
                  → 𝓕-resp-id ≡ 𝓖-resp-id [ Resp-id ]
                  → 𝓕-resp-∘  ≡ 𝓖-resp-∘  [ Resp-∘  ]
                  → record { map₀ = 𝓖 ₀_; map₁ = 𝓖 ₁_; resp-id = 𝓕-resp-id; resp-∘ = 𝓕-resp-∘ }
                  ≡ record { map₀ = 𝓖 ₀_; map₁ = 𝓖 ₁_; resp-id = 𝓖-resp-id; resp-∘ = 𝓖-resp-∘ }
                  [ 𝓒 ⟶ 𝓓 ]
    irrelevance refl refl = refl

record NaturalTransformation {𝓒 𝓓} (𝓕 𝓖 : 𝓒 ⟶ 𝓓) : Set where
  field
    component : ∀ {A} → 𝓓 ∣ 𝓕 ₀(A) ⟶ 𝓖 ₀(A)

  private
    η = component

  field
    natural : ∀ {A B} {f : 𝓒 ∣ A ⟶ B} → η ∘ 𝓕 ₁(f) ≡ 𝓖 ₁(f) ∘ η

open NaturalTransformation public

infix 4 _⟹_
_⟹_ = NaturalTransformation
{-# DISPLAY NaturalTransformation 𝓕 𝓖 = 𝓕 ⟹ 𝓖 #-}

infix 6 _⋆
_⋆ = component
{-# DISPLAY component α = α ⋆ #-}

infix 6 _₍_₎
_₍_₎ : ∀ {𝓒 𝓓} {𝓕 𝓖 : 𝓒 ⟶ 𝓓} (α : 𝓕 ⟹ 𝓖) (A : ob 𝓒) → 𝓓 ∣ 𝓕 ₀(A) ⟶ 𝓖 ₀(A)
α ₍ A ₎ = component α {A = A}

natural⁼ : ∀ {𝓒 𝓓} {𝓕 𝓖 : 𝓒 ⟶ 𝓓} {α β : 𝓕 ⟹ 𝓖}
  → component α ≡ component β [ (∀ {A} → 𝓓 ∣ 𝓕 ₀(A) ⟶ 𝓖 ₀(A)) ]
  →           α ≡           β
natural⁼ {𝓒} {𝓓} {𝓕} {𝓖} {α} {β} refl = irrelevance (ƛ⁼ $ ƛ⁼ $ ƛ⁼ $ uip (natural α) (natural β))
  where Natural = ∀ {A B} {f : 𝓒 ∣ A ⟶ B} → β ⋆ ∘ 𝓕 ₁(f) ≡ 𝓖 ₁(f) ∘ β ⋆

        irrelevance : ∀ {α-natural β-natural : Natural}
                      → α-natural ≡ β-natural [ Natural ]
                      → record { component = component β; natural = α-natural }
                      ≡ record { component = component β; natural = β-natural }
                      [ 𝓕 ⟹ 𝓖 ]
        irrelevance refl = refl

Function : Set → Set → Set
Function A B = A → B

instance
  𝓢𝓮𝓽-categoric : CategoricalOp Function
  𝓢𝓮𝓽-categoric = record
    { id  = λ x → x
    ; _∘_ = λ g f x → g (f x)
    }

𝓢𝓮𝓽 : Category
𝓢𝓮𝓽 = record
  { ob = Set
  ; hom = Function
  ; op = 𝓢𝓮𝓽-categoric
  ; ∘-identityˡ = refl
  ; ∘-identityʳ = refl
  ; ∘-assoc = refl
  }
