open import Category.Base renaming (Ob to ob; Hom to hom)
module CartesianClosed.InternalLanguage (𝓒 : Category) where
open import Prelude

-- Internal language of a category is just the syntactic representation of the
-- category. A category is, by definition, some objects and hom-sets on those
-- objects. Symbols like "g ∘ f" are just syntactic constructs that denotes
-- categorical operations. Those syntactic constructs themselves are actually
-- isomorphic to some logic systems. This is the famous "Curry-Howard-Lambek
-- Correspondence".
--
-- Here let's use cartesian-closed category as an example. The internal language
-- of a cartesian-closed category corresponds to minimal logic.
--
-- On logic side:                       | On Category theory side:
--                                      |
-- ---------------- (WEAKEN)            | ------------------ (WEAKEN)
--  Γ , A |- ↑ : Γ                      |  π₁ : Γ × A --> Γ
--                                      |
--                                      |
-- ------------------- (VAR)            | ------------------ (VAR)
--  Γ , A |- var₀ : A                   |  π₂ : Γ × A --> A
--                                      |
--                                      |
--  Γ , A |-   t :     B                |    t : Γ × A --> B
-- ---------------------- (ABS)         | ----------------------- (ABS)
--  Γ     |- λ t : A → B                |  λ t : Γ     --> B ^ A
--                                      |
--                                      |
--  Γ |-       t : A → B                |              t   : Γ --> B ^ A
--  Γ |-       u : A                    |              u   : Γ --> A
-- ---------------------- (APP)         | ------------------------------- (APP)
--  Γ |- app t u : B                    |  app ∘ ⟨ t , u ⟩ : Γ --> B
--                                      |
--                                      |
--  Γ |-     σ : Δ                      |        σ   : Γ --> Δ
--  Γ |-     t : A                      |        t   : Γ --> A
-- -------------------- (PAIR)          | ------------------------- (PAIR)
--  Γ |- σ , t : Δ , A                  |  ⟨ σ , t ⟩ : Γ --> Δ × A
--                                      |
--                                      |
-- ------------- (EMPTY)                | ------------- (EMPTY)
--  Γ |- [] : ·                         |  ! : Γ --> 𝟙
--                                      |
--                                      |
-- ------------- (ID)                   | -------------- (ID)
--  Γ |- id : Γ                         |  id : Γ --> Γ
--                                      |
--                                      |
--  Γ |-     ρ : Δ                      |      ρ : Γ --> Δ
--  Δ |-     σ : Ξ                      |      σ : Δ --> Ξ
-- ---------------- (COMPOSE)           | ----------------- (COMPOSE)
--  Γ |- σ ∘ ρ : Ξ                      |  σ ∘ ρ : Γ --> Ξ
--
-- Given any cartesian-closed category 𝓒, there is a corresponding logic system
-- with types being the objects of 𝓒 and terms being freely generated from
-- variables, lambda abstraction and function application, etc.
-- This is the internal language of 𝓒. Let's call it 𝓛𝓪𝓷𝓰(𝓒).

data Ob : Set where
  `_ : ob 𝓒 → Ob
  `𝟙   : Ob
  _`×_ : Ob → Ob → Ob
  _`⇒_ : Ob → Ob → Ob

data Hom : Ob → Ob → Set where
  `id : ∀ {`A} → Hom `A `A
  _○_ : ∀ {`A `B `C} → Hom `B `C → Hom `A `B → Hom `A `C

  `π₁ : ∀ {`A `B} → Hom (`A `× `B) `A
  `π₂ : ∀ {`A `B} → Hom (`A `× `B) `B
  `⟨_,_⟩ : ∀ {`A `B `X} → Hom `X `A → Hom `X `B → Hom `X (`A `× `B)

  `! : ∀ {`X} → Hom `X `𝟙
