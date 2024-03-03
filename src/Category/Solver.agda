open import Category.Base using (Category)
module Category.Solver where
open import Prelude hiding (id; _∘_)

module NbE (𝐂 : Category) where
  open Category 𝐂
  
  private
    variable
      A B C : Ob

  infixr 5 _“∘”_
  data Syn : Ob → Ob → Set where
    “_”  : Hom A B → Syn A B
    “id” : Syn A A
    _“∘”_ : Syn B C → Syn A B → Syn A C

  instance
    Syn-⟦⟧ : Bracket (Syn A B)
    Syn-⟦⟧ = record { ⟦_⟧ = ⟦_⟧' } where
      ⟦_⟧' : Syn A B → Hom A B
      ⟦ “ f ” ⟧' = f
      ⟦ “id”  ⟧' = id
      ⟦ g “∘” f ⟧' = ⟦ g ⟧' ∘ ⟦ f ⟧'

  Nf : Ob → Ob → Set
  Nf = Star Hom

  instance
    Nf-⟦⟧ : Bracket (Nf A B)
    Nf-⟦⟧ = record { ⟦_⟧ = ⟦_⟧' } where
      ⟦_⟧' : Nf A B → Hom A B
      ⟦ ε ⟧' = id
      ⟦ fs ▻ f ⟧' = ⟦ fs ⟧' ∘ f

  nf : Syn A B → Nf A B
  nf (“ f ”) = ε ▻ f
  nf (“id” ) = ε
  nf (g “∘” f) = nf g ▻▻ nf f

  ⟦⟧-resp-∘ : ∀ (fs : Nf A B) {gs : Nf B C} → ⟦ gs ▻▻ fs ⟧ ≡ ⟦ gs ⟧ ∘ ⟦ fs ⟧
  ⟦⟧-resp-∘ ε = sym ∘-identityʳ
  ⟦⟧-resp-∘ (fs ▻ f) {gs} = begin
    ⟦ gs ▻▻ fs ▻ f ⟧       ≡⟨ refl ⟩
    ⟦  gs ▻▻    fs ⟧ ∘ f   ≡⟨ ⦇ ⟦⟧-resp-∘ fs ∘ refl ⦈ ⟩
    (⟦ gs ⟧ ∘ ⟦ fs ⟧) ∘ f  ≡⟨ ∘-assoc ⟩
    ⟦  gs ⟧ ∘ ⟦ fs ▻ f ⟧   ∎

  sound : ∀ (f : Syn A B) → ⟦ nf f ⟧ ≡ ⟦ f ⟧
  sound (“ f ”) = ∘-identityˡ
  sound (“id” ) = refl
  sound (g “∘” f) = begin
    ⟦ nf g ▻▻    nf f ⟧  ≡⟨ ⟦⟧-resp-∘ $ nf f ⟩
    ⟦ nf g ⟧ ∘ ⟦ nf f ⟧  ≡⟨ ⦇ sound g ∘ sound f ⦈ ⟩
    ⟦    g ⟧ ∘ ⟦    f ⟧  ∎

  equate : ∀ (f g : Syn A B) → nf f ≡ nf g → ⟦ f ⟧ ≡ ⟦ g ⟧
  equate f g hyp = begin
    ⟦    f ⟧  ≡⟨ sound f ⟲⟩
    ⟦ nf f ⟧  ≡⟨ cong ⟦_⟧ hyp ⟩
    ⟦ nf g ⟧  ≡⟨ sound g ⟩
    ⟦    g ⟧  ∎

module Tactic where
  open import Prelude.Reflection

  private
    pattern `id =
      def (quote Categorical.id) (_ h∷ _ h∷ _ v∷ _ h∷ [])

    pattern _`∘_ g f =
      def (quote Categorical._∘_) (_ h∷ _ h∷ _ v∷ _ h∷ _ h∷ _ h∷ g v∷ f v∷ [])

    don't-reduce : List Name
    don't-reduce = quote Categorical.id ∷ quote Categorical._∘_ ∷ []

    translate : Term → TC Term
    translate `id = return $ con (quote NbE.“id”) []
--    translate (g `∘ f) =
    translate (def (quote Categorical._∘_) (_ h∷ _ h∷ _ v∷ _ h∷ _ h∷ _ h∷ g v∷ f v∷ [])) = do
      ef ← translate f
      eg ← translate g
      return $ con (quote NbE._“∘”_) (eg v∷ ef v∷ [])
    translate t = return $ con (quote NbE.“_”) (t v∷ [])

    pattern `refl = con (quote refl) []

    pattern `equate 𝐂 lhs rhs = def (quote NbE.equate) (𝐂 v∷ lhs v∷ rhs v∷ `refl v∷ [])

    solver : Category → TC Solver
    solver 𝐂 = do
      quote' 𝐂 >>= λ 𝐂 → return $ record
        { don't-reduce = don't-reduce
        ; translate = translate
        ; equate = `equate 𝐂
        } {- do
      `𝐂 ← quote' 𝐂
      return (record
      { don't-reduce = don't-reduce
      ; translate = translate
      ; equate = `equate 𝐂
      })
-}

  ∘-assoc! : Category → Term → TC ⊤
  ∘-assoc! 𝐂 t = do
    solver ← solver 𝐂
    let open Solver solver
    solve! t -- solve! t
--      where open Solver (solver 𝐂)

open Tactic public
