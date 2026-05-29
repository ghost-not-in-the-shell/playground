module Representable.Base where
open import Prelude
open import Category.Base
open import Category.Instances.Functors
open import Functor.Base
open import Functor.Instances.Hom
open import Natural.Base
open import Natural.Iso
open import Universal.Element
import Yoneda.Base
open ApplicativeReasoning

record Representable {𝓒 : Category} (𝐹 : 𝓒 ⟶ 𝓢𝓮𝓽) : Type where
  constructor _,_
  field
    object : Ob 𝓒
  private
    A = object
  field
    represents : 𝓒 ⦅ A ,-⦆ ⟹ 𝐹
  private
    α = represents
  field
    ⦃ iso ⦄ : is-iso (Hom [ 𝓒 , 𝓢𝓮𝓽 ]) α

  _ : [ 𝓒 , 𝓢𝓮𝓽 ] ⦅ 𝓒 ⦅ A ,-⦆ ≅ 𝐹 ⦆
  _ = fwd α

-- Corollary 4.3.2 [Basic Category Theroy]
representable→element : ∀ {𝓒} {𝐹 : 𝓒 ⟶ 𝓢𝓮𝓽} → Representable 𝐹 → Element 𝐹
representable→element {𝓒} {𝐹} (A , α) =
  let open Yoneda.Base.Covariant 𝓒 {𝐹}

      instance
        _ : ∀ {B} → is-iso Function {𝓒 ⦅ A , B ⦆} {⌞ 𝐹 ₀(B) ⌟} (α ₍ B ₎)
        _ = Map→Function ⦃ to-component α ⦄

      u : ⌞ 𝐹 ₀(A) ⌟
      u = α ↓

      mediate : ∀ {X} (x : ⌞ 𝐹 ₀(X) ⌟) → 𝓒 ⦅ A , X ⦆
      mediate x = α ⁻¹ ₋ $ x

      commute : ∀ {B} {x : ⌞ 𝐹 ₀(B) ⌟}
        → let x̅ = α ⁻¹ ₋ $ x in
          (𝐹 ₁(x̅) $ u) ≡ x
      commute {B} {x} =
        let x̅ = α ⁻¹ ₋ $ x
        in begin
        (𝐹 ₁(x̅) $ u)        ≡⟨ refl ⟩
        ((u   ↑)₋ $ x̅)      ≡⟨ refl ⟩
        ((α ↓ ↑)₋ $ x̅)      ≡⟨ cong (λ - → (- α)₋ $ x̅) (∘-invʳ _↑) ⟩
        ( α ₋     $ x̅)      ≡⟨ refl ⟩
        ( α ₋ $ α ⁻¹ ₋ $ x) ≡⟨ refl ⟩
        ( α ₋ ∘ α ⁻¹ ₋ $ x) ≡⟨ cong (_$ x) (∘-invʳ (α ₋)) ⟩
        (     id       $ x) ≡⟨ refl ⟩
                         x  ∎

      unique : ∀ {B} {x : ⌞ 𝐹 ₀(B) ⌟}
        → {⁇ : 𝓒 ⦅ A , B ⦆}
        → (⁇-commute : (𝐹 ₁(⁇) $ u) ≡ x)
        → ⁇ ≡ (α ⁻¹ ₋ $ x)
      unique {B} {x} {⁇} ⁇-commute = sym $ begin
        (α ⁻¹ ₋ $ x)                      ≡⟨ cong (α ⁻¹ ₋ $_) ⁇-commute ⟨
        (α ⁻¹ ₋ $ 𝐹 ₁(⁇) $ u)             ≡⟨ refl ⟩
        (α ⁻¹ ₋ $ 𝐹 ₁(⁇) $ α ₋ $ id₍ A ₎) ≡⟨ refl ⟩
        (α ⁻¹ ₋ ∘ 𝐹 ₁(⁇) $ α ₋ $ id₍ A ₎) ≡⟨ cong (_$ α ₋ $ id) (natural (α ⁻¹)) ⟩
        ((⁇ ∘_) ∘ α ⁻¹ ₋ $ α ₋ $ id₍ A ₎) ≡⟨ refl ⟩
        ((⁇ ∘_) ∘ α ⁻¹ ₋ ∘ α ₋ $ id₍ A ₎) ≡⟨ ⦇ refl₍ ⁇ ∘_ ₎ ○ ∘-invˡ (α ₋) $ - ⦈ ⟩
        ((⁇ ∘_) ∘        id    $ id₍ A ₎) ≡⟨ refl ⟩
        ((⁇ ∘_)                $ id₍ A ₎) ≡⟨ refl ⟩
        ( ⁇ ∘                    id₍ A ₎) ≡⟨ ∘-idʳ 𝓒 ⟩
          ⁇                               ∎
  in record
  { object  = A
  ; element = u
  ; mediate = mediate
  ; commute = commute
  ; unique = unique
  }

element→representable : ∀ {𝓒} {𝐹 : 𝓒 ⟶ 𝓢𝓮𝓽} → Element 𝐹 → Representable 𝐹
element→representable {𝓒} {𝐹} A,u =
  let open Yoneda.Base.Covariant 𝓒 {𝐹}
      open Element A,u renaming (object to A; element to u; mediate to _♯)

      α : 𝓒 ⦅ A ,-⦆ ⟹ 𝐹
      α = u ↑

      α₋ : ∀ {X} → 𝓒 ⦅ A , X ⦆ → ⌞ 𝐹 ₀(X) ⌟
      α₋(f) = 𝐹 ₁(f) $ u

      α₋⁻¹ : ∀ {X} → ⌞ 𝐹 ₀(X) ⌟ → 𝓒 ⦅ A , X ⦆
      α₋⁻¹(x) = x ♯

      instance
        _ : ∀ {X} → is-iso Function {𝓒 ⦅ A , X ⦆} α₋
        _ = record
          { bwd = α₋⁻¹
          ; ∘-invˡ = ext λ f → sym (unique refl)
          ; ∘-invʳ = ext λ x → commute
          }
  in record
  { object = A
  ; represents = α
  ; iso = from-component α
  }
