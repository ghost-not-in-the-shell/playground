module Limit.Instances.Terminal where
open import Prelude
open import Category.Base

module _ 𝓒 where
  record is-terminal 𝟙 : Type where
    no-eta-equality
    field
      mediate : ∀ {X} → 𝓒 ⦅ X , 𝟙 ⦆
    private <>′ = mediate
    field
      unique : ∀ {X} {⁇ : 𝓒 ⦅ X , 𝟙 ⦆} → ⁇ ≡ <>′

    unique₂ : ∀ {X} {⁇₁ ⁇₂ : 𝓒 ⦅ X , 𝟙 ⦆} → ⁇₁ ≡ ⁇₂
    unique₂ = trans unique (sym unique)

  record Terminal : Type where
    no-eta-equality
    field
      apex : Ob 𝓒
      terminal : is-terminal apex

    open is-terminal terminal public

  module 𝟙 ⦃ term : Terminal ⦄ where
    module _ where
      open Terminal term public hiding (apex)

    instance
      terminalOp : TerminalOp (Hom 𝓒)
      terminalOp = record
        { 𝟙  = term .apex
        ; <> = term .mediate
        } where open Terminal

    <>∘ : ∀ {A B} {f : 𝓒 ⦅ A , B ⦆} → <> ∘ f ≡ <>
    <>∘ = unique

{-# DISPLAY Terminal.apex _ = 𝟙 #-}
{-# DISPLAY is-terminal.mediate _ = <> #-}

module _ {𝓒} ⦃ _ : Terminal 𝓒 ⦄ where
  open import Category.Instances.Functors
  open import Functor.Base
  open import Natural.Base

  private instance
    _ = 𝟙.terminalOp 𝓒

  instance
    𝓕𝓾𝓷-terminal : ∀ {𝓑} → Terminal [ 𝓑 , 𝓒 ]
    𝓕𝓾𝓷-terminal {𝓑} =
      let 𝟙′ : 𝓑 ⟶ 𝓒
          𝟙′ = record
            { map₀ = λ _ → 𝟙
            ; map₁ = λ _ → <>
            ; resp-id = sym (𝟙.unique 𝓒)
            ; resp-∘  = sym (𝟙.unique 𝓒)
            }

          <>′ : {𝑋 : 𝓑 ⟶ 𝓒} → 𝑋 ⟹ 𝟙′
          <>′ = record
            { component = <>
            ; natural = 𝟙.unique₂ 𝓒
            }
      in record
      { apex = 𝟙′
      ; terminal = record
        { mediate = <>′
        ; unique = ext λ {A} → 𝟙.unique 𝓒
        }
      }
