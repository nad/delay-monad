------------------------------------------------------------------------
-- A type used to index a combined definition of strong and weak
-- bisimilarity and expansion
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Delay-monad.Bisimilarity.Kind where

open import Equality.Propositional
open import Prelude

-- The three different relations are defined as a single relation,
-- indexed by the Kind type.

data Not-strong-kind : Type where
  weak expansion : Not-strong-kind

data Kind : Type where
  strong : Kind
  other  : Not-strong-kind → Kind

-- Kind equality is decidable.

infix 4 _≟-Kind_ _≟-Not-strong-kind_

_≟-Not-strong-kind_ : Decidable-equality Not-strong-kind
weak      ≟-Not-strong-kind weak      = yes refl
weak      ≟-Not-strong-kind expansion = no λ ()
expansion ≟-Not-strong-kind weak      = no λ ()
expansion ≟-Not-strong-kind expansion = yes refl

_≟-Kind_ : Decidable-equality Kind
_≟-Kind_ strong     strong     = yes refl
_≟-Kind_ strong     (other _)  = no λ()
_≟-Kind_ (other _)  strong     = no λ()
_≟-Kind_ (other k₁) (other k₂) =
  ⊎-map (cong other)
        (λ { hyp refl → hyp refl })
        (k₁ ≟-Not-strong-kind k₂)
