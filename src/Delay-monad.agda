------------------------------------------------------------------------
-- The delay monad, defined coinductively
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Delay-monad where

open import Equality.Propositional
open import Prelude

open import Bijection equality-with-J using (_↔_)

-- The delay monad.

mutual

  data Delay {a} (A : Set a) (i : Size) : Set a where
    now   : A          → Delay A i
    later : Delay′ A i → Delay A i

  record Delay′ {a} (A : Set a) (i : Size) : Set a where
    coinductive
    field
      force : {j : Size< i} → Delay A j

open Delay′ public

module _ {a} {A : Set a} where

  mutual

    -- A non-terminating computation.

    never : Delay A ∞
    never = later never′

    never′ : Delay′ A ∞
    force never′ = never

  -- Removes a later constructor, if possible.

  drop-later : ∀ {i} {j : Size< i} → Delay A i → Delay A j
  drop-later (now   x) = now x
  drop-later (later x) = force x

  -- An unfolding lemma for Delay.

  Delay↔ : ∀ {i} → Delay A i ↔ A ⊎ Delay′ A i
  Delay↔ = record
    { surjection = record
      { logical-equivalence = record
        { to   = λ { (now x) → inj₁ x; (later x) → inj₂ x }
        ; from = [ now , later ]
        }
      ; right-inverse-of = [ (λ _ → refl) , (λ _ → refl) ]
      }
    ; left-inverse-of = λ { (now _) → refl; (later _) → refl }
    }
