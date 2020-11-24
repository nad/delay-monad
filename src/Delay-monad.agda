------------------------------------------------------------------------
-- The delay monad, defined coinductively
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Delay-monad where

open import Equality.Propositional
open import Prelude
open import Prelude.Size

open import Bijection equality-with-J using (_↔_)
open import Conat equality-with-J

-- The delay monad.

mutual

  data Delay {a} (A : Type a) (i : Size) : Type a where
    now   : A          → Delay A i
    later : Delay′ A i → Delay A i

  record Delay′ {a} (A : Type a) (i : Size) : Type a where
    coinductive
    field
      force : {j : Size< i} → Delay A j

open Delay′ public

module _ {a} {A : Type a} where

  mutual

    -- A non-terminating computation.

    never : ∀ {i} → Delay A i
    never = later never′

    never′ : ∀ {i} → Delay′ A i
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

  -- The number of steps in a computation (the number of later
  -- constructors).

  steps : ∀ {i} → Delay A i → Conat i
  steps (now   _) = zero
  steps (later x) = suc λ { .force → steps (x .force) }
