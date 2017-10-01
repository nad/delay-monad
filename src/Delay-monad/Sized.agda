------------------------------------------------------------------------
-- The delay monad, defined coinductively, with a sized type parameter
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Delay-monad.Sized where

open import Prelude

-- The delay monad.

mutual

  data Delay {a} (A : Size → Set a) (i : Size) : Set a where
    now   : A i        → Delay A i
    later : Delay′ A i → Delay A i

  record Delay′ {a} (A : Size → Set a) (i : Size) : Set a where
    coinductive
    field
      force : {j : Size< i} → Delay A j

open Delay′ public

module _ {a} {A : Size → Set a} where

  mutual

    -- A non-terminating computation.

    never : ∀ {i} → Delay A i
    never = later never′

    never′ : ∀ {i} → Delay′ A i
    force never′ = never

  -- Removes a later constructor, if possible.

  drop-later : Delay A ∞ → Delay A ∞
  drop-later (now   x) = now x
  drop-later (later x) = force x
