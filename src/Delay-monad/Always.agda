------------------------------------------------------------------------
-- The "always true" predicate, □
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Delay-monad.Always where

open import Prelude
open import Prelude.Size

open import Delay-monad
open import Delay-monad.Monad

-- The "always true" predicate, □.

mutual

  data □ {a p} {A : Type a} (i : Size) (P : A → Type p) :
         Delay A ∞ → Type (a ⊔ p) where
    now   : ∀ {x} → P x → □ i P (now x)
    later : ∀ {x} → □′ i P (force x) → □ i P (later x)

  record □′ {a p} {A : Type a} (i : Size) (P : A → Type p)
            (x : Delay A ∞) : Type (a ⊔ p) where
    coinductive
    field
      force : {j : Size< i} → □ j P x

open □′ public

-- □ is closed, in a certain sense, under bind.

□->>= :
  ∀ {i a b p q}
    {A : Type a} {B : Type b} {P : A → Type p} {Q : B → Type q}
    {x : Delay A ∞} {f : A → Delay B ∞} →
  □ i P x → (∀ {x} → P x → □ i Q (f x)) → □ i Q (x >>=′ f)
□->>= (now P-x)   □-f = □-f P-x
□->>= (later □-x) □-f = later λ { .force → □->>= (force □-x) □-f }
