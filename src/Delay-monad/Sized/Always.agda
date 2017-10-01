------------------------------------------------------------------------
-- The "always true" predicate, □
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Delay-monad.Sized.Always where

open import Prelude

open import Delay-monad.Sized
open import Delay-monad.Sized.Monad

-- The "always true" predicate, □.

mutual

  data □ {a p} {A : Size → Set a} (i : Size) (P : A ∞ → Set p) :
         Delay A ∞ → Set (a ⊔ p) where
    now   : ∀ {x} → P x → □ i P (now x)
    later : ∀ {x} → □′ i P (force x) → □ i P (later x)

  record □′ {a p} {A : Size → Set a} (i : Size) (P : A ∞ → Set p)
            (x : Delay A ∞) : Set (a ⊔ p) where
    coinductive
    field
      force : {j : Size< i} → □ j P x

open □′ public

-- □ is closed, in a certain sense, under bind.

□->>= :
  ∀ {i a b p q}
    {A : Size → Set a} {B : Size → Set b}
    {P : A ∞ → Set p} {Q : B ∞ → Set q}
    {x : Delay A ∞} {f : ∀ {i} → A i → Delay B i} →
  □ i P x → (∀ {x} → P x → □ i Q (f x)) → □ i Q (x >>= f)
□->>= (now P-x)   □-f = □-f P-x
□->>= (later □-x) □-f = later λ { .force → □->>= (force □-x) □-f }
