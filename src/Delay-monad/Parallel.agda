------------------------------------------------------------------------
-- A combinator for running two computations in parallel
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Delay-monad.Parallel where

import Equality.Propositional as Eq
open import Prelude
open import Prelude.Size

open import Conat Eq.equality-with-J as Conat
  using (zero; suc; force; max)

open import Delay-monad
open import Delay-monad.Bisimilarity
open import Delay-monad.Bisimilarity.Kind
open import Delay-monad.Monad

private

  variable
    a b             : Level
    A B             : Set a
    i               : Size
    k               : Kind
    x x₁ x₂ y y₁ y₂ : Delay A ∞
    x′ y′           : Delay′ A ∞

-- Parallel composition of computations.

infix 10 _∣_

_∣_ : Delay A i → Delay B i → Delay (A × B) i
now x   ∣ now y   = now (x , y)
now x   ∣ later y = later λ { .force → now x ∣ y .force }
later x ∣ now y   = later λ { .force → x .force ∣ now y }
later x ∣ later y = later λ { .force → x .force ∣ y .force }

-- The number of later constructors in x ∣ y is bisimilar to the
-- maximum of the number of later constructors in x and the number of
-- later constructors in y.

steps-∣∼max-steps-steps :
  Conat.[ i ] steps (x ∣ y) ∼ max (steps x) (steps y)
steps-∣∼max-steps-steps {x = now _}   {y = now _}   = zero
steps-∣∼max-steps-steps {x = later _} {y = now _}   = suc λ { .force → steps-∣∼max-steps-steps }
steps-∣∼max-steps-steps {x = now _}   {y = later _} = suc λ { .force → steps-∣∼max-steps-steps }
steps-∣∼max-steps-steps {x = later _} {y = later _} = suc λ { .force → steps-∣∼max-steps-steps }

-- The _∣_ operator can be expressed using other functions (up to
-- expansion).

∣-≲ : [ i ] x ∣ y ≲ (x >>=′ λ x → y >>=′ λ y → now (x , y))
∣-≲ {x = now x} {y = now y}   = now (x , y)  ∎
∣-≲ {x = now x} {y = later y} = later λ { .force →
  (now x >>=′ λ x → y .force >>=′ λ y → now (x , y))  ≳⟨ ∣-≲ ⟩∎
  now x ∣ y .force                                    ∎ }
∣-≲ {x = later x} {y = now y}   = later λ { .force →
  (x .force >>=′ λ x → now y >>=′ λ y → now (x , y))  ≳⟨ ∣-≲ ⟩∎
  x .force ∣ now y                                    ∎ }
∣-≲ {x = later x} {y = later y} = later λ { .force →
  (x .force >>=′ λ x → later y >>=′ λ y → now (x , y))   ≳⟨ ((x .force ∎) >>=-cong λ _ → laterˡ (_ ∎)) ⟩
  (x .force >>=′ λ x → y .force >>=′ λ y → now (x , y))  ≳⟨ ∣-≲ ⟩∎
  x .force ∣ y .force                                    ∎ }

-- The _∣_ operator is commutative (up to swapping of results).

∣-comm : [ i ] x ∣ y ∼ map′ swap (y ∣ x)
∣-comm {x = now x}   {y = now y}   = reflexive _
∣-comm {x = now x}   {y = later y} = later λ { .force → ∣-comm }
∣-comm {x = later x} {y = now y}   = later λ { .force → ∣-comm }
∣-comm {x = later x} {y = later y} = later λ { .force → ∣-comm }

-- Rearrangement lemmas for _∣_.

∣-later :
  x ∣ later y′ ∼ later (record { force = drop-later x ∣ y′ .force })
∣-later {x = now x}   = later λ { .force → _ ∎ }
∣-later {x = later x} = later λ { .force → _ ∎ }

later-∣ :
  later x′ ∣ y ∼ later (record { force = x′ .force ∣ drop-later y })
later-∣ {x′ = x′} {y = y} =
  later x′ ∣ y                                                     ∼⟨ ∣-comm ⟩
  map′ swap (y ∣ later x′)                                         ∼⟨ map-cong _ ∣-later ⟩
  map′ swap (later (record { force = drop-later y ∣ x′ .force }))  ∼⟨ (later λ { .force → symmetric ∣-comm }) ⟩
  later (record { force = x′ .force ∣ drop-later y })              ∎

-- The _∣_ operator preserves strong and weak bisimilarity and
-- expansion.

infix 10 _∣-cong_

_∣-cong_ :
  [ i ] x₁ ⟨ k ⟩ x₂ →
  [ i ] y₁ ⟨ k ⟩ y₂ →
  [ i ] x₁ ∣ y₁ ⟨ k ⟩ x₂ ∣ y₂
now      ∣-cong now      = now
now      ∣-cong later  q = later λ { .force → now ∣-cong q .force }
now      ∣-cong laterˡ q = laterˡ (now ∣-cong q)
now      ∣-cong laterʳ q = laterʳ (now ∣-cong q)
later  p ∣-cong now      = later λ { .force → p .force ∣-cong now }
laterˡ p ∣-cong now      = laterˡ (p ∣-cong now)
laterʳ p ∣-cong now      = laterʳ (p ∣-cong now)

later  p ∣-cong later  q = later λ { .force → p .force ∣-cong q .force }
laterʳ p ∣-cong laterʳ q = laterʳ (p ∣-cong q)
laterˡ p ∣-cong laterˡ q = laterˡ (p ∣-cong q)

later {x = x₁} {y = x₂} p ∣-cong laterˡ {x = y₁} {y = y₂} q =
  later x₁ ∣ later y₁                                   ∼⟨ (later λ { .force → _ ∎ }) ⟩
  later (record { force = x₁ .force ∣ y₁ .force })      ?⟨ (later λ { .force → p .force ∣-cong drop-laterʳ q }) ⟩∼
  later (record { force = x₂ .force ∣ drop-later y₂ })  ∼⟨ symmetric later-∣ ⟩
  later x₂ ∣ y₂                                         ∎

later {x = x₁} {y = x₂} p ∣-cong laterʳ {x = y₁} {y = y₂} q =
  later x₁ ∣ y₁                                         ∼⟨ later-∣ ⟩
  later (record { force = x₁ .force ∣ drop-later y₁ })  ≈⟨ (later λ { .force → p .force ∣-cong drop-laterˡ q }) ⟩∼
  later (record { force = x₂ .force ∣ y₂ .force })      ∼⟨ (later λ { .force → _ ∎ }) ⟩
  later x₂ ∣ later y₂                                   ∎

laterˡ {x = x₁} {y = x₂} p ∣-cong later {x = y₁} {y = y₂} q =
  later x₁ ∣ later y₁                                   ∼⟨ (later λ { .force → _ ∎ }) ⟩
  later (record { force = x₁ .force ∣ y₁ .force })      ?⟨ (later λ { .force → drop-laterʳ p ∣-cong q .force }) ⟩∼
  later (record { force = drop-later x₂ ∣ y₂ .force })  ∼⟨ symmetric ∣-later ⟩
  x₂ ∣ later y₂                                         ∎

laterʳ {x = x₁} {y = x₂} p ∣-cong later {x = y₁} {y = y₂} q =
  x₁ ∣ later y₁                                         ∼⟨ ∣-later ⟩
  later (record { force = drop-later x₁ ∣ y₁ .force })  ≈⟨ (later λ { .force → drop-laterˡ p ∣-cong q .force }) ⟩∼
  later (record { force = x₂ .force ∣ y₂ .force })      ∼⟨ (later λ { .force → _ ∎ }) ⟩
  later x₂ ∣ later y₂                                   ∎

laterˡ {x = x₁} {y = x₂} p ∣-cong laterʳ {x = y₁} {y = y₂} q =
  later x₁ ∣ y₁                                         ∼⟨ later-∣ ⟩
  later (record { force = x₁ .force ∣ drop-later y₁ })  ≈⟨ (later λ { .force → drop-laterʳ p ∣-cong drop-laterˡ q }) ⟩∼
  later (record { force = drop-later x₂ ∣ y₂ .force })  ∼⟨ symmetric ∣-later ⟩
  x₂ ∣ later y₂                                         ∎

laterʳ {x = x₁} {y = x₂} p ∣-cong laterˡ {x = y₁} {y = y₂} q =
  x₁ ∣ later y₁                                         ∼⟨ ∣-later ⟩
  later (record { force = drop-later x₁ ∣ y₁ .force })  ≈⟨ (later λ { .force → drop-laterˡ p ∣-cong drop-laterʳ q }) ⟩∼
  later (record { force = x₂ .force ∣ drop-later y₂ })  ∼⟨ symmetric later-∣ ⟩
  later x₂ ∣ y₂                                         ∎
