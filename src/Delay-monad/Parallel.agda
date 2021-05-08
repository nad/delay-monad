------------------------------------------------------------------------
-- A combinator for running two computations in parallel
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

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
import Delay-monad.Sequential as S

private

  variable
    a b             : Level
    A B             : Type a
    i               : Size
    k               : Kind
    f f₁ f₂ g       : Delay (A → B) ∞
    x x₁ x₂ y y₁ y₂ : Delay A ∞
    f′              : Delay′ (A → B) ∞
    x′              : Delay′ A ∞
    h               : A → B
    z               : A

------------------------------------------------------------------------
-- The _⊛_ operator

-- Parallel composition of computations.

infixl 6 _⊛_

_⊛_ : Delay (A → B) i → Delay A i → Delay B i
now f   ⊛ now x   = now (f x)
now f   ⊛ later x = later λ { .force → now f ⊛ x .force }
later f ⊛ now x   = later λ { .force → f .force ⊛ now x }
later f ⊛ later x = later λ { .force → f .force ⊛ x .force }

-- The number of later constructors in f ⊛ x is bisimilar to the
-- maximum of the number of later constructors in f and the number of
-- later constructors in x.

steps-⊛∼max-steps-steps :
  Conat.[ i ] steps (f ⊛ x) ∼ max (steps f) (steps x)
steps-⊛∼max-steps-steps {f = now _}   {x = now _}   = zero
steps-⊛∼max-steps-steps {f = now _}   {x = later _} = suc λ { .force → steps-⊛∼max-steps-steps }
steps-⊛∼max-steps-steps {f = later _} {x = now _}   = suc λ { .force → steps-⊛∼max-steps-steps }
steps-⊛∼max-steps-steps {f = later _} {x = later _} = suc λ { .force → steps-⊛∼max-steps-steps }

-- Rearrangement lemmas for _⊛_.

later-⊛ :
  later f′ ⊛ x ∼ later (record { force = f′ .force ⊛ drop-later x })
later-⊛ {x = now _}   = later λ { .force → _ ∎ }
later-⊛ {x = later _} = later λ { .force → _ ∎ }

⊛-later :
  f ⊛ later x′ ∼ later (record { force = drop-later f ⊛ x′ .force })
⊛-later {f = now _}   = later λ { .force → _ ∎ }
⊛-later {f = later _} = later λ { .force → _ ∎ }

-- The _⊛_ operator preserves strong and weak bisimilarity and
-- expansion.

infixl 6 _⊛-cong_

_⊛-cong_ :
  [ i ] f₁ ⟨ k ⟩ f₂ →
  [ i ] x₁ ⟨ k ⟩ x₂ →
  [ i ] f₁ ⊛ x₁ ⟨ k ⟩ f₂ ⊛ x₂
now      ⊛-cong now      = now
now      ⊛-cong later  q = later λ { .force → now ⊛-cong q .force }
now      ⊛-cong laterˡ q = laterˡ (now ⊛-cong q)
now      ⊛-cong laterʳ q = laterʳ (now ⊛-cong q)
later  p ⊛-cong now      = later λ { .force → p .force ⊛-cong now }
laterˡ p ⊛-cong now      = laterˡ (p ⊛-cong now)
laterʳ p ⊛-cong now      = laterʳ (p ⊛-cong now)

later  p ⊛-cong later  q = later λ { .force → p .force ⊛-cong q .force }
laterʳ p ⊛-cong laterʳ q = laterʳ (p ⊛-cong q)
laterˡ p ⊛-cong laterˡ q = laterˡ (p ⊛-cong q)

later {x = f₁} {y = f₂} p ⊛-cong laterˡ {x = x₁} {y = x₂} q =
  later f₁ ⊛ later x₁                                   ∼⟨ (later λ { .force → _ ∎ }) ⟩
  later (record { force = f₁ .force ⊛ x₁ .force })      ?⟨ (later λ { .force → p .force ⊛-cong drop-laterʳ q }) ⟩∼
  later (record { force = f₂ .force ⊛ drop-later x₂ })  ∼⟨ symmetric later-⊛ ⟩
  later f₂ ⊛ x₂                                         ∎

later {x = f₁} {y = f₂} p ⊛-cong laterʳ {x = x₁} {y = x₂} q =
  later f₁ ⊛ x₁                                         ∼⟨ later-⊛ ⟩
  later (record { force = f₁ .force ⊛ drop-later x₁ })  ≈⟨ (later λ { .force → p .force ⊛-cong drop-laterˡ q }) ⟩∼
  later (record { force = f₂ .force ⊛ x₂ .force })      ∼⟨ (later λ { .force → _ ∎ }) ⟩
  later f₂ ⊛ later x₂                                   ∎

laterˡ {x = f₁} {y = f₂} p ⊛-cong later {x = x₁} {y = x₂} q =
  later f₁ ⊛ later x₁                                   ∼⟨ (later λ { .force → _ ∎ }) ⟩
  later (record { force = f₁ .force ⊛ x₁ .force })      ?⟨ (later λ { .force → drop-laterʳ p ⊛-cong q .force }) ⟩∼
  later (record { force = drop-later f₂ ⊛ x₂ .force })  ∼⟨ symmetric ⊛-later ⟩
  f₂ ⊛ later x₂                                         ∎

laterʳ {x = f₁} {y = f₂} p ⊛-cong later {x = x₁} {y = x₂} q =
  f₁ ⊛ later x₁                                         ∼⟨ ⊛-later ⟩
  later (record { force = drop-later f₁ ⊛ x₁ .force })  ≈⟨ (later λ { .force → drop-laterˡ p ⊛-cong q .force }) ⟩∼
  later (record { force = f₂ .force ⊛ x₂ .force })      ∼⟨ (later λ { .force → _ ∎ }) ⟩
  later f₂ ⊛ later x₂                                   ∎

laterˡ {x = f₁} {y = f₂} p ⊛-cong laterʳ {x = x₁} {y = x₂} q =
  later f₁ ⊛ x₁                                         ∼⟨ later-⊛ ⟩
  later (record { force = f₁ .force ⊛ drop-later x₁ })  ≈⟨ (later λ { .force → drop-laterʳ p ⊛-cong drop-laterˡ q }) ⟩∼
  later (record { force = drop-later f₂ ⊛ x₂ .force })  ∼⟨ symmetric ⊛-later ⟩
  f₂ ⊛ later x₂                                         ∎

laterʳ {x = f₁} {y = f₂} p ⊛-cong laterˡ {x = x₁} {y = x₂} q =
  f₁ ⊛ later x₁                                         ∼⟨ ⊛-later ⟩
  later (record { force = drop-later f₁ ⊛ x₁ .force })  ≈⟨ (later λ { .force → drop-laterˡ p ⊛-cong drop-laterʳ q }) ⟩∼
  later (record { force = f₂ .force ⊛ drop-later x₂ })  ∼⟨ symmetric later-⊛ ⟩
  later f₂ ⊛ x₂                                         ∎

-- The _⊛_ operator is (kind of) commutative.

⊛-comm : [ i ] f ⊛ x ∼ map′ (flip _$_) x ⊛ f
⊛-comm {f = now f}   {x = now x}   = reflexive _
⊛-comm {f = now f}   {x = later x} = later λ { .force → ⊛-comm }
⊛-comm {f = later f} {x = now x}   = later λ { .force → ⊛-comm }
⊛-comm {f = later f} {x = later x} = later λ { .force → ⊛-comm }

-- The function map′ can be expressed using _⊛_.

map∼now-⊛ : [ i ] map′ h x ∼ now h ⊛ x
map∼now-⊛ {x = now x}   = now
map∼now-⊛ {x = later x} = later λ { .force → map∼now-⊛ }

-- The applicative functor laws hold up to strong bisimilarity.

now-id-⊛ : [ i ] now id ⊛ x ∼ x
now-id-⊛ {x = now x}   = now
now-id-⊛ {x = later x} = later λ { .force → now-id-⊛ }

now-∘-⊛-⊛-⊛ :
  [ i ] now (λ f → f ∘_) ⊛ f ⊛ g ⊛ x ∼ f ⊛ (g ⊛ x)
now-∘-⊛-⊛-⊛ {f = now _}   {g = now _}   {x = now _}   = now
now-∘-⊛-⊛-⊛ {f = now _}   {g = now _}   {x = later _} = later λ { .force → now-∘-⊛-⊛-⊛ }
now-∘-⊛-⊛-⊛ {f = now _}   {g = later _} {x = now _}   = later λ { .force → now-∘-⊛-⊛-⊛ }
now-∘-⊛-⊛-⊛ {f = now _}   {g = later _} {x = later _} = later λ { .force → now-∘-⊛-⊛-⊛ }
now-∘-⊛-⊛-⊛ {f = later _} {g = now _}   {x = now _}   = later λ { .force → now-∘-⊛-⊛-⊛ }
now-∘-⊛-⊛-⊛ {f = later _} {g = now _}   {x = later _} = later λ { .force → now-∘-⊛-⊛-⊛ }
now-∘-⊛-⊛-⊛ {f = later _} {g = later _} {x = now _}   = later λ { .force → now-∘-⊛-⊛-⊛ }
now-∘-⊛-⊛-⊛ {f = later _} {g = later _} {x = later _} = later λ { .force → now-∘-⊛-⊛-⊛ }

now-⊛-now : [ i ] now h ⊛ now z ∼ now (h z)
now-⊛-now = now

⊛-now : [ i ] f ⊛ now z ∼ now (λ f → f z) ⊛ f
⊛-now {f = now f}   = now
⊛-now {f = later f} = later λ { .force → ⊛-now }

-- Sequential composition is an expansion of parallel composition.

⊛≳⊛ : [ i ] f S.⊛ x ≳ f ⊛ x
⊛≳⊛ {f = now f} {x = now x}   = now (f x)  ∎
⊛≳⊛ {f = now f} {x = later x} = later λ { .force →
  now f S.⊛ x .force  ≳⟨ ⊛≳⊛ ⟩∎
  now f ⊛ x .force    ∎ }
⊛≳⊛ {f = later f} {x = now x} = later λ { .force →
  f .force S.⊛ now x  ≳⟨ ⊛≳⊛ ⟩∎
  f .force ⊛ now x    ∎ }
⊛≳⊛ {f = later f} {x = later x} = later λ { .force →
  f .force S.⊛ later x   ≳⟨ ((f .force ∎) >>=-cong λ _ → laterˡ (_ ∎)) ⟩
  f .force S.⊛ x .force  ≳⟨ ⊛≳⊛ ⟩∎
  f .force ⊛ x .force    ∎ }

------------------------------------------------------------------------
-- The _∣_ operator

-- Parallel composition of computations.

infix 10 _∣_

_∣_ : Delay A i → Delay B i → Delay (A × B) i
x ∣ y = map′ _,_ x ⊛ y

-- The number of later constructors in x ∣ y is bisimilar to the
-- maximum of the number of later constructors in x and the number of
-- later constructors in y.

steps-∣∼max-steps-steps :
  Conat.[ i ] steps (x ∣ y) ∼ max (steps x) (steps y)
steps-∣∼max-steps-steps {x = x} {y = y} =
  steps (x ∣ y)                       Conat.∼⟨ Conat.reflexive-∼ _ ⟩
  steps (map′ _,_ x ⊛ y)              Conat.∼⟨ steps-⊛∼max-steps-steps ⟩
  max (steps (map′ _,_ x)) (steps y)  Conat.∼⟨ Conat.max-cong (steps-map′ x) (Conat.reflexive-∼ _) ⟩∎
  max (steps x) (steps y)             ∎∼

-- The _∣_ operator preserves strong and weak bisimilarity and
-- expansion.

infix 10 _∣-cong_

_∣-cong_ :
  [ i ] x₁ ⟨ k ⟩ x₂ →
  [ i ] y₁ ⟨ k ⟩ y₂ →
  [ i ] x₁ ∣ y₁ ⟨ k ⟩ x₂ ∣ y₂
p ∣-cong q = map-cong _,_ p ⊛-cong q

-- The _∣_ operator is commutative (up to swapping of results).

∣-comm : [ i ] x ∣ y ∼ map′ swap (y ∣ x)
∣-comm {x = x} {y = y} =
  x ∣ y                                                          ∼⟨⟩
  map′ _,_ x ⊛ y                                                 ∼⟨ ⊛-comm ⟩
  map′ (flip _$_) y ⊛ map′ _,_ x                                 ∼⟨ map∼now-⊛ ⊛-cong map∼now-⊛ ⟩
  now (flip _$_) ⊛ y ⊛ (now _,_ ⊛ x)                             ∼⟨ symmetric now-∘-⊛-⊛-⊛ ⟩
  now (λ f → f ∘_) ⊛ (now (flip _$_) ⊛ y) ⊛ now _,_ ⊛ x          ∼⟨ symmetric now-∘-⊛-⊛-⊛ ⊛-cong (_ ∎) ⊛-cong (_ ∎) ⟩
  now _∘_ ⊛ now (λ f → f ∘_) ⊛ now (flip _$_) ⊛ y ⊛ now _,_ ⊛ x  ∼⟨⟩
  now (λ x f y → f y x) ⊛ y ⊛ now _,_ ⊛ x                        ∼⟨ ⊛-now ⊛-cong (_ ∎) ⟩
  now (_$ _,_) ⊛ (now (λ x f y → f y x) ⊛ y) ⊛ x                 ∼⟨ symmetric now-∘-⊛-⊛-⊛ ⊛-cong (_ ∎) ⟩
  now _∘_ ⊛ now (_$ _,_) ⊛ now (λ x f y → f y x) ⊛ y ⊛ x         ∼⟨⟩
  now (curry swap) ⊛ y ⊛ x                                       ∼⟨⟩
  now _∘_ ⊛ now (swap ∘_) ⊛ now _,_ ⊛ y ⊛ x                      ∼⟨ now-∘-⊛-⊛-⊛ ⊛-cong (_ ∎) ⟩
  now (swap ∘_) ⊛ (now _,_ ⊛ y) ⊛ x                              ∼⟨ (_ ∎) ⊛-cong symmetric map∼now-⊛ ⊛-cong (_ ∎) ⟩
  now (swap ∘_) ⊛ map′ _,_ y ⊛ x                                 ∼⟨⟩
  now _∘_ ⊛ now swap ⊛ map′ _,_ y ⊛ x                            ∼⟨ now-∘-⊛-⊛-⊛ ⟩
  now swap ⊛ (map′ _,_ y ⊛ x)                                    ∼⟨ symmetric map∼now-⊛ ⟩
  map′ swap (map′ _,_ y ⊛ x)                                     ∼⟨⟩
  map′ swap (y ∣ x)                                              ∎

-- Sequential composition is an expansion of parallel composition.

∣≳∣ : [ i ] x S.∣ y ≳ x ∣ y
∣≳∣ {x = x} {y = y} =
  x S.∣ y           ∼⟨⟩
  map′ _,_ x S.⊛ y  ≳⟨ ⊛≳⊛ ⟩
  map′ _,_ x ⊛ y    ∼⟨⟩
  x ∣ y             ∎
