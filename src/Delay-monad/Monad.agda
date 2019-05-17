------------------------------------------------------------------------
-- The delay monad is a monad up to strong bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Delay-monad.Monad where

open import Equality.Propositional
open import Prelude
open import Prelude.Size

open import Conat equality-with-J as Conat using (zero; suc; force)
open import Monad equality-with-J

open import Delay-monad
open import Delay-monad.Bisimilarity as B

------------------------------------------------------------------------
-- Map, join and bind

-- A universe-polymorphic variant of map.

map′ : ∀ {i a b} {A : Set a} {B : Set b} →
       (A → B) → Delay A i → Delay B i
map′ f (now   x) = now (f x)
map′ f (later x) = later λ { .force → map′ f (force x) }

-- Join.

join : ∀ {i a} {A : Set a} →
       Delay (Delay A i) i → Delay A i
join (now   x) = x
join (later x) = later λ { .force → join (force x) }

-- A universe-polymorphic variant of bind.

infixl 5 _>>=′_

_>>=′_ : ∀ {i a b} {A : Set a} {B : Set b} →
         Delay A i → (A → Delay B i) → Delay B i
x >>=′ f = join (map′ f x)

instance

  -- A raw monad instance.

  delay-raw-monad : ∀ {a i} → Raw-monad (λ (A : Set a) → Delay A i)
  Raw-monad.return delay-raw-monad = now
  Raw-monad._>>=_  delay-raw-monad = _>>=′_

------------------------------------------------------------------------
-- Monad laws

left-identity′ :
  ∀ {a b} {A : Set a} {B : Set b} x (f : A → Delay B ∞) →
  return x >>=′ f ∼ f x
left-identity′ x f = reflexive (f x)

right-identity′ : ∀ {a i} {A : Set a} (x : Delay A ∞) →
                  [ i ] x >>= return ∼ x
right-identity′ (now   x) = now
right-identity′ (later x) = later λ { .force →
                              right-identity′ (force x) }

associativity′ :
  ∀ {a b c i} {A : Set a} {B : Set b} {C : Set c} →
  (x : Delay A ∞) (f : A → Delay B ∞) (g : B → Delay C ∞) →
  [ i ] x >>=′ (λ x → f x >>=′ g) ∼ x >>=′ f >>=′ g
associativity′ (now   x) f g = reflexive (f x >>=′ g)
associativity′ (later x) f g = later λ { .force →
                                 associativity′ (force x) f g }

-- The delay monad is a monad (assuming extensionality).

delay-monad :
  ∀ {a} → B.Extensionality a → Monad (λ (A : Set a) → Delay A ∞)
Monad.raw-monad      (delay-monad ext)       = delay-raw-monad
Monad.left-identity  (delay-monad ext) x f   = ext (left-identity′ x f)
Monad.right-identity (delay-monad ext) x     = ext (right-identity′ x)
Monad.associativity  (delay-monad ext) x f g = ext (associativity′ x f g)

------------------------------------------------------------------------
-- The functions map′, join and _>>=′_ preserve strong and weak
-- bisimilarity and expansion

map-cong : ∀ {k i a b} {A : Set a} {B : Set b}
           (f : A → B) {x y : Delay A ∞} →
           [ i ] x ⟨ k ⟩ y → [ i ] map′ f x ⟨ k ⟩ map′ f y
map-cong f now        = now
map-cong f (later  p) = later λ { .force → map-cong f (force p) }
map-cong f (laterˡ p) = laterˡ (map-cong f p)
map-cong f (laterʳ p) = laterʳ (map-cong f p)

join-cong : ∀ {k i a} {A : Set a} {x y : Delay (Delay A ∞) ∞} →
            [ i ] x ⟨ k ⟩ y → [ i ] join x ⟨ k ⟩ join y
join-cong now        = reflexive _
join-cong (later  p) = later λ { .force → join-cong (force p) }
join-cong (laterˡ p) = laterˡ (join-cong p)
join-cong (laterʳ p) = laterʳ (join-cong p)

infixl 5 _>>=-cong_

_>>=-cong_ :
  ∀ {k i a b} {A : Set a} {B : Set b}
    {x y : Delay A ∞} {f g : A → Delay B ∞} →
  [ i ] x ⟨ k ⟩ y → (∀ z → [ i ] f z ⟨ k ⟩ g z) →
  [ i ] x >>=′ f ⟨ k ⟩ y >>=′ g
now      >>=-cong  q = q _
later  p >>=-cong  q = later λ { .force → force p >>=-cong q }
laterˡ p >>=-cong  q = laterˡ (p >>=-cong q)
laterʳ p >>=-cong  q = laterʳ (p >>=-cong q)

------------------------------------------------------------------------
-- Some lemmas relating monadic combinators to steps

-- Use of map′ does not affect the number of steps in the computation.

steps-map′ :
  ∀ {i a b} {A : Set a} {B : Set b} {f : A → B}
  (x : Delay A ∞) →
  Conat.[ i ] steps (map′ f x) ∼ steps x
steps-map′ (now x)   = zero
steps-map′ (later x) = suc λ { .force → steps-map′ (x .force) }

-- Use of _⟨$⟩_ does not affect the number of steps in the
-- computation.

steps-⟨$⟩ :
  ∀ {i ℓ} {A B : Set ℓ} {f : A → B}
  (x : Delay A ∞) →
  Conat.[ i ] steps (f ⟨$⟩ x) ∼ steps x
steps-⟨$⟩ (now x)   = zero
steps-⟨$⟩ (later x) = suc λ { .force → steps-⟨$⟩ (x .force) }
