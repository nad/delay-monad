------------------------------------------------------------------------
-- A monad-like structure
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Delay-monad.Sized.Monad where

open import Prelude
open import Prelude.Size

open import Delay-monad.Sized
open import Delay-monad.Sized.Bisimilarity

------------------------------------------------------------------------
-- Monadic combinators

-- Return.

return : ∀ {i a} {A : Size → Set a} → A i → Delay A i
return = now

-- Map. Note the function argument's type.

map : ∀ {i a b} {A : Size → Set a} {B : Size → Set b} →
      ({j : Size< (ssuc i)} → A j → B j) → Delay A i → Delay B i
map f (now   x) = now (f x)
map f (later x) = later λ { .force → map f (force x) }

-- Join.

join : ∀ {i a} {A : Size → Set a} →
       Delay (Delay A) i → Delay A i
join (now   x) = x
join (later x) = later λ { .force → join (force x) }

-- Bind. Note the function argument's type.

infixl 5 _>>=_

_>>=_ : ∀ {i a b} {A : Size → Set a} {B : Size → Set b} →
        Delay A i → ({j : Size< (ssuc i)} → A j → Delay B j) →
        Delay B i
x >>= f = join (map f x)

------------------------------------------------------------------------
-- Monad laws

left-identity :
  ∀ {a b} {A : Size → Set a} {B : Size → Set b}
  x (f : ∀ {i} → A i → Delay B i) →
  return x >>= f ∼ f x
left-identity x f = reflexive (f x)

right-identity : ∀ {a i} {A : Size → Set a} (x : Delay A ∞) →
                 [ i ] x >>= return ∼ x
right-identity (now   x) = now
right-identity (later x) = later λ { .force →
                             right-identity (force x) }

associativity :
  ∀ {a b c i} {A : Size → Set a} {B : Size → Set b} {C : Size → Set c} →
  (x : Delay A ∞) (f : ∀ {i} → A i → Delay B i)
  (g : ∀ {i} → B i → Delay C i) →
  [ i ] x >>= (λ x → f x >>= g) ∼ x >>= f >>= g
associativity (now   x) f g = reflexive (f x >>= g)
associativity (later x) f g = later λ { .force →
                                associativity (force x) f g }

------------------------------------------------------------------------
-- The functions map, join and _>>=_ preserve strong and weak
-- bisimilarity and expansion

map-cong : ∀ {k i a b} {A : Size → Set a} {B : Size → Set b}
           (f : ∀ {i} → A i → B i) {x y : Delay A ∞} →
           [ i ] x ⟨ k ⟩ y → [ i ] map f x ⟨ k ⟩ map f y
map-cong f now        = now
map-cong f (later  p) = later λ { .force → map-cong f (force p) }
map-cong f (laterˡ p) = laterˡ (map-cong f p)
map-cong f (laterʳ p) = laterʳ (map-cong f p)

join-cong : ∀ {k i a} {A : Size → Set a} {x y : Delay (Delay A) ∞} →
              [ i ] x ⟨ k ⟩ y → [ i ] join x ⟨ k ⟩ join y
join-cong now        = reflexive _
join-cong (later  p) = later λ { .force → join-cong (force p) }
join-cong (laterˡ p) = laterˡ (join-cong p)
join-cong (laterʳ p) = laterʳ (join-cong p)

infixl 5 _>>=-cong_

_>>=-cong_ :
  ∀ {k i a b} {A : Size → Set a} {B : Size → Set b}
    {x y : Delay A ∞} {f g : ∀ {i} → A i → Delay B i} →
  [ i ] x ⟨ k ⟩ y → (∀ z → [ i ] f z ⟨ k ⟩ g z) →
  [ i ] x >>= f ⟨ k ⟩ y >>= g
now      >>=-cong q = q _
later  p >>=-cong q = later λ { .force → force p >>=-cong q }
laterˡ p >>=-cong q = laterˡ (p >>=-cong q)
laterʳ p >>=-cong q = laterʳ (p >>=-cong q)

------------------------------------------------------------------------
-- A lemma

-- The function map can be expressed using _>>=′_ and now.

map∼>>=-now :
  ∀ {i a b} {A : Size → Set a} {B : Size → Set b}
    {f : ∀ {i} → A i → B i} (x : Delay A ∞) →
  [ i ] map f x ∼ x >>= now ∘ f
map∼>>=-now (now x)   = now
map∼>>=-now (later x) = later λ { .force → map∼>>=-now (x .force) }
