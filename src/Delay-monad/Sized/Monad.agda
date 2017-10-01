------------------------------------------------------------------------
-- A monad-like structure
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Delay-monad.Sized.Monad where

open import Prelude hiding (module W)

open import Delay-monad.Sized
open import Delay-monad.Sized.Strong-bisimilarity as S
open import Delay-monad.Sized.Weak-bisimilarity as W

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
left-identity x f = S.reflexive (f x)

right-identity : ∀ {a} {A : Size → Set a} (x : Delay A ∞) →
                 x >>= return ∼ x
right-identity (now   x) = now
right-identity (later x) = later λ { .force →
                             right-identity (force x) }

associativity :
  ∀ {a b c} {A : Size → Set a} {B : Size → Set b} {C : Size → Set c} →
  (x : Delay A ∞) (f : ∀ {i} → A i → Delay B i)
  (g : ∀ {i} → B i → Delay C i) →
  x >>= (λ x → f x >>= g) ∼ x >>= f >>= g
associativity (now   x) f g = S.reflexive (f x >>= g)
associativity (later x) f g = later λ { .force →
                                associativity (force x) f g }

------------------------------------------------------------------------
-- The functions map, join and _>>=_ preserve strong bisimilarity

map-cong-∼ : ∀ {i a b} {A : Size → Set a} {B : Size → Set b}
             (f : ∀ {i} → A i → B i) {x y : Delay A ∞} →
             [ i ] x ∼ y → [ i ] map f x ∼ map f y
map-cong-∼ f now       = now
map-cong-∼ f (later p) = later λ { .force → map-cong-∼ f (force p) }

join-cong-∼ : ∀ {i a} {A : Size → Set a} {x y : Delay (Delay A) ∞} →
              [ i ] x ∼ y → [ i ] join x ∼ join y
join-cong-∼ now       = S.reflexive _
join-cong-∼ (later p) = later λ { .force → join-cong-∼ (force p) }

infixl 5 _>>=-cong-∼_

_>>=-cong-∼_ :
  ∀ {i a b} {A : Size → Set a} {B : Size → Set b}
    {x y : Delay A ∞} {f g : ∀ {i} → A i → Delay B i} →
  [ i ] x ∼ y → (∀ z → [ i ] f z ∼ g z) →
  [ i ] x >>= f ∼ y >>= g
now     >>=-cong-∼ q = q _
later p >>=-cong-∼ q = later λ { .force → force p >>=-cong-∼ q }

------------------------------------------------------------------------
-- The functions map, join and _>>=_ preserve weak bisimilarity

map-cong-≈ : ∀ {i a b} {A : Size → Set a} {B : Size → Set b}
             (f : ∀ {i} → A i → B i) {x y : Delay A ∞} →
             [ i ] x ≈ y → [ i ] map f x ≈ map f y
map-cong-≈ f now        = now
map-cong-≈ f (later  p) = later λ { .force → map-cong-≈ f (force p) }
map-cong-≈ f (laterˡ p) = laterˡ (map-cong-≈ f p)
map-cong-≈ f (laterʳ p) = laterʳ (map-cong-≈ f p)

join-cong-≈ : ∀ {i a} {A : Size → Set a} {x y : Delay (Delay A) ∞} →
              [ i ] x ≈ y → [ i ] join x ≈ join y
join-cong-≈ now        = W.reflexive _
join-cong-≈ (later  p) = later λ { .force → join-cong-≈ (force p) }
join-cong-≈ (laterˡ p) = laterˡ (join-cong-≈ p)
join-cong-≈ (laterʳ p) = laterʳ (join-cong-≈ p)

infixl 5 _>>=-cong-≈_

_>>=-cong-≈_ :
  ∀ {i a b} {A : Size → Set a} {B : Size → Set b}
    {x y : Delay A ∞} {f g : ∀ {i} → A i → Delay B i} →
  [ i ] x ≈ y → (∀ z → [ i ] f z ≈ g z) →
  [ i ] x >>= f ≈ y >>= g
now      >>=-cong-≈  q = q _
later  p >>=-cong-≈  q = later λ { .force → force p >>=-cong-≈ q }
laterˡ p >>=-cong-≈  q = laterˡ (p >>=-cong-≈ q)
laterʳ p >>=-cong-≈  q = laterʳ (p >>=-cong-≈ q)
