------------------------------------------------------------------------
-- Least upper bounds
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Delay-monad.Least-upper-bound where

open import Equality.Propositional
open import Prelude hiding (_⊔_)

open import Nat equality-with-J

open import Delay-monad
open import Delay-monad.Partial-order

module _ {a} {A : Set a} where

  -- Least upper bounds (if they exist).

  infix 10 _⊔_

  _⊔_ : ∀ {i} → Delay A i → Delay A i → Delay A i
  now x   ⊔ _       = now x
  later x ⊔ now y   = now y
  later x ⊔ later y = later λ { .force → force x ⊔ force y }

  -- The computation x ⊔ y is smaller than or equal to every upper
  -- bound of x and y.

  ⊔-least-upper-bound : ∀ {i x y z} →
                        [ i ] x ⊑ z → [ i ] y ⊑ z → [ i ] x ⊔ y ⊑ z
  ⊔-least-upper-bound               now        _ = now
  ⊔-least-upper-bound               (laterʳ p) q = laterʳ (⊔-least-upper-bound p (laterʳ⁻¹ q))
  ⊔-least-upper-bound {y = now y}   (laterˡ _) q = q
  ⊔-least-upper-bound {y = later y} (laterˡ p) q = laterˡ λ { .force →
                                                     ⊔-least-upper-bound (force p) (laterˡ⁻¹ q) }

  -- If x and y have a lower bound, then this is also a lower bound of
  -- x ⊔ y.

  ⊔-lower-bound : ∀ {i x y z} → [ i ] z ⊑ x → [ i ] z ⊑ y → [ i ] z ⊑ x ⊔ y
  ⊔-lower-bound               now        _ = now
  ⊔-lower-bound               (laterˡ p) q = laterˡ λ { .force →
                                               ⊔-lower-bound (force p) (laterˡ⁻¹ q) }
  ⊔-lower-bound {y = now y}   (laterʳ _) q = q
  ⊔-lower-bound {y = later y} (laterʳ p) q = laterʳ (⊔-lower-bound p (laterʳ⁻¹ q))

  -- If x and y have an upper bound, then x ⊔ y is an upper bound
  -- of y.

  ⊔-upper-boundʳ : ∀ {i x y z} →
                   [ i ] x ⊑ z → [ i ] y ⊑ z → [ i ] y ⊑ x ⊔ y
  ⊔-upper-boundʳ               now        q = q
  ⊔-upper-boundʳ               (laterʳ p) q = ⊔-upper-boundʳ p (laterʳ⁻¹ q)
  ⊔-upper-boundʳ {y = now y}   (laterˡ _) _ = now
  ⊔-upper-boundʳ {y = later y} (laterˡ p) q =
    later-cong λ { .force → ⊔-upper-boundʳ (force p) (laterˡ⁻¹ q) }

  -- If x and y have an upper bound, then x ⊔ y is an upper bound
  -- of x.

  ⊔-upper-boundˡ : ∀ {i x y z} →
                   [ i ] x ⊑ z → [ i ] y ⊑ z → [ i ] x ⊑ x ⊔ y
  ⊔-upper-boundˡ               now        q = now
  ⊔-upper-boundˡ               (laterʳ p) q = ⊔-upper-boundˡ p (laterʳ⁻¹ q)
  ⊔-upper-boundˡ {y = later y} (laterˡ p) q = later-cong λ { .force →
                                                ⊔-upper-boundˡ (force p) (laterˡ⁻¹ q) }
  ⊔-upper-boundˡ {y = now y}   (laterˡ p) q = laterˡ λ { .force →
                                                ⊔-upper-boundʳ q (force p) }

  -- A variant of the lower/upper bound lemmas.

  ⊔-lower-upper-bound : ∀ {i x y z} →
                        x ⊑ y → [ i ] y ⊑ z → [ i ] y ⊑ x ⊔ z
  ⊔-lower-upper-bound               now        _            = now
  ⊔-lower-upper-bound               (laterʳ p) q            = laterˡ λ { .force →
                                                                ⊔-lower-upper-bound p (laterˡ⁻¹ q) }
  ⊔-lower-upper-bound               (laterˡ p) (laterʳ q)   = laterʳ (⊔-lower-upper-bound (force p) q)
  ⊔-lower-upper-bound {z = now z}   (laterˡ _) q            = q
  ⊔-lower-upper-bound {z = later z} (laterˡ p) (laterˡ q)   = later-cong λ { .force →
                                                                ⊔-lower-upper-bound
                                                                  (laterʳ⁻¹ (force p))
                                                                  (laterʳ⁻¹ (force q)) }

  -- If x terminates, then x ⊔ y also terminates.

  ⊔-⇓ˡ : ∀ {i x y} {z : A} →
         Terminates i x z → ∃ λ z′ → Terminates i (x ⊔ y) z′
  ⊔-⇓ˡ               now        = _ , now
  ⊔-⇓ˡ {y = now y}   (laterʳ p) = _ , now
  ⊔-⇓ˡ {y = later y} (laterʳ p) = Σ-map id laterʳ (⊔-⇓ˡ p)

  -- If y terminates, then x ⊔ y also terminates.

  ⊔-⇓ʳ : ∀ {i} x {y} {z : A} →
         Terminates i y z → ∃ λ z′ → Terminates i (x ⊔ y) z′
  ⊔-⇓ʳ (now x)   _          = _ , now
  ⊔-⇓ʳ (later x) now        = _ , now
  ⊔-⇓ʳ (later x) (laterʳ p) = Σ-map id laterʳ (⊔-⇓ʳ (force x) p)

-- Increasing sequences.

Increasing-sequence : ∀ {a} → Set a → Set a
Increasing-sequence A =
  ∃ λ (f : ℕ → Delay A ∞) → ∀ n → f n ⊑ f (suc n)

module _ {a} {A : Set a} where

  -- The tail of an increasing sequence.

  tailˢ : Increasing-sequence A → Increasing-sequence A
  tailˢ = Σ-map (_∘ suc) (_∘ suc)

  -- Later sequence elements are larger.

  later-larger : (s : Increasing-sequence A) →
                 ∀ {m n} → m ≤ n → proj₁ s m ⊑ proj₁ s n
  later-larger s (≤-refl′ refl)   = reflexive _
  later-larger s (≤-step′ p refl) =
    transitive (later-larger s p) (proj₂ s _)

  -- Least upper bounds of increasing sequences.

  ⨆ : ∀ {i} → Increasing-sequence A → Delay A i
  ⨆ s = proj₁ s 0 ⊔ later λ { .force → ⨆ (tailˢ s) }

  -- ⨆ s is smaller than or equal to every upper bound of s.

  ⨆-least-upper-bound :
    ∀ {i} (s : Increasing-sequence A) ub →
    (∀ n → [ i ] proj₁ s n ⊑ ub) → [ i ] ⨆ s ⊑ ub
  ⨆-least-upper-bound s ub is-ub =
    ⊔-least-upper-bound
      (is-ub 0)
      (laterˡ λ { .force →
         ⨆-least-upper-bound (tailˢ s) ub (is-ub ∘ suc) })

  -- If every element in s terminates with a given value, then ⨆ s
  -- terminates with the same value.

  ⨆-⇓ : ∀ {i x} (s : Increasing-sequence A) →
        (∀ n → proj₁ s n ⇓ x) → Terminates i (⨆ s) x
  ⨆-⇓ s s-⇓ =
    ⊑now→⇓→⇓ (⨆-least-upper-bound s _ (λ n → symmetric (s-⇓ n)))
             (proj₂ (⊔-⇓ˡ (s-⇓ 0)))

  -- If s has a lower bound, then this is also a lower bound of ⨆ s.

  ⨆-lower-bound : ∀ {i} (s : Increasing-sequence A) lb →
                  (∀ n → lb ⊑ proj₁ s n) → [ i ] lb ⊑ ⨆ s
  ⨆-lower-bound s (now x)    is-lb = ⨆-⇓ s is-lb
  ⨆-lower-bound s (later lb) is-lb =
    ⊔-lower-bound
      (is-lb 0)
      (later-cong λ { .force →
         ⨆-lower-bound (tailˢ s) (force lb) λ n →
           laterˡ⁻¹ (transitive (is-lb n) (proj₂ s n)) })

  -- ⨆ s is an upper bound of s.

  ⨆-upper-bound : ∀ {i} (s : Increasing-sequence A) →
                  ∀ n → [ i ] proj₁ s n ⊑ ⨆ s
  ⨆-upper-bound s zero    = ⨆-lower-bound s (proj₁ s 0)
                              (λ n → later-larger s (zero≤ n))
  ⨆-upper-bound s (suc n) = ⊔-lower-upper-bound
                              (later-larger s (zero≤ (suc n)))
                              (laterʳ (⨆-upper-bound (tailˢ s) n))
