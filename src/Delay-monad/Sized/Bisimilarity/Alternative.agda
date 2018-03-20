------------------------------------------------------------------------
-- Alternative definitions of weak bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Prelude

module Delay-monad.Sized.Bisimilarity.Alternative
  {a} {A : Size → Set a} where

open import Equality.Propositional as E
open import Logical-equivalence using (_⇔_)

open import Function-universe equality-with-J hiding (_∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J

open import Delay-monad.Sized
open import Delay-monad.Sized.Bisimilarity
open import Delay-monad.Sized.Termination

-- An alternative definition of weak bisimilarity (discussed by
-- Capretta in "General Recursion via Coinductive Types", and
-- basically the one used in the paper "Partiality, Revisited: The
-- Partiality Monad as a Quotient Inductive-Inductive Type" by
-- Altenkirch, Danielsson and Kraus).
--
-- This definition is pointwise logically equivalent to the one above,
-- see Delay-monad.Sized.Partial-order.≈⇔≈₂.

infix 4 _≈₂_

_≈₂_ : Delay A ∞ → Delay A ∞ → Set a
x ≈₂ y = ∀ z → x ⇓ z ⇔ y ⇓ z

-- If A ∞ is a set, then this alternative definition of weak
-- bisimilarity is propositional (assuming extensionality), unlike _≈_
-- (see Delay-monad.Sized.Bisimilarity.¬-≳≈-propositional).

≈₂-propositional :
  E.Extensionality a a →
  Is-set (A ∞) → ∀ {x y} → Is-proposition (x ≈₂ y)
≈₂-propositional ext A-set =
  Π-closure ext 1 λ _ →
  ⇔-closure ext 1 (Terminates-propositional A-set)
                  (Terminates-propositional A-set)

-- Another alternative definition of weak bisimilarity, basically the
-- one given by Capretta in "General Recursion via Coinductive Types".

infix 4 [_]_≈₃_ [_]_≈₃′_ _≈₃_

mutual

  data [_]_≈₃_ (i : Size) : Delay A ∞ → Delay A ∞ → Set a where
    both-terminate : ∀ {x y v} → x ⇓ v → y ⇓ v → [ i ] x ≈₃ y
    later          : ∀ {x y} →
                     [ i ] force x ≈₃′ force y →
                     [ i ] later x ≈₃  later y

  record [_]_≈₃′_ (i : Size) (x y : Delay A ∞) : Set a where
    coinductive
    field
      force : {j : Size< i} → [ j ] x ≈₃ y

open [_]_≈₃′_ public

_≈₃_ : Delay A ∞ → Delay A ∞ → Set a
_≈₃_ = [ ∞ ]_≈₃_

-- If ∀ i → A i is inhabited, then this definition is not
-- propositional.

¬-≈₃-propositional : (∀ i → A i) → ¬ (∀ {x y} → Is-proposition (x ≈₃ y))
¬-≈₃-propositional x =
  (∀ {x y} → Is-proposition (x ≈₃ y))  ↝⟨ (λ prop → prop) ⟩
  Is-proposition (y ≈₃ y)              ↝⟨ _⇔_.to propositional⇔irrelevant ⟩
  Proof-irrelevant (y ≈₃ y)            ↝⟨ (_$ _) ∘ (_$ _) ⟩
  proof₁ ≡ proof₂                      ↝⟨ (λ ()) ⟩□
  ⊥                                    □
  where
  y : Delay A ∞
  y = later λ { .force {j = j} → now (x j) }

  proof₁ : y ≈₃ y
  proof₁ = both-terminate (laterʳ now) (laterʳ now)

  proof₂ : y ≈₃ y
  proof₂ = later λ { .force → both-terminate now now }

-- The last definition of weak bisimilarity given above is pointwise
-- logically equivalent to _≈_. Note that the proof is
-- size-preserving.

≈⇔≈₃ : ∀ {i x y} → [ i ] x ≈ y ⇔ [ i ] x ≈₃ y
≈⇔≈₃ = record { to = to; from = from }
  where
  mutual

    laterˡ′ : ∀ {i x x′ y} →
              x′ ≡ force x →
              [ i ] x′      ≈₃ y →
              [ i ] later x ≈₃ y
    laterˡ′ eq (both-terminate x⇓ y⇓) = both-terminate
                                          (laterʳ (subst (_⇓ _) eq x⇓))
                                          y⇓
    laterˡ′ eq (later p)              = later (laterˡ″ eq p)

    laterˡ″ : ∀ {i x x′ y} →
              later x′ ≡ x →
              [ i ] force x′ ≈₃′ y →
              [ i ] x        ≈₃′ y
    force (laterˡ″ refl p) = laterˡ′ refl (force p)

  mutual

    laterʳ′ : ∀ {i x y y′} →
              y′ ≡ force y →
              [ i ] x ≈₃ y′ →
              [ i ] x ≈₃ later y
    laterʳ′ eq (both-terminate x⇓ y⇓) = both-terminate
                                          x⇓
                                          (laterʳ (subst (_⇓ _) eq y⇓))
    laterʳ′ eq (later p)              = later (laterʳ″ eq p)

    laterʳ″ : ∀ {i x y y′} →
              later y′ ≡ y →
              [ i ] x ≈₃′ force y′ →
              [ i ] x ≈₃′ y
    force (laterʳ″ refl p) = laterʳ′ refl (force p)

  to : ∀ {i x y} → [ i ] x ≈ y → [ i ] x ≈₃ y
  to now        = both-terminate now now
  to (later  p) = later λ { .force → to (force p) }
  to (laterˡ p) = laterˡ′ refl (to p)
  to (laterʳ p) = laterʳ′ refl (to p)

  from⇓ : ∀ {i x y v} → x ⇓ v → y ⇓ v → [ i ] x ≈ y
  from⇓ now        now        = now
  from⇓ p          (laterʳ q) = laterʳ (from⇓ p q)
  from⇓ (laterʳ p) q          = laterˡ (from⇓ p q)

  from : ∀ {i x y} → [ i ] x ≈₃ y → [ i ] x ≈ y
  from (both-terminate x⇓v y⇓v) = from⇓ x⇓v y⇓v
  from (later p)                = later λ { .force → from (force p) }
