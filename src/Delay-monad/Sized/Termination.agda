------------------------------------------------------------------------
-- Termination
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

open import Prelude
open import Prelude.Size

module Delay-monad.Sized.Termination {a} {A : Size → Type a} where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)

open import Bijection equality-with-J using (_↔_)
open import Double-negation equality-with-J
open import H-level equality-with-J
open import Monad equality-with-J

open import Delay-monad.Sized
open import Delay-monad.Sized.Bisimilarity hiding (_∎; step-≡ˡ)

-- Termination predicates.

Terminates : Size → Delay A ∞ → A ∞ → Type a
Terminates i x y = [ i ] now y ≈ x

infix 4 _⇓_

_⇓_ : Delay A ∞ → A ∞ → Type a
_⇓_ = Terminates ∞

-- Terminates i is pointwise isomorphic to Terminates ∞.
--
-- Note that Terminates carves out an "inductive fragment" of [_]_≈_:
-- the only "coinductive" constructor, later, does not target
-- Terminates.

Terminates↔⇓ : ∀ {i x y} → Terminates i x y ↔ x ⇓ y
Terminates↔⇓ = record
  { surjection = record
    { logical-equivalence = record
      { to   = to
      ; from = from _
      }
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = from∘to
  }
  where
  to : ∀ {i x y} → Terminates i x y → x ⇓ y
  to now        = now
  to (laterʳ p) = laterʳ (to p)

  from : ∀ i {x y} → x ⇓ y → Terminates i x y
  from _ now        = now
  from _ (laterʳ p) = laterʳ (from _ p)

  to∘from : ∀ {i x y} (p : x ⇓ y) → to (from i p) ≡ p
  to∘from now        = refl
  to∘from (laterʳ p) = cong laterʳ (to∘from p)

  from∘to : ∀ {i x y} (p : Terminates i x y) → from i (to p) ≡ p
  from∘to now        = refl
  from∘to (laterʳ p) = cong laterʳ (from∘to p)

-- The termination relation respects weak bisimilarity.
--
-- This function cannot be made size-preserving in its second argument
-- if ∀ i → A i is inhabited, see
-- Delay-monad.Sized.Bisimilarity.Negative.

⇓-respects-≈ : ∀ {i x y z} →
               Terminates i x z → x ≈ y → Terminates i y z
⇓-respects-≈ = transitive-≈-now

-- If a computation does not terminate, then it is weakly bisimilar
-- to never.

¬⇓→⇑ : ∀ {i} x → ¬ (∃ λ y → x ⇓ y) → [ i ] never ≈ x
¬⇓→⇑ (now   x) ¬⇓ = ⊥-elim (¬⇓ (_ , now))
¬⇓→⇑ (later x) ¬⇓ = later λ { .force → ¬⇓→⇑ _ (¬⇓ ∘ Σ-map id laterʳ) }

-- In the double-negation monad every computation is weakly
-- bisimilar to either never or now something.

¬¬[⇑⊎⇓] : ∀ x → ¬¬ (never ≈ x ⊎ ∃ λ y → x ⇓ y)
¬¬[⇑⊎⇓] x = [ inj₂ , inj₁ ∘ ¬⇓→⇑ _ ] ⟨$⟩ excluded-middle

-- If A ∞ is a set, then the termination predicate is propositional.

Terminates-propositional :
  Is-set (A ∞) → ∀ {i x y} → Is-proposition (Terminates i x y)
Terminates-propositional A-set {i} = λ p q → irr p q refl
  where
  irr :
    ∀ {x y y′}
    (p : [ i ] now y  ≈ x)
    (q : [ i ] now y′ ≈ x)
    (y≡y′ : y ≡ y′) →
    subst (([ i ]_≈ x) ∘ now) y≡y′ p ≡ q
  irr         (laterʳ p) (laterʳ q) refl = cong laterʳ (irr p q refl)
  irr {y = y} now        now        y≡y  =
    subst (([ i ]_≈ now y) ∘ now) y≡y  now  ≡⟨ cong (λ eq → subst (([ i ]_≈ now y) ∘ now) eq _) (A-set y≡y refl) ⟩
    subst (([ i ]_≈ now y) ∘ now) refl now  ≡⟨⟩
    now                                     ∎

-- If x terminates with y and z, then y is equal to z.

termination-value-unique :
  ∀ {i x y z} → Terminates i x y → Terminates i x z → y ≡ z
termination-value-unique now        now        = refl
termination-value-unique (laterʳ p) (laterʳ q) =
  termination-value-unique p q

-- If A ∞ is a set, then ∃ λ y → x ⇓ y is propositional.

∃-Terminates-propositional :
  Is-set (A ∞) → ∀ {i x} → Is-proposition (∃ (Terminates i x))
∃-Terminates-propositional A-set (y₁ , x⇓y₁) (y₂ , x⇓y₂) =
  Σ-≡,≡→≡
    (termination-value-unique x⇓y₁ x⇓y₂)
    (Terminates-propositional A-set _ _)
