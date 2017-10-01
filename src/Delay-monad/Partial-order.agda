------------------------------------------------------------------------
-- A partial order
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Delay-monad.Partial-order {a} {A : Set a} where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (module W)

open import Bijection equality-with-J using (_↔_)
open import Double-negation equality-with-J
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import Monad equality-with-J

open import Delay-monad
open import Delay-monad.Strong-bisimilarity using ([_]_∼_)
open import Delay-monad.Weak-bisimilarity as W
  using ([_]_≈_; _≈_; force)

-- An ordering relation.
--
-- Capretta defines a logically equivalent relation in "General
-- Recursion via Coinductive Types".
--
-- Benton, Kennedy and Varming define a relation that is perhaps
-- logically equivalent in "Some Domain Theory and Denotational
-- Semantics in Coq".

infix 4 [_]_⊑_ [_]_⊑′_ _⊑_ _⊑′_

mutual

  data [_]_⊑_ (i : Size) : Delay A ∞ → Delay A ∞ → Set a where
    now    : ∀ {x} → [ i ] now x ⊑ now x
    laterʳ : ∀ {x y} → [ i ] x ⊑ force y → [ i ] x ⊑ later y
    laterˡ : ∀ {x y} → [ i ] force x ⊑′ y → [ i ] later x ⊑ y

  record [_]_⊑′_ (i : Size) (x y : Delay A ∞) : Set a where
    coinductive
    field
      force : {j : Size< i} → [ j ] x ⊑ y

open [_]_⊑′_ public

_⊑_ : Delay A ∞ → Delay A ∞ → Set a
_⊑_ = [ ∞ ]_⊑_

_⊑′_ : Delay A ∞ → Delay A ∞ → Set a
_⊑′_ = [ ∞ ]_⊑′_

-- A derived "constructor".

later-cong : ∀ {i x y} →
             [ i ] force x ⊑′ force y → [ i ] later x ⊑ later y
later-cong p = laterʳ (laterˡ p)

-- Termination predicates.

Terminates : Size → Delay A ∞ → A → Set a
Terminates i x y = [ i ] now y ⊑ x

_⇓_ : Delay A ∞ → A → Set a
_⇓_ = Terminates ∞

-- If x terminates with the values y and z, then y is equal to z.

⇓→⇓→≡ : ∀ {i x y z} → Terminates i x y → Terminates i x z → y ≡ z
⇓→⇓→≡ now        now        = refl
⇓→⇓→≡ (laterʳ p) (laterʳ q) = ⇓→⇓→≡ p q

-- If x is smaller than or equal to now y, and x terminates, then
-- x terminates with the value y.

⊑now→⇓→⇓ : ∀ {i x} {y z : A} →
           x ⊑ now y → Terminates i x z → Terminates i x y
⊑now→⇓→⇓ now        now        = now
⊑now→⇓→⇓ (laterˡ p) (laterʳ q) = laterʳ (⊑now→⇓→⇓ (force p) q)

-- The notion of termination defined here is pointwise isomorphic to
-- the one defined in Delay-monad.Weak-bisimilarity.

⇓↔⇓ : ∀ {i x y} → Terminates i x y ↔ W.Terminates i x y
⇓↔⇓ = record
  { surjection = record
    { logical-equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = from∘to
  }
  where
  to : ∀ {i x y} → Terminates i x y → W.Terminates i x y
  to now        = W.now
  to (laterʳ p) = W.laterʳ (to p)

  from : ∀ {i x y} → W.Terminates i x y → Terminates i x y
  from W.now        = now
  from (W.laterʳ p) = laterʳ (from p)

  from∘to : ∀ {i x y} (p : Terminates i x y) → from (to p) ≡ p
  from∘to now        = refl
  from∘to (laterʳ p) = cong laterʳ (from∘to p)

  to∘from : ∀ {i x y} (p : W.Terminates i x y) → to (from p) ≡ p
  to∘from W.now        = refl
  to∘from (W.laterʳ p) = cong W.laterʳ (to∘from p)

-- Terminates i is pointwise isomorphic to Terminates ∞.

Terminates↔⇓ : ∀ {i x y} → Terminates i x y ↔ x ⇓ y
Terminates↔⇓ {i} {x} {y} =
  Terminates i x y    ↝⟨ ⇓↔⇓ ⟩
  W.Terminates i x y  ↝⟨ W.Terminates↔⇓ ⟩
  x W.⇓ y             ↝⟨ inverse ⇓↔⇓ ⟩□
  x ⇓ y               □

-- The computation never is smaller than or equal to all other
-- computations.

never⊑ : ∀ {i} x → [ i ] never ⊑ x
never⊑ (now x)   = laterˡ λ { .force → never⊑ (now x) }
never⊑ (later x) = later-cong λ { .force → never⊑ (force x) }

-- The computation never does not terminate.

now⋢never : ∀ {i x} → ¬ Terminates i never x
now⋢never (laterʳ p) = now⋢never p

-- One can remove later constructors.

laterˡ⁻¹ : ∀ {i} {j : Size< i} {x y} →
           [ i ] later x ⊑ y →
           [ j ] force x ⊑ y
laterˡ⁻¹ (laterʳ p) = laterʳ (laterˡ⁻¹ p)
laterˡ⁻¹ (laterˡ p) = force p

laterʳ⁻¹ : ∀ {i x y} →
           [ i ] x ⊑ later y →
           [ i ] x ⊑ force y
laterʳ⁻¹ (laterʳ p) = p
laterʳ⁻¹ (laterˡ p) = laterˡ λ { .force → laterʳ⁻¹ (force p) }

later-cong⁻¹ : ∀ {i} {j : Size< i} {x y} →
               [ i ] later x ⊑ later y →
               [ j ] force x ⊑ force y
later-cong⁻¹ p = laterʳ⁻¹ (laterˡ⁻¹ p)

-- Weak bisimilarity is contained in the ordering relation.

≈→⊑ : ∀ {i x y} → [ i ] x ≈ y → [ i ] x ⊑ y
≈→⊑ W.now        = now
≈→⊑ (W.later  p) = later-cong λ { .force → ≈→⊑ (force p) }
≈→⊑ (W.laterˡ p) = laterˡ λ { .force → ≈→⊑ p }
≈→⊑ (W.laterʳ p) = laterʳ (≈→⊑ p)

-- The ordering relation is antisymmetric (with respect to weak
-- bisimilarity).

antisymmetric : ∀ {i x y} →
                [ i ] x ⊑ y → [ i ] y ⊑ x → [ i ] x ≈ y
antisymmetric {x = now   x} {y = now  .x} now        _          = W.now
antisymmetric {x = now   x} {y = later y} (laterʳ p) q          = W.laterʳ (_↔_.to ⇓↔⇓ p)
antisymmetric {x = later x} {y = now   y} p          (laterʳ q) = W.laterˡ (W.symmetric (_↔_.to ⇓↔⇓ q))
antisymmetric {x = later x} {y = later y} p          q          =
  W.later λ { .force → antisymmetric (later-cong⁻¹ p) (later-cong⁻¹ q) }

-- An alternative characterisation of weak bisimilarity.

≈⇔⊑×⊒ : ∀ {i x y} → [ i ] x ≈ y ⇔ ([ i ] x ⊑ y × [ i ] y ⊑ x)
≈⇔⊑×⊒ = record
  { to   = λ p → ≈→⊑ p , ≈→⊑ (W.symmetric p)
  ; from = uncurry antisymmetric
  }

-- The ordering relation is reflexive.

reflexive : ∀ {i} x → [ i ] x ⊑ x
reflexive (now x)   = now
reflexive (later x) = later-cong λ { .force → reflexive (force x) }

-- Certain instances of symmetry also hold.

symmetric : ∀ {i} {x : A} {y} →
            Terminates i y x → [ i ] y ⊑ now x
symmetric now        = now
symmetric (laterʳ p) = laterˡ λ { .force → symmetric p }

-- The ordering relation is transitive.

transitive : ∀ {i} {x y z : Delay A ∞} →
             [ i ] x ⊑ y → y ⊑ z → [ i ] x ⊑ z
transitive p          now        = p
transitive p          (laterʳ q) = laterʳ (transitive p q)
transitive (laterʳ p) (laterˡ q) = transitive p (force q)
transitive (laterˡ p) q          = laterˡ λ { .force →
                                     transitive (force p) q }

-- The termination relation respects weak bisimilarity.

⇓-respects-≈ : ∀ {i x y z} → Terminates i x z → x ≈ y → Terminates i y z
⇓-respects-≈ now        q = ≈→⊑ q
⇓-respects-≈ (laterʳ p) q = ⇓-respects-≈ p (W.laterˡ⁻¹ q)

-- The ordering relation respects weak bisimilarity.

transitive-≈⊑ : ∀ {i x y z} → [ i ] x ≈ y → y ⊑ z → [ i ] x ⊑ z
transitive-≈⊑ p q = transitive (≈→⊑ p) q

transitive-⊑≈ : ∀ {i x y z} → [ i ] x ⊑ y → y ≈ z → [ i ] x ⊑ z
transitive-⊑≈ p          W.now        = p
transitive-⊑≈ (laterʳ p) (W.later  q) = laterʳ (transitive-⊑≈ p (force q))
transitive-⊑≈ (laterˡ p) q            = laterˡ λ { .force →
                                          transitive-⊑≈ (force p) q }
transitive-⊑≈ (laterʳ p) (W.laterˡ q) = transitive-⊑≈ p q
transitive-⊑≈ p          (W.laterʳ q) = laterʳ (transitive-⊑≈ p q)

-- There is a transitivity-like function that produces an ordering
-- proof from one weak bisimilarity proof and one ordering proof, in
-- such a way that the size of the ordering proof is preserved, iff A
-- is uninhabited.

Transitivity-≈⊑ʳ =
  ∀ {i} {x y z : Delay A ∞} → x ≈ y → [ i ] y ⊑ z → [ i ] x ⊑ z

size-preserving-transitivity-≈⊑ʳ⇔uninhabited : Transitivity-≈⊑ʳ ⇔ ¬ A
size-preserving-transitivity-≈⊑ʳ⇔uninhabited = record
  { to   = Transitivity-≈⊑ʳ                                    ↝⟨ (λ trans {i x} →

               [ i ] later (record { force = now x }) ∼ never        ↝⟨ ≈→⊑ ∘ W.∼→≈ ⟩
               [ i ] later (record { force = now x }) ⊑ never        ↝⟨ trans (W.laterʳ W.now) ⟩
               [ i ] now x ⊑ never                                   ↝⟨ _↔_.to ⇓↔⇓ ⟩□
               [ i ] now x ≈ never                                   □) ⟩

           W.Laterˡ⁻¹-∼≈′                                      ↝⟨ _⇔_.to W.size-preserving-laterˡ⁻¹-∼≈′⇔uninhabited ⟩

           ¬ A                                                 □
  ; from = ¬ A               ↝⟨ W.uninhabited→trivial ⟩
           (∀ x y → x ≈ y)   ↝⟨ (λ trivial _ _ → ≈→⊑ (trivial _ _)) ⟩
           (∀ x y → x ⊑ y)   ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Transitivity-≈⊑ʳ  □
  }

-- Transitivity can be made size-preserving in the second argument iff
-- A is uninhabited.

Transitivityʳ =
  ∀ {i} {x y z : Delay A ∞} → x ⊑ y → [ i ] y ⊑ z → [ i ] x ⊑ z

size-preserving-transitivityʳ⇔uninhabited : Transitivityʳ ⇔ ¬ A
size-preserving-transitivityʳ⇔uninhabited = record
  { to   = Transitivityʳ     ↝⟨ _∘ ≈→⊑ ⟩
           Transitivity-≈⊑ʳ  ↝⟨ _⇔_.to size-preserving-transitivity-≈⊑ʳ⇔uninhabited ⟩□
           ¬ A               □
  ; from = ¬ A              ↝⟨ W.uninhabited→trivial ⟩
           (∀ x y → x ≈ y)  ↝⟨ (λ trivial _ _ → ≈→⊑ (trivial _ _)) ⟩
           (∀ x y → x ⊑ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Transitivityʳ    □
  }

-- There is a transitivity-like function that produces an ordering
-- proof from one ordering proof and one weak bisimilarity proof, in
-- such a way that the size of the weak bisimilarity proof is
-- preserved, iff A is uninhabited.

Transitivity-⊑≈ʳ =
  ∀ {i} {x y z : Delay A ∞} → x ⊑ y → [ i ] y ≈ z → [ i ] x ⊑ z

size-preserving-transitivity-⊑≈ʳ⇔uninhabited : Transitivity-⊑≈ʳ ⇔ ¬ A
size-preserving-transitivity-⊑≈ʳ⇔uninhabited = record
  { to   = Transitivity-⊑≈ʳ                                    ↝⟨ (λ trans {i x} →

               [ i ] later (record { force = now x }) ∼ never        ↝⟨ W.∼→≈ ⟩
               [ i ] later (record { force = now x }) ≈ never        ↝⟨ trans (laterʳ now) ⟩
               [ i ] now x ⊑ never                                   ↝⟨ _↔_.to ⇓↔⇓ ⟩□
               [ i ] now x ≈ never                                   □) ⟩

           W.Laterˡ⁻¹-∼≈′                                      ↝⟨ _⇔_.to W.size-preserving-laterˡ⁻¹-∼≈′⇔uninhabited ⟩

           ¬ A                                                 □
  ; from = ¬ A               ↝⟨ W.uninhabited→trivial ⟩
           (∀ x y → x ≈ y)   ↝⟨ (λ trivial _ _ → ≈→⊑ (trivial _ _)) ⟩
           (∀ x y → x ⊑ y)   ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Transitivity-⊑≈ʳ  □
  }

-- An alternative characterisation of the ordering relation.
--
-- Capretta proves a similar result in "General Recursion via
-- Coinductive Types".
--
-- One might wonder if the equivalence can be made size-preserving in
-- some way. However, note that x ⇓ y is in bijective correspondence
-- with Terminates i x y for any size i (see Terminates↔⇓).

⊑⇔⇓→⇓ : ∀ {x y} → x ⊑ y ⇔ (∀ z → x ⇓ z → y ⇓ z)
⊑⇔⇓→⇓ = record
  { to   = to
  ; from = from _
  }
  where
  to : ∀ {x y} → x ⊑ y → ∀ z → x ⇓ z → y ⇓ z
  to p          z now   = p
  to (laterʳ p) z q          = laterʳ (to p z q)
  to (laterˡ p) z (laterʳ q) = to (force p) z q

  from : ∀ x {y} → (∀ z → x ⇓ z → y ⇓ z) → x ⊑ y
  from (now x)   p = p x now
  from (later x) p = laterˡ λ { .force →
                       from (force x) (λ z q → p z (laterʳ q)) }

-- An alternative characterisation of weak bisimilarity.

≈⇔≈₂ : {x y : Delay A ∞} → x ≈ y ⇔ x W.≈₂ y
≈⇔≈₂ {x} {y} =
  x ≈ y                                                  ↝⟨ ≈⇔⊑×⊒ ⟩
  x ⊑ y × y ⊑ x                                          ↝⟨ ⊑⇔⇓→⇓ ×-cong ⊑⇔⇓→⇓ ⟩
  (∀ z → x ⇓ z → y ⇓ z) × (∀ z → y ⇓ z → x ⇓ z)          ↝⟨ ∀-cong _ (λ _ → →-cong _ (from-bijection ⇓↔⇓) (from-bijection ⇓↔⇓))
                                                              ×-cong
                                                            ∀-cong _ (λ _ → →-cong _ (from-bijection ⇓↔⇓) (from-bijection ⇓↔⇓)) ⟩
  (∀ z → x W.⇓ z → y W.⇓ z) × (∀ z → y W.⇓ z → x W.⇓ z)  ↝⟨ record { to   = uncurry λ to from z → record { to = to z; from = from z }
                                                                   ; from = λ hyp → _⇔_.to ∘ hyp , _⇔_.from ∘ hyp
                                                                   } ⟩□
  (∀ z → x W.⇓ z ⇔ y W.⇓ z)                              □

-- If A is a set, then every computation is weakly bisimilar to either
-- never or now something (assuming excluded middle and
-- extensionality).

⇑⊎⇓ :
  Excluded-middle a → Extensionality a a →
  Is-set A → (x : Delay A ∞) → never ≈ x ⊎ ∃ λ y → x W.⇓ y
⇑⊎⇓ em ext A-set x =
  ⊎-map (_⇔_.from ≈⇔≈₂) id $
  Excluded-middle→Double-negation-elimination em
    (⊎-closure-propositional
       (λ { x⇑ (y , x⇓y) →
            W.now≉never (now y  W.≈⟨ x⇓y ⟩
                         x      W.≈⟨ W.symmetric (_⇔_.from ≈⇔≈₂ x⇑) ⟩∎
                         never  ∎) })
       (W.≈₂-propositional ext A-set)
       (W.∃-Terminates-propositional A-set))
    (⊎-map (_⇔_.to ≈⇔≈₂) id ⟨$⟩ W.¬¬[⇑⊎⇓] x)
