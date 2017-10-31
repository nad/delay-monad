------------------------------------------------------------------------
-- Weak bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Delay-monad.Weak-bisimilarity {a} {A : Set a} where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Double-negation equality-with-J
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import Monad equality-with-J

open import Delay-monad
open import Delay-monad.Strong-bisimilarity as S
  using ([_]_∼_; [_]_∼′_; _∼_; now; later; force)

-- Weak bisimilarity, defined using mixed induction and coinduction.

infix 4 [_]_≈_ [_]_≈′_ _≈_ _≈′_

mutual

  data [_]_≈_ (i : Size) : (x y : Delay A ∞) → Set a where
    now    : ∀ {x} → [ i ] now x ≈ now x
    later  : ∀ {x y} →
             [ i ] force x ≈′ force y →
             [ i ] later x ≈  later y
    laterˡ : ∀ {x y} →
             [ i ] force x ≈ y →
             [ i ] later x ≈ y
    laterʳ : ∀ {x y} →
             [ i ] x ≈ force y →
             [ i ] x ≈ later y

  record [_]_≈′_ (i : Size) (x y : Delay A ∞) : Set a where
    coinductive
    field
      force : {j : Size< i} → [ j ] x ≈ y

open [_]_≈′_ public

_≈_ : Delay A ∞ → Delay A ∞ → Set a
_≈_ = [ ∞ ]_≈_

_≈′_ : Delay A ∞ → Delay A ∞ → Set a
_≈′_ = [ ∞ ]_≈′_

-- Strong bisimilarity is contained in weak bisimilarity.

∼→≈ : ∀ {i x y} → [ i ] x ∼ y → [ i ] x ≈ y
∼→≈ now       = now
∼→≈ (later p) = later λ { .force → ∼→≈ (force p) }

-- Termination predicates.

Terminates : Size → Delay A ∞ → A → Set a
Terminates i x y = [ i ] now y ≈ x

infix 4 _⇓_

_⇓_ : Delay A ∞ → A → Set a
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

-- The computation now x is not weakly bisimilar to never.

now≉never : ∀ {i x} → ¬ [ i ] now x ≈ never
now≉never (laterʳ p) = now≉never p

-- Sometimes one can remove later constructors.

laterʳ⁻¹ : ∀ {i} {j : Size< i} {x y} →
           [ i ] x ≈ later y →
           [ j ] x ≈ force y
laterʳ⁻¹ (later  p) = laterˡ (force p)
laterʳ⁻¹ (laterʳ p) = p
laterʳ⁻¹ (laterˡ p) = laterˡ (laterʳ⁻¹ p)

laterˡ⁻¹ : ∀ {i} {j : Size< i} {x y} →
           [ i ] later x ≈ y →
           [ j ] force x ≈ y
laterˡ⁻¹ (later  p) = laterʳ (force p)
laterˡ⁻¹ (laterʳ p) = laterʳ (laterˡ⁻¹ p)
laterˡ⁻¹ (laterˡ p) = p

later⁻¹ : ∀ {i} {j : Size< i} {x y} →
          [ i ] later x ≈ later y →
          [ j ] force x ≈ force y
later⁻¹ (later  p) = force p
later⁻¹ (laterʳ p) = laterˡ⁻¹ p
later⁻¹ (laterˡ p) = laterʳ⁻¹ p

-- Weak bisimilarity is reflexive.

reflexive : ∀ {i} (x : Delay A ∞) → [ i ] x ≈ x
reflexive (now   x) = now
reflexive (later x) = later λ { .force → reflexive (force x) }

-- Weak bisimilarity is symmetric.

symmetric : ∀ {i} {x y : Delay A ∞} →
            [ i ] x ≈ y →
            [ i ] y ≈ x
symmetric now        = now
symmetric (later  p) = later λ { .force → symmetric (force p) }
symmetric (laterˡ p) = laterʳ (symmetric p)
symmetric (laterʳ p) = laterˡ (symmetric p)

-- The termination relation respects weak bisimilarity.
--
-- This function cannot be made size-preserving in its second argument
-- (unless A is uninhabited), see below.

⇓-respects-≈ : ∀ {i} {x y : Delay A ∞} {z} →
               Terminates i x z → x ≈ y → Terminates i y z
⇓-respects-≈ now        now        = now
⇓-respects-≈ (laterʳ p) q          = ⇓-respects-≈ p (laterˡ⁻¹ q)
⇓-respects-≈ p          (laterʳ q) = laterʳ (⇓-respects-≈ p q)

-- Weak bisimilarity is transitive.

transitive-now : ∀ {i x} {y z : Delay A ∞} →
                 [ i ] now x ≈ y → y ≈ z → [ i ] now x ≈ z
transitive-now = ⇓-respects-≈

mutual

  transitive-later : ∀ {i x} {y z : Delay A ∞} →
                     later x ≈ y → y ≈ z → [ i ] later x ≈ z
  transitive-later p          (later  q) = later λ { .force →
                                             transitive (later⁻¹ p) (force q) }
  transitive-later p          (laterʳ q) = later λ { .force →
                                             transitive (laterˡ⁻¹ p) q }
  transitive-later p          (laterˡ q) = transitive-later (laterʳ⁻¹ p) q
  transitive-later (laterˡ p) q          = laterˡ (transitive p q)

  transitive : ∀ {i} {x y z : Delay A ∞} →
               x ≈ y → y ≈ z → [ i ] x ≈ z
  transitive {x = now   x} p q = transitive-now   p q
  transitive {x = later x} p q = transitive-later p q

-- Some size-preserving variants of transitivity.
--
-- Many size-preserving variants cannot be defined (unless A is
-- uninhabited), see below.

transitive-∼≈ :
  ∀ {i} {x y z : Delay A ∞} →
  x ∼ y → [ i ] y ≈ z → [ i ] x ≈ z
transitive-∼≈ now       q          = q
transitive-∼≈ (later p) (later  q) = later λ { .force →
                                       transitive-∼≈ (force p) (force q) }
transitive-∼≈ (later p) (laterˡ q) = laterˡ (transitive-∼≈ (force p) q)
transitive-∼≈ p         (laterʳ q) = laterʳ (transitive-∼≈ p q)

transitive-≈∼ :
  ∀ {i} {x y z : Delay A ∞} →
  [ i ] x ≈ y → y ∼ z → [ i ] x ≈ z
transitive-≈∼ p q =
  symmetric (transitive-∼≈ (S.symmetric q) (symmetric p))

-- Some equational reasoning combinators.

infix  -1 finally-≈ _∎≈
infixr -2 _≈⟨_⟩_ _≈⟨_⟩∼_ _≈⟨_⟩′∼_ _≈⟨⟩_ _∼⟨_⟩≈_ _≡⟨_⟩≈_ _≡⟨_⟩′≈_ _≳⟨⟩_

_∎≈ : ∀ {i} (x : Delay A ∞) → [ i ] x ≈ x
_∎≈ = reflexive

_≈⟨_⟩_ : ∀ (x : Delay A ∞) {y z} →
         x ≈ y → y ≈ z → x ≈ z
_ ≈⟨ p ⟩ q = transitive p q

_≈⟨_⟩∼_ : ∀ {i} (x : Delay A ∞) {y z} →
          [ i ] x ≈ y → y ∼ z → [ i ] x ≈ z
_ ≈⟨ p ⟩∼ q = transitive-≈∼ p q

_≈⟨_⟩′∼_ : ∀ {i} (x : Delay A ∞) {y z} →
           [ i ] x ≈′ y → y ∼ z → [ i ] x ≈′ z
force (_ ≈⟨ p ⟩′∼ q) = transitive-≈∼ (force p) q

_≈⟨⟩_ : ∀ {i} (x : Delay A ∞) {y} →
        [ i ] x ≈ y → [ i ] x ≈ y
_ ≈⟨⟩ p = p

_∼⟨_⟩≈_ : ∀ {i} (x : Delay A ∞) {y z} →
          x ∼ y → [ i ] y ≈ z → [ i ] x ≈ z
_ ∼⟨ p ⟩≈ q = transitive-∼≈ p q

_≡⟨_⟩≈_ : ∀ {i} (x : Delay A ∞) {y z} →
          x ≡ y → [ i ] y ≈ z → [ i ] x ≈ z
_≡⟨_⟩≈_ {i} _ p q = subst ([ i ]_≈ _) (sym p) q

_≡⟨_⟩′≈_ : ∀ {i} (x : Delay A ∞) {y z} →
           x ≡ y → [ i ] y ≈′ z → [ i ] x ≈′ z
force (_ ≡⟨ p ⟩′≈ q) = _ ≡⟨ p ⟩≈ force q

_≳⟨⟩_ : ∀ {i} (x : Delay A ∞) {y} →
        [ i ] drop-later x ≈ y → [ i ] x ≈ y
now x   ≳⟨⟩ p = p
later x ≳⟨⟩ p = laterˡ p

finally-≈ : ∀ {i} (x y : Delay A ∞) →
            [ i ] x ≈ y → [ i ] x ≈ y
finally-≈ _ _ p = p

syntax finally-≈ x y p = x ≈⟨ p ⟩∎ y ∎

-- The following size-preserving variant of laterʳ⁻¹ and laterˡ⁻¹ can
-- be defined.
--
-- Several other variants cannot be defined (unless A is uninhabited),
-- see below.

laterˡʳ⁻¹ :
  ∀ {i} {x y : Delay′ A ∞} →
  [ i ] later x ≈ force y →
  [ i ] force x ≈ later y →
  [ i ] force x ≈ force y
laterˡʳ⁻¹ {i} p q = laterˡʳ⁻¹′ p q refl refl
  where
  laterˡʳ⁻¹″ :
    ∀ {x′ y′} {x y : Delay′ A ∞} →
    ({j : Size< i} → [ j ] x′ ≈ force y) →
    ({j : Size< i} → [ j ] force x ≈ y′) →
    later x ≡ x′ → later y ≡ y′ →
    [ i ] later x ≈ later y
  laterˡʳ⁻¹″ p q refl refl = later λ { .force → laterˡʳ⁻¹ p q }

  laterˡʳ⁻¹′ :
    ∀ {x′ y′} {x y : Delay′ A ∞} →
    [ i ] later x ≈ y′ →
    [ i ] x′ ≈ later y →
    x′ ≡ force x → y′ ≡ force y →
    [ i ] x′ ≈ y′
  laterˡʳ⁻¹′ (later  p) (later  q) x′≡  y′≡  = laterˡʳ⁻¹″ (force p)                (force q)                x′≡ y′≡
  laterˡʳ⁻¹′ (laterʳ p) (later  q) x′≡  y′≡  = laterˡʳ⁻¹″ (λ { {_} → laterˡ⁻¹ p }) (force q)                x′≡ y′≡
  laterˡʳ⁻¹′ (later  p) (laterˡ q) x′≡  y′≡  = laterˡʳ⁻¹″ (force p)                (λ { {_} → laterʳ⁻¹ q }) x′≡ y′≡
  laterˡʳ⁻¹′ (laterʳ p) (laterˡ q) x′≡  y′≡  = laterˡʳ⁻¹″ (λ { {_} → laterˡ⁻¹ p }) (λ { {_} → laterʳ⁻¹ q }) x′≡ y′≡
  laterˡʳ⁻¹′ (laterˡ p) _          refl refl = p
  laterˡʳ⁻¹′ _          (laterʳ q) refl y′≡  = subst ([ i ] _ ≈_) (sym y′≡) q

-- If a computation does not terminate, then it is weakly bisimilar
-- to never.

¬⇓→⇑ : ∀ {i} x → ¬ (∃ λ y → x ⇓ y) → [ i ] never ≈ x
¬⇓→⇑ (now   x) ¬⇓ = ⊥-elim (¬⇓ (_ , now))
¬⇓→⇑ (later x) ¬⇓ = later λ { .force → ¬⇓→⇑ _ (¬⇓ ∘ Σ-map id laterʳ) }

-- In the double-negation monad every computation is weakly
-- bisimilar to either never or now something.

¬¬[⇑⊎⇓] : ∀ x → ¬¬ (never ≈ x ⊎ ∃ λ y → x ⇓ y)
¬¬[⇑⊎⇓] x = [ inj₂ , inj₁ ∘ ¬⇓→⇑ _ ] ⟨$⟩ excluded-middle

-- The notion of weak bisimilarity defined here is not necessarily
-- propositional.

¬-≈-proposition : ¬ (∀ {x y} → Is-proposition (x ≈ y))
¬-≈-proposition =
  (∀ {x y} → Is-proposition (x ≈ y))  ↝⟨ (λ prop → _⇔_.to propositional⇔irrelevant (prop {x = never} {y = never})) ⟩
  Proof-irrelevant (never ≈ never)    ↝⟨ (λ irr → irr _ _) ⟩
  proof₁ ≡ proof₂                     ↝⟨ (λ ()) ⟩□
  ⊥₀                                  □
  where
  proof₁ : never ≈ never
  proof₁ = later λ { .force → proof₁ }

  proof₂ : never ≈ never
  proof₂ = laterˡ proof₁

-- However, if A is a set, then the termination predicate is
-- propositional.

Terminates-propositional :
  Is-set A → ∀ {i x y} → Is-proposition (Terminates i x y)
Terminates-propositional A-set {i} =
  _⇔_.from propositional⇔irrelevant (λ p q → irr p q refl)
  where
  irr :
    ∀ {x y y′}
    (p : [ i ] now y  ≈ x)
    (q : [ i ] now y′ ≈ x)
    (y≡y′ : y ≡ y′) →
    subst (([ i ]_≈ x) ∘ now) y≡y′ p ≡ q
  irr         (laterʳ p) (laterʳ q) refl = cong laterʳ (irr p q refl)
  irr {y = y} now        now        y≡y  =
    subst (([ i ]_≈ now y) ∘ now) y≡y  now  ≡⟨ cong (λ eq → subst _ eq _) (_⇔_.to set⇔UIP A-set y≡y refl) ⟩
    subst (([ i ]_≈ now y) ∘ now) refl now  ≡⟨⟩
    now                                     ∎

-- If x terminates with y and z, then y is equal to z.

termination-value-unique :
  ∀ {i x y z} → Terminates i x y → Terminates i x z → y ≡ z
termination-value-unique now        now        = refl
termination-value-unique (laterʳ p) (laterʳ q) =
  termination-value-unique p q

-- If A is a set, then ∃ λ y → x ⇓ y is propositional.

∃-Terminates-propositional :
  Is-set A → ∀ {i x} → Is-proposition (∃ (Terminates i x))
∃-Terminates-propositional A-set =
  _⇔_.from propositional⇔irrelevant λ where
    (y₁ , x⇓y₁) (y₂ , x⇓y₂) →
      Σ-≡,≡→≡
        (termination-value-unique x⇓y₁ x⇓y₂)
        (_⇔_.to propositional⇔irrelevant
           (Terminates-propositional A-set) _ _)

------------------------------------------------------------------------
-- Alternative definitions of weak bisimilarity

-- An alternative definition of weak bisimilarity (basically the one
-- used in the paper "Partiality, Revisited: The Partiality Monad as a
-- Quotient Inductive-Inductive Type" by Altenkirch, Danielsson and
-- Kraus).
--
-- This definition is pointwise logically equivalent to the one above,
-- see Delay-monad.Partial-order.≈⇔≈₂.

infix 4 _≈₂_

_≈₂_ : Delay A ∞ → Delay A ∞ → Set a
x ≈₂ y = ∀ z → x ⇓ z ⇔ y ⇓ z

-- If A is a set, then this alternative definition of weak
-- bisimilarity is propositional (assuming extensionality).

≈₂-propositional :
  Extensionality a a →
  Is-set A → ∀ {x y} → Is-proposition (x ≈₂ y)
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

-- If A is inhabited, then this definition is not propositional.

¬-≈₃-propositional : A → ¬ (∀ {x y} → Is-proposition (x ≈₃ y))
¬-≈₃-propositional x =
  (∀ {x y} → Is-proposition (x ≈₃ y))  ↝⟨ (λ prop → prop) ⟩
  Is-proposition (y ≈₃ y)              ↝⟨ _⇔_.to propositional⇔irrelevant ⟩
  Proof-irrelevant (y ≈₃ y)            ↝⟨ (_$ _) ∘ (_$ _) ⟩
  proof₁ ≡ proof₂                      ↝⟨ (λ ()) ⟩□
  ⊥                                    □
  where
  y : Delay A ∞
  y = later λ { .force → now x }

  proof₁ : y ≈₃ y
  proof₁ = both-terminate (laterʳ now) (laterʳ now)

  proof₂ : y ≈₃ y
  proof₂ = later λ { .force → both-terminate now now }

-- The last definition of weak bisimilarity given above is pointwise
-- logically equivalent to the first one. Note that the proof is
-- size-preserving.
--
-- (Given suitable notions of extensionality the two definitions are
-- not pointwise isomorphic, because given such assumptions there is
-- only one proof of never ≈₃ never, but multiple proofs of
-- never ≈ never. However, there is no Agda proof of this claim in
-- this module.)

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

------------------------------------------------------------------------
-- Lemmas stating that certain size-preserving functions can be
-- defined iff A is uninhabited

-- A lemma used in several of the proofs below: If A is uninhabited,
-- then weak bisimilarity is trivial.

uninhabited→trivial : ∀ {i} → ¬ A → ∀ x y → [ i ] x ≈ y
uninhabited→trivial ¬A (now   x) _         = ⊥-elim (¬A x)
uninhabited→trivial ¬A (later x) (now   y) = ⊥-elim (¬A y)
uninhabited→trivial ¬A (later x) (later y) =
  later λ { .force → uninhabited→trivial ¬A (force x) (force y) }

-- A variant of laterˡ⁻¹ in which one occurrence of weak bisimilarity
-- is replaced by strong bisimilarity, and both arguments are
-- specialised, can be made size-preserving iff A is uninhabited.
--
-- This lemma is used to prove all similar results below (directly or
-- indirectly), with the exception that an alternative, more direct
-- proof is also given for one of the results.

Laterˡ⁻¹-∼≈ = ∀ {i} {x : A} →
              [ i ] later (λ { .force → now x }) ∼ never →
              [ i ] now x                        ≈ never

size-preserving-laterˡ⁻¹-∼≈⇔uninhabited : Laterˡ⁻¹-∼≈ ⇔ ¬ A
size-preserving-laterˡ⁻¹-∼≈⇔uninhabited = record
  { to   = Laterˡ⁻¹-∼≈  ↝⟨ (λ laterˡ⁻¹-∼≈ x → contradiction (laterˡ⁻¹-∼≈ {_}) x ∞) ⟩□
           ¬ A          □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _} _ → trivial _ _) ⟩□
           Laterˡ⁻¹-∼≈      □
  }
  where

  module _ (laterˡ⁻¹-∼≈ : Laterˡ⁻¹-∼≈) (x : A) where

    mutual

      now≈never : ∀ {i} → [ i ] now x ≈ never
      now≈never = laterˡ⁻¹-∼≈ (later now∼never)

      now∼never : ∀ {i} → [ i ] now x ∼′ never
      force now∼never {j = j} = ⊥-elim (contradiction j)

      contradiction : Size → ⊥
      contradiction i = now≉never (now≈never {i = i})

-- A variant of Laterˡ⁻¹-∼≈ which it is sometimes easier to work with.

Laterˡ⁻¹-∼≈′ = ∀ {i} {x : A} →
               [ i ] later (record { force = now x }) ∼ never →
               [ i ] now x                            ≈ never

size-preserving-laterˡ⁻¹-∼≈′⇔uninhabited : Laterˡ⁻¹-∼≈′ ⇔ ¬ A
size-preserving-laterˡ⁻¹-∼≈′⇔uninhabited =
  Laterˡ⁻¹-∼≈′  ↝⟨ record { to   = _∘ S.transitive (later λ { .force → now })
                          ; from = _∘ S.transitive (later λ { .force → now })
                          } ⟩
  Laterˡ⁻¹-∼≈   ↝⟨ size-preserving-laterˡ⁻¹-∼≈⇔uninhabited ⟩□
  ¬ A           □

-- A variant of laterʳ⁻¹ in which one occurrence of weak bisimilarity
-- is replaced by strong bisimilarity, and both arguments are
-- specialised, can be made size-preserving iff A is uninhabited.

Laterʳ⁻¹-∼≈ = ∀ {i x} →
              [ i ] never ∼ later (record { force = now x }) →
              [ i ] never ≈ now x

size-preserving-laterʳ⁻¹-∼≈⇔uninhabited : Laterʳ⁻¹-∼≈ ⇔ ¬ A
size-preserving-laterʳ⁻¹-∼≈⇔uninhabited =
  Laterʳ⁻¹-∼≈   ↝⟨ record { to   = λ laterʳ⁻¹ → symmetric ∘ laterʳ⁻¹ ∘ S.symmetric
                          ; from = λ laterˡ⁻¹ → symmetric ∘ laterˡ⁻¹ ∘ S.symmetric
                          } ⟩
  Laterˡ⁻¹-∼≈′  ↝⟨ size-preserving-laterˡ⁻¹-∼≈′⇔uninhabited ⟩□
  ¬ A           □

-- The function laterˡ⁻¹ can be made size-preserving iff A is
-- uninhabited.

Laterˡ⁻¹ = ∀ {i x y} →
           [ i ] later x ≈ y →
           [ i ] force x ≈ y

size-preserving-laterˡ⁻¹⇔uninhabited : Laterˡ⁻¹ ⇔ ¬ A
size-preserving-laterˡ⁻¹⇔uninhabited = record
  { to   = Laterˡ⁻¹     ↝⟨ _∘ ∼→≈ ⟩
           Laterˡ⁻¹-∼≈  ↝⟨ _⇔_.to size-preserving-laterˡ⁻¹-∼≈⇔uninhabited ⟩□
           ¬ A          □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _ _} _ → trivial _ _) ⟩□
           Laterˡ⁻¹         □
  }

-- The function laterʳ⁻¹ can be made size-preserving iff A is
-- uninhabited.

Laterʳ⁻¹ = ∀ {i x y} →
           [ i ] x ≈ later y →
           [ i ] x ≈ force y

size-preserving-laterʳ⁻¹⇔uninhabited : Laterʳ⁻¹ ⇔ ¬ A
size-preserving-laterʳ⁻¹⇔uninhabited =
  Laterʳ⁻¹  ↝⟨ record { to   = λ laterʳ⁻¹ → symmetric ∘ laterʳ⁻¹ ∘ symmetric
                      ; from = λ laterˡ⁻¹ → symmetric ∘ laterˡ⁻¹ ∘ symmetric
                      } ⟩
  Laterˡ⁻¹  ↝⟨ size-preserving-laterˡ⁻¹⇔uninhabited ⟩□

  ¬ A       □

-- A variant of ⇓-respects-≈ in which _≈_ is replaced by _∼_ can be
-- made size-preserving in the second argument iff A is uninhabited.

⇓-Respects-∼ʳ = ∀ {i} {x y : Delay A ∞} {z} →
                x ⇓ z → [ i ] x ∼ y → Terminates i y z

size-preserving-⇓-respects-∼ʳ⇔uninhabited : ⇓-Respects-∼ʳ ⇔ ¬ A
size-preserving-⇓-respects-∼ʳ⇔uninhabited = record
  { to   = ⇓-Respects-∼ʳ  ↝⟨ (λ resp → resp (laterʳ now)) ⟩
           Laterˡ⁻¹-∼≈    ↝⟨ _⇔_.to size-preserving-laterˡ⁻¹-∼≈⇔uninhabited ⟩
           ¬ A            □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           ⇓-Respects-∼ʳ    □
  }

-- The lemma ⇓-respects-≈ can be made size-preserving in the second
-- argument iff A is uninhabited.

⇓-Respects-≈ʳ = ∀ {i} {x y : Delay A ∞} {z} →
                x ⇓ z → [ i ] x ≈ y → Terminates i y z

size-preserving-⇓-respects-≈ʳ⇔uninhabited : ⇓-Respects-≈ʳ ⇔ ¬ A
size-preserving-⇓-respects-≈ʳ⇔uninhabited = record
  { to   = ⇓-Respects-≈ʳ  ↝⟨ (λ resp x⇓z → resp x⇓z ∘ ∼→≈) ⟩
           ⇓-Respects-∼ʳ  ↝⟨ _⇔_.to size-preserving-⇓-respects-∼ʳ⇔uninhabited ⟩□
           ¬ A            □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           ⇓-Respects-≈ʳ    □
  }

-- There is a variant of transitivity-≈∼ that preserves the size of
-- the second argument iff A is uninhabited.

Transitivity-≈∼ʳ = ∀ {i} {x y z : Delay A ∞} →
                   x ≈ y → [ i ] y ∼ z → [ i ] x ≈ z

size-preserving-transitivity-≈∼ʳ⇔uninhabited : Transitivity-≈∼ʳ ⇔ ¬ A
size-preserving-transitivity-≈∼ʳ⇔uninhabited = record
  { to   = Transitivity-≈∼ʳ  ↝⟨ (λ trans → trans) ⟩
           ⇓-Respects-∼ʳ     ↝⟨ _⇔_.to size-preserving-⇓-respects-∼ʳ⇔uninhabited ⟩□
           ¬ A               □
  ; from = ¬ A               ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≈ y)   ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Transitivity-≈∼ʳ  □
  }

-- There is a variant of transitivity-∼≈ that preserves the size of
-- the first argument iff A is uninhabited.

Transitivity-∼≈ˡ = ∀ {i} {x y z : Delay A ∞} →
                   [ i ] x ∼ y → y ≈ z → [ i ] x ≈ z

size-preserving-transitivity-∼≈ˡ⇔uninhabited : Transitivity-∼≈ˡ ⇔ ¬ A
size-preserving-transitivity-∼≈ˡ⇔uninhabited =
  Transitivity-∼≈ˡ  ↝⟨ record { to   = λ trans {_ _ _ _} p q →
                                         symmetric (trans (S.symmetric q) (symmetric p))
                              ; from = λ trans {_ _ _ _} p q →
                                         symmetric (trans (symmetric q) (S.symmetric p))
                              } ⟩
  Transitivity-≈∼ʳ  ↝⟨ size-preserving-transitivity-≈∼ʳ⇔uninhabited ⟩□

  ¬ A               □

-- There is a transitivity proof that preserves the size of the
-- second argument iff A is uninhabited.

Transitivityʳ = ∀ {i} {x y z : Delay A ∞} →
                x ≈ y → [ i ] y ≈ z → [ i ] x ≈ z

size-preserving-transitivityʳ⇔uninhabited : Transitivityʳ ⇔ ¬ A
size-preserving-transitivityʳ⇔uninhabited = record
  { to   = Transitivityʳ  ↝⟨ (λ trans → trans) ⟩
           ⇓-Respects-≈ʳ  ↝⟨ _⇔_.to size-preserving-⇓-respects-≈ʳ⇔uninhabited ⟩□
           ¬ A            □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Transitivityʳ    □
  }

-- There is a transitivity proof that preserves the size of the
-- first argument iff A is uninhabited.

Transitivityˡ = ∀ {i} {x y z : Delay A ∞} →
                [ i ] x ≈ y → y ≈ z → [ i ] x ≈ z

size-preserving-transitivityˡ⇔uninhabited : Transitivityˡ ⇔ ¬ A
size-preserving-transitivityˡ⇔uninhabited =
  Transitivityˡ  ↝⟨ record { to   = λ trans {_ _ _ _} p q →
                                      symmetric (trans (symmetric q) (symmetric p))
                           ; from = λ trans {_ _ _ _} p q →
                                      symmetric (trans (symmetric q) (symmetric p))
                           } ⟩
  Transitivityʳ  ↝⟨ size-preserving-transitivityʳ⇔uninhabited ⟩□

  ¬ A            □

-- There is a fully size-preserving variant of transitivity iff A is
-- uninhabited.

Transitivity = ∀ {i} {x y z : Delay A ∞} →
               [ i ] x ≈ y → [ i ] y ≈ z → [ i ] x ≈ z

size-preserving-transitivity⇔uninhabited : Transitivity ⇔ ¬ A
size-preserving-transitivity⇔uninhabited = record
  { to   = Transitivity   ↝⟨ (λ trans → trans) ⟩
           Transitivityˡ  ↝⟨ _⇔_.to size-preserving-transitivityˡ⇔uninhabited ⟩
           ¬ A            □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Transitivity     □
  }

-- The following two lemmas provide an alternative proof of one
-- direction of the previous lemma (with a small change to one of the
-- types).

-- If there is a transitivity proof that is size-preserving in both
-- arguments, then weak bisimilarity is trivial.

size-preserving-transitivity→trivial :
  (∀ {i} x {y z : Delay A ∞} → [ i ] x ≈ y → [ i ] y ≈ z → [ i ] x ≈ z) →
  ∀ {i} (x y : Delay A ∞) → [ i ] x ≈ y
size-preserving-transitivity→trivial _≈⟨_⟩_ x y =
  (x                         ≈⟨ laterʳ (x ∎ʷ) ⟩
  (later (λ { .force → x })  ≈⟨ later (λ { .force → size-preserving-transitivity→trivial _≈⟨_⟩_ x y }) ⟩
  (later (λ { .force → y })  ≈⟨ laterˡ (y ∎ʷ) ⟩
  (y                         ∎ʷ))))
  where
  _∎ʷ = reflexive

-- If there is a transitivity proof that is size-preserving in both
-- arguments, then the carrier type A is not inhabited.

size-preserving-transitivity→uninhabited :
  (∀ {i} x {y z : Delay A ∞} →
   [ i ] x ≈ y → [ i ] y ≈ z → [ i ] x ≈ z) →
  ¬ A
size-preserving-transitivity→uninhabited trans x =
  now≉never (size-preserving-transitivity→trivial trans (now x) never)
