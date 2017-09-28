------------------------------------------------------------------------
-- The expansion relation
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Delay-monad.Expansion {a} {A : Set a} where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Function-universe equality-with-J hiding (_∘_)
open import H-level equality-with-J

open import Delay-monad
open import Delay-monad.Strong-bisimilarity as Strong
  using ([_]_∼_; _∼_; now; later; force)
open import Delay-monad.Weak-bisimilarity as Weak
  using ([_]_≈_; _≈_; now; later; laterˡ; laterʳ; force)

------------------------------------------------------------------------
-- The expansion relation

-- The expansion relation, defined using mixed induction and
-- coinduction.

infix 4 [_]_≳_ [_]_≳′_ _≳_ _≳′_ _≲_ _≲′_

mutual

  data [_]_≳_ (i : Size) : (x y : Delay A ∞) → Set a where
    now    : ∀ {x} → [ i ] now x ≳ now x
    later  : ∀ {x y} →
             [ i ] force x ≳′ force y →
             [ i ] later x ≳  later y
    laterˡ : ∀ {x y} →
             [ i ] force x ≳ y →
             [ i ] later x ≳ y

  record [_]_≳′_ (i : Size) (x y : Delay A ∞) : Set a where
    coinductive
    field
      force : {j : Size< i} → [ j ] x ≳ y

open [_]_≳′_ public

_≳_ _≳′_ _≲_ _≲′_ : Delay A ∞ → Delay A ∞ → Set a
_≳_  = [ ∞ ]_≳_
_≳′_ = [ ∞ ]_≳′_
_≲_  = flip _≳_
_≲′_ = flip _≳′_

------------------------------------------------------------------------
-- Conversion lemmas

-- Strong bisimilarity is contained in the expansion relation.

∼→≳ : ∀ {i x y} → [ i ] x ∼ y → [ i ] x ≳ y
∼→≳ now       = now
∼→≳ (later p) = later λ { .force → ∼→≳ (force p) }

-- The expansion relation is contained in weak bisimilarity.

≳→≈ : ∀ {i x y} → [ i ] x ≳ y → [ i ] x ≈ y
≳→≈ now        = now
≳→≈ (later  p) = later λ { .force → ≳→≈ (force p) }
≳→≈ (laterˡ p) = laterˡ (≳→≈ p)

-- In some cases weak bisimilarity is contained in the expansion
-- relation.

≈→≳-now : ∀ {i x y} → [ i ] x ≈ now y → [ i ] x ≳ now y
≈→≳-now now        = now
≈→≳-now (laterˡ p) = laterˡ (≈→≳-now p)

≈→≳-never : ∀ {i x} → [ i ] never ≈ x → [ i ] never ≳ x
≈→≳-never (later  p) = later λ { .force → ≈→≳-never (force p) }
≈→≳-never (laterˡ p) = ≈→≳-never p
≈→≳-never (laterʳ p) = later λ { .force → ≈→≳-never p }

-- In some cases the expansion relation is contained in strong
-- bisimilarity.

≳→∼-never : ∀ {i x} → [ i ] never ≳ x → [ i ] never ∼ x
≳→∼-never (later  p) = later λ { .force → ≳→∼-never (force p) }
≳→∼-never (laterˡ p) = ≳→∼-never p

------------------------------------------------------------------------
-- Some negative results

-- The computation never is not an expansion of now x.

never≵now : ∀ {i x} → ¬ [ i ] never ≳ now x
never≵now {i} = Weak.now≉never {i = i} ∘ Weak.symmetric ∘ ≳→≈

-- The computation now x is not an expansion of never.

now≵never : ∀ {i x} → ¬ [ i ] now x ≳ never
now≵never = Weak.now≉never ∘ ≳→≈

-- The expansion relation defined here is not pointwise propositional.

¬-≳-proposition : ¬ (∀ {x y} → Is-proposition (x ≳ y))
¬-≳-proposition =
  (∀ {x y} → Is-proposition (x ≳ y))  ↝⟨ (λ prop → _⇔_.to propositional⇔irrelevant (prop {x = never} {y = never})) ⟩
  Proof-irrelevant (never ≳ never)    ↝⟨ (λ irr → irr _ _) ⟩
  proof₁ ≡ proof₂                     ↝⟨ (λ ()) ⟩□
  ⊥₀                                  □
  where
  proof₁ : never ≳ never
  proof₁ = later λ { .force → proof₁ }

  proof₂ : never ≳ never
  proof₂ = laterˡ proof₁

------------------------------------------------------------------------
-- Sometimes one can remove later constructors

-- One can remove a later constructor to the right.

laterʳ⁻¹ : ∀ {i} {j : Size< i} {x y} →
           [ i ] x ≳ later y →
           [ j ] x ≳ force y
laterʳ⁻¹ (later  p) = laterˡ (force p)
laterʳ⁻¹ (laterˡ p) = laterˡ (laterʳ⁻¹ p)

-- One can remove one later constructor on each side.

later⁻¹ : ∀ {i} {j : Size< i} {x y} →
          [ i ] later x ≳ later y →
          [ j ] force x ≳ force y
later⁻¹ (later  p) = force p
later⁻¹ (laterˡ p) = laterʳ⁻¹ p

-- The following size-preserving variant of laterʳ⁻¹ can be defined.
--
-- Several other later-removing lemmas cannot be defined (unless A is
-- uninhabited), see below.

laterˡʳ⁻¹ :
  ∀ {i} {x y : Delay′ A ∞} →
  [ i ] later x ≳ force y →
  [ i ] force x ≳ later y →
  [ i ] force x ≳ force y
laterˡʳ⁻¹ {i} p q = laterˡʳ⁻¹′ p q refl refl
  where
  laterˡʳ⁻¹″ :
    ∀ {x′ y′} {x y : Delay′ A ∞} →
    ({j : Size< i} → [ j ] x′ ≳ force y) →
    ({j : Size< i} → [ j ] force x ≳ y′) →
    later x ≡ x′ → later y ≡ y′ →
    [ i ] later x ≳ later y
  laterˡʳ⁻¹″ p q refl refl = later λ { .force → laterˡʳ⁻¹ p q }

  laterˡʳ⁻¹′ :
    ∀ {x′ y′} {x y : Delay′ A ∞} →
    [ i ] later x ≳ y′ →
    [ i ] x′ ≳ later y →
    x′ ≡ force x → y′ ≡ force y →
    [ i ] x′ ≳ y′
  laterˡʳ⁻¹′ (later  p) (later  q) x′≡  y′≡  = laterˡʳ⁻¹″ (force p) (force q)                x′≡ y′≡
  laterˡʳ⁻¹′ (later  p) (laterˡ q) x′≡  y′≡  = laterˡʳ⁻¹″ (force p) (λ { {_} → laterʳ⁻¹ q }) x′≡ y′≡
  laterˡʳ⁻¹′ (laterˡ p) _          refl refl = p

------------------------------------------------------------------------
-- The expansion relation is a partial order (up to weak bisimilarity)

-- The expansion relation is reflexive.

reflexive : ∀ {i} (x : Delay A ∞) → [ i ] x ≳ x
reflexive (now x)   = now
reflexive (later x) = later λ { .force → reflexive (force x) }

-- The expansion relation is antisymmetric (up to weak bisimilarity).

antisymmetric :
  ∀ {i} {x y : Delay A ∞} →
  [ i ] x ≳ y → [ i ] y ≳ x → [ i ] x ≈ y
antisymmetric p _ = ≳→≈ p

-- The expansion relation is transitive.

transitive : ∀ {i} {x y z : Delay A ∞} →
             x ≳ y → [ i ] y ≳ z → [ i ] x ≳ z
transitive {x = now x}   now now = now
transitive {x = later x} p   q   = trans-later p q
  where
  trans-later : ∀ {i x} {y z : Delay A ∞} →
                later x ≳ y → [ i ] y ≳ z → [ i ] later x ≳ z
  trans-later p          (later  q) = later λ { .force →
                                        transitive (later⁻¹ p) (force q) }
  trans-later p          (laterˡ q) = trans-later (laterʳ⁻¹ p) q
  trans-later (laterˡ p) q          = laterˡ (transitive p q)

-- Some size-preserving variants of transitivity.
--
-- Many size-preserving variants cannot be defined (unless A is
-- uninhabited), see below.

transitive-≳∼ :
  ∀ {i} {x y z : Delay A ∞} →
  [ i ] x ≳ y → [ i ] y ∼ z → [ i ] x ≳ z
transitive-≳∼ now        now       = now
transitive-≳∼ (later  p) (later q) = later λ { .force →
                                       transitive-≳∼ (force p) (force q) }
transitive-≳∼ (laterˡ p) q         = laterˡ (transitive-≳∼ p q)

transitive-∼≳ :
  ∀ {i} {x y z : Delay A ∞} →
  x ∼ y → [ i ] y ≳ z → [ i ] x ≳ z
transitive-∼≳ = transitive ∘ ∼→≳

transitive-≳≈ :
  ∀ {i} {x y z : Delay A ∞} →
  x ≳ y → [ i ] y ≈ z → [ i ] x ≈ z
transitive-≳≈ {x = now x}   now q = q
transitive-≳≈ {x = later x} p   q = trans-later p q
  where
  trans-later : ∀ {i x} {y z : Delay A ∞} →
                later x ≳ y → [ i ] y ≈ z → [ i ] later x ≈ z
  trans-later p          (later  q) = later λ { .force →
                                        transitive-≳≈ (later⁻¹ p) (force q) }
  trans-later (later  p) (laterʳ q) = later λ { .force →
                                        transitive-≳≈ (force p) (Weak.laterˡ⁻¹ q) }
  trans-later p          (laterˡ q) = trans-later (laterʳ⁻¹ p) q
  trans-later (laterˡ p) q          = laterˡ (transitive-≳≈ p q)

transitive-≈≲ :
  ∀ {i} {x y z : Delay A ∞} →
  [ i ] x ≈ y → y ≲ z → [ i ] x ≈ z
transitive-≈≲ p q = Weak.symmetric (transitive-≳≈ q (Weak.symmetric p))

-- Some special cases of symmetry hold.

symmetric-neverˡ : ∀ {i x} → [ i ] never ≳ x → [ i ] x ≳ never
symmetric-neverˡ (later  p) = later λ { .force →
                                symmetric-neverˡ (force p) }
symmetric-neverˡ (laterˡ p) = symmetric-neverˡ p

symmetric-neverʳ : ∀ {i x} → [ i ] x ≳ never → [ i ] never ≳ x
symmetric-neverʳ (later  p) = later λ { .force →
                                symmetric-neverʳ (force p) }
symmetric-neverʳ (laterˡ p) = later λ { .force → symmetric-neverʳ p }

------------------------------------------------------------------------
-- Lemmas stating that functions of certain types can be defined iff A
-- is uninhabited

-- A lemma used in several of the proofs below: If A is uninhabited,
-- then the expansion relation is trivial.

uninhabited→trivial : ∀ {i} → ¬ A → ∀ x y → [ i ] x ≳ y
uninhabited→trivial ¬A (now x)   _         = ⊥-elim (¬A x)
uninhabited→trivial ¬A (later x) (now y)   = ⊥-elim (¬A y)
uninhabited→trivial ¬A (later x) (later y) =
  later λ { .force → uninhabited→trivial ¬A (force x) (force y) }

-- There is a function that removes a later constructor to the left,
-- for computations of specific forms, iff A is uninhabited.

Laterˡ⁻¹′ = ∀ {x} →
            later (record { force = now x }) ≳
            later (record { force = now x }) →
            now x ≳ later (record { force = now x })

laterˡ⁻¹′⇔uninhabited : Laterˡ⁻¹′ ⇔ ¬ A
laterˡ⁻¹′⇔uninhabited = record
  { to = Laterˡ⁻¹′                        ↝⟨ (λ hyp _ → hyp) ⟩
         (∀ x → y x ≳ y x → now x ≳ y x)  ↝⟨ (λ hyp x → hyp x (reflexive _)) ⟩
         (∀ x → now x ≳ y x)              ↝⟨ (λ hyp x → now-x≵y x (hyp x)) ⟩□
         ¬ A                              □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≳ y)  ↝⟨ (λ hyp {_} _ → hyp _ _) ⟩□
           Laterˡ⁻¹′        □
  }
  where
  module _ (x : A) where

    y : Delay A ∞
    y = later _

    now-x≵y : ¬ now x ≳ y
    now-x≵y ()

-- There is a function that removes a later constructor to the left
-- iff A is uninhabited.

Laterˡ⁻¹ = ∀ {x y} → later x ≳ y → force x ≳ y

laterˡ⁻¹⇔uninhabited : Laterˡ⁻¹ ⇔ ¬ A
laterˡ⁻¹⇔uninhabited = record
  { to = Laterˡ⁻¹   ↝⟨ (λ hyp → hyp) ⟩
         Laterˡ⁻¹′  ↝⟨ _⇔_.to laterˡ⁻¹′⇔uninhabited ⟩
         ¬ A        □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≳ y)  ↝⟨ (λ hyp {_ _} _ → hyp _ _) ⟩□
           Laterˡ⁻¹         □
  }

-- The following variants of transitivity can be proved iff A is
-- uninhabited.

Transitivity-≈≳ = {x y z : Delay A ∞} → x ≈ y → y ≳ z → x ≳ z
Transitivity-≳≈ = {x y z : Delay A ∞} → x ≳ y → y ≈ z → x ≳ z

transitive-≈≳⇔uninhabited : Transitivity-≈≳ ⇔ ¬ A
transitive-≈≳⇔uninhabited = record
  { to = Transitivity-≈≳  ↝⟨ (λ trans → trans (laterʳ (Weak.reflexive _))) ⟩
         Laterˡ⁻¹         ↝⟨ _⇔_.to laterˡ⁻¹⇔uninhabited ⟩□
         ¬ A              □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≳ y)  ↝⟨ (λ hyp {_ _ _} _ _ → hyp _ _) ⟩□
           Transitivity-≈≳  □
  }

transitive-≳≈⇔uninhabited : Transitivity-≳≈ ⇔ ¬ A
transitive-≳≈⇔uninhabited = record
  { to = Transitivity-≳≈  ↝⟨ (λ trans {_ y} lx≳y → later⁻¹ {y = record { force = y }}
                                                           (trans lx≳y (laterʳ (Weak.reflexive _)))) ⟩
         Laterˡ⁻¹         ↝⟨ _⇔_.to laterˡ⁻¹⇔uninhabited ⟩□
         ¬ A              □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≳ y)  ↝⟨ (λ hyp {_ _ _} _ _ → hyp _ _) ⟩□
           Transitivity-≳≈  □
  }

------------------------------------------------------------------------
-- Lemmas stating that size-preserving functions of certain types can
-- be defined iff A is uninhabited

-- A variant of laterʳ⁻¹ in which one occurrence of the expansion
-- relation is replaced by strong bisimilarity, and both arguments are
-- specialised, can be made size-preserving iff A is uninhabited.

Laterʳ⁻¹-∼≳ = ∀ {i x} →
              [ i ] never ∼ later (record { force = now x }) →
              [ i ] never ≳ now x

size-preserving-laterʳ⁻¹-∼≳⇔uninhabited : Laterʳ⁻¹-∼≳ ⇔ ¬ A
size-preserving-laterʳ⁻¹-∼≳⇔uninhabited = record
  { to   = Laterʳ⁻¹-∼≳       ↝⟨ ≳→≈ ∘_ ⟩
           Weak.Laterʳ⁻¹-∼≈  ↝⟨ _⇔_.to Weak.size-preserving-laterʳ⁻¹-∼≈⇔uninhabited ⟩□
           ¬ A               □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≳ y)  ↝⟨ (λ trivial {_ _} _ → trivial _ _) ⟩□
           Laterʳ⁻¹-∼≳      □
  }

-- The function laterʳ⁻¹ can be made size-preserving iff A is
-- uninhabited.

Laterʳ⁻¹ = ∀ {i x y} → [ i ] x ≳ later y → [ i ] x ≳ force y

size-preserving-laterʳ⁻¹⇔uninhabited : Laterʳ⁻¹ ⇔ ¬ A
size-preserving-laterʳ⁻¹⇔uninhabited = record
  { to   = Laterʳ⁻¹     ↝⟨ _∘ ∼→≳ ⟩
           Laterʳ⁻¹-∼≳  ↝⟨ _⇔_.to size-preserving-laterʳ⁻¹-∼≳⇔uninhabited ⟩□
           ¬ A          □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≳ y)  ↝⟨ (λ trivial {_ _ _} _ → trivial _ _) ⟩□
           Laterʳ⁻¹         □
  }

-- There is a variant of transitive-∼≳ that preserves the size of the
-- first argument iff A is uninhabited.

Transitivity-∼≳ˡ = ∀ {i} {x y z : Delay A ∞} →
                   [ i ] x ∼ y → y ≳ z → [ i ] x ≳ z

size-preserving-transitivity-∼≳ˡ⇔uninhabited : Transitivity-∼≳ˡ ⇔ ¬ A
size-preserving-transitivity-∼≳ˡ⇔uninhabited = record
  { to   = Transitivity-∼≳ˡ  ↝⟨ (λ trans never∼lnx → trans never∼lnx (laterˡ now) ) ⟩
           Laterʳ⁻¹-∼≳       ↝⟨ _⇔_.to size-preserving-laterʳ⁻¹-∼≳⇔uninhabited ⟩□
           ¬ A               □
  ; from = ¬ A               ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≳ y)   ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Transitivity-∼≳ˡ  □
  }

-- There is a transitivity proof that preserves the size of the
-- first argument iff A is uninhabited.

Transitivityˡ = ∀ {i} {x y z : Delay A ∞} →
                [ i ] x ≳ y → y ≳ z → [ i ] x ≳ z

size-preserving-transitivityˡ⇔uninhabited : Transitivityˡ ⇔ ¬ A
size-preserving-transitivityˡ⇔uninhabited = record
  { to   = Transitivityˡ     ↝⟨ _∘ ∼→≳ ⟩
           Transitivity-∼≳ˡ  ↝⟨ _⇔_.to size-preserving-transitivity-∼≳ˡ⇔uninhabited ⟩□
           ¬ A               □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≳ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Transitivityˡ    □
  }

-- There is a variant of transitive-≳≈ that preserves the size of the
-- first argument iff A is uninhabited.

Transitivity-≳≈ˡ = ∀ {i} {x y z : Delay A ∞} →
                   [ i ] x ≳ y → y ≈ z → [ i ] x ≈ z

size-preserving-transitivity-≳≈ˡ⇔uninhabited : Transitivity-≳≈ˡ ⇔ ¬ A
size-preserving-transitivity-≳≈ˡ⇔uninhabited = record
  { to   = Transitivity-≳≈ˡ       ↝⟨ _∘ ∼→≳ ⟩
           Weak.Transitivity-∼≈ˡ  ↝⟨ _⇔_.to Weak.size-preserving-transitivity-∼≈ˡ⇔uninhabited ⟩
           ¬ A                    □
  ; from = ¬ A               ↝⟨ Weak.uninhabited→trivial ⟩
           (∀ x y → x ≈ y)   ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Transitivity-≳≈ˡ  □
  }

-- More lemmas of a similar kind.

Transitivity-≈≲ʳ = ∀ {i} {x y z : Delay A ∞} →
                   x ≈ y → [ i ] z ≳ y → [ i ] x ≈ z

size-preserving-transitivity-≈≲ʳ⇔uninhabited : Transitivity-≈≲ʳ ⇔ ¬ A
size-preserving-transitivity-≈≲ʳ⇔uninhabited =
  Transitivity-≈≲ʳ  ↝⟨ record { to   = λ trans x≳y y≈z → Weak.symmetric (trans (Weak.symmetric y≈z) x≳y)
                              ; from = λ trans x≈y y≲z → Weak.symmetric (trans y≲z (Weak.symmetric x≈y))
                              } ⟩
  Transitivity-≳≈ˡ  ↝⟨ size-preserving-transitivity-≳≈ˡ⇔uninhabited ⟩□
  ¬ A               □

Transitivity-≈≳ˡ = ∀ {i} {x y z : Delay A ∞} →
                   [ i ] x ≈ y → y ≳ z → [ i ] x ≈ z

size-preserving-transitivity-≈≳ˡ⇔uninhabited : Transitivity-≈≳ˡ ⇔ ¬ A
size-preserving-transitivity-≈≳ˡ⇔uninhabited = record
  { to   = Transitivity-≈≳ˡ  ↝⟨ (λ trans x≈ly → trans x≈ly (laterˡ (reflexive _))) ⟩
           Weak.Laterʳ⁻¹     ↝⟨ _⇔_.to Weak.size-preserving-laterʳ⁻¹⇔uninhabited ⟩
           ¬ A               □
  ; from = ¬ A               ↝⟨ Weak.uninhabited→trivial ⟩
           (∀ x y → x ≈ y)   ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Transitivity-≈≳ˡ  □
  }
