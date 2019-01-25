------------------------------------------------------------------------
-- A variant of weak bisimilarity that can be used to relate the
-- number of steps in two computations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Delay-monad.Quantitative-weak-bisimilarity {a} {A : Set a} where

open import Conat
  using (Conat; zero; suc; force; ⌜_⌝; _+_; _*_;
         [_]_≤_; step-≤; step-∼≤; _∎≤; step-∼; _∎∼)
open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (_+_; _*_)

open import Function-universe equality-with-J as F hiding (id; _∘_)

open import Delay-monad
open import Delay-monad.Bisimilarity as B
  using (now; later; laterˡ; laterʳ; force)

------------------------------------------------------------------------
-- The relation

mutual

  -- Quantitative weak bisimilarity. [ ∞ ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ y
  -- is a variant of x B.≈ y for which the number of later
  -- constructors in x is bounded by nˡ plus 1 + mˡ times the number
  -- of later constructors in y, and the number of later constructors
  -- in y is bounded by nʳ plus 1 + mʳ times the number of later
  -- constructors in x (see ≈⇔≈×steps≤steps² below).

  infix 4 [_∣_∣_∣_∣_]_≈_ [_∣_∣_∣_∣_]_≈′_

  data [_∣_∣_∣_∣_]_≈_
         (i : Size) (mˡ mʳ : Conat ∞) :
         Conat ∞ → Conat ∞ → Delay A ∞ → Delay A ∞ → Set a where
    now    : ∀ {x nˡ nʳ} → [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] now x ≈ now x
    later  : ∀ {x y nˡ nʳ} →
             [ i ∣ mˡ ∣ mʳ ∣ nˡ + mˡ ∣ nʳ + mʳ ] x .force ≈′ y .force →
             [ i ∣ mˡ ∣ mʳ ∣ nˡ      ∣ nʳ      ] later x  ≈  later y
    laterˡ : ∀ {x y nˡ nʳ} →
             [ i ∣ mˡ ∣ mʳ ∣ nˡ .force ∣ nʳ ] x .force ≈ y →
             [ i ∣ mˡ ∣ mʳ ∣ suc nˡ    ∣ nʳ ] later x  ≈ y
    laterʳ : ∀ {x y nˡ nʳ} →
             [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ .force ] x ≈ y .force →
             [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ suc nʳ    ] x ≈ later y

  record [_∣_∣_∣_∣_]_≈′_
           (i : Size) (mˡ mʳ nˡ nʳ : Conat ∞)
           (x y : Delay A ∞) : Set a where
    coinductive
    field
      force : {j : Size< i} → [ j ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ y

open [_∣_∣_∣_∣_]_≈′_ public

-- Specialised variants of [_∣_∣_∣_∣_]_≈_ and [_∣_∣_∣_∣_]_≈′_.

infix 4 [_∣_∣_]_≈_ [_∣_∣_]_≈′_

[_∣_∣_]_≈_ : Size → Conat ∞ → Conat ∞ → Delay A ∞ → Delay A ∞ → Set a
[ i ∣ mˡ ∣ mʳ ] x ≈ y = [ i ∣ mˡ ∣ mʳ ∣ zero ∣ zero ] x ≈ y

[_∣_∣_]_≈′_ : Size → Conat ∞ → Conat ∞ → Delay A ∞ → Delay A ∞ → Set a
[ i ∣ mˡ ∣ mʳ ] x ≈′ y = [ i ∣ mˡ ∣ mʳ ∣ zero ∣ zero ] x ≈′ y

-- Quantitative expansion.

infix 4 [_∣_∣_]_≳_ [_∣_∣_]_≳′_ [_∣_]_≳_ [_∣_]_≳′_

[_∣_∣_]_≳_ : Size → Conat ∞ → Conat ∞ → Delay A ∞ → Delay A ∞ → Set a
[ i ∣ m ∣ n ] x ≳ y = [ i ∣ m ∣ zero ∣ n ∣ zero ] x ≈ y

[_∣_∣_]_≳′_ : Size → Conat ∞ → Conat ∞ → Delay A ∞ → Delay A ∞ → Set a
[ i ∣ m ∣ n ] x ≳′ y = [ i ∣ m ∣ zero ∣ n ∣ zero ] x ≈′ y

[_∣_]_≳_ : Size → Conat ∞ → Delay A ∞ → Delay A ∞ → Set a
[ i ∣ m ] x ≳ y = [ i ∣ m ∣ zero ] x ≳ y

[_∣_]_≳′_ : Size → Conat ∞ → Delay A ∞ → Delay A ∞ → Set a
[ i ∣ m ] x ≳′ y = [ i ∣ m ∣ zero ] x ≳′ y

-- The converse of quantitative expansion.

infix 4 [_∣_∣_]_≲_ [_∣_∣_]_≲′_ [_∣_]_≲_ [_∣_]_≲′_

[_∣_∣_]_≲_ : Size → Conat ∞ → Conat ∞ → Delay A ∞ → Delay A ∞ → Set a
[ i ∣ m ∣ n ] x ≲ y = [ i ∣ m ∣ n ] y ≳ x

[_∣_∣_]_≲′_ : Size → Conat ∞ → Conat ∞ → Delay A ∞ → Delay A ∞ → Set a
[ i ∣ m ∣ n ] x ≲′ y = [ i ∣ m ∣ n ] y ≳′ x

[_∣_]_≲_ : Size → Conat ∞ → Delay A ∞ → Delay A ∞ → Set a
[ i ∣ m ] x ≲ y = [ i ∣ m ] y ≳ x

[_∣_]_≲′_ : Size → Conat ∞ → Delay A ∞ → Delay A ∞ → Set a
[ i ∣ m ] x ≲′ y = [ i ∣ m ] y ≳′ x

------------------------------------------------------------------------
-- Conversions

-- Weakening.

weaken :
  ∀ {i mˡ mˡ′ mʳ mʳ′ nˡ nˡ′ nʳ nʳ′ x y} →
  [ ∞ ] mˡ ≤ mˡ′ → [ ∞ ] mʳ ≤ mʳ′ →
  [ ∞ ] nˡ ≤ nˡ′ → [ ∞ ] nʳ ≤ nʳ′ →
  [ i ∣ mˡ  ∣ mʳ  ∣ nˡ  ∣ nʳ  ] x ≈ y →
  [ i ∣ mˡ′ ∣ mʳ′ ∣ nˡ′ ∣ nʳ′ ] x ≈ y
weaken pˡ pʳ = λ where
  qˡ       qʳ       now        → now
  (suc qˡ) qʳ       (laterˡ r) → laterˡ (weaken pˡ pʳ (qˡ .force) qʳ r)
  qˡ       (suc qʳ) (laterʳ r) → laterʳ (weaken pˡ pʳ qˡ (qʳ .force) r)
  qˡ       qʳ       (later r)  → later λ { .force →
                                   weaken pˡ pʳ
                                     (qˡ Conat.+-mono pˡ)
                                     (qʳ Conat.+-mono pʳ)
                                     (r .force) }

weakenˡʳ :
  ∀ {i mˡ mʳ nˡ nˡ′ nʳ nʳ′ x y} →
  [ ∞ ] nˡ ≤ nˡ′ → [ ∞ ] nʳ ≤ nʳ′ →
  [ i ∣ mˡ ∣ mʳ ∣ nˡ  ∣ nʳ  ] x ≈ y →
  [ i ∣ mˡ ∣ mʳ ∣ nˡ′ ∣ nʳ′ ] x ≈ y
weakenˡʳ = weaken (_ ∎≤) (_ ∎≤)

weakenˡ :
  ∀ {i mˡ mʳ nˡ nˡ′ nʳ x y} →
  [ ∞ ] nˡ ≤ nˡ′ →
  [ i ∣ mˡ ∣ mʳ ∣ nˡ  ∣ nʳ ] x ≈ y →
  [ i ∣ mˡ ∣ mʳ ∣ nˡ′ ∣ nʳ ] x ≈ y
weakenˡ p = weakenˡʳ p (_ ∎≤)

weakenʳ :
  ∀ {i mˡ mʳ nˡ nʳ nʳ′ x y} →
  [ ∞ ] nʳ ≤ nʳ′ →
  [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ  ] x ≈ y →
  [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ′ ] x ≈ y
weakenʳ p = weakenˡʳ (_ ∎≤) p

-- Strong bisimilarity is contained in quantitative weak bisimilarity.

∼→≈ : ∀ {i mˡ mʳ nˡ nʳ x y} →
      B.[ i ] x ∼ y → [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ y
∼→≈ now       = now
∼→≈ (later p) = later λ { .force → ∼→≈ (p .force) }

-- Quantitative expansion is contained in expansion.

≳→≳ : ∀ {i m n x y} →
      [ i ∣ m ∣ n ] x ≳ y → B.[ i ] x ≳ y
≳→≳ now        = now
≳→≳ (later p)  = later λ { .force → ≳→≳ (p .force) }
≳→≳ (laterˡ p) = laterˡ (≳→≳ p)

-- Quantitative weak bisimilarity is contained in weak bisimilarity.

≈→≈ : ∀ {i mˡ mʳ nˡ nʳ x y} →
      [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ y → B.[ i ] x ≈ y
≈→≈ now        = now
≈→≈ (later p)  = later λ { .force → ≈→≈ (p .force) }
≈→≈ (laterˡ p) = laterˡ (≈→≈ p)
≈→≈ (laterʳ p) = laterʳ (≈→≈ p)

-- In some cases expansion is contained in quantitative expansion.

≳→≳-steps :
  ∀ {m x y i} → B.[ i ] x ≳ y → [ i ∣ m ∣ steps x ] x ≳ y
≳→≳-steps     now               = now
≳→≳-steps     (laterˡ p)        = laterˡ (≳→≳-steps p)
≳→≳-steps {m} (later {x = x} p) = later λ { .force →
  weakenˡ lemma (≳→≳-steps (p .force)) }
  where
  lemma =
    steps (x .force)     ≤⟨ Conat.≤suc ⟩
    steps (later x)      ≤⟨ Conat.m≤m+n ⟩
    steps (later x) + m  ∎≤

-- In some cases weak bisimilarity is contained in quantitative weak
-- bisimilarity.

≈→≈-steps :
  ∀ {mˡ mʳ x y i} →
  B.[ i ] x ≈ y → [ i ∣ mˡ ∣ mʳ ∣ steps x ∣ steps y ] x ≈ y
≈→≈-steps           now                       = now
≈→≈-steps           (laterˡ p)                = laterˡ (≈→≈-steps p)
≈→≈-steps           (laterʳ p)                = laterʳ (≈→≈-steps p)
≈→≈-steps {mˡ} {mʳ} (later {x = x} {y = y} p) = later λ { .force →
  weakenˡʳ x-lemma y-lemma (≈→≈-steps (p .force)) }
  where
  x-lemma =
    steps (x .force)      ≤⟨ Conat.≤suc ⟩
    steps (later x)       ≤⟨ Conat.m≤m+n ⟩
    steps (later x) + mˡ  ∎≤

  y-lemma =
    steps (y .force)      ≤⟨ Conat.≤suc ⟩
    steps (later y)       ≤⟨ Conat.m≤m+n ⟩
    steps (later y) + mʳ  ∎≤

-- In some cases quantitative weak bisimilarity is contained in strong
-- bisimilarity.

never≈→∼ :
  ∀ {i mˡ mʳ nˡ nʳ x} →
  [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] never ≈ x → B.[ i ] never ∼ x
never≈→∼ (later  p) = later λ { .force → never≈→∼ (p .force) }
never≈→∼ (laterˡ p) = never≈→∼ p
never≈→∼ (laterʳ p) = later λ { .force → never≈→∼ p }

≈never→∼ :
  ∀ {i mˡ mʳ nˡ nʳ x} →
  [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ never → B.[ i ] x ∼ never
≈never→∼ (later  p) = later λ { .force → ≈never→∼ (p .force) }
≈never→∼ (laterˡ p) = later λ { .force → ≈never→∼ p }
≈never→∼ (laterʳ p) = ≈never→∼ p

≈→∼ : ∀ {i x y} → [ i ∣ zero ∣ zero ] x ≈ y → B.[ i ] x ∼ y
≈→∼ now       = now
≈→∼ (later p) = later λ { .force → ≈→∼ (p .force) }

------------------------------------------------------------------------
-- Reflexivity, symmetry/antisymmetry, transitivity

-- Quantitative weak bisimilarity is reflexive.

reflexive-≈ : ∀ {i mˡ mʳ nˡ nʳ} x → [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ x
reflexive-≈ (now _)   = now
reflexive-≈ (later x) = later λ { .force → reflexive-≈ (x .force) }

-- Quantitative weak bisimilarity is symmetric (in a certain sense).

symmetric-≈ :
  ∀ {i mˡ mʳ nˡ nʳ x y} →
  [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ y →
  [ i ∣ mʳ ∣ mˡ ∣ nʳ ∣ nˡ ] y ≈ x
symmetric-≈ now        = now
symmetric-≈ (later p)  = later λ { .force → symmetric-≈ (p .force) }
symmetric-≈ (laterˡ p) = laterʳ (symmetric-≈ p)
symmetric-≈ (laterʳ p) = laterˡ (symmetric-≈ p)

-- Three variants of transitivity.

transitive-≳∼ :
  ∀ {i m n x y z} →
  [ i ∣ m ∣ n ] x ≳ y → B.[ i ] y ∼ z → [ i ∣ m ∣ n ] x ≳ z
transitive-≳∼ = λ where
  now        now       → now
  (laterˡ p) q         → laterˡ (transitive-≳∼ p q)
  (later  p) (later q) → later λ { .force →
                           transitive-≳∼ (p .force) (q .force) }

transitive-≈∼ :
  ∀ {i mˡ mʳ nˡ nʳ x y z} →
  [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ y → y B.∼ z →
  [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ z
transitive-≈∼ = λ where
  now        now       → now
  (later  p) (later q) → later λ { .force →
                           transitive-≈∼ (p .force) (q .force) }
  (laterˡ p) q         → laterˡ (transitive-≈∼ p q)
  (laterʳ p) (later q) → laterʳ (transitive-≈∼ p (q .force))

transitive-∼≈ :
  ∀ {i mˡ mʳ nˡ nʳ x y z} →
  x B.∼ y → [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] y ≈ z →
  [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ z
transitive-∼≈ = λ where
  now       now        → now
  (later p) (later q)  → later λ { .force →
                           transitive-∼≈ (p .force) (q .force) }
  (later p) (laterˡ q) → laterˡ (transitive-∼≈ (p .force) q)
  p         (laterʳ q) → laterʳ (transitive-∼≈ p q)

-- Equational reasoning combinators.

infix  -1 _∎ˢ
infixr -2 step-∼≈ˢ step-≳∼ˢ step-≈∼ˢ _≳⟨⟩ˢ_ step-≡≈ˢ _∼⟨⟩ˢ_

_∎ˢ : ∀ {i mˡ mʳ nˡ nʳ} x → [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ x
_∎ˢ = reflexive-≈

step-∼≈ˢ : ∀ {i mˡ mʳ nˡ nʳ} x {y z} →
           [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] y ≈ z → x B.∼ y →
           [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ z
step-∼≈ˢ _ y≈z x∼y = transitive-∼≈ x∼y y≈z

syntax step-∼≈ˢ x y≈z x∼y = x ∼⟨ x∼y ⟩ˢ y≈z

step-≳∼ˢ : ∀ {i m n} x {y z} →
           B.[ i ] y ∼ z → [ i ∣ m ∣ n ] x ≳ y →
           [ i ∣ m ∣ n ] x ≳ z
step-≳∼ˢ _ y∼z x≳y = transitive-≳∼ x≳y y∼z

syntax step-≳∼ˢ x y∼z x≳y = x ≳⟨ x≳y ⟩ˢ y∼z

step-≈∼ˢ : ∀ {i mˡ mʳ nˡ nʳ} x {y z} →
           y B.∼ z → [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ y →
           [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ z
step-≈∼ˢ _ y∼z x≈y = transitive-≈∼ x≈y y∼z

syntax step-≈∼ˢ x y∼z x≈y = x ≈⟨ x≈y ⟩ˢ y∼z

_≳⟨⟩ˢ_ : ∀ {i mˡ mʳ nˡ nʳ} x {y} →
         [ i ∣ mˡ ∣ mʳ ∣ nˡ         ∣ nʳ ] drop-later x ≈ y →
         [ i ∣ mˡ ∣ mʳ ∣ ⌜ 1 ⌝ + nˡ ∣ nʳ ] x ≈ y
now _   ≳⟨⟩ˢ p = weakenˡ Conat.≤suc p
later _ ≳⟨⟩ˢ p = laterˡ p

step-≡≈ˢ : ∀ {i mˡ mʳ nˡ nʳ} x {y z} →
           [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] y ≈ z → x ≡ y →
           [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ z
step-≡≈ˢ _ y≈z refl = y≈z

syntax step-≡≈ˢ x y≈z x≡y = x ≡⟨ x≡y ⟩ˢ y≈z

_∼⟨⟩ˢ_ : ∀ {i mˡ mʳ nˡ nʳ} x {y} →
         [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ y →
         [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ y
_ ∼⟨⟩ˢ x≈y = x≈y

------------------------------------------------------------------------
-- Some results related to the steps function

-- If y is a quantitative expansion of x, then it contains at least as
-- many later constructors as x.

steps-mono :
  ∀ {i m n x y} → [ i ∣ m ∣ n ] x ≲ y → [ i ] steps x ≤ steps y
steps-mono = B.steps-mono ∘ ≳→≳

-- If [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ y holds, then the number of later
-- constructors in x is bounded by nˡ plus 1 + mˡ times the number of
-- later constructors in y.

steps-+-*ʳ :
  ∀ {mˡ mʳ nˡ nʳ i x y} →
  [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ y →
  [ i ] steps x ≤ nˡ + (⌜ 1 ⌝ + mˡ) * steps y
steps-+-*ʳ {mˡ} {mʳ} {nˡ} {nʳ} = λ where
  now → zero

  (later {x = x} {y = y} p) →
    steps (later x)                                                 ∼⟨ suc (λ { .force → _ ∎∼ }) ⟩≤
    suc (λ { .force → steps (x .force) })                           ≤⟨ suc (λ { .force → steps-+-*ʳ (p .force) }) ⟩
    suc (λ { .force → nˡ + mˡ + (⌜ 1 ⌝ + mˡ) * steps (y .force) })  ∼⟨ suc (λ { .force → Conat.symmetric-∼ (Conat.+-assoc nˡ) }) ⟩≤
    ⌜ 1 ⌝ + nˡ + (mˡ + (⌜ 1 ⌝ + mˡ) * steps (y .force))             ∼⟨ Conat.suc+∼+suc ⟩≤
    nˡ + ((⌜ 1 ⌝ + mˡ) + (⌜ 1 ⌝ + mˡ) * steps (y .force))           ∼⟨ (nˡ ∎∼) Conat.+-cong Conat.symmetric-∼ Conat.*suc∼+* ⟩≤
    nˡ + (⌜ 1 ⌝ + mˡ) * steps (later y)                             ∎≤

  (laterˡ {x = x} {y = y} {nˡ = nˡ} p) →
    steps (later x)                               ∼⟨ suc (λ { .force → _ ∎∼ }) ⟩≤
    ⌜ 1 ⌝ + steps (x .force)                      ≤⟨ (_ Conat.∎≤) Conat.+-mono steps-+-*ʳ p ⟩
    ⌜ 1 ⌝ + (nˡ .force + (⌜ 1 ⌝ + mˡ) * steps y)  ∼⟨ suc (λ { .force → _ ∎∼ }) ⟩≤
    suc nˡ + (⌜ 1 ⌝ + mˡ) * steps y               ∎≤

  (laterʳ {x = x} {y = y} {nʳ = nʳ} p) →
    steps x                                                ≤⟨ steps-+-*ʳ p ⟩
    nˡ + (⌜ 1 ⌝ + mˡ) * steps (y .force)                   ≤⟨ (nˡ ∎≤) Conat.+-mono Conat.m≤n+m ⟩
    nˡ + ((⌜ 1 ⌝ + mˡ) + (⌜ 1 ⌝ + mˡ) * steps (y .force))  ∼⟨ (nˡ ∎∼) Conat.+-cong Conat.symmetric-∼ Conat.*suc∼+* ⟩≤
    nˡ + (⌜ 1 ⌝ + mˡ) * steps (later y)                    ∎≤

-- If [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ y holds, then the number of later
-- constructors in y is bounded by nʳ plus 1 + mʳ times the number of
-- later constructors in x.

steps-+-*ˡ :
  ∀ {mˡ mʳ nˡ nʳ i x y} →
  [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ y →
  [ i ] steps y ≤ nʳ + (⌜ 1 ⌝ + mʳ) * steps x
steps-+-*ˡ = steps-+-*ʳ ∘ symmetric-≈

-- [ ∞ ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ y holds iff x and y are weakly
-- bisimilar and the number of later constructors in x and y are
-- related in a certain way.

≈⇔≈×steps≤steps² :
  ∀ {mˡ mʳ nˡ nʳ x y} →
  [ ∞ ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ y ⇔
  x B.≈ y ×
  [ ∞ ] steps x ≤ nˡ + (⌜ 1 ⌝ + mˡ) * steps y ×
  [ ∞ ] steps y ≤ nʳ + (⌜ 1 ⌝ + mʳ) * steps x
≈⇔≈×steps≤steps² {mˡ} {mʳ} {x = x} {y} = record
  { to   = λ p → ≈→≈ p , steps-+-*ʳ p , steps-+-*ˡ p
  ; from = λ { (p , q , r) → from p q r }
  }
  where
  from-lemma :
    ∀ {m n} {x y : Delay′ A ∞} {i} {j : Size< i} →
    [ i ] steps (later x) ≤ n + (⌜ 1 ⌝ + m) * steps (later y) →
    [ j ] steps (x .force) ≤ n + m + (⌜ 1 ⌝ + m) * steps (y .force)
  from-lemma {m} {n} {x} {y} hyp = Conat.cancel-suc-≤ lemma .force
    where
    lemma =
      ⌜ 1 ⌝ + steps (x .force)                            ∼⟨ suc (λ { .force → _ ∎∼ }) ⟩≤
      steps (later x)                                     ≤⟨ hyp ⟩
      n + (⌜ 1 ⌝ + m) * steps (later y)                   ∼⟨ (n ∎∼) Conat.+-cong Conat.*suc∼+* ⟩≤
      n + ((⌜ 1 ⌝ + m) + (⌜ 1 ⌝ + m) * steps (y .force))  ∼⟨ Conat.symmetric-∼ Conat.suc+∼+suc ⟩≤
      ⌜ 1 ⌝ + n + (m + (⌜ 1 ⌝ + m) * steps (y .force))    ∼⟨ suc (λ { .force → _ ∎∼ }) ⟩≤
      ⌜ 1 ⌝ + (n + (m + (⌜ 1 ⌝ + m) * steps (y .force)))  ∼⟨ suc (λ { .force → Conat.+-assoc n }) ⟩≤
      ⌜ 1 ⌝ + (n + m + (⌜ 1 ⌝ + m) * steps (y .force))    ∎≤

  from :
    ∀ {nˡ nʳ i x y} →
    B.[ i ] x ≈ y →
    [ ∞ ] steps x ≤ nˡ + (⌜ 1 ⌝ + mˡ) * steps y →
    [ ∞ ] steps y ≤ nʳ + (⌜ 1 ⌝ + mʳ) * steps x →
    [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ y
  from now _ _ = now

  from (later p) q r = later λ { .force →
    from (p .force) (from-lemma q) (from-lemma r) }

  from (laterˡ {y = later _} p) q r = later λ { .force →
    from (B.laterʳ⁻¹ p) (from-lemma q) (from-lemma r) }

  from (laterʳ {x = later _} p) q r = later λ { .force →
    from (B.laterˡ⁻¹ p) (from-lemma q) (from-lemma r) }

  from {nˡ = zero}  (laterˡ {y = now _} p) ()
  from {nˡ = suc _} (laterˡ {y = now _} p) (suc q) _ =
    laterˡ (from p (q .force) zero)

  from {nʳ = zero}  (laterʳ {x = now _} p) _ ()
  from {nʳ = suc _} (laterʳ {x = now _} p) _ (suc r) =
    laterʳ (from p zero (r .force))

-- [ ∞ ∣ m ∣ n ] x ≳ y holds iff x is an expansion of y and the number
-- of later constructors in x and y are related in a certain way.

≳⇔≳×steps≤steps :
  ∀ {m n x y} →
  [ ∞ ∣ m ∣ n ] x ≳ y ⇔
  x B.≳ y × [ ∞ ] steps x ≤ n + (⌜ 1 ⌝ + m) * steps y
≳⇔≳×steps≤steps {m} {n} {x} {y} =
  [ ∞ ∣ m ∣ n ] x ≳ y                                  ↝⟨ ≈⇔≈×steps≤steps² ⟩

  x B.≈ y ×
  [ ∞ ] steps x ≤ n + (⌜ 1 ⌝ + m) * steps y ×
  [ ∞ ] steps y ≤ (⌜ 1 ⌝ + ⌜ 0 ⌝) * steps x            ↝⟨ F.id ×-cong F.id ×-cong (_ ∎∼) Conat.≤-cong-∼ lemma ⟩

  x B.≈ y ×
  [ ∞ ] steps x ≤ n + (⌜ 1 ⌝ + m) * steps y ×
  [ ∞ ] steps y ≤ steps x                              ↝⟨ record { to = B.symmetric; from = B.symmetric } ×-cong from-isomorphism ×-comm ⟩

  y B.≈ x ×
  [ ∞ ] steps y ≤ steps x ×
  [ ∞ ] steps x ≤ n + (⌜ 1 ⌝ + m) * steps y            ↔⟨ ×-assoc ⟩

  (y B.≈ x ×
   [ ∞ ] steps y ≤ steps x) ×
  [ ∞ ] steps x ≤ n + (⌜ 1 ⌝ + m) * steps y            ↝⟨ inverse B.≲⇔≈×steps≤steps ×-cong F.id ⟩□

  x B.≳ y × [ ∞ ] steps x ≤ n + (⌜ 1 ⌝ + m) * steps y  □
  where
  lemma =
    (⌜ 1 ⌝ + ⌜ 0 ⌝) * steps x  ∼⟨ suc (λ { .force → _ ∎∼ }) Conat.*-cong (_ ∎∼) ⟩
    ⌜ 1 ⌝ * steps x            ∼⟨ Conat.*-left-identity _ ⟩
    steps x                    ∎∼

-- [ ∞ ∣ m ∣ n ] x ≳ y holds iff x is weakly bisimilar to y and the
-- number of later constructors in x and y are related in a certain
-- way.

≳⇔≈×steps≤steps² :
  ∀ {m n x y} →
  [ ∞ ∣ m ∣ n ] x ≳ y ⇔
  x B.≈ y ×
  [ ∞ ] steps y ≤ steps x ×
  [ ∞ ] steps x ≤ n + (⌜ 1 ⌝ + m) * steps y
≳⇔≈×steps≤steps² {m} {n} {x} {y} =
  [ ∞ ∣ m ∣ n ] x ≳ y                        ↝⟨ ≳⇔≳×steps≤steps ⟩

  x B.≳ y ×
  [ ∞ ] steps x ≤ n + (⌜ 1 ⌝ + m) * steps y  ↝⟨ B.≲⇔≈×steps≤steps ×-cong F.id ⟩

  (y B.≈ x ×
   [ ∞ ] steps y ≤ steps x) ×
  [ ∞ ] steps x ≤ n + (⌜ 1 ⌝ + m) * steps y  ↔⟨ inverse ×-assoc ⟩

  y B.≈ x ×
  [ ∞ ] steps y ≤ steps x ×
  [ ∞ ] steps x ≤ n + (⌜ 1 ⌝ + m) * steps y  ↝⟨ record { to = B.symmetric; from = B.symmetric } ×-cong F.id ⟩□

  x B.≈ y ×
  [ ∞ ] steps y ≤ steps x ×
  [ ∞ ] steps x ≤ n + (⌜ 1 ⌝ + m) * steps y  □

-- The left-to-right direction of ≳⇔≳×steps≤steps can be made
-- size-preserving.

≳→≳×steps≤steps :
  ∀ {i m n x y} →
  [ i ∣ m ∣ n ] x ≳ y →
  B.[ i ] x ≳ y × [ i ] steps x ≤ n + (⌜ 1 ⌝ + m) * steps y
≳→≳×steps≤steps x≳y = ≳→≳ x≳y , steps-+-*ʳ x≳y

-- The right-to-left direction of ≳⇔≳×steps≤steps can be made
-- size-preserving iff A is uninhabited.

≳×steps≤steps→≳⇔uninhabited :
  (∀ {i m n x y} →
   B.[ i ] x ≳ y ×
   [ i ] steps x ≤ n + (⌜ 1 ⌝ + m) * steps y →
   [ i ∣ m ∣ n ] x ≳ y)
    ⇔
  ¬ A
≳×steps≤steps→≳⇔uninhabited = record
  { to   = flip to
  ; from =
    ¬ A                                           ↝⟨ (λ ¬A {_ _ _ _ _} → ∼→≈ (B.uninhabited→trivial ¬A _ _)) ⟩

    (∀ {i m n x y} → [ i ∣ m ∣ n ] x ≳ y)         ↝⟨ (λ hyp {_ _ _ _ _} _ → hyp {_}) ⟩□

    (∀ {i m n x y} →
     B.[ i ] x ≳ y ×
     [ i ] steps x ≤ n + (⌜ 1 ⌝ + m) * steps y →
     [ i ∣ m ∣ n ] x ≳ y)                         □
  }
  where
  strengthen-≳now :
    ∀ {i m n x y} →
    [ i ∣ m ∣ n ] x ≳ now y →
    [ ∞ ∣ m ∣ n ] x ≳ now y
  strengthen-≳now now        = now
  strengthen-≳now (laterˡ p) = laterˡ (strengthen-≳now p)

  to :
    A →
    ¬ (∀ {i m n x y} →
       B.[ i ] x ≳ y ×
       [ i ] steps x ≤ n + (⌜ 1 ⌝ + m) * steps y →
       [ i ∣ m ∣ n ] x ≳ y)
  to x =
    (∀ {i m n x y} →
     B.[ i ] x ≳ y ×
     [ i ] steps x ≤ n + (⌜ 1 ⌝ + m) * steps y →
     [ i ∣ m ∣ n ] x ≳ y)                                         ↝⟨ (λ hyp → curry hyp) ⟩

    (∀ {i m n} →
     B.[ i ] f m ≳ now x →
     [ i ] steps (f m) ≤ n + zero →
     [ i ∣ zero ∣ n ] f m ≳ now x)                                ↝⟨ (λ hyp {_ _ _} p → hyp (≳now _) (complicate p)) ⟩

    (∀ {i m n} → [ i ] ⌜ m ⌝ ≤ n → [ i ∣ zero ∣ n ] f m ≳ now x)  ↝⟨ strengthen-≳now ∘_ ⟩

    (∀ {i m n} → [ i ] ⌜ m ⌝ ≤ n → [ ∞ ∣ zero ∣ n ] f m ≳ now x)  ↝⟨ (λ hyp {_ _ _} p → steps-+-*ʳ (hyp p)) ⟩

    (∀ {i m n} → [ i ] ⌜ m ⌝ ≤ n → [ ∞ ] steps (f m) ≤ n + zero)  ↝⟨ (λ hyp {_ _ _} p → simplify (hyp p)) ⟩

    (∀ {i m n} → [ i ] ⌜ m ⌝ ≤ n → [ ∞ ] ⌜ m ⌝ ≤ n)               ↝⟨ (λ hyp → hyp) ⟩

    (∀ {i} → [ i ] ⌜ 2 ⌝ ≤ ⌜ 1 ⌝ → [ ∞ ] ⌜ 2 ⌝ ≤ ⌜ 1 ⌝)           ↝⟨ Conat.no-strengthening-≤-21 ⟩□

    ⊥                                                             □
    where
    f : ∀ {i} → ℕ → Delay A i
    f zero    = now x
    f (suc n) = later λ { .force → f n }

    ≳now : ∀ {i} n → B.[ i ] f n ≳ now x
    ≳now zero    = now
    ≳now (suc n) = laterˡ (≳now n)

    ∼steps : ∀ {i} n → Conat.[ i ] ⌜ n ⌝ ∼ steps (f n)
    ∼steps zero    = zero
    ∼steps (suc n) = suc λ { .force → ∼steps n }

    complicate :
      ∀ {m n i} → [ i ] ⌜ m ⌝ ≤ n → [ i ] steps (f m) ≤ n + zero
    complicate {m} {n} p =
      steps (f m) ∼⟨ Conat.symmetric-∼ (∼steps m) ⟩≤
      ⌜ m ⌝       ≤⟨ p ⟩
      n           ∼⟨ Conat.symmetric-∼ (Conat.+-right-identity _) ⟩≤
      n + zero    ∎≤

    simplify :
      ∀ {m n i} → [ i ] steps (f m) ≤ n + zero → [ i ] ⌜ m ⌝ ≤ n
    simplify {m} {n} p =
      ⌜ m ⌝        ∼⟨ ∼steps m ⟩≤
      steps (f m)  ≤⟨ p ⟩
      n + zero     ∼⟨ Conat.+-right-identity _ ⟩≤
      n            ∎≤

-- The left-to-right direction of ≈⇔≈×steps≤steps² can be made
-- size-preserving.

≈→≈×steps≤steps² :
  ∀ {i mˡ mʳ nˡ nʳ x y} →
  [ ∞ ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ y →
  B.[ i ] x ≈ y ×
  [ i ] steps x ≤ nˡ + (⌜ 1 ⌝ + mˡ) * steps y ×
  [ i ] steps y ≤ nʳ + (⌜ 1 ⌝ + mʳ) * steps x
≈→≈×steps≤steps² x≈y = ≈→≈ x≈y , steps-+-*ʳ x≈y , steps-+-*ˡ x≈y

-- The right-to-left direction of ≈⇔≈×steps≤steps² can be made
-- size-preserving iff A is uninhabited.

≈×steps≤steps²→≈⇔uninhabited :
  (∀ {i mˡ mʳ nˡ nʳ x y} →
   B.[ i ] x ≈ y ×
   [ i ] steps x ≤ nˡ + (⌜ 1 ⌝ + mˡ) * steps y ×
   [ i ] steps y ≤ nʳ + (⌜ 1 ⌝ + mʳ) * steps x →
   [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ y)
    ⇔
  ¬ A
≈×steps≤steps²→≈⇔uninhabited = record
  { to =
    (∀ {i mˡ mʳ nˡ nʳ x y} →
     B.[ i ] x ≈ y ×
     [ i ] steps x ≤ nˡ + (⌜ 1 ⌝ + mˡ) * steps y ×
     [ i ] steps y ≤ nʳ + (⌜ 1 ⌝ + mʳ) * steps x →
     [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ y)               ↝⟨ (λ { hyp (p , q) → hyp (B.≳→ p , q , lemma (B.steps-mono p)) }) ⟩

    (∀ {i m n x y} →
     B.[ i ] x ≳ y ×
     [ i ] steps x ≤ n + (⌜ 1 ⌝ + m) * steps y →
     [ i ∣ m ∣ n ] x ≳ y)                           ↝⟨ _⇔_.to ≳×steps≤steps→≳⇔uninhabited ⟩□

    ¬ A                                             □
  ; from =
    ¬ A                                                        ↝⟨ (λ ¬A {_ _ _ _ _} → ∼→≈ (B.uninhabited→trivial ¬A _ _)) ⟩

    (∀ {i mˡ mʳ nˡ nʳ x y} → [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ y)  ↝⟨ (λ hyp {_ _ _ _ _ _ _} _ → hyp {_}) ⟩□

    (∀ {i mˡ mʳ nˡ nʳ x y} →
     B.[ i ] x ≈ y ×
     [ i ] steps x ≤ nˡ + (⌜ 1 ⌝ + mˡ) * steps y ×
     [ i ] steps y ≤ nʳ + (⌜ 1 ⌝ + mʳ) * steps x →
     [ i ∣ mˡ ∣ mʳ ∣ nˡ ∣ nʳ ] x ≈ y)                          □
  }
  where
  lemma :
    ∀ {m n i} →
    [ i ] m ≤ n →
    [ i ] m ≤ (⌜ 1 ⌝ + ⌜ 0 ⌝) * n
  lemma {m} {n} p =
    m                    ≤⟨ p ⟩
    n                    ∼⟨ Conat.symmetric-∼ (Conat.*-left-identity _) ⟩≤
    ⌜ 1 ⌝ * n            ∼⟨ Conat.symmetric-∼ (Conat.+-right-identity _) Conat.*-cong (_ ∎∼) ⟩≤
    (⌜ 1 ⌝ + ⌜ 0 ⌝) * n  ∎≤
