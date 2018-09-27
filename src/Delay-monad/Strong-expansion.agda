------------------------------------------------------------------------
-- A variant of expansion that can be used to state that one
-- computation is at most a certain positive factor "slower" than
-- another
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Delay-monad.Strong-expansion {a} {A : Set a} where

open import Conat
  using (Conat; zero; suc; force; ⌜_⌝; _+_; _*_;
         [_]_≤_; step-≤; step-∼≤; _∎≤; step-∼; _∎∼)
open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (_+_; _*_)

open import Function-universe equality-with-J as F hiding (id; _∘_)

open import Delay-monad
open import Delay-monad.Bisimilarity as B
  using (now; later; laterˡ; force)

------------------------------------------------------------------------
-- The relation

mutual

  -- Strong expansion. [ ∞ ∣ m ∣ n ] x ≳ y is a variant of x B.≳ y for
  -- which the number of later constructors in x is bounded by n plus
  -- 1 + m times the number of later constructors in y (see
  -- ≲⇔≲×steps≤steps below).

  infix 4 [_∣_∣_]_≳_ [_∣_∣_]_≳′_

  data [_∣_∣_]_≳_ (i : Size) (m : Conat ∞) :
                  Conat ∞ → Delay A ∞ → Delay A ∞ → Set a where
    now    : ∀ {x n} → [ i ∣ m ∣ n ] now x ≳ now x
    later  : ∀ {x y n} →
             [ i ∣ m ∣ n + m ] x .force ≳′ y .force →
             [ i ∣ m ∣ n ]     later x  ≳  later y
    laterˡ : ∀ {x y n} →
             [ i ∣ m ∣ n .force ] x .force ≳ y →
             [ i ∣ m ∣ suc n    ] later x  ≳ y

  record [_∣_∣_]_≳′_ (i : Size) (m n : Conat ∞)
                     (x : Delay A ∞) (y : Delay A ∞) : Set a where
    coinductive
    field
      force : {j : Size< i} → [ j ∣ m ∣ n ] x ≳ y

open [_∣_∣_]_≳′_ public

-- Specialised variants of [_∣_∣_]_≳_ and [_∣_∣_]_≳′_.

infix 4 [_∣_]_≳_ [_∣_]_≳′_

[_∣_]_≳_ : Size → Conat ∞ → Delay A ∞ → Delay A ∞ → Set a
[ i ∣ m ] x ≳ y = [ i ∣ m ∣ zero ] x ≳ y

[_∣_]_≳′_ : Size → Conat ∞ → Delay A ∞ → Delay A ∞ → Set a
[ i ∣ m ] x ≳′ y = [ i ∣ m ∣ zero ] x ≳′ y

-- The converse of strong expansion.

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

weaken₂ :
  ∀ {i m m′ n n′ x y} →
  [ ∞ ] m ≤ m′ → [ ∞ ] n ≤ n′ →
  [ i ∣ m ∣ n ] x ≳ y → [ i ∣ m′ ∣ n′ ] x ≳ y
weaken₂ m≤m′ n≤n′ now       = now
weaken₂ m≤m′ n≤n′ (later p) = later λ { .force →
  weaken₂ m≤m′ (n≤n′ Conat.+-mono m≤m′) (p .force) }
weaken₂ m≤m′ (suc n≤n′) (laterˡ p) =
  laterˡ (weaken₂ m≤m′ (n≤n′ .force) p)

weaken :
  ∀ {i m n n′ x y} →
  [ ∞ ] n ≤ n′ →
  [ i ∣ m ∣ n ] x ≳ y → [ i ∣ m ∣ n′ ] x ≳ y
weaken = weaken₂ (_ ∎≤)

-- Strong bisimilarity is contained in strong expansion.

∼→≳ : ∀ {i m n x y} → B.[ i ] x ∼ y → [ i ∣ m ∣ n ] x ≳ y
∼→≳ now       = now
∼→≳ (later p) = later λ { .force → ∼→≳ (p .force) }

-- Strong expansion is contained in expansion.

≳→≳ : ∀ {i m n x y} → [ i ∣ m ∣ n ] x ≳ y → B.[ i ] x ≳ y
≳→≳ now        = now
≳→≳ (later p)  = later λ { .force → ≳→≳ (p .force) }
≳→≳ (laterˡ p) = laterˡ (≳→≳ p)

-- In some cases expansion is contained in strong expansion.

≳→≳-steps :
  ∀ {i m x y} → B.[ i ] x ≳ y → [ i ∣ m ∣ steps x ] x ≳ y
≳→≳-steps         now               = now
≳→≳-steps         (laterˡ p)        = laterˡ (≳→≳-steps p)
≳→≳-steps {m = m} (later {x = x} p) = later λ { .force →
  weaken lemma (≳→≳-steps (p .force)) }
  where
  lemma =
    steps (x .force)     ≤⟨ Conat.≤suc ⟩
    steps (later x)      ≤⟨ Conat.m≤m+n ⟩
    steps (later x) + m  ∎≤

-- In some cases strong expansion is contained in strong bisimilarity.

never≳→∼ : ∀ {i m n x} → [ i ∣ m ∣ n ] never ≳ x → B.[ i ] never ∼ x
never≳→∼ (later  p) = later λ { .force → never≳→∼ (p .force) }
never≳→∼ (laterˡ p) = never≳→∼ p

≳never→∼ : ∀ {i m n x} → [ i ∣ m ∣ n ] x ≳ never → B.[ i ] x ∼ never
≳never→∼ (later  p) = later λ { .force → ≳never→∼ (p .force) }
≳never→∼ (laterˡ p) = later λ { .force → ≳never→∼ p }

≳→∼ : ∀ {i x y} → [ i ∣ zero ∣ zero ] x ≳ y → B.[ i ] x ∼ y
≳→∼ now       = now
≳→∼ (later p) = later λ { .force → ≳→∼ (p .force) }

------------------------------------------------------------------------
-- Reflexivity, symmetry/antisymmetry, transitivity

-- Strong expansion is reflexive.

reflexive-≳ : ∀ {i m n} x → [ i ∣ m ∣ n ] x ≳ x
reflexive-≳ (now _)   = now
reflexive-≳ (later x) = later λ { .force → reflexive-≳ (force x) }

-- Some special cases of symmetry hold for strong expansion.

symmetric-≳-neverˡ :
  ∀ {i m n x} → [ i ∣ m ∣ n ] never ≳ x → [ i ∣ m ∣ n ] x ≳ never
symmetric-≳-neverˡ = ∼→≳ ∘ B.symmetric ∘ never≳→∼

symmetric-≳-neverʳ :
  ∀ {i m n x} → [ i ∣ m ∣ n ] x ≳ never → [ i ∣ m ∣ n ] never ≳ x
symmetric-≳-neverʳ = ∼→≳ ∘ B.symmetric ∘ ≳never→∼

-- Two variants of transitivity.

transitive-≳∼ :
  ∀ {i m n x y z} →
  [ i ∣ m ∣ n ] x ≳ y → B.[ i ] y ∼ z → [ i ∣ m ∣ n ] x ≳ z
transitive-≳∼ = λ where
  now        now       → now
  (laterˡ p) q         → laterˡ (transitive-≳∼ p q)
  (later  p) (later q) → later λ { .force →
                           transitive-≳∼ (p .force) (q .force) }

transitive-∼≳ :
  ∀ {i m n x y z} →
  x B.∼ y → [ i ∣ m ∣ n ] y ≳ z → [ i ∣ m ∣ n ] x ≳ z
transitive-∼≳ = λ where
  now       now        → now
  (later p) (later q)  → later λ { .force →
                           transitive-∼≳ (p .force) (q .force) }
  (later p) (laterˡ q) → laterˡ (transitive-∼≳ (p .force) q)

-- Equational reasoning combinators.

infix  -1 _∎≳
infixr -2 step-∼≳ step-≳∼≳ _≳⟨⟩≳_ step-≡≳ _∼⟨⟩≳_

_∎≳ : ∀ {i m n} x → [ i ∣ m ∣ n ] x ≳ x
_∎≳ = reflexive-≳

step-∼≳ : ∀ {i m n} x {y z} →
          [ i ∣ m ∣ n ] y ≳ z → x B.∼ y → [ i ∣ m ∣ n ] x ≳ z
step-∼≳ _ y≳z x∼y = transitive-∼≳ x∼y y≳z

syntax step-∼≳ x y≳z x∼y = x ∼⟨ x∼y ⟩≳ y≳z

step-≳∼≳ : ∀ {i m n} x {y z} →
           B.[ i ] y ∼ z → [ i ∣ m ∣ n ] x ≳ y → [ i ∣ m ∣ n ] x ≳ z
step-≳∼≳ _ y∼z x≳y = transitive-≳∼ x≳y y∼z

syntax step-≳∼≳ x y∼z x≳y = x ≳⟨ x≳y ⟩∼≳ y∼z

_≳⟨⟩≳_ : ∀ {i m n} x {y} →
         [ i ∣ m ∣ n ] drop-later x ≳ y → [ i ∣ m ∣ ⌜ 1 ⌝ + n ] x ≳ y
now _   ≳⟨⟩≳ p = weaken Conat.≤suc p
later _ ≳⟨⟩≳ p = laterˡ p

step-≡≳ : ∀ {i m n} x {y z} →
          [ i ∣ m ∣ n ] y ≳ z → x ≡ y → [ i ∣ m ∣ n ] x ≳ z
step-≡≳ _ y≳z refl = y≳z

syntax step-≡≳ x y≳z x≡y = x ≡⟨ x≡y ⟩≳ y≳z

_∼⟨⟩≳_ : ∀ {i m n} x {y} →
         [ i ∣ m ∣ n ] x ≳ y → [ i ∣ m ∣ n ] x ≳ y
_ ∼⟨⟩≳ x≳y = x≳y

------------------------------------------------------------------------
-- Some results related to the steps function

-- If y is an expansion of x, then it contains at least as many later
-- constructors as x.

steps-mono :
  ∀ {i m n x y} → [ i ∣ m ∣ n ] x ≲ y → [ i ] steps x ≤ steps y
steps-mono = B.steps-mono ∘ ≳→≳

-- If [ i ∣ m ∣ n ] x ≲ y holds, then the number of later constructors
-- in y is bounded by n plus 1 + m times the number of later
-- constructors in x.

steps-antitone-+-* :
  ∀ {m n i x y} →
  [ i ∣ m ∣ n ] x ≲ y →
  [ i ] steps y ≤ n + (⌜ 1 ⌝ + m) * steps x
steps-antitone-+-* now                               = zero
steps-antitone-+-* {m} {n} (later {x = y} {y = x} p) =
  steps (later y)                                              ∼⟨ suc (λ { .force → _ ∎∼ }) ⟩≤
  suc (λ { .force → steps (y .force) })                        ≤⟨ suc (λ { .force → steps-antitone-+-* (p .force) }) ⟩
  suc (λ { .force → n + m + (⌜ 1 ⌝ + m) * steps (x .force) })  ∼⟨ suc (λ { .force → Conat.symmetric-∼ (Conat.+-assoc n) }) ⟩≤
  ⌜ 1 ⌝ + n + (m + (⌜ 1 ⌝ + m) * steps (x .force))             ∼⟨ Conat.suc+∼+suc ⟩≤
  n + ((⌜ 1 ⌝ + m) + (⌜ 1 ⌝ + m) * steps (x .force))           ∼⟨ (n ∎∼) Conat.+-cong Conat.symmetric-∼ Conat.*suc∼+* ⟩≤
  n + (⌜ 1 ⌝ + m) * steps (later x)                            ∎≤
steps-antitone-+-* {m} (laterˡ {x = y} {y = x} {n = n} p) =
  steps (later y)                             ∼⟨ suc (λ { .force → _ ∎∼ }) ⟩≤
  ⌜ 1 ⌝ + steps (y .force)                    ≤⟨ (_ Conat.∎≤) Conat.+-mono steps-antitone-+-* p ⟩
  ⌜ 1 ⌝ + (n .force + (⌜ 1 ⌝ + m) * steps x)  ∼⟨ suc (λ { .force → _ ∎∼ }) ⟩≤
  suc n + (⌜ 1 ⌝ + m) * steps x               ∎≤

-- If [ i ∣ m ] x ≲ y holds, then the number of later constructors
-- in y is bounded by 1 + m times the number of later constructors
-- in x.

steps-antitone-* :
  ∀ {i m x y} →
  [ i ∣ m ] x ≲ y → [ i ] steps y ≤ (⌜ 1 ⌝ + m) * steps x
steps-antitone-* = steps-antitone-+-*

-- [ ∞ ∣ m ∣ n ] x ≲ y holds iff y is an expansion of x and the number
-- of later constructors in y is bounded by n plus 1 + m times the
-- number of later constructors in x.

≲⇔≲×steps≤steps :
  ∀ {m n x y} →
  [ ∞ ∣ m ∣ n ] x ≲ y ⇔
  x B.≲ y × [ ∞ ] steps y ≤ n + (⌜ 1 ⌝ + m) * steps x
≲⇔≲×steps≤steps {x = x} {y} = record
  { to   = λ p → ≳→≳ p , steps-antitone-+-* p
  ; from = uncurry from ∘ Σ-map id (from-lemma₂ x y)
  }
  where
  from-lemma₁ :
    ∀ {m n} {x y : Delay′ A ∞} {i} {j : Size< i} →
    [ i ] steps (later y) ≤ (⌜ 1 ⌝ + m) * steps (later x) + n →
    [ j ] steps (y .force) ≤ (⌜ 1 ⌝ + m) * steps (x .force) + (n + m)
  from-lemma₁ {m} {n} {x} {y} hyp = Conat.cancel-suc-≤ lemma₂ .force
    where
    lemma₁ =
      m + (⌜ 1 ⌝ + m) * steps (x .force) + n    ∼⟨ Conat.+-comm m Conat.+-cong (_ ∎∼) ⟩
      (⌜ 1 ⌝ + m) * steps (x .force) + m + n    ∼⟨ Conat.symmetric-∼ (Conat.+-assoc ((⌜ 1 ⌝ + _) * steps (x .force))) ⟩
      (⌜ 1 ⌝ + m) * steps (x .force) + (m + n)  ∼⟨ ((⌜ 1 ⌝ + _) * steps (x .force) ∎∼) Conat.+-cong Conat.+-comm m ⟩
      (⌜ 1 ⌝ + m) * steps (x .force) + (n + m)  ∎∼

    lemma₂ =
      ⌜ 1 ⌝ + steps (y .force)                            ∼⟨ suc (λ { .force → _ ∎∼ }) ⟩≤
      steps (later y)                                     ≤⟨ hyp ⟩
      (⌜ 1 ⌝ + m) * steps (later x) + n                   ∼⟨ Conat.*suc∼+* Conat.+-cong (n ∎∼) ⟩≤
      ⌜ 1 ⌝ + m + (⌜ 1 ⌝ + m) * steps (x .force) + n      ∼⟨ suc (λ { .force → _ ∎∼ }) ⟩≤
      ⌜ 1 ⌝ + (m + (⌜ 1 ⌝ + m) * steps (x .force) + n)    ∼⟨ suc (λ { .force → lemma₁ }) ⟩≤
      ⌜ 1 ⌝ + ((⌜ 1 ⌝ + m) * steps (x .force) + (n + m))  ∼⟨ suc (λ { .force → _ ∎∼ }) ⟩≤
      ⌜ 1 ⌝ + (⌜ 1 ⌝ + m) * steps (x .force) + (n + m)    ∎≤

  from-lemma₂ :
    ∀ {m n} (x y : Delay A ∞) {i} →
    [ i ] steps y ≤ n + (⌜ 1 ⌝ + m) * steps x →
    [ i ] steps y ≤ (⌜ 1 ⌝ + m) * steps x + n
  from-lemma₂ {m} {n} x y hyp =
    steps y                    ≤⟨ hyp ⟩
    n + (⌜ 1 ⌝ + m) * steps x  ∼⟨ Conat.+-comm n ⟩≤
    (⌜ 1 ⌝ + m) * steps x + n  ∎≤

  from :
    ∀ {x y m n i} →
    B.[ i ] x ≲ y →
    [ ∞ ] steps y ≤ (⌜ 1 ⌝ + m) * steps x + n →
    [ i ∣ m ∣ n ] x ≲ y
  from now                      _       = now
  from (later p)                q       = later λ { .force →
                                            from (p .force)
                                                 (from-lemma₁ q) }
  from (laterˡ {y = now _}   p) (suc q) = laterˡ (from p (q .force))
  from (laterˡ {y = later _} p) q       =
    later λ { .force → from (B.laterʳ⁻¹ p) (from-lemma₁ q) }

-- [ ∞ ∣ m ∣ n ] x ≲ y holds iff x and y are weakly bisimilar and the
-- number of later constructors in y is bounded from below by the
-- number of later constructors in x and bounded from above by n plus
-- 1 + m times the number of later constructors in x.

≲⇔≈×steps≤steps² :
  ∀ {m n x y} →
  [ ∞ ∣ m ∣ n ] x ≲ y ⇔
  x B.≈ y ×
  [ ∞ ] steps x ≤ steps y ×
  [ ∞ ] steps y ≤ n + (⌜ 1 ⌝ + m) * steps x
≲⇔≈×steps≤steps² {m} {n} {x} {y} =
  [ ∞ ∣ m ∣ n ] x ≲ y                                        ↝⟨ ≲⇔≲×steps≤steps ⟩

  B.[ ∞ ] x ≲ y × [ ∞ ] steps y ≤ n + (⌜ 1 ⌝ + m) * steps x  ↝⟨ B.≲⇔≈×steps≤steps ×-cong F.id ⟩

  (B.[ ∞ ] x ≈ y × [ ∞ ] steps x ≤ steps y) ×
  [ ∞ ] steps y ≤ n + (⌜ 1 ⌝ + m) * steps x                  ↔⟨ inverse ×-assoc ⟩□

  B.[ ∞ ] x ≈ y ×
  [ ∞ ] steps x ≤ steps y ×
  [ ∞ ] steps y ≤ n + (⌜ 1 ⌝ + m) * steps x                  □
