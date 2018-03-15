------------------------------------------------------------------------
-- Some negative results related to weak bisimilarity and expansion
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Prelude

module Delay-monad.Sized.Bisimilarity.Negative
  {a} {A : Size → Set a} where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)

open import Function-universe equality-with-J hiding (id; _∘_)

open import Delay-monad.Sized
open import Delay-monad.Sized.Bisimilarity
open import Delay-monad.Sized.Termination

------------------------------------------------------------------------
-- Lemmas stating that functions of certain types cannot be defined if
-- ∀ i → A i is inhabited

-- If a special case of a variant of laterˡ⁻¹ for (fully defined)
-- expansion can be defined, then ∀ i → A i is uninhabited.

Laterˡ⁻¹-≳′ = (x : ∀ i → A i) →
              later (record { force = λ {j} → now (x j) }) ≳
              later (record { force = λ {j} → now (x j) }) →
              now (x ∞) ≳ later (record { force = λ {j} → now (x j) })

laterˡ⁻¹-≳′→uninhabited : Laterˡ⁻¹-≳′ → ¬ (∀ i → A i)
laterˡ⁻¹-≳′→uninhabited =
  Laterˡ⁻¹-≳′                          ↔⟨⟩
  (∀ x → y x ≳ y x → now (x ∞) ≳ y x)  ↝⟨ (λ hyp x → hyp x (reflexive _)) ⟩
  (∀ x → now (x ∞) ≳ y x)              ↝⟨ (λ hyp x → now-x≵y x (hyp x)) ⟩□
  ¬ (∀ i → A i)                        □
  where
  module _ (x : ∀ i → A i) where

    y : Delay A ∞
    y = later (record { force = λ {j} → now (x j) })

    now-x≵y : ¬ now (x ∞) ≳ y
    now-x≵y ()

-- If a variant of laterˡ⁻¹ for (fully defined) expansion can be
-- defined, then ∀ i → A i is uninhabited.

Laterˡ⁻¹-≳ = ∀ {x} {y : Delay A ∞} → later x ≳ y → force x ≳ y

laterˡ⁻¹-≳→uninhabited : Laterˡ⁻¹-≳ → ¬ (∀ i → A i)
laterˡ⁻¹-≳→uninhabited =
  Laterˡ⁻¹-≳     ↝⟨ (λ hyp _ → hyp) ⟩
  Laterˡ⁻¹-≳′    ↝⟨ laterˡ⁻¹-≳′→uninhabited ⟩□
  ¬ (∀ i → A i)  □

-- If the following variants of transitivity can be proved, then
-- ∀ i → A i is uninhabited.

Transitivity-≈≳≳ = {x y z : Delay A ∞} → x ≈ y → y ≳ z → x ≳ z
Transitivity-≳≈≳ = {x y z : Delay A ∞} → x ≳ y → y ≈ z → x ≳ z

transitive-≈≳≳→uninhabited : Transitivity-≈≳≳ → ¬ (∀ i → A i)
transitive-≈≳≳→uninhabited =
  Transitivity-≈≳≳  ↝⟨ (λ trans → trans (laterʳ (reflexive _))) ⟩
  Laterˡ⁻¹-≳        ↝⟨ laterˡ⁻¹-≳→uninhabited ⟩□
  ¬ (∀ i → A i)     □

transitive-≳≈≳→uninhabited : Transitivity-≳≈≳ → ¬ (∀ i → A i)
transitive-≳≈≳→uninhabited =
  Transitivity-≳≈≳                                 ↝⟨ (λ trans x ln≳ln → later⁻¹ {y = λ { .force → y x }}
                                                                                 (trans ln≳ln (laterʳ (reflexive _)))) ⟩
  ((x : ∀ i → A i) → y x ≳ y x → now (x ∞) ≳ y x)  ↝⟨ (λ hyp x _ → case hyp x (reflexive _) of λ ()) ⟩
  Laterˡ⁻¹-≳′                                      ↝⟨ laterˡ⁻¹-≳′→uninhabited ⟩□
  ¬ (∀ i → A i)                                    □
  where
  y : (x : ∀ i → A i) → ∀ {i} → Delay A i
  y x = later (λ { .force {j} → now (x j) })

------------------------------------------------------------------------
-- Lemmas stating that certain size-preserving functions cannot be
-- defined if ∀ i → A i is inhabited, and related results

-- If a variant of laterˡ⁻¹ in which one occurrence of weak
-- bisimilarity is replaced by strong bisimilarity, and both arguments
-- are specialised, can be made size-preserving, then ∀ i → A i is
-- uninhabited.
--
-- This lemma is used to prove all other similar results below
-- (directly or indirectly).

Laterˡ⁻¹-∼≈ = ∀ {i} (x : ∀ i → A i) →
              [ i ] later (λ { .force {j = j} → now (x j) }) ∼ never →
              [ i ] now {A = A} (x ∞)                        ≈ never

size-preserving-laterˡ⁻¹-∼≈→uninhabited :
  Laterˡ⁻¹-∼≈ → ¬ (∀ i → A i)
size-preserving-laterˡ⁻¹-∼≈→uninhabited laterˡ⁻¹-∼≈ x =
  contradiction ∞
  where

  mutual

    now≈never : ∀ {i} → [ i ] now (x ∞) ≈ never
    now≈never = laterˡ⁻¹-∼≈ x (later now∼never)

    now∼never : ∀ {i} → [ i ] now (x ∞) ∼′ never
    force now∼never {j = j} = ⊥-elim (contradiction j)

    contradiction : Size → ⊥
    contradiction i = now≉never (now≈never {i = i})

-- A logically equivalent variant of Laterˡ⁻¹-∼≈ which it is sometimes
-- easier to work with.

Laterˡ⁻¹-∼≈′ = ∀ {i} (x : ∀ i → A i) →
               [ i ] later (record { force = λ {j} → now (x j) }) ∼ never →
               [ i ] now {A = A} (x ∞)                            ≈ never

size-preserving-laterˡ⁻¹-∼≈⇔size-preserving-laterˡ⁻¹-∼≈′ :
  Laterˡ⁻¹-∼≈ ⇔ Laterˡ⁻¹-∼≈′
size-preserving-laterˡ⁻¹-∼≈⇔size-preserving-laterˡ⁻¹-∼≈′ = record
  { to   = λ laterˡ⁻¹ x → laterˡ⁻¹ x ∘ transitive-∼ˡ (later λ { .force → now })
  ; from = λ laterˡ⁻¹ x → laterˡ⁻¹ x ∘ transitive-∼ˡ (later λ { .force → now })
  }

-- The type Laterˡ⁻¹-∼≈′ is logically equivalent to the similar type
-- Laterʳ⁻¹-∼≈′.

Laterʳ⁻¹-∼≈′ = ∀ {i} (x : ∀ i → A i) →
               [ i ] never ∼ later (record { force = λ {j} → now (x j) }) →
               [ i ] never ≈ now {A = A} (x ∞)

size-preserving-laterˡ⁻¹-∼≈′⇔size-preserving-laterʳ⁻¹-∼≈′ :
  Laterˡ⁻¹-∼≈′ ⇔ Laterʳ⁻¹-∼≈′
size-preserving-laterˡ⁻¹-∼≈′⇔size-preserving-laterʳ⁻¹-∼≈′ =
  Laterˡ⁻¹-∼≈′  ↝⟨ record { to   = λ laterˡ⁻¹ {_} _ → symmetric ∘ laterˡ⁻¹ _ ∘ symmetric
                          ; from = λ laterʳ⁻¹ {_} _ → symmetric ∘ laterʳ⁻¹ _ ∘ symmetric
                          } ⟩□
  Laterʳ⁻¹-∼≈′  □

-- The type Laterʳ⁻¹-∼≈′ is logically equivalent to the similar type
-- Laterʳ⁻¹-∼≳′.

Laterʳ⁻¹-∼≳′ = ∀ {i} (x : ∀ i → A i) →
               [ i ] never ∼ later (record { force = λ {j} → now (x j) }) →
               [ i ] never ≳ now {A = A} (x ∞)

size-preserving-laterʳ⁻¹-∼≈′⇔size-preserving-laterʳ⁻¹-∼≳′ :
  Laterʳ⁻¹-∼≈′ ⇔ Laterʳ⁻¹-∼≳′
size-preserving-laterʳ⁻¹-∼≈′⇔size-preserving-laterʳ⁻¹-∼≳′ =
  Laterʳ⁻¹-∼≈′  ↝⟨ record { to   = λ laterʳ⁻¹ {_} _ → ≈→-now ∘ laterʳ⁻¹ _
                          ; from = λ laterʳ⁻¹ {_} _ → ≳→     ∘ laterʳ⁻¹ _
                          } ⟩□
  Laterʳ⁻¹-∼≳′  □

-- If Laterʳ⁻¹-∼≳′ is inhabited, then ∀ i → A i is uninhabited.

size-preserving-laterʳ⁻¹-∼≳′→uninhabited : Laterʳ⁻¹-∼≳′ → ¬ (∀ i → A i)
size-preserving-laterʳ⁻¹-∼≳′→uninhabited =
  Laterʳ⁻¹-∼≳′   ↝⟨ _⇔_.from size-preserving-laterʳ⁻¹-∼≈′⇔size-preserving-laterʳ⁻¹-∼≳′ ⟩
  Laterʳ⁻¹-∼≈′   ↝⟨ _⇔_.from size-preserving-laterˡ⁻¹-∼≈′⇔size-preserving-laterʳ⁻¹-∼≈′ ⟩
  Laterˡ⁻¹-∼≈′   ↝⟨ _⇔_.from size-preserving-laterˡ⁻¹-∼≈⇔size-preserving-laterˡ⁻¹-∼≈′ ⟩
  Laterˡ⁻¹-∼≈    ↝⟨ size-preserving-laterˡ⁻¹-∼≈→uninhabited ⟩□
  ¬ (∀ i → A i)  □

-- Having a size-preserving variant of laterˡ⁻¹ is logically
-- equivalent to having a size-preserving variant of laterʳ⁻¹ (for
-- weak bisimilarity).

Laterˡ⁻¹-≈ = ∀ {i x} {y : Delay A ∞} →
             [ i ] later x ≈ y →
             [ i ] force x ≈ y

Laterʳ⁻¹-≈ = ∀ {i} {x : Delay A ∞} {y} →
             [ i ] x ≈ later y →
             [ i ] x ≈ force y

size-preserving-laterˡ⁻¹-≈⇔size-preserving-laterʳ⁻¹-≈ :
  Laterˡ⁻¹-≈ ⇔ Laterʳ⁻¹-≈
size-preserving-laterˡ⁻¹-≈⇔size-preserving-laterʳ⁻¹-≈ = record
  { to   = λ laterʳ⁻¹ → symmetric ∘ laterʳ⁻¹ ∘ symmetric
  ; from = λ laterˡ⁻¹ → symmetric ∘ laterˡ⁻¹ ∘ symmetric
  }

-- If laterˡ⁻¹ can be made size-preserving, then ∀ i → A i is
-- uninhabited.

size-preserving-laterˡ⁻¹-≈→uninhabited : Laterˡ⁻¹-≈ → ¬ (∀ i → A i)
size-preserving-laterˡ⁻¹-≈→uninhabited =
  Laterˡ⁻¹-≈     ↝⟨ (λ laterˡ⁻¹ _ → laterˡ⁻¹ ∘ ∼→) ⟩
  Laterˡ⁻¹-∼≈    ↝⟨ size-preserving-laterˡ⁻¹-∼≈→uninhabited ⟩□
  ¬ (∀ i → A i)  □

-- If laterʳ⁻¹ can be made size-preserving for expansion, then
-- ∀ i → A i is uninhabited.

Laterʳ⁻¹-≳ = ∀ {i} {x : Delay A ∞} {y} →
             [ i ] x ≳ later y →
             [ i ] x ≳ force y

size-preserving-laterʳ⁻¹-≳→uninhabited : Laterʳ⁻¹-≳ → ¬ (∀ i → A i)
size-preserving-laterʳ⁻¹-≳→uninhabited =
  Laterʳ⁻¹-≳     ↝⟨ (λ laterʳ⁻¹ {_} _ p → laterʳ⁻¹ (∼→ p)) ⟩
  Laterʳ⁻¹-∼≳′   ↝⟨ size-preserving-laterʳ⁻¹-∼≳′→uninhabited ⟩□
  ¬ (∀ i → A i)  □

-- If a variant of ⇓-respects-≈ in which _≈_ is replaced by _∼_ can be
-- made size-preserving in the second argument, then ∀ i → A i is
-- uninhabited.

⇓-Respects-∼ʳ = ∀ {i} {x y : Delay A ∞} {z} →
                x ⇓ z → [ i ] x ∼ y → Terminates i y z

size-preserving-⇓-respects-∼ʳ→uninhabited :
  ⇓-Respects-∼ʳ → ¬ (∀ i → A i)
size-preserving-⇓-respects-∼ʳ→uninhabited =
  ⇓-Respects-∼ʳ  ↝⟨ (λ resp _ → resp (laterʳ now)) ⟩
  Laterˡ⁻¹-∼≈    ↝⟨ size-preserving-laterˡ⁻¹-∼≈→uninhabited ⟩□
  ¬ (∀ i → A i)  □

-- If ⇓-respects-≈ can be made size-preserving in the second argument,
-- then ∀ i → A i is uninhabited.

⇓-Respects-≈ʳ = ∀ {i} {x y : Delay A ∞} {z} →
                x ⇓ z → [ i ] x ≈ y → Terminates i y z

size-preserving-⇓-respects-≈ʳ→uninhabited :
  ⇓-Respects-≈ʳ → ¬ (∀ i → A i)
size-preserving-⇓-respects-≈ʳ→uninhabited =
  ⇓-Respects-≈ʳ  ↝⟨ (λ trans x⇓z → trans x⇓z ∘ ∼→) ⟩
  ⇓-Respects-∼ʳ  ↝⟨ size-preserving-⇓-respects-∼ʳ→uninhabited ⟩□
  ¬ (∀ i → A i)  □

-- Having a transitivity-like proof, taking weak bisimilarity and
-- strong bisimilarity to weak bisimilarity, that preserves the size
-- of the second argument, is logically equivalent to having a
-- transitivity-like proof, taking strong bisimilarity and weak
-- bisimilarity to weak bisimilarity, that preserves the size of the
-- first argument.

Transitivity-≈∼ʳ = ∀ {i} {x y z : Delay A ∞} →
                   x ≈ y → [ i ] y ∼ z → [ i ] x ≈ z

Transitivity-∼≈ˡ = ∀ {i} {x y z : Delay A ∞} →
                   [ i ] x ∼ y → y ≈ z → [ i ] x ≈ z

size-preserving-transitivity-≈∼ʳ⇔size-preserving-transitivity-∼≈ˡ :
  Transitivity-≈∼ʳ ⇔ Transitivity-∼≈ˡ
size-preserving-transitivity-≈∼ʳ⇔size-preserving-transitivity-∼≈ˡ =
  record
    { to   = λ trans p q → symmetric (trans (symmetric q) (symmetric p))
    ; from = λ trans p q → symmetric (trans (symmetric q) (symmetric p))
    }

-- If there is a transitivity-like proof, taking weak bisimilarity and
-- strong bisimilarity to weak bisimilarity, that preserves the size
-- of the second argument, then ∀ i → A i is uninhabited.

size-preserving-transitivity-≈∼ʳ→uninhabited :
  Transitivity-≈∼ʳ → ¬ (∀ i → A i)
size-preserving-transitivity-≈∼ʳ→uninhabited =
  Transitivity-≈∼ʳ  ↝⟨ (λ trans → trans) ⟩
  ⇓-Respects-∼ʳ     ↝⟨ size-preserving-⇓-respects-∼ʳ→uninhabited ⟩
  ¬ (∀ i → A i)     □

-- If there is a transitivity-like proof, taking strong bisimilarity
-- and expansion to expansion, that preserves the size of the first
-- argument, then ∀ i → A i is uninhabited.

Transitivity-∼≳ˡ = ∀ {i} {x y z : Delay A ∞} →
                   [ i ] x ∼ y → y ≳ z → [ i ] x ≳ z

size-preserving-transitivity-∼≳ˡ→uninhabited :
  Transitivity-∼≳ˡ → ¬ (∀ i → A i)
size-preserving-transitivity-∼≳ˡ→uninhabited =
  Transitivity-∼≳ˡ  ↝⟨ (λ trans _ p → trans p (laterˡ now)) ⟩
  Laterʳ⁻¹-∼≳′      ↝⟨ size-preserving-laterʳ⁻¹-∼≳′→uninhabited ⟩
  ¬ (∀ i → A i)     □

-- Having a transitivity proof for weak bisimilarity that preserves
-- the size of the first argument is logically equivalent to having
-- one that preserves the size of the second argument.

Transitivity-≈ˡ = ∀ {i} {x y z : Delay A ∞} →
                  [ i ] x ≈ y → y ≈ z → [ i ] x ≈ z

Transitivity-≈ʳ = ∀ {i} {x y z : Delay A ∞} →
                x ≈ y → [ i ] y ≈ z → [ i ] x ≈ z

size-preserving-transitivity-≈ˡ⇔size-preserving-transitivity-≈ʳ :
  Transitivity-≈ˡ ⇔ Transitivity-≈ʳ
size-preserving-transitivity-≈ˡ⇔size-preserving-transitivity-≈ʳ = record
  { to   = λ trans p q → symmetric (trans (symmetric q) (symmetric p))
  ; from = λ trans p q → symmetric (trans (symmetric q) (symmetric p))
  }

-- If there is a transitivity proof for weak bisimilarity that
-- preserves the size of the second argument, then ∀ i → A i is
-- uninhabited.

size-preserving-transitivity-≈ʳ→uninhabited :
  Transitivity-≈ʳ → ¬ (∀ i → A i)
size-preserving-transitivity-≈ʳ→uninhabited =
  Transitivity-≈ʳ  ↝⟨ (λ trans → trans) ⟩
  ⇓-Respects-≈ʳ    ↝⟨ size-preserving-⇓-respects-≈ʳ→uninhabited ⟩□
  ¬ (∀ i → A i)    □

-- If there is a transitivity proof for expansion that preserves the
-- size of the first argument, then ∀ i → A i is uninhabited.

Transitivity-≳ˡ = ∀ {i} {x y z : Delay A ∞} →
                  [ i ] x ≳ y → y ≳ z → [ i ] x ≳ z

size-preserving-transitivity-≳ˡ→uninhabited :
  Transitivity-≳ˡ → ¬ (∀ i → A i)
size-preserving-transitivity-≳ˡ→uninhabited =
  Transitivity-≳ˡ   ↝⟨ (λ trans → trans ∘ ∼→) ⟩
  Transitivity-∼≳ˡ  ↝⟨ size-preserving-transitivity-∼≳ˡ→uninhabited ⟩□
  ¬ (∀ i → A i)     □

-- If there is a fully size-preserving transitivity proof for weak
-- bisimilarity, then ∀ i → A i is uninhabited.

Transitivity-≈ = ∀ {i} {x y z : Delay A ∞} →
                 [ i ] x ≈ y → [ i ] y ≈ z → [ i ] x ≈ z

size-preserving-transitivity-≈→uninhabited :
  Transitivity-≈ → ¬ (∀ i → A i)
size-preserving-transitivity-≈→uninhabited =
  Transitivity-≈   ↝⟨ (λ trans → trans) ⟩
  Transitivity-≈ʳ  ↝⟨ size-preserving-transitivity-≈ʳ→uninhabited ⟩□
  ¬ (∀ i → A i)    □

-- If there is a fully size-preserving transitivity proof for
-- expansion, then ∀ i → A i is uninhabited.

Transitivity-≳ = ∀ {i} {x y z : Delay A ∞} →
                 [ i ] x ≳ y → [ i ] y ≳ z → [ i ] x ≳ z

size-preserving-transitivity-≳→uninhabited :
  Transitivity-≳ → ¬ (∀ i → A i)
size-preserving-transitivity-≳→uninhabited =
  Transitivity-≳   ↝⟨ (λ trans → trans) ⟩
  Transitivity-≳ˡ  ↝⟨ size-preserving-transitivity-≳ˡ→uninhabited ⟩□
  ¬ (∀ i → A i)    □

-- There is a transitivity-like proof, taking expansion and weak
-- bisimilarity to weak bisimilarity, that preserves the size of the
-- first argument, iff there is a transitivity-like proof, taking weak
-- bisimilarity and the converse of expansion to weak bisimilarity,
-- that preserves the size of the second argument.

Transitivity-≳≈ˡ = ∀ {i} {x y z : Delay A ∞} →
                   [ i ] x ≳ y → y ≈ z → [ i ] x ≈ z

Transitivity-≈≲ʳ = ∀ {i} {x y z : Delay A ∞} →
                   x ≈ y → [ i ] y ≲ z → [ i ] x ≈ z

size-preserving-transitivity-≳≈ˡ⇔size-preserving-transitivity-≈≲ʳ :
  Transitivity-≳≈ˡ ⇔ Transitivity-≈≲ʳ
size-preserving-transitivity-≳≈ˡ⇔size-preserving-transitivity-≈≲ʳ =
  record
    { to   = λ trans x≈y y≲z → symmetric (trans y≲z (symmetric x≈y))
    ; from = λ trans x≳y y≈z → symmetric (trans (symmetric y≈z) x≳y)
    }

-- If there is a transitivity-like proof, taking expansion and weak
-- bisimilarity to weak bisimilarity, that preserves the size of the
-- first argument, then ∀ i → A i is uninhabited.

size-preserving-transitivity-≳≈ˡ→uninhabited :
  Transitivity-≳≈ˡ → ¬ (∀ i → A i)
size-preserving-transitivity-≳≈ˡ→uninhabited =
  Transitivity-≳≈ˡ  ↝⟨ _∘ ∼→ ⟩
  Transitivity-∼≈ˡ  ↝⟨ _⇔_.from size-preserving-transitivity-≈∼ʳ⇔size-preserving-transitivity-∼≈ˡ ⟩
  Transitivity-≈∼ʳ  ↝⟨ size-preserving-transitivity-≈∼ʳ→uninhabited ⟩□
  ¬ (∀ i → A i)     □

-- There is a transitivity-like proof, taking expansion and weak
-- bisimilarity to weak bisimilarity, that preserves the size of both
-- arguments, iff there is a transitivity-like proof, taking weak
-- bisimilarity and the converse of expansion to weak bisimilarity,
-- that also preserves the size of both arguments.

Transitivity-≳≈ = ∀ {i} {x y z : Delay A ∞} →
                  [ i ] x ≳ y → [ i ] y ≈ z → [ i ] x ≈ z

Transitivity-≈≲ = ∀ {i} {x y z : Delay A ∞} →
                  [ i ] x ≈ y → [ i ] y ≲ z → [ i ] x ≈ z

size-preserving-transitivity-≳≈⇔size-preserving-transitivity-≈≲ :
  Transitivity-≳≈ ⇔ Transitivity-≈≲
size-preserving-transitivity-≳≈⇔size-preserving-transitivity-≈≲ =
  record
    { to   = λ trans x≈y y≲z → symmetric (trans y≲z (symmetric x≈y))
    ; from = λ trans x≳y y≈z → symmetric (trans (symmetric y≈z) x≳y)
    }

-- If there is a transitivity-like proof, taking expansion and weak
-- bisimilarity to weak bisimilarity, that preserves the size of both
-- arguments, then ∀ i → A i is uninhabited.

size-preserving-transitivity-≳≈→uninhabited :
  Transitivity-≳≈ → ¬ (∀ i → A i)
size-preserving-transitivity-≳≈→uninhabited =
  Transitivity-≳≈   ↝⟨ (λ trans → trans) ⟩
  Transitivity-≳≈ˡ  ↝⟨ size-preserving-transitivity-≳≈ˡ→uninhabited ⟩□
  ¬ (∀ i → A i)     □

-- If there is a transitivity-like proof, taking weak bisimilarity and
-- expansion to weak bisimilarity, that preserves the size of the
-- first argument, then ∀ i → A i is uninhabited.

Transitivity-≈≳ˡ = ∀ {i} {x y z : Delay A ∞} →
                   [ i ] x ≈ y → y ≳ z → [ i ] x ≈ z

size-preserving-transitivity-≈≳ˡ→uninhabited :
  Transitivity-≈≳ˡ → ¬ (∀ i → A i)
size-preserving-transitivity-≈≳ˡ→uninhabited =
  Transitivity-≈≳ˡ  ↝⟨ (λ trans {_ _ _} x≈ly → trans x≈ly (laterˡ (reflexive _))) ⟩
  Laterʳ⁻¹-≈        ↝⟨ _⇔_.from size-preserving-laterˡ⁻¹-≈⇔size-preserving-laterʳ⁻¹-≈ ⟩
  Laterˡ⁻¹-≈        ↝⟨ size-preserving-laterˡ⁻¹-≈→uninhabited ⟩
  ¬ (∀ i → A i)     □

------------------------------------------------------------------------
-- Lemmas stating that certain types are inhabited if A ∞ is
-- uninhabited

-- If A ∞ is uninhabited, then Laterˡ⁻¹-≳′ is inhabited.

uninhabited→laterˡ⁻¹-≳′ : ¬ A ∞ → Laterˡ⁻¹-≳′
uninhabited→laterˡ⁻¹-≳′ =
  ¬ A ∞            ↝⟨ uninhabited→trivial ⟩
  (∀ x y → x ≳ y)  ↝⟨ (λ trivial _ _ → trivial _ _) ⟩□
  Laterˡ⁻¹-≳′      □

-- If A ∞ is uninhabited, then a variant of laterˡ⁻¹ for (fully
-- defined) expansion can be defined.

uninhabited→laterˡ⁻¹-≳ : ¬ A ∞ → Laterˡ⁻¹-≳
uninhabited→laterˡ⁻¹-≳ =
  ¬ A ∞            ↝⟨ uninhabited→trivial ⟩
  (∀ x y → x ≳ y)  ↝⟨ (λ trivial {_ _} _ → trivial _ _) ⟩□
  Laterˡ⁻¹-≳       □

-- If A ∞ is uninhabited, then a transitivity-like proof taking weak
-- bisimilarity and expansion to expansion can be defined.

uninhabited→transitivity-≈≳≳ : ¬ A ∞ → Transitivity-≈≳≳
uninhabited→transitivity-≈≳≳ =
  ¬ A ∞             ↝⟨ uninhabited→trivial ⟩
  (∀ x y → x ≳ y)   ↝⟨ (λ trivial {_ _ _} _ _ → trivial _ _) ⟩□
  Transitivity-≈≳≳  □

-- If A ∞ is uninhabited, then a transitivity-like proof taking
-- expansion and weak bisimilarity to expansion can be defined.

uninhabited→transitivity-≳≈≳ : ¬ A ∞ → Transitivity-≳≈≳
uninhabited→transitivity-≳≈≳ =
  ¬ A ∞             ↝⟨ uninhabited→trivial ⟩
  (∀ x y → x ≳ y)   ↝⟨ (λ trivial {_ _ _} _ _ → trivial _ _) ⟩□
  Transitivity-≳≈≳  □

-- If A ∞ is uninhabited, then Laterˡ⁻¹-∼≈ is inhabited.

uninhabited→size-preserving-laterˡ⁻¹-∼≈ : ¬ A ∞ → Laterˡ⁻¹-∼≈
uninhabited→size-preserving-laterˡ⁻¹-∼≈ =
  ¬ A ∞            ↝⟨ uninhabited→trivial ⟩
  (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_} _ _ → trivial _ _) ⟩□
  Laterˡ⁻¹-∼≈      □

-- If A ∞ is uninhabited, then laterˡ⁻¹ can be made size-preserving.

uninhabited→size-preserving-laterˡ⁻¹ : ¬ A ∞ → Laterˡ⁻¹-≈
uninhabited→size-preserving-laterˡ⁻¹ =
  ¬ A ∞            ↝⟨ uninhabited→trivial ⟩
  (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _ _} _ → trivial _ _) ⟩□
  Laterˡ⁻¹-≈       □

-- If A ∞ is uninhabited, then a variant of ⇓-respects-≈ in which _≈_
-- is replaced by _∼_ can be made size-preserving in the second
-- argument.

uninhabited→size-preserving-⇓-respects-∼ʳ : ¬ A ∞ → ⇓-Respects-∼ʳ
uninhabited→size-preserving-⇓-respects-∼ʳ =
  ¬ A ∞            ↝⟨ uninhabited→trivial ⟩
  (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
  ⇓-Respects-∼ʳ    □

-- If A ∞ is uninhabited, then ⇓-respects-≈ can be made
-- size-preserving in the second argument.

uninhabited→size-preserving-⇓-respects-≈ʳ : ¬ A ∞ → ⇓-Respects-≈ʳ
uninhabited→size-preserving-⇓-respects-≈ʳ =
  ¬ A ∞            ↝⟨ uninhabited→trivial ⟩
  (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
  ⇓-Respects-≈ʳ    □

-- If A ∞ is uninhabited, then there is a transitivity-like proof,
-- taking weak bisimilarity and strong bisimilarity to weak
-- bisimilarity, that preserves the size of the second argument.

uninhabited→size-preserving-transitivity-≈∼ʳ : ¬ A ∞ → Transitivity-≈∼ʳ
uninhabited→size-preserving-transitivity-≈∼ʳ =
  ¬ A ∞             ↝⟨ uninhabited→trivial ⟩
  (∀ x y → x ≈ y)   ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
  Transitivity-≈∼ʳ  □

-- If A ∞ is uninhabited, then there is a transitivity-like proof,
-- taking strong bisimilarity and expansion to expansion, that
-- preserves the size of the first argument.

uninhabited→size-preserving-transitivity-∼≳ˡ : ¬ A ∞ → Transitivity-∼≳ˡ
uninhabited→size-preserving-transitivity-∼≳ˡ =
  ¬ A ∞             ↝⟨ uninhabited→trivial ⟩
  (∀ x y → x ≳ y)   ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
  Transitivity-∼≳ˡ  □

-- If A ∞ is uninhabited, then there is a transitivity proof for weak
-- bisimilarity that preserves the size of the second argument.

uninhabited→size-preserving-transitivity-≈ʳ : ¬ A ∞ → Transitivity-≈ʳ
uninhabited→size-preserving-transitivity-≈ʳ =
  ¬ A ∞            ↝⟨ uninhabited→trivial ⟩
  (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
  Transitivity-≈ʳ  □

-- If A ∞ is uninhabited, then there is a transitivity proof for
-- expansion that preserves the size of the first argument.

uninhabited→size-preserving-transitivity-≳ˡ : ¬ A ∞ → Transitivity-≳ˡ
uninhabited→size-preserving-transitivity-≳ˡ =
  ¬ A ∞            ↝⟨ uninhabited→trivial ⟩
  (∀ x y → x ≳ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
  Transitivity-≳ˡ  □

-- If A ∞ is uninhabited, then there is a fully size-preserving
-- transitivity proof for weak bisimilarity.

uninhabited→size-preserving-transitivity-≈ : ¬ A ∞ → Transitivity-≈
uninhabited→size-preserving-transitivity-≈ =
  ¬ A ∞            ↝⟨ uninhabited→trivial ⟩
  (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
  Transitivity-≈   □

-- If A ∞ is uninhabited, then there is a fully size-preserving
-- transitivity proof for expansion.

uninhabited→size-preserving-transitivity-≳ : ¬ A ∞ → Transitivity-≳
uninhabited→size-preserving-transitivity-≳ =
  ¬ A ∞            ↝⟨ uninhabited→trivial ⟩
  (∀ x y → x ≳ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
  Transitivity-≳   □

-- If A ∞ is uninhabited, then there is a transitivity-like proof,
-- taking expansion and weak bisimilarity to weak bisimilarity, that
-- preserves the size of the first argument.

uninhabited→size-preserving-transitivity-≳≈ˡ : ¬ A ∞ → Transitivity-≳≈ˡ
uninhabited→size-preserving-transitivity-≳≈ˡ =
  ¬ A ∞             ↝⟨ uninhabited→trivial ⟩
  (∀ x y → x ≈ y)   ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
  Transitivity-≳≈ˡ  □

-- If A ∞ is uninhabited, then there is a transitivity-like proof,
-- taking expansion and weak bisimilarity to weak bisimilarity, that
-- preserves the size of both arguments.

uninhabited→size-preserving-transitivity-≳≈ : ¬ A ∞ → Transitivity-≳≈
uninhabited→size-preserving-transitivity-≳≈ =
  ¬ A ∞            ↝⟨ uninhabited→trivial ⟩
  (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
  Transitivity-≳≈  □

-- If A ∞ is uninhabited, then there is a transitivity-like proof,
-- taking weak bisimilarity and expansion to weak bisimilarity, that
-- preserves the size of the first argument.

uninhabited→size-preserving-transitivity-≈≳ˡ : ¬ A ∞ → Transitivity-≈≳ˡ
uninhabited→size-preserving-transitivity-≈≳ˡ =
  ¬ A ∞             ↝⟨ uninhabited→trivial ⟩
  (∀ x y → x ≈ y)   ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
  Transitivity-≈≳ˡ  □
