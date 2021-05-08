------------------------------------------------------------------------
-- Some negative results related to weak bisimilarity and expansion
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

open import Prelude

module Delay-monad.Bisimilarity.Negative {a} {A : Type a} where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude.Size

open import Function-universe equality-with-J hiding (id; _∘_)

open import Delay-monad
open import Delay-monad.Bisimilarity
open import Delay-monad.Termination

------------------------------------------------------------------------
-- Lemmas stating that functions of certain types can be defined iff A
-- is uninhabited

-- The computation now x is an expansion of
-- later (record { force = now x }) for every x : A iff A is
-- uninhabited.

Now≳later-now = (x : A) → now x ≳ later (record { force = now x })

now≳later-now⇔uninhabited : Now≳later-now ⇔ ¬ A
now≳later-now⇔uninhabited = record
  { to   = Now≳later-now  ↝⟨ (λ hyp x → case hyp x of λ ()) ⟩□
           ¬ A            □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≳ y)  ↝⟨ (λ hyp _ → hyp _ _) ⟩□
           Now≳later-now    □
  }

-- A variant of laterˡ⁻¹ for (fully defined) expansion can be defined
-- iff A is uninhabited.

Laterˡ⁻¹-≳ = ∀ {x} {y : Delay A ∞} → later x ≳ y → force x ≳ y

laterˡ⁻¹-≳⇔uninhabited : Laterˡ⁻¹-≳ ⇔ ¬ A
laterˡ⁻¹-≳⇔uninhabited = record
  { to   = Laterˡ⁻¹-≳     ↝⟨ (λ hyp _ → hyp (reflexive _)) ⟩
           Now≳later-now  ↝⟨ _⇔_.to now≳later-now⇔uninhabited ⟩□
           ¬ A            □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≳ y)  ↝⟨ (λ hyp {_ _} _ → hyp _ _) ⟩□
           Laterˡ⁻¹-≳       □
  }

-- The following variants of transitivity can be proved iff A is
-- uninhabited.

Transitivity-≈≳≳ = {x y z : Delay A ∞} → x ≈ y → y ≳ z → x ≳ z
Transitivity-≳≈≳ = {x y z : Delay A ∞} → x ≳ y → y ≈ z → x ≳ z

transitive-≈≳≳⇔uninhabited : Transitivity-≈≳≳ ⇔ ¬ A
transitive-≈≳≳⇔uninhabited = record
  { to   = Transitivity-≈≳≳  ↝⟨ (λ trans → trans (laterʳ (reflexive _))) ⟩
           Laterˡ⁻¹-≳        ↝⟨ _⇔_.to laterˡ⁻¹-≳⇔uninhabited ⟩□
           ¬ A               □
  ; from = ¬ A               ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≳ y)   ↝⟨ (λ hyp {_ _ _} _ _ → hyp _ _) ⟩□
           Transitivity-≈≳≳  □
  }

transitive-≳≈≳⇔uninhabited : Transitivity-≳≈≳ ⇔ ¬ A
transitive-≳≈≳⇔uninhabited = record
  { to   = Transitivity-≳≈≳  ↝⟨ (λ trans {_ y} lx≳y → later⁻¹ {y = record { force = y }}
                                                              (trans lx≳y (laterʳ (reflexive _)))) ⟩
           Laterˡ⁻¹-≳        ↝⟨ _⇔_.to laterˡ⁻¹-≳⇔uninhabited ⟩□
           ¬ A               □
  ; from = ¬ A               ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≳ y)   ↝⟨ (λ hyp {_ _ _} _ _ → hyp _ _) ⟩□
           Transitivity-≳≈≳  □
  }

------------------------------------------------------------------------
-- Lemmas stating that certain size-preserving functions can be
-- defined iff A is uninhabited

-- A variant of laterˡ⁻¹ in which one occurrence of weak bisimilarity
-- is replaced by strong bisimilarity, and both arguments are
-- specialised, can be made size-preserving iff A is uninhabited.
--
-- This lemma is used to prove all other similar results below
-- (directly or indirectly), with the exception that an alternative,
-- more direct proof is also given for one of the results.

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
  Laterˡ⁻¹-∼≈′  ↝⟨ record { to   = _∘ transitive-∼ʳ (later λ { .force → now })
                          ; from = _∘ transitive-∼ʳ (later λ { .force → now })
                          } ⟩
  Laterˡ⁻¹-∼≈   ↝⟨ size-preserving-laterˡ⁻¹-∼≈⇔uninhabited ⟩□
  ¬ A           □

-- A variant of laterʳ⁻¹ for weak bisimilarity in which one occurrence
-- of weak bisimilarity is replaced by strong bisimilarity, and both
-- arguments are specialised, can be made size-preserving iff A is
-- uninhabited.

Laterʳ⁻¹-∼≈ = ∀ {i} {x : A} →
              [ i ] never ∼ later (record { force = now x }) →
              [ i ] never ≈ now x

size-preserving-laterʳ⁻¹-∼≈⇔uninhabited : Laterʳ⁻¹-∼≈ ⇔ ¬ A
size-preserving-laterʳ⁻¹-∼≈⇔uninhabited =
  Laterʳ⁻¹-∼≈   ↝⟨ record { to   = λ laterʳ⁻¹ → symmetric ∘ laterʳ⁻¹ ∘ symmetric
                          ; from = λ laterˡ⁻¹ → symmetric ∘ laterˡ⁻¹ ∘ symmetric
                          } ⟩
  Laterˡ⁻¹-∼≈′  ↝⟨ size-preserving-laterˡ⁻¹-∼≈′⇔uninhabited ⟩□
  ¬ A           □

-- A variant of laterʳ⁻¹ for expansion in which one occurrence of the
-- expansion relation is replaced by strong bisimilarity, and both
-- arguments are specialised, can be made size-preserving iff A is
-- uninhabited.

Laterʳ⁻¹-∼≳ = ∀ {i} {x : A} →
              [ i ] never ∼ later (record { force = now x }) →
              [ i ] never ≳ now x

size-preserving-laterʳ⁻¹-∼≳⇔uninhabited : Laterʳ⁻¹-∼≳ ⇔ ¬ A
size-preserving-laterʳ⁻¹-∼≳⇔uninhabited = record
  { to   = Laterʳ⁻¹-∼≳  ↝⟨ ≳→ ∘_ ⟩
           Laterʳ⁻¹-∼≈  ↝⟨ _⇔_.to size-preserving-laterʳ⁻¹-∼≈⇔uninhabited ⟩□
           ¬ A          □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≳ y)  ↝⟨ (λ trivial {_ _} _ → trivial _ _) ⟩□
           Laterʳ⁻¹-∼≳      □
  }

-- The function laterˡ⁻¹ can be made size-preserving iff A is
-- uninhabited.

Laterˡ⁻¹-≈ = ∀ {i x} {y : Delay A ∞} →
             [ i ] later x ≈ y → [ i ] force x ≈ y

size-preserving-laterˡ⁻¹-≈⇔uninhabited : Laterˡ⁻¹-≈ ⇔ ¬ A
size-preserving-laterˡ⁻¹-≈⇔uninhabited = record
  { to   = Laterˡ⁻¹-≈   ↝⟨ _∘ ∼→ ⟩
           Laterˡ⁻¹-∼≈  ↝⟨ _⇔_.to size-preserving-laterˡ⁻¹-∼≈⇔uninhabited ⟩□
           ¬ A          □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _ _} _ → trivial _ _) ⟩□
           Laterˡ⁻¹-≈       □
  }

-- The function laterʳ⁻¹ can be made size-preserving for weak
-- bisimilarity iff A is uninhabited.

Laterʳ⁻¹-≈ = ∀ {i} {x : Delay A ∞} {y} →
             [ i ] x ≈ later y → [ i ] x ≈ force y

size-preserving-laterʳ⁻¹-≈⇔uninhabited : Laterʳ⁻¹-≈ ⇔ ¬ A
size-preserving-laterʳ⁻¹-≈⇔uninhabited =
  Laterʳ⁻¹-≈  ↝⟨ record { to   = λ laterʳ⁻¹ → symmetric ∘ laterʳ⁻¹ ∘ symmetric
                        ; from = λ laterˡ⁻¹ → symmetric ∘ laterˡ⁻¹ ∘ symmetric
                        } ⟩
  Laterˡ⁻¹-≈  ↝⟨ size-preserving-laterˡ⁻¹-≈⇔uninhabited ⟩□

  ¬ A         □

-- The function laterʳ⁻¹ can be made size-preserving for expansion iff
-- A is uninhabited.

Laterʳ⁻¹-≳ = ∀ {i} {x : Delay A ∞} {y} →
             [ i ] x ≳ later y → [ i ] x ≳ force y

size-preserving-laterʳ⁻¹-≳⇔uninhabited : Laterʳ⁻¹-≳ ⇔ ¬ A
size-preserving-laterʳ⁻¹-≳⇔uninhabited = record
  { to   = Laterʳ⁻¹-≳   ↝⟨ _∘ ∼→ ⟩
           Laterʳ⁻¹-∼≳  ↝⟨ _⇔_.to size-preserving-laterʳ⁻¹-∼≳⇔uninhabited ⟩□
           ¬ A          □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≳ y)  ↝⟨ (λ trivial {_ _ _} _ → trivial _ _) ⟩□
           Laterʳ⁻¹-≳       □
  }

-- A variant of ⇓-respects-≈ in which _≈_ is replaced by _∼_ can be
-- made size-preserving in the second argument iff A is uninhabited.

⇓-Respects-∼ʳ = ∀ {i x y} {z : A} →
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

⇓-Respects-≈ʳ = ∀ {i x y} {z : A} →
                x ⇓ z → [ i ] x ≈ y → Terminates i y z

size-preserving-⇓-respects-≈ʳ⇔uninhabited : ⇓-Respects-≈ʳ ⇔ ¬ A
size-preserving-⇓-respects-≈ʳ⇔uninhabited = record
  { to   = ⇓-Respects-≈ʳ  ↝⟨ (λ resp x⇓z → resp x⇓z ∘ ∼→) ⟩
           ⇓-Respects-∼ʳ  ↝⟨ _⇔_.to size-preserving-⇓-respects-∼ʳ⇔uninhabited ⟩□
           ¬ A            □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           ⇓-Respects-≈ʳ    □
  }

-- There is a transitivity-like proof, taking weak bisimilarity and
-- strong bisimilarity to weak bisimilarity, that preserves the size
-- of the second argument iff A is uninhabited.

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

-- There is a transitivity-like proof, taking strong bisimilarity and
-- weak bisimilarity to weak bisimilarity, that preserves the size of
-- the first argument iff A is uninhabited.

Transitivity-∼≈ˡ = ∀ {i} {x y z : Delay A ∞} →
                   [ i ] x ∼ y → y ≈ z → [ i ] x ≈ z

size-preserving-transitivity-∼≈ˡ⇔uninhabited : Transitivity-∼≈ˡ ⇔ ¬ A
size-preserving-transitivity-∼≈ˡ⇔uninhabited =
  Transitivity-∼≈ˡ  ↝⟨ record { to   = λ trans {_ _ _ _} p q →
                                         symmetric (trans (symmetric q) (symmetric p))
                              ; from = λ trans {_ _ _ _} p q →
                                         symmetric (trans (symmetric q) (symmetric p))
                              } ⟩
  Transitivity-≈∼ʳ  ↝⟨ size-preserving-transitivity-≈∼ʳ⇔uninhabited ⟩□

  ¬ A               □

-- There is a transitivity-like proof, taking strong bisimilarity and
-- expansion to expansion, that preserves the size of the first
-- argument iff A is uninhabited.

Transitivity-∼≳ˡ = ∀ {i} {x y z : Delay A ∞} →
                   [ i ] x ∼ y → y ≳ z → [ i ] x ≳ z

size-preserving-transitivity-∼≳ˡ⇔uninhabited : Transitivity-∼≳ˡ ⇔ ¬ A
size-preserving-transitivity-∼≳ˡ⇔uninhabited = record
  { to   = Transitivity-∼≳ˡ  ↝⟨ (λ trans never∼lnx → trans never∼lnx (laterˡ now)) ⟩
           Laterʳ⁻¹-∼≳       ↝⟨ _⇔_.to size-preserving-laterʳ⁻¹-∼≳⇔uninhabited ⟩□
           ¬ A               □
  ; from = ¬ A               ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≳ y)   ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Transitivity-∼≳ˡ  □
  }

-- There is a transitivity proof for weak bisimilarity that preserves
-- the size of the second argument iff A is uninhabited.

Transitivity-≈ʳ = ∀ {i} {x y z : Delay A ∞} →
                  x ≈ y → [ i ] y ≈ z → [ i ] x ≈ z

size-preserving-transitivity-≈ʳ⇔uninhabited : Transitivity-≈ʳ ⇔ ¬ A
size-preserving-transitivity-≈ʳ⇔uninhabited = record
  { to   = Transitivity-≈ʳ  ↝⟨ (λ trans → trans) ⟩
           ⇓-Respects-≈ʳ    ↝⟨ _⇔_.to size-preserving-⇓-respects-≈ʳ⇔uninhabited ⟩□
           ¬ A              □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Transitivity-≈ʳ  □
  }

-- There is a transitivity proof for weak bisimilarity that preserves
-- the size of the first argument iff A is uninhabited.

Transitivity-≈ˡ = ∀ {i} {x y z : Delay A ∞} →
                  [ i ] x ≈ y → y ≈ z → [ i ] x ≈ z

size-preserving-transitivity-≈ˡ⇔uninhabited : Transitivity-≈ˡ ⇔ ¬ A
size-preserving-transitivity-≈ˡ⇔uninhabited =
  Transitivity-≈ˡ  ↝⟨ record { to   = λ trans {_ _ _ _} p q →
                                        symmetric (trans (symmetric q) (symmetric p))
                             ; from = λ trans {_ _ _ _} p q →
                                        symmetric (trans (symmetric q) (symmetric p))
                             } ⟩
  Transitivity-≈ʳ  ↝⟨ size-preserving-transitivity-≈ʳ⇔uninhabited ⟩□

  ¬ A              □

-- There is a transitivity proof for expansion that preserves the size
-- of the first argument iff A is uninhabited.

Transitivity-≳ˡ = ∀ {i} {x y z : Delay A ∞} →
                  [ i ] x ≳ y → y ≳ z → [ i ] x ≳ z

size-preserving-transitivity-≳ˡ⇔uninhabited : Transitivity-≳ˡ ⇔ ¬ A
size-preserving-transitivity-≳ˡ⇔uninhabited = record
  { to   = Transitivity-≳ˡ   ↝⟨ _∘ ∼→ ⟩
           Transitivity-∼≳ˡ  ↝⟨ _⇔_.to size-preserving-transitivity-∼≳ˡ⇔uninhabited ⟩□
           ¬ A               □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≳ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Transitivity-≳ˡ  □
  }

-- There is a fully size-preserving transitivity proof for weak
-- bisimilarity iff A is uninhabited.

Transitivity-≈ = ∀ {i} {x y z : Delay A ∞} →
                 [ i ] x ≈ y → [ i ] y ≈ z → [ i ] x ≈ z

size-preserving-transitivity-≈⇔uninhabited : Transitivity-≈ ⇔ ¬ A
size-preserving-transitivity-≈⇔uninhabited = record
  { to   = Transitivity-≈   ↝⟨ (λ trans → trans) ⟩
           Transitivity-≈ˡ  ↝⟨ _⇔_.to size-preserving-transitivity-≈ˡ⇔uninhabited ⟩
           ¬ A              □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Transitivity-≈   □
  }

-- The following two lemmas provide an alternative proof of one
-- direction of the previous lemma (with a small change to one of the
-- types).

-- If there is a transitivity proof for weak bisimilarity that is
-- size-preserving in both arguments, then weak bisimilarity is
-- trivial.

size-preserving-transitivity-≈→trivial :
  (∀ {i} x {y z : Delay A ∞} →
   [ i ] x ≈ y → [ i ] y ≈ z → [ i ] x ≈ z) →
  ∀ {i} (x y : Delay A ∞) → [ i ] x ≈ y
size-preserving-transitivity-≈→trivial _≈⟨_⟩ʷ_ x y =
  (x                         ≈⟨ laterʳ (x ∎ʷ) ⟩ʷ
  (later (λ { .force → x })  ≈⟨ later (λ { .force → size-preserving-transitivity-≈→trivial _≈⟨_⟩ʷ_ x y }) ⟩ʷ
  (later (λ { .force → y })  ≈⟨ laterˡ (y ∎ʷ) ⟩ʷ
  (y                         ∎ʷ))))
  where
  _∎ʷ = reflexive

-- If there is a transitivity proof for weak bisimilarity that is
-- size-preserving in both arguments, then the carrier type A is not
-- inhabited.

size-preserving-transitivity-≈→uninhabited :
  (∀ {i} x {y z : Delay A ∞} →
   [ i ] x ≈ y → [ i ] y ≈ z → [ i ] x ≈ z) →
  ¬ A
size-preserving-transitivity-≈→uninhabited trans x =
  now≉never (size-preserving-transitivity-≈→trivial trans (now x) never)

-- There is a fully size-preserving transitivity proof for expansion
-- iff A is uninhabited.

Transitivity-≳ = ∀ {i} {x y z : Delay A ∞} →
                 [ i ] x ≳ y → [ i ] y ≳ z → [ i ] x ≳ z

size-preserving-transitivity-≳⇔uninhabited : Transitivity-≳ ⇔ ¬ A
size-preserving-transitivity-≳⇔uninhabited = record
  { to   = Transitivity-≳   ↝⟨ id ⟩
           Transitivity-≳ˡ  ↝⟨ _⇔_.to size-preserving-transitivity-≳ˡ⇔uninhabited ⟩□
           ¬ A              □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≳ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Transitivity-≳   □
  }

-- There is a transitivity-like proof, taking expansion and weak
-- bisimilarity to weak bisimilarity, that preserves the size of the
-- first argument iff A is uninhabited.

Transitivity-≳≈ˡ = ∀ {i} {x y z : Delay A ∞} →
                   [ i ] x ≳ y → y ≈ z → [ i ] x ≈ z

size-preserving-transitivity-≳≈ˡ⇔uninhabited : Transitivity-≳≈ˡ ⇔ ¬ A
size-preserving-transitivity-≳≈ˡ⇔uninhabited = record
  { to   = Transitivity-≳≈ˡ  ↝⟨ _∘ ∼→ ⟩
           Transitivity-∼≈ˡ  ↝⟨ _⇔_.to size-preserving-transitivity-∼≈ˡ⇔uninhabited ⟩
           ¬ A               □
  ; from = ¬ A               ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≈ y)   ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Transitivity-≳≈ˡ  □
  }

-- There is a transitivity-like proof, taking expansion and weak
-- bisimilarity to weak bisimilarity, that preserves the size of both
-- arguments iff A is uninhabited.

Transitivity-≳≈ = ∀ {i} {x y z : Delay A ∞} →
                  [ i ] x ≳ y → [ i ] y ≈ z → [ i ] x ≈ z

size-preserving-transitivity-≳≈⇔uninhabited : Transitivity-≳≈ ⇔ ¬ A
size-preserving-transitivity-≳≈⇔uninhabited = record
  { to   = Transitivity-≳≈   ↝⟨ id ⟩
           Transitivity-≳≈ˡ  ↝⟨ _⇔_.to size-preserving-transitivity-≳≈ˡ⇔uninhabited ⟩
           ¬ A               □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Transitivity-≳≈  □
  }

-- There is a transitivity-like proof, taking weak bisimilarity and
-- the converse of expansion to weak bisimilarity, that preserves the
-- size of the second argument iff A is uninhabited.

Transitivity-≈≲ʳ = ∀ {i} {x y z : Delay A ∞} →
                   x ≈ y → [ i ] y ≲ z → [ i ] x ≈ z

size-preserving-transitivity-≈≲ʳ⇔uninhabited : Transitivity-≈≲ʳ ⇔ ¬ A
size-preserving-transitivity-≈≲ʳ⇔uninhabited =
  Transitivity-≈≲ʳ  ↝⟨ record { to   = λ trans x≳y y≈z → symmetric (trans (symmetric y≈z) x≳y)
                              ; from = λ trans x≈y y≲z → symmetric (trans y≲z (symmetric x≈y))
                              } ⟩
  Transitivity-≳≈ˡ  ↝⟨ size-preserving-transitivity-≳≈ˡ⇔uninhabited ⟩□
  ¬ A               □

-- There is a transitivity-like proof, taking weak bisimilarity and
-- the converse of expansion to weak bisimilarity, that preserves the
-- size of both arguments iff A is uninhabited.

Transitivity-≈≲ = ∀ {i} {x y z : Delay A ∞} →
                  [ i ] x ≈ y → [ i ] y ≲ z → [ i ] x ≈ z

size-preserving-transitivity-≈≲⇔uninhabited : Transitivity-≈≲ ⇔ ¬ A
size-preserving-transitivity-≈≲⇔uninhabited =
  Transitivity-≈≲  ↝⟨ record { to   = λ trans x≳y y≈z → symmetric (trans (symmetric y≈z) x≳y)
                             ; from = λ trans x≈y y≲z → symmetric (trans y≲z (symmetric x≈y))
                             } ⟩
  Transitivity-≳≈  ↝⟨ size-preserving-transitivity-≳≈⇔uninhabited ⟩□
  ¬ A              □

-- There is a transitivity-like proof, taking weak bisimilarity and
-- expansion to weak bisimilarity, that preserves the size of the
-- first argument iff A is uninhabited.

Transitivity-≈≳ˡ = ∀ {i} {x y z : Delay A ∞} →
                   [ i ] x ≈ y → y ≳ z → [ i ] x ≈ z

size-preserving-transitivity-≈≳ˡ⇔uninhabited : Transitivity-≈≳ˡ ⇔ ¬ A
size-preserving-transitivity-≈≳ˡ⇔uninhabited = record
  { to   = Transitivity-≈≳ˡ  ↝⟨ (λ trans x≈ly → trans x≈ly (laterˡ (reflexive _))) ⟩
           Laterʳ⁻¹-≈        ↝⟨ _⇔_.to size-preserving-laterʳ⁻¹-≈⇔uninhabited ⟩
           ¬ A               □
  ; from = ¬ A               ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≈ y)   ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Transitivity-≈≳ˡ  □
  }
