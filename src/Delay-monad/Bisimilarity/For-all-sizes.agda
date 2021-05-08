------------------------------------------------------------------------
-- Strong bisimilarity for partially defined values, along with a
-- proof showing that this relation is pointwise isomorphic to path
-- equality
------------------------------------------------------------------------

{-# OPTIONS --cubical --sized-types #-}

module Delay-monad.Bisimilarity.For-all-sizes where

open import Equality.Path hiding (ext)
open import Prelude
open import Prelude.Size

open import Bijection equality-with-J using (_↔_)

open import Delay-monad

private
  variable
    a : Level
    A : Type a
    x : A
    i : Size

mutual

  -- A variant of strong bisimilarity that relates values of any size,
  -- not only those of size ∞.
  --
  -- Note: I have not managed to prove that this relation is pointwise
  -- isomorphic to strong bisimilarity as defined in
  -- Delay-monad.Bisimilarity (when the relation is restricted to
  -- fully defined values).

  infix 4 [_]_∼ˢ_ [_]_∼ˢ′_

  data [_]_∼ˢ_ {A : Type a} (i : Size) :
               Delay A i → Delay A i → Type a where
    now   : [ i ] now x ∼ˢ now x
    later : {x y : Delay′ A i} →
            [ i ] x ∼ˢ′ y → [ i ] later x ∼ˢ later y

  record [_]_∼ˢ′_ {A : Type a}
                  (i : Size) (x y : Delay′ A i) : Type a where
    coinductive
    field
      force : {j : Size< i} → [ j ] x .force ∼ˢ y .force

open [_]_∼ˢ′_ public

mutual

  -- Strong bisimilarity is reflexive. Note that the proof is
  -- size-preserving.

  reflexiveˢ : (x : Delay A i) → [ i ] x ∼ˢ x
  reflexiveˢ (now x)   = now
  reflexiveˢ (later x) = later (reflexiveˢ′ x)

  reflexiveˢ′ : (x : Delay′ A i) → [ i ] x ∼ˢ′ x
  reflexiveˢ′ x .force = reflexiveˢ (x .force)

mutual

  -- Extensionality: Strong bisimilarity implies equality.

  ext : {x y : Delay A i} →
        [ i ] x ∼ˢ y → x ≡ y
  ext now       = refl
  ext (later p) = cong later (ext′ p)

  ext′ : {x y : Delay′ A i} →
         [ i ] x ∼ˢ′ y → x ≡ y
  ext′ p i .force = ext (p .force) i

mutual

  -- The extensionality proof maps reflexivity to reflexivity.

  ext-reflexiveˢ :
    (x : Delay A i) →
    ext (reflexiveˢ x) ≡ refl {x = x}
  ext-reflexiveˢ         (now x)   = refl
  ext-reflexiveˢ {i = i} (later x) =
    ext (reflexiveˢ (later x))         ≡⟨⟩
    cong later (ext′ (reflexiveˢ′ x))  ≡⟨ cong (cong later) (ext′-reflexiveˢ′ x) ⟩
    cong later refl                    ≡⟨⟩
    refl                               ∎

  ext′-reflexiveˢ′ :
    (x : Delay′ A i) →
    ext′ (reflexiveˢ′ x) ≡ refl {x = x}
  ext′-reflexiveˢ′ x i j .force = ext-reflexiveˢ (x .force) i j

-- Equality implies strong bisimilarity.

≡⇒∼ : {x y : Delay A i} → x ≡ y → [ i ] x ∼ˢ y
≡⇒∼ {x = x} eq = subst ([ _ ] x ∼ˢ_) eq (reflexiveˢ x)

≡⇒∼′ : {x y : Delay′ A i} → x ≡ y → [ i ] x ∼ˢ′ y
≡⇒∼′ eq .force = ≡⇒∼ (cong (λ x → x .force) eq)

private

  ≡⇒∼″ : {x y : Delay′ A i} → x ≡ y → [ i ] x ∼ˢ′ y
  ≡⇒∼″ {x = x} eq = subst ([ _ ] x ∼ˢ′_) eq (reflexiveˢ′ x)

-- The three lemmas above map reflexivity to reflexivity.

≡⇒∼-refl :
  {x : Delay A i} →
  ≡⇒∼ (refl {x = x}) ≡ reflexiveˢ x
≡⇒∼-refl {x = x} =
  ≡⇒∼ refl                                 ≡⟨⟩
  subst ([ _ ] x ∼ˢ_) refl (reflexiveˢ x)  ≡⟨ subst-refl ([ _ ] x ∼ˢ_) (reflexiveˢ x) ⟩∎
  reflexiveˢ x                             ∎

≡⇒∼′-refl :
  {x : Delay′ A i} →
  ≡⇒∼′ (refl {x = x}) ≡ reflexiveˢ′ x
≡⇒∼′-refl i .force = ≡⇒∼-refl i

private

  ≡⇒∼″-refl :
    {x : Delay′ A i} →
    ≡⇒∼″ (refl {x = x}) ≡ reflexiveˢ′ x
  ≡⇒∼″-refl {x = x} =
    ≡⇒∼″ refl                                  ≡⟨⟩
    subst ([ _ ] x ∼ˢ′_) refl (reflexiveˢ′ x)  ≡⟨ subst-refl ([ _ ] x ∼ˢ′_) (reflexiveˢ′ x) ⟩∎
    reflexiveˢ′ x                              ∎

  -- ≡⇒∼′ and ≡⇒″ are pointwise equal.

  ≡⇒∼′≡≡⇒∼″ :
    {x y : Delay′ A i} {eq : x ≡ y} →
    ≡⇒∼′ eq ≡ ≡⇒∼″ eq
  ≡⇒∼′≡≡⇒∼″ = elim
    (λ eq → ≡⇒∼′ eq ≡ ≡⇒∼″ eq)
    (λ x →
       ≡⇒∼′ refl      ≡⟨ ≡⇒∼′-refl ⟩
       reflexiveˢ′ x  ≡⟨ sym ≡⇒∼″-refl ⟩∎
       ≡⇒∼″ refl      ∎)
    _

private

  -- Extensionality and ≡⇒∼/≡⇒∼′ are inverses.

  ext∘≡⇒∼ :
    {x y : Delay A i}
    (eq : x ≡ y) → ext (≡⇒∼ eq) ≡ eq
  ext∘≡⇒∼ = elim
    (λ eq → ext (≡⇒∼ eq) ≡ eq)
    (λ x → ext (≡⇒∼ refl)      ≡⟨ cong ext ≡⇒∼-refl ⟩
           ext (reflexiveˢ x)  ≡⟨ ext-reflexiveˢ x ⟩∎
           refl                ∎)

  ext′∘≡⇒∼′ :
    {x y : Delay′ A i}
    (eq : x ≡ y) → ext′ (≡⇒∼′ eq) ≡ eq
  ext′∘≡⇒∼′ = elim
    (λ eq → ext′ (≡⇒∼′ eq) ≡ eq)
    (λ x → ext′ (≡⇒∼′ refl)      ≡⟨ cong ext′ ≡⇒∼′-refl ⟩
           ext′ (reflexiveˢ′ x)  ≡⟨ ext′-reflexiveˢ′ x ⟩∎
           refl                  ∎)

  mutual

    ≡⇒∼∘ext :
      {x y : Delay A i}
      (eq : [ i ] x ∼ˢ y) →
      ≡⇒∼ (ext eq) ≡ eq
    ≡⇒∼∘ext now =
      ≡⇒∼ (ext now)  ≡⟨⟩
      ≡⇒∼ refl       ≡⟨ ≡⇒∼-refl ⟩∎
      now            ∎
    ≡⇒∼∘ext (later {x = x} {y = y} p) =
      ≡⇒∼ (ext (later p))                                    ≡⟨⟩

      ≡⇒∼ (cong later (ext′ p))                              ≡⟨⟩

      subst ([ _ ] later x ∼ˢ_) (cong later (ext′ p))
        (later (reflexiveˢ′ x))                              ≡⟨ sym $ subst-∘ ([ _ ] later x ∼ˢ_) later _ {p = later (reflexiveˢ′ x)} ⟩

      subst (λ y → [ _ ] later x ∼ˢ later y) (ext′ p)
        (later (reflexiveˢ′ x))                              ≡⟨ elim¹
                                                                  (λ eq → subst (λ y → [ _ ] later x ∼ˢ later y) eq (later (reflexiveˢ′ x)) ≡
                                                                          later (subst ([ _ ] x ∼ˢ′_) eq (reflexiveˢ′ x))) (
          subst (λ y → [ _ ] later x ∼ˢ later y) refl
            (later (reflexiveˢ′ x))                                 ≡⟨ subst-refl (λ y → [ _ ] later x ∼ˢ later y) _ ⟩

          later (reflexiveˢ′ x)                                     ≡⟨ cong later $ sym $ subst-refl ([ _ ] x ∼ˢ′_) _ ⟩∎

          later (subst ([ _ ] x ∼ˢ′_) refl (reflexiveˢ′ x))         ∎)
                                                                  (ext′ p) ⟩
      later (subst ([ _ ] x ∼ˢ′_) (ext′ p) (reflexiveˢ′ x))  ≡⟨⟩

      later (≡⇒∼″ (ext′ p))                                  ≡⟨ cong later $ sym ≡⇒∼′≡≡⇒∼″ ⟩

      later (≡⇒∼′ (ext′ p))                                  ≡⟨ cong later (≡⇒∼′∘ext′ p) ⟩∎

      later p                                                ∎

    ≡⇒∼′∘ext′ :
      {x y : Delay′ A i}
      (eq : [ i ] x ∼ˢ′ y) →
      ≡⇒∼′ (ext′ eq) ≡ eq
    ≡⇒∼′∘ext′ eq i .force = ≡⇒∼∘ext (eq .force) i

-- Strong bisimilarity and equality are pointwise isomorphic.

∼↔≡ : {x y : Delay A i} → [ i ] x ∼ˢ y ↔ x ≡ y
∼↔≡ = record
  { surjection = record
    { logical-equivalence = record
      { to   = ext
      ; from = ≡⇒∼
      }
    ; right-inverse-of = ext∘≡⇒∼
    }
  ; left-inverse-of = ≡⇒∼∘ext
  }

∼′↔≡ : {x y : Delay′ A i} → [ i ] x ∼ˢ′ y ↔ x ≡ y
∼′↔≡ = record
  { surjection = record
    { logical-equivalence = record
      { to   = ext′
      ; from = ≡⇒∼′
      }
    ; right-inverse-of = ext′∘≡⇒∼′
    }
  ; left-inverse-of = ≡⇒∼′∘ext′
  }
