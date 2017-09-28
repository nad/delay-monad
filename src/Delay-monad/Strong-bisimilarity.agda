------------------------------------------------------------------------
-- Strong bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Delay-monad.Strong-bisimilarity where

open import Equality.Propositional using (_≡_; subst; cong; sym)
open import Prelude

open import Delay-monad

module _ {a} {A : Set a} where

  -- Strong bisimilarity.

  infix 4 [_]_∼_ [_]_∼′_ _∼_ _∼′_

  mutual

    data [_]_∼_ (i : Size) : (x y : Delay A ∞) → Set a where
      now   : ∀ {x} → [ i ] now x ∼ now x
      later : ∀ {x y} →
              [ i ] force x ∼′ force y →
              [ i ] later x ∼  later y

    record [_]_∼′_ (i : Size) (x y : Delay A ∞) : Set a where
      coinductive
      field
        force : {j : Size< i} → [ j ] x ∼ y

  open [_]_∼′_ public

  _∼_ : Delay A ∞ → Delay A ∞ → Set a
  _∼_ = [ ∞ ]_∼_

  _∼′_ : Delay A ∞ → Delay A ∞ → Set a
  _∼′_ = [ ∞ ]_∼′_

-- A statement of extensionality: strongly bisimilar computations are
-- equal.

Extensionality : (ℓ : Level) → Set (lsuc ℓ)
Extensionality a =
  {A : Set a} {x y : Delay A ∞} → x ∼ y → x ≡ y

-- Another form of extensionality.

Extensionality′ : (ℓ : Level) → Set (lsuc ℓ)
Extensionality′ a =
  {A : Set a} {x y : Delay′ A ∞} → force x ∼′ force y → x ≡ y

-- The latter form of extensionality implies the former.

Extensionality′→Extensionality :
  ∀ {ℓ} → Extensionality′ ℓ → Extensionality ℓ
Extensionality′→Extensionality ext {x = x} {y = y} p =
  cong (λ x → force x)
       (ext {x = λ { .force → x }} {y = λ { .force → y }}
            λ { .force → p })

module _ {a} {A : Set a} where

  -- Strong bisimilarity is reflexive.

  reflexive : ∀ {i} (x : Delay A ∞) → [ i ] x ∼ x
  reflexive (now x)   = now
  reflexive (later x) = later λ { .force → reflexive (force x) }

  -- Strong bisimilarity is symmetric.

  symmetric : ∀ {i} {x y : Delay A ∞} →
              [ i ] x ∼ y → [ i ] y ∼ x
  symmetric now       = now
  symmetric (later p) = later λ { .force → symmetric (force p) }

  -- Strong bisimilarity is transitive.

  transitive : ∀ {i} {x y z : Delay A ∞} →
               [ i ] x ∼ y → [ i ] y ∼ z → [ i ] x ∼ z
  transitive now       now       = now
  transitive (later p) (later q) =
    later λ { .force → transitive (force p) (force q) }

  -- Some equational reasoning combinators.

  infix  -1 finally-∼ _∎∼
  infixr -2 _∼⟨_⟩_ _∼⟨⟩_ _≡⟨_⟩∼_

  _∎∼ : ∀ {i} (x : Delay A ∞) → [ i ] x ∼ x
  _∎∼ = reflexive

  _∼⟨_⟩_ : ∀ {i} (x : Delay A ∞) {y z} →
           [ i ] x ∼ y → [ i ] y ∼ z → [ i ] x ∼ z
  _ ∼⟨ p ⟩ q = transitive p q

  _∼⟨⟩_ : ∀ {i} (x : Delay A ∞) {y} →
          [ i ] x ∼ y → [ i ] x ∼ y
  _ ∼⟨⟩ p = p

  _≡⟨_⟩∼_ : ∀ {i} (x : Delay A ∞) {y z} →
            x ≡ y → [ i ] y ∼ z → [ i ] x ∼ z
  _≡⟨_⟩∼_ {i} _ p q = subst ([ i ]_∼ _) (sym p) q

  finally-∼ : ∀ {i} (x y : Delay A ∞) →
              [ i ] x ∼ y → [ i ] x ∼ y
  finally-∼ _ _ p = p

  syntax finally-∼ x y p = x ∼⟨ p ⟩∎ y ∎
