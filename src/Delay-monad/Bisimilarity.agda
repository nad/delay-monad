------------------------------------------------------------------------
-- A combined definition of strong and weak bisimilarity and
-- expansion, along with various properties
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

module Delay-monad.Bisimilarity where

open import Equality.Propositional as E using (_≡_)
open import Logical-equivalence using (_⇔_)
open import Prelude
open import Prelude.Size

open import Conat E.equality-with-J as Conat
  using (zero; suc; force; [_]_≤_)
open import Function-universe E.equality-with-J hiding (_∘_; Kind)

open import Delay-monad
open import Delay-monad.Bisimilarity.Kind

------------------------------------------------------------------------
-- The code below is defined for a fixed type A

module _ {a} {A : Type a} where

  ----------------------------------------------------------------------
  -- The relations

  mutual

    -- A combined definition of all three relations. The definition
    -- uses mixed induction and coinduction.

    infix 4 [_]_⟨_⟩_ [_]_⟨_⟩′_

    data [_]_⟨_⟩_ (i : Size) :
           Delay A ∞ → Kind → Delay A ∞ → Type a where
      now    : ∀ {k x} → [ i ] now x ⟨ k ⟩ now x
      later  : ∀ {k x y} →
               [ i ] force x ⟨ k ⟩′ force y →
               [ i ] later x ⟨ k ⟩ later y
      laterˡ : ∀ {k x y} →
               [ i ] force x ⟨ other k ⟩ y →
               [ i ] later x ⟨ other k ⟩ y
      laterʳ : ∀ {x y} →
               [ i ] x ⟨ other weak ⟩ force y →
               [ i ] x ⟨ other weak ⟩ later y

    record [_]_⟨_⟩′_ (i : Size)
             (x : Delay A ∞) (k : Kind) (y : Delay A ∞) : Type a where
      coinductive
      field
        force : {j : Size< i} → [ j ] x ⟨ k ⟩ y

  open [_]_⟨_⟩′_ public

  -- Strong bisimilarity.

  infix 4 [_]_∼_ [_]_∼′_ _∼_ _∼′_

  [_]_∼_ : Size → Delay A ∞ → Delay A ∞ → Type a
  [_]_∼_ = [_]_⟨ strong ⟩_

  [_]_∼′_ : Size → Delay A ∞ → Delay A ∞ → Type a
  [_]_∼′_ = [_]_⟨ strong ⟩′_

  _∼_ : Delay A ∞ → Delay A ∞ → Type a
  _∼_ = [ ∞ ]_∼_

  _∼′_ : Delay A ∞ → Delay A ∞ → Type a
  _∼′_ = [ ∞ ]_∼′_

  -- Expansion.

  infix 4 [_]_≳_ [_]_≳′_ _≳_ _≳′_

  [_]_≳_ : Size → Delay A ∞ → Delay A ∞ → Type a
  [_]_≳_ = [_]_⟨ other expansion ⟩_

  [_]_≳′_ : Size → Delay A ∞ → Delay A ∞ → Type a
  [_]_≳′_ = [_]_⟨ other expansion ⟩′_

  _≳_ : Delay A ∞ → Delay A ∞ → Type a
  _≳_ = [ ∞ ]_≳_

  _≳′_ : Delay A ∞ → Delay A ∞ → Type a
  _≳′_ = [ ∞ ]_≳′_

  -- The converse of expansion.

  infix 4 [_]_≲_ [_]_≲′_ _≲_ _≲′_

  [_]_≲_ : Size → Delay A ∞ → Delay A ∞ → Type a
  [_]_≲_ i = flip [ i ]_⟨ other expansion ⟩_

  [_]_≲′_ : Size → Delay A ∞ → Delay A ∞ → Type a
  [_]_≲′_ i = flip [ i ]_⟨ other expansion ⟩′_

  _≲_ : Delay A ∞ → Delay A ∞ → Type a
  _≲_ = [ ∞ ]_≲_

  _≲′_ : Delay A ∞ → Delay A ∞ → Type a
  _≲′_ = [ ∞ ]_≲′_

  -- Weak bisimilarity.

  infix 4 [_]_≈_ [_]_≈′_ _≈_ _≈′_

  [_]_≈_ : Size → Delay A ∞ → Delay A ∞ → Type a
  [_]_≈_ = [_]_⟨ other weak ⟩_

  [_]_≈′_ : Size → Delay A ∞ → Delay A ∞ → Type a
  [_]_≈′_ = [_]_⟨ other weak ⟩′_

  _≈_ : Delay A ∞ → Delay A ∞ → Type a
  _≈_ = [ ∞ ]_≈_

  _≈′_ : Delay A ∞ → Delay A ∞ → Type a
  _≈′_ = [ ∞ ]_≈′_

  ----------------------------------------------------------------------
  -- Conversions

  -- Strong bisimilarity is contained in the other relations (and
  -- itself).

  ∼→ : ∀ {k i x y} → [ i ] x ∼ y → [ i ] x ⟨ k ⟩ y
  ∼→ now       = now
  ∼→ (later p) = later λ { .force → ∼→ (force p) }

  -- Expansion is contained in weak bisimilarity (and expansion).

  ≳→ : ∀ {k i x y} → [ i ] x ≳ y → [ i ] x ⟨ other k ⟩ y
  ≳→ now        = now
  ≳→ (later p)  = later λ { .force → ≳→ (force p) }
  ≳→ (laterˡ p) = laterˡ (≳→ p)

  -- In some cases weak bisimilarity is contained in expansion (and
  -- itself).

  ≈→-now : ∀ {k i x y} → [ i ] x ≈ now y → [ i ] x ⟨ other k ⟩ now y
  ≈→-now now        = now
  ≈→-now (laterˡ p) = laterˡ (≈→-now p)

  -- In some cases all three relations are contained in strong
  -- bisimilarity.

  →∼-neverˡ : ∀ {k i x} → [ i ] never ⟨ k ⟩ x → [ i ] never ∼ x
  →∼-neverˡ (later  p) = later λ { .force → →∼-neverˡ (force p) }
  →∼-neverˡ (laterˡ p) = →∼-neverˡ p
  →∼-neverˡ (laterʳ p) = later λ { .force → →∼-neverˡ p }

  →∼-neverʳ : ∀ {k i x} → [ i ] x ⟨ k ⟩ never → [ i ] x ∼ never
  →∼-neverʳ (later  p) = later λ { .force → →∼-neverʳ (force p) }
  →∼-neverʳ (laterˡ p) = later λ { .force → →∼-neverʳ p }
  →∼-neverʳ (laterʳ p) = →∼-neverʳ p

  ----------------------------------------------------------------------
  -- Removing later constructors

  -- Later constructors can sometimes be removed.

  drop-laterʳ :
    ∀ {k i} {j : Size< i} {x y} →
    [ i ] x ⟨ other k ⟩ y →
    [ j ] x ⟨ other k ⟩ drop-later y
  drop-laterʳ now        = now
  drop-laterʳ (later  p) = laterˡ (force p)
  drop-laterʳ (laterʳ p) = p
  drop-laterʳ (laterˡ p) = laterˡ (drop-laterʳ p)

  drop-laterˡ :
    ∀ {i} {j : Size< i} {x y} →
    [ i ] x ≈ y →
    [ j ] drop-later x ≈ y
  drop-laterˡ now        = now
  drop-laterˡ (later  p) = laterʳ (force p)
  drop-laterˡ (laterʳ p) = laterʳ (drop-laterˡ p)
  drop-laterˡ (laterˡ p) = p

  drop-laterˡʳ :
    ∀ {k i} {j : Size< i} {x y} →
    [ i ] x ⟨ k ⟩ y →
    [ j ] drop-later x ⟨ k ⟩ drop-later y
  drop-laterˡʳ now        = now
  drop-laterˡʳ (later  p) = force p
  drop-laterˡʳ (laterʳ p) = drop-laterˡ p
  drop-laterˡʳ (laterˡ p) = drop-laterʳ p

  -- Special cases of the functions above.

  laterʳ⁻¹ : ∀ {k i} {j : Size< i} {x y} →
             [ i ] x ⟨ other k ⟩ later y →
             [ j ] x ⟨ other k ⟩ force y
  laterʳ⁻¹ = drop-laterʳ

  laterˡ⁻¹ : ∀ {i} {j : Size< i} {x y} →
             [ i ] later x ≈ y →
             [ j ] force x ≈ y
  laterˡ⁻¹ = drop-laterˡ

  later⁻¹ : ∀ {k i} {j : Size< i} {x y} →
            [ i ] later x ⟨ k ⟩ later y →
            [ j ] force x ⟨ k ⟩ force y
  later⁻¹ = drop-laterˡʳ

  -- The following size-preserving variant of laterʳ⁻¹ and laterˡ⁻¹
  -- can be defined.
  --
  -- Several other variants cannot be defined (unless A is
  -- uninhabited), see Delay-monad.Bisimilarity.Negative.

  laterˡʳ⁻¹ :
    ∀ {k i x y} →
    [ i ] later x ⟨ other k ⟩ force y →
    [ i ] force x ⟨ other k ⟩ later y →
    [ i ] force x ⟨ other k ⟩ force y
  laterˡʳ⁻¹ {k} {i} p q = laterˡʳ⁻¹′ p q E.refl E.refl
    where
    laterˡʳ⁻¹″ :
      ∀ {x′ y′ x y} →
      ({j : Size< i} → [ j ] x′ ⟨ other k ⟩ force y) →
      ({j : Size< i} → [ j ] force x ⟨ other k ⟩ y′) →
      x′ ≡ later x → y′ ≡ later y →
      [ i ] later x ⟨ other k ⟩ later y
    laterˡʳ⁻¹″ p q E.refl E.refl = later λ { .force → laterˡʳ⁻¹ p q }

    laterˡʳ⁻¹′ :
      ∀ {x′ y′ x y} →
      [ i ] later x ⟨ other k ⟩ y′ →
      [ i ] x′ ⟨ other k ⟩ later y →
      force x {j = ∞} ≡ x′ → force y ≡ y′ →
      [ i ] x′ ⟨ other k ⟩ y′
    laterˡʳ⁻¹′ (later  p) (later  q) ≡x′    ≡y′    = laterˡʳ⁻¹″ (force p)                (force q)                ≡x′ ≡y′
    laterˡʳ⁻¹′ (laterʳ p) (later  q) ≡x′    ≡y′    = laterˡʳ⁻¹″ (λ { {_} → laterˡ⁻¹ p }) (force q)                ≡x′ ≡y′
    laterˡʳ⁻¹′ (later  p) (laterˡ q) ≡x′    ≡y′    = laterˡʳ⁻¹″ (force p)                (λ { {_} → laterʳ⁻¹ q }) ≡x′ ≡y′
    laterˡʳ⁻¹′ (laterʳ p) (laterˡ q) ≡x′    ≡y′    = laterˡʳ⁻¹″ (λ { {_} → laterˡ⁻¹ p }) (λ { {_} → laterʳ⁻¹ q }) ≡x′ ≡y′
    laterˡʳ⁻¹′ (laterˡ p) _          E.refl E.refl = p
    laterˡʳ⁻¹′ _          (laterʳ q) E.refl ≡y′    = E.subst ([ i ] _ ⟨ _ ⟩_) ≡y′ q

  ----------------------------------------------------------------------
  -- Reflexivity, symmetry/antisymmetry, transitivity

  -- All three relations are reflexive.

  reflexive : ∀ {k i} x → [ i ] x ⟨ k ⟩ x
  reflexive (now _)   = now
  reflexive (later x) = later λ { .force → reflexive (force x) }

  -- Strong and weak bisimilarity are symmetric.

  symmetric :
    ∀ {k i x y} {¬≳ : if k ≟-Kind other expansion then ⊥ else ⊤} →
    [ i ] x ⟨ k ⟩ y → [ i ] y ⟨ k ⟩ x
  symmetric now                   = now
  symmetric (laterˡ {k = weak} p) = laterʳ (symmetric p)
  symmetric (laterʳ p)            = laterˡ (symmetric p)
  symmetric {¬≳ = ¬≳} (later p)   =
    later λ { .force → symmetric {¬≳ = ¬≳} (force p) }

  symmetric {¬≳ = ()} (laterˡ {k = expansion} _)

  -- Some special cases of symmetry hold for expansion.

  symmetric-neverˡ : ∀ {i x} → [ i ] never ≳ x → [ i ] x ≳ never
  symmetric-neverˡ = ∼→ ∘ symmetric ∘ →∼-neverˡ

  symmetric-neverʳ : ∀ {i x} → [ i ] x ≳ never → [ i ] never ≳ x
  symmetric-neverʳ = ∼→ ∘ symmetric ∘ →∼-neverʳ

  -- The expansion relation is antisymmetric (up to weak
  -- bisimilarity).

  antisymmetric-≳ : ∀ {i x y} → [ i ] x ≳ y → [ i ] y ≳ x → [ i ] x ≈ y
  antisymmetric-≳ p _ = ≳→ p

  -- Several more or less size-preserving variants of transitivity.
  --
  -- Many size-preserving variants cannot be defined (unless A is
  -- uninhabited), see Delay-monad.Bisimilarity.Negative.

  transitive-∼ʳ :
    ∀ {k i x y z}
      {¬≈ : if k ≟-Kind other weak then ⊥ else ⊤} →
    [ i ] x ⟨ k ⟩ y → [ i ] y ∼ z → [ i ] x ⟨ k ⟩ z
  transitive-∼ʳ           now        now       = now
  transitive-∼ʳ {¬≈ = ¬≈} (laterˡ p) q         = laterˡ
                                                   (transitive-∼ʳ {¬≈ = ¬≈} p q)
  transitive-∼ʳ {¬≈ = ()} (laterʳ _) _
  transitive-∼ʳ {¬≈ = ¬≈} (later  p) (later q) =
    later λ { .force → transitive-∼ʳ {¬≈ = ¬≈} (force p) (force q) }

  transitive-∼ˡ :
    ∀ {k i x y z} →
    x ∼ y → [ i ] y ⟨ k ⟩ z → [ i ] x ⟨ k ⟩ z
  transitive-∼ˡ now       now        = now
  transitive-∼ˡ (later p) (later q)  = later λ { .force →
                                         transitive-∼ˡ (force p) (force q) }
  transitive-∼ˡ (later p) (laterˡ q) = laterˡ (transitive-∼ˡ (force p) q)
  transitive-∼ˡ p         (laterʳ q) = laterʳ (transitive-∼ˡ p q)

  transitive-∞∼ʳ :
    ∀ {k i x y z} →
    [ i ] x ⟨ k ⟩ y → y ∼ z → [ i ] x ⟨ k ⟩ z
  transitive-∞∼ʳ now        now       = now
  transitive-∞∼ʳ (later p)  (later q) = later λ { .force →
                                          transitive-∞∼ʳ (force p) (force q) }
  transitive-∞∼ʳ (laterˡ p) q         = laterˡ (transitive-∞∼ʳ p q)
  transitive-∞∼ʳ (laterʳ p) (later q) = laterʳ (transitive-∞∼ʳ p (force q))

  transitive-≳ˡ :
    ∀ {k i x y z} →
    x ≳ y → [ i ] y ⟨ other k ⟩ z → [ i ] x ⟨ other k ⟩ z
  transitive-≳ˡ now        now        = now
  transitive-≳ˡ (later p)  (later q)  = later λ { .force →
                                          transitive-≳ˡ (force p) (force q) }
  transitive-≳ˡ (later p)  (laterˡ q) = laterˡ (transitive-≳ˡ (force p) q)
  transitive-≳ˡ (laterˡ p) q          = laterˡ (transitive-≳ˡ p q)
  transitive-≳ˡ p          (laterʳ q) = laterʳ (transitive-≳ˡ p q)

  transitive-≈≲ :
    ∀ {i x y z} →
    [ i ] x ≈ y → y ≲ z → [ i ] x ≈ z
  transitive-≈≲ p q = symmetric (transitive-≳ˡ q (symmetric p))

  transitive-≈-now :
    ∀ {i x′ y z} →
    let x = now x′ in
    [ i ] x ≈ y → y ≈ z → [ i ] x ≈ z
  transitive-≈-now now        now        = now
  transitive-≈-now (laterʳ p) q          = transitive-≈-now p (laterˡ⁻¹ q)
  transitive-≈-now p          (laterʳ q) = laterʳ (transitive-≈-now p q)

  mutual

    transitive-≈-later :
      ∀ {i x′ y z} →
      let x = later x′ in
      x ≈ y → y ≈ z → [ i ] x ≈ z
    transitive-≈-later p          (later q)  = later λ { .force →
                                                 transitive-≈ (later⁻¹ p) (force q) }
    transitive-≈-later p          (laterʳ q) = laterʳ (transitive-≈-later p q)
    transitive-≈-later p          (laterˡ q) = transitive-≈ (laterʳ⁻¹ p) q
    transitive-≈-later (laterˡ p) q          = laterˡ (transitive-≈ p q)

    transitive-≈ : ∀ {i x y z} → x ≈ y → y ≈ z → [ i ] x ≈ z
    transitive-≈ {x = now   x} p q = transitive-≈-now   p q
    transitive-≈ {x = later x} p q = transitive-≈-later p q

  -- Equational reasoning combinators.

  infix  -1 _∎ finally finally-≳ finally-≈
  infixr -2 step-∼ˡ step-∼∼ step-≳∼ step-≈∼ step-?∼ step-≳ˡ step-≈
            _≳⟨⟩_ step-≡ˡ _∼⟨⟩_

  _∎ : ∀ {k i} x → [ i ] x ⟨ k ⟩ x
  _∎ = reflexive

  finally : ∀ {k i} x y →
            [ i ] x ⟨ k ⟩ y → [ i ] x ⟨ k ⟩ y
  finally _ _ x?y = x?y

  syntax finally x y x≈y = x ?⟨ x≈y ⟩∎ y ∎

  finally-≳ : ∀ {i} x y →
              [ i ] x ≳ y → [ i ] x ≳ y
  finally-≳ _ _ x≳y = x≳y

  syntax finally-≳ x y x≳y = x ≳⟨ x≳y ⟩∎ y ∎

  finally-≈ : ∀ {i} x y →
              [ i ] x ≈ y → [ i ] x ≈ y
  finally-≈ _ _ x≈y = x≈y

  syntax finally-≈ x y x≈y = x ≈⟨ x≈y ⟩∎ y ∎

  step-∼ˡ : ∀ {k i} x {y z} →
            [ i ] y ⟨ k ⟩ z → x ∼ y → [ i ] x ⟨ k ⟩ z
  step-∼ˡ _ y⟨⟩z x∼y = transitive-∼ˡ x∼y y⟨⟩z

  syntax step-∼ˡ x y⟨⟩z x∼y = x ∼⟨ x∼y ⟩ y⟨⟩z

  step-∼∼ : ∀ {i} x {y z} →
            [ i ] y ∼ z → [ i ] x ∼ y → [ i ] x ∼ z
  step-∼∼ _ y∼z x∼y = transitive-∼ʳ x∼y y∼z

  syntax step-∼∼ x y∼z x∼y = x ∼⟨ x∼y ⟩∼ y∼z

  step-≳∼ : ∀ {i} x {y z} →
            [ i ] y ∼ z → [ i ] x ≳ y → [ i ] x ≳ z
  step-≳∼ _ y∼z x≳y = transitive-∼ʳ x≳y y∼z

  syntax step-≳∼ x y∼z x≳y = x ≳⟨ x≳y ⟩∼ y∼z

  step-≈∼ : ∀ {i} x {y z} →
            y ∼ z → [ i ] x ≈ y → [ i ] x ≈ z
  step-≈∼ _ y∼z x≈y = transitive-∞∼ʳ x≈y y∼z

  syntax step-≈∼ x y∼z x≈y = x ≈⟨ x≈y ⟩∼ y∼z

  step-?∼ : ∀ {k i} x {y z} →
            y ∼ z → [ i ] x ⟨ k ⟩ y → [ i ] x ⟨ k ⟩ z
  step-?∼ _ y∼z x?y = transitive-∞∼ʳ x?y y∼z

  syntax step-?∼ x y∼z x?y = x ?⟨ x?y ⟩∼ y∼z

  step-≳ˡ : ∀ {k i} x {y z} →
            [ i ] y ⟨ other k ⟩ z → x ≳ y →
            [ i ] x ⟨ other k ⟩ z
  step-≳ˡ _ y≳≈z x≳y = transitive-≳ˡ x≳y y≳≈z

  syntax step-≳ˡ x y≳≈z x≳y = x ≳⟨ x≳y ⟩ y≳≈z

  step-≈ : ∀ {i} x {y z} →
           y ≈ z → x ≈ y → [ i ] x ≈ z
  step-≈ _ y≈z x≈y = transitive-≈ x≈y y≈z

  syntax step-≈ x y≈z x≈y = x ≈⟨ x≈y ⟩ y≈z

  _≳⟨⟩_ : ∀ {k i} x {y} →
          [ i ] drop-later x ⟨ other k ⟩ y → [ i ] x ⟨ other k ⟩ y
  now _   ≳⟨⟩ p = p
  later _ ≳⟨⟩ p = laterˡ p

  step-≡ˡ : ∀ {k i} x {y z} →
            [ i ] y ⟨ k ⟩ z → x ≡ y → [ i ] x ⟨ k ⟩ z
  step-≡ˡ _ y⟨⟩z E.refl = y⟨⟩z

  syntax step-≡ˡ x y⟨⟩z x≡y = x ≡⟨ x≡y ⟩ y⟨⟩z

  _∼⟨⟩_ : ∀ {k i} x {y} →
          [ i ] x ⟨ k ⟩ y → [ i ] x ⟨ k ⟩ y
  _ ∼⟨⟩ x≈y = x≈y

  ------------------------------------------------------------------------
  -- Some results related to the steps function

  -- If x and y are strongly bisimilar, then they contain the same
  -- number of later constructors.

  steps-cong :
    ∀ {x y i} → [ i ] x ∼ y → Conat.[ i ] steps x ∼ steps y
  steps-cong now       = zero
  steps-cong (later p) = suc λ { .force → steps-cong (p .force) }

  -- If y is an expansion of x, then it contains at least as many
  -- later constructors as x.

  steps-mono :
    ∀ {x y i} → [ i ] x ≲ y → [ i ] steps x ≤ steps y
  steps-mono now                        = zero
  steps-mono (later p)                  = suc λ { .force →
                                            steps-mono (p .force) }
  steps-mono (laterˡ {x = x} {y = y} p) =
    steps y           ≤⟨ steps-mono p ⟩
    steps (x .force)  ≤⟨ Conat.≤suc ⟩
    steps (later x)   ∎≤
    where
    open Conat using (step-≤; _∎≤)

  -- The computation y is an expansion of x iff x and y are weakly
  -- bisimilar and y contains at least as many later constructors
  -- as x.

  ≲⇔≈×steps≤steps :
    ∀ {i x y} →
    [ i ] x ≲ y ⇔ [ i ] x ≈ y × [ i ] steps x ≤ steps y
  ≲⇔≈×steps≤steps = record
    { to   = λ p → symmetric (≳→ p) , steps-mono p
    ; from = uncurry from
    }
    where
    from :
      ∀ {x y i} →
      [ i ] x ≈ y →
      [ i ] steps x ≤ steps y →
      [ i ] x ≲ y
    from {now _}             p zero    = ≈→-now (symmetric p)
    from {later _} {now _}   _ ()
    from {later _} {later _} p (suc q) =
      later λ { .force → from (later⁻¹ p) (q .force) }

  ----------------------------------------------------------------------
  -- Some results related to negation

  -- The computation never is not related to now x.

  never≉now : ∀ {k i x} → ¬ [ i ] never ⟨ k ⟩ now x
  never≉now (laterˡ p) = never≉now p

  -- The computation now x is not related to never.

  now≉never : ∀ {k i x} → ¬ [ i ] now x ⟨ k ⟩ never
  now≉never (laterʳ p) = now≉never p

  -- If A is uninhabited, then the three relations defined above are
  -- trivial.

  uninhabited→trivial : ∀ {k i} → ¬ A → ∀ x y → [ i ] x ⟨ k ⟩ y
  uninhabited→trivial ¬A (now   x) _         = ⊥-elim (¬A x)
  uninhabited→trivial ¬A (later x) (now   y) = ⊥-elim (¬A y)
  uninhabited→trivial ¬A (later x) (later y) =
    later λ { .force → uninhabited→trivial ¬A (force x) (force y) }

  -- Expansion and weak bisimilarity are not pointwise propositional.

  ¬-≳≈-propositional :
    ∀ {k} → ¬ (∀ {x y} → E.Is-proposition ([ ∞ ] x ⟨ other k ⟩ y))
  ¬-≳≈-propositional {k} =
    (∀ {x y} → E.Is-proposition ([ ∞ ] x ⟨ other k ⟩ y))  ↝⟨ (λ prop → prop {x = never} {y = never}) ⟩
    E.Is-proposition ([ ∞ ] never ⟨ other k ⟩ never)      ↝⟨ (λ irr → irr _ _) ⟩
    proof₁ ≡ proof₂                                       ↝⟨ (λ ()) ⟩□
    ⊥₀                                                    □
    where
    proof₁ : ∀ {i} → [ i ] never ⟨ other k ⟩ never
    proof₁ = later λ { .force → proof₁ }

    proof₂ : ∀ {i} → [ i ] never ⟨ other k ⟩ never
    proof₂ = laterˡ proof₁

------------------------------------------------------------------------
-- A statement of extensionality for strong bisimilarity

-- A statement of extensionality: strongly bisimilar computations are
-- equal.

Extensionality : (ℓ : Level) → Type (lsuc ℓ)
Extensionality a =
  {A : Type a} {x y : Delay A ∞} → x ∼ y → x ≡ y

-- Another form of extensionality.

Extensionality′ : (ℓ : Level) → Type (lsuc ℓ)
Extensionality′ a =
  {A : Type a} {x y : Delay′ A ∞} → force x ∼′ force y → x ≡ y

-- The latter form of extensionality implies the former.

Extensionality′→Extensionality :
  ∀ {ℓ} → Extensionality′ ℓ → Extensionality ℓ
Extensionality′→Extensionality ext {x = x} {y = y} p =
  E.cong (λ x → force x)
         (ext {x = λ { .force → x }} {y = λ { .force → y }}
              λ { .force → p })
