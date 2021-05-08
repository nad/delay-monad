------------------------------------------------------------------------
-- An observation about weak bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

module Delay-monad.Bisimilarity.Observation where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude
open import Prelude.Size

open import Function-universe equality-with-J as F hiding (_∘_)
open import H-level.Closure equality-with-J

------------------------------------------------------------------------
-- The D type

mutual

  -- A mixed inductive-coinductive type.

  data D (i : Size) : Type where
    -- Output a boolean and continue. Note that this constructor is
    -- inductive.
    put : Bool → D i → D i

    -- Wait. The intention is that finite delay should not be
    -- "observable" (as captured by weak bisimilarity).
    later : D′ i → D i

  record D′ (i : Size) : Type where
    coinductive
    field
      force : {j : Size< i} → D j

open D′ public

private
  variable
    b b′  : Bool
    n     : ℕ
    i     : Size
    x y z : D ∞
    x′ y′ : D′ ∞

-- Making put inductive is a bit strange, because one can construct a
-- coinductive variant of it by using later.

put′ : Bool → D′ i → D i
put′ b x = later λ { .force → put b (x .force) }

------------------------------------------------------------------------
-- Weak bisimilarity

-- The output relation: x [ n ]≡ b means that x can output at least n
-- times, and the n-th output is b.

data _[_]≡_ : D ∞ → ℕ → Bool → Type where
  put-zero : put b x [ zero ]≡ b
  put-suc  : x [ n ]≡ b → put b′ x [ suc n ]≡ b
  later    : x′ .force [ n ]≡ b → later x′ [ n ]≡ b

-- The output relation is propositional.

[]≡-propositional : Is-proposition (x [ n ]≡ b)
[]≡-propositional {b = true}  put-zero put-zero = refl
[]≡-propositional {b = false} put-zero put-zero = refl
[]≡-propositional (put-suc p) (put-suc q) =
  cong put-suc ([]≡-propositional p q)
[]≡-propositional (later p) (later q) =
  cong later ([]≡-propositional p q)

-- Weak bisimilarity. Two computations are weakly bisimilar if the
-- output relation cannot distinguish between them.

_≈_ : D ∞ → D ∞ → Type
x ≈ y = ∀ {n b} → x [ n ]≡ b ⇔ y [ n ]≡ b

-- Weak bisimilarity is propositional (assuming extensionality).

≈-propositional :
  Extensionality lzero lzero →
  Is-proposition (x ≈ y)
≈-propositional ext =
  implicit-Π-closure ext 1 λ _ →
  implicit-Π-closure ext 1 λ _ →
  ⇔-closure ext 1 []≡-propositional []≡-propositional

-- The put constructor and the function put′ are closely related.

put≈put′ : put b (x′ .force) ≈ put′ b x′
put≈put′ ._⇔_.to   q         = later q
put≈put′ ._⇔_.from (later q) = q

-- Weak bisimilarity is an equivalence relation.

reflexive-≈ : x ≈ x
reflexive-≈ = F.id

symmetric-≈ : x ≈ y → y ≈ x
symmetric-≈ x≈y = F.inverse x≈y

transitive-≈ : x ≈ y → y ≈ z → x ≈ z
transitive-≈ x≈y y≈z = y≈z F.∘ x≈y

-- The later constructor can be removed to the left and to the right.

laterˡ⁻¹ : later x′ ≈ y → x′ .force ≈ y
laterˡ⁻¹ p ._⇔_.to   q = _⇔_.to p (later q)
laterˡ⁻¹ p ._⇔_.from q with _⇔_.from p q
…                      | later q′ = q′

laterʳ⁻¹ : x ≈ later y′ → x ≈ y′ .force
laterʳ⁻¹ = symmetric-≈ ∘ laterˡ⁻¹ ∘ symmetric-≈

later⁻¹ : later x′ ≈ later y′ → x′ .force ≈ y′ .force
later⁻¹ = laterˡ⁻¹ ∘ laterʳ⁻¹

-- The put constructor can be removed if it is removed on both sides
-- at the same time.

put⁻¹ : put b x ≈ put b′ y → x ≈ y
put⁻¹ p ._⇔_.to   q with _⇔_.to p (put-suc q)
…                   | put-suc q′ = q′
put⁻¹ p ._⇔_.from q with _⇔_.from p (put-suc q)
…                   | put-suc q′ = q′

------------------------------------------------------------------------
-- Not weak bisimilarity

module Not-weak-bisimilarity where

  mutual

    infix 4 [_]_≈_ [_]_≈′_

    -- After having seen the definition of weak bisimilarity in
    -- Delay-monad.Bisimilarity one might believe that weak
    -- bisimilarity for D can be defined in the following way:

    data [_]_≈_ (i : Size) : D ∞ → D ∞ → Type where
      put    : [ i ] x ≈ y → [ i ] put b x ≈ put b y
      later  : [ i ] x′ .force ≈′ y′ .force → [ i ] later x′ ≈ later y′
      laterˡ : [ i ] x′ .force ≈ y → [ i ] later x′ ≈ y
      laterʳ : [ i ] x ≈ y′ .force → [ i ] x ≈ later y′

    record [_]_≈′_ (i : Size) (x y : D ∞) : Type where
      coinductive
      field
        force : {j : Size< i} → [ j ] x ≈ y

  open [_]_≈′_ public

  -- The relation [ i ]_≈_ is reflexive and symmetric.

  reflexive-[]≈ : [ i ] x ≈ x
  reflexive-[]≈ {x = put _ _} = put reflexive-[]≈
  reflexive-[]≈ {x = later _} = later λ { .force → reflexive-[]≈ }

  symmetric-[]≈ : [ i ] x ≈ y → [ i ] y ≈ x
  symmetric-[]≈ (put p)    = put (symmetric-[]≈ p)
  symmetric-[]≈ (later p)  = later λ { .force →
                               symmetric-[]≈ (p .force) }
  symmetric-[]≈ (laterˡ p) = laterʳ (symmetric-[]≈ p)
  symmetric-[]≈ (laterʳ p) = laterˡ (symmetric-[]≈ p)

  -- However, the relation [ ∞ ]_≈_ is not transitive.

  ¬-transitive-≈ :
    ¬ (∀ {x y z} → [ ∞ ] x ≈ y → [ ∞ ] y ≈ z → [ ∞ ] x ≈ z)
  ¬-transitive-≈ trans = x≉z x≈z
    where
    x̲ : D i
    x̲ = later λ { .force → put true (put true x̲) }

    y̲ : D i
    y̲ = later λ { .force → put true y̲ }

    z̲ : D i
    z̲ = put true (later λ { .force → put true z̲ })

    x≈y : [ i ] x̲ ≈ y̲
    x≈y = later λ { .force → put (laterʳ (put x≈y)) }

    y≈z : [ i ] y̲ ≈ z̲
    y≈z = laterˡ (put (later λ { .force → put y≈z }))

    x≉z : ¬ [ ∞ ] x̲ ≈ z̲
    x≉z (laterˡ (put (laterʳ (put p)))) = x≉z p

    x≈z : [ ∞ ] x̲ ≈ z̲
    x≈z = trans x≈y y≈z

  -- Thus the two relations _≈_ and [ ∞ ]_≈_ are not pointwise
  -- logically equivalent.

  ¬≈⇔[]≈ : ¬ (∀ {x y} → x ≈ y ⇔ [ ∞ ] x ≈ y)
  ¬≈⇔[]≈ =
    (∀ {x y} → x ≈ y ⇔ [ ∞ ] x ≈ y)                        ↝⟨ (λ hyp x≈y y≈z → _⇔_.to hyp (transitive-≈ (_⇔_.from hyp x≈y) (_⇔_.from hyp y≈z))) ⟩
    (∀ {x y z} → [ ∞ ] x ≈ y → [ ∞ ] y ≈ z → [ ∞ ] x ≈ z)  ↝⟨ ¬-transitive-≈ ⟩□
    ⊥                                                      □

  -- The relation [ ∞ ]_≈_ is contained in _≈_.

  []≈→≈ : [ ∞ ] x ≈ y → x ≈ y
  []≈→≈ = λ p → record { to = ≈→→ p; from = ≈→→ (symmetric-[]≈ p) }
    where
    ≈→→ : [ ∞ ] x ≈ y → x [ n ]≡ b → y [ n ]≡ b
    ≈→→ (put p)    put-zero    = put-zero
    ≈→→ (put p)    (put-suc q) = put-suc (≈→→ p q)
    ≈→→ (later p)  (later q)   = later (≈→→ (p .force) q)
    ≈→→ (laterˡ p) (later q)   = ≈→→ p q
    ≈→→ (laterʳ p) q           = later (≈→→ p q)

  -- The relation _≈_ is not contained in [ ∞ ]_≈_.

  ¬≈→[]≈ : ¬ (∀ {x y} → x ≈ y → [ ∞ ] x ≈ y)
  ¬≈→[]≈ =
    (∀ {x y} → x ≈ y → [ ∞ ] x ≈ y)  ↝⟨ (λ hyp → record { to = hyp; from = []≈→≈ }) ⟩
    (∀ {x y} → x ≈ y ⇔ [ ∞ ] x ≈ y)  ↝⟨ ¬≈⇔[]≈ ⟩□
    ⊥                                □

------------------------------------------------------------------------
-- An alternative definition of weak bisimilarity

mutual

  infix 4 [_]_≈_ [_]_≈′_

  -- The problem with Not-weak-bisimilarity.[_]_≈_ is that its put
  -- constructor is inductive. The put constructor of D is inductive,
  -- but as noted above (put′, put≈put′) this is a bit strange, and it
  -- might make more sense to make put coinductive.
  --
  -- The following definition of weak bisimilarity uses a coinductive
  -- put constructor.

  data [_]_≈_ (i : Size) : D ∞ → D ∞ → Type where
    put    : [ i ] x ≈′ y → [ i ] put b x ≈ put b y
    later  : [ i ] x′ .force ≈′ y′ .force → [ i ] later x′ ≈ later y′
    laterˡ : [ i ] x′ .force ≈ y → [ i ] later x′ ≈ y
    laterʳ : [ i ] x ≈ y′ .force → [ i ] x ≈ later y′

  record [_]_≈′_ (i : Size) (x y : D ∞) : Type where
    coinductive
    field
      force : {j : Size< i} → [ j ] x ≈ y

open [_]_≈′_ public

-- The relation [ ∞ ]_≈_ is not propositional.

¬-≈[]-propositional : ¬ (∀ {x y} → Is-proposition ([ ∞ ] x ≈ y))
¬-≈[]-propositional =
  (∀ {x y} → Is-proposition ([ ∞ ] x ≈ y))  ↝⟨ (λ prop → prop _ _) ⟩
  proof₁ ≡ proof₂                           ↝⟨ (λ ()) ⟩□
  ⊥                                         □
  where
  never : D i
  never = later λ { .force → never }

  proof₁ : ∀ {i} → [ i ] never ≈ never
  proof₁ = later λ { .force → proof₁ }

  proof₂ : ∀ {i} → [ i ] never ≈ never
  proof₂ = laterˡ proof₁

-- The relation [ i ]_≈_ is reflexive and symmetric.

reflexive-[]≈ : [ i ] x ≈ x
reflexive-[]≈ {x = put _ _} = put   λ { .force → reflexive-[]≈ }
reflexive-[]≈ {x = later _} = later λ { .force → reflexive-[]≈ }

symmetric-[]≈ : [ i ] x ≈ y → [ i ] y ≈ x
symmetric-[]≈ (put p)    = put   λ { .force → symmetric-[]≈ (p .force) }
symmetric-[]≈ (later p)  = later λ { .force → symmetric-[]≈ (p .force) }
symmetric-[]≈ (laterˡ p) = laterʳ (symmetric-[]≈ p)
symmetric-[]≈ (laterʳ p) = laterˡ (symmetric-[]≈ p)

-- The two relations _≈_ and [ ∞ ]_≈_ are pointwise logically
-- equivalent.

≈⇔[]≈ : x ≈ y ⇔ [ ∞ ] x ≈ y
≈⇔[]≈ = record
  { to   = to _ _
  ; from = λ p → record { to = from p; from = from (symmetric-[]≈ p) }
  }
  where
  from : [ ∞ ] x ≈ y → x [ n ]≡ b → y [ n ]≡ b
  from (put p)    put-zero    = put-zero
  from (put p)    (put-suc q) = put-suc (from (p .force) q)
  from (later p)  (later q)   = later (from (p .force) q)
  from (laterˡ p) (later q)   = from p q
  from (laterʳ p) q           = later (from p q)

  mutual

    to : ∀ x y → x ≈ y → [ i ] x ≈ y
    to (put b x) y         p = symmetric-[]≈ (to′ (symmetric-≈ p)
                                                  (_⇔_.to p put-zero))
    to x         (put b y) p = to′ p (_⇔_.from p put-zero)
    to (later x) (later y) p = later λ { .force → to _ _ (later⁻¹ p) }

    to′ : x ≈ put b y → x [ zero ]≡ b → [ i ] x ≈ put b y
    to′ p put-zero  = put λ { .force → to _ _ (put⁻¹ p) }
    to′ p (later q) = laterˡ (to′ (laterˡ⁻¹ p) q)

-- The relation [ ∞ ]_≈_ is transitive.

transitive-[]≈ : [ ∞ ] x ≈ y → [ ∞ ] y ≈ z → [ ∞ ] x ≈ z
transitive-[]≈ p q =
  _⇔_.to ≈⇔[]≈ (transitive-≈ (_⇔_.from ≈⇔[]≈ p) (_⇔_.from ≈⇔[]≈ q))
