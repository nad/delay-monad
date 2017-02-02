------------------------------------------------------------------------
-- Partiality algebras
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- The code below uses ideas and concepts from "Inductive types in
-- homotopy type theory" by Awodey, Gambino and Sojakova, and
-- "Inductive Types in Homotopy Type Theory" by Sojakova.

module Partiality-algebra where

open import Equality.Propositional
open import Interval using (ext)
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (id) renaming (_∘_ to _⊚_)

open import Bijection equality-with-J as Bijection using (_↔_)
open import Category equality-with-J as Category
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level hiding (Type)
open import H-level.Closure equality-with-J
open import Structure-identity-principle equality-with-J
open import Surjection equality-with-J using (_↠_)
open import Univalence-axiom equality-with-J

------------------------------------------------------------------------
-- Partiality algebras

-- Partiality algebras for certain universe levels and types, with a
-- certain underlying type.

record Partiality-algebra-with
  {a p} (Type : Set p) q (A : Set a) : Set (a ⊔ p ⊔ lsuc q) where

  -- A binary relation on the type.

  infix 4 _⊑_ _⊒_

  field
    _⊑_ : Type → Type → Set q

  _⊒_ : Type → Type → Set q
  _⊒_ x y = y ⊑ x

  -- Increasing sequences.

  Increasing-sequence : Set (p ⊔ q)
  Increasing-sequence = ∃ λ (f : ℕ → Type) → ∀ n → f n ⊑ f (suc n)

  -- Projection functions for Increasing-sequence.

  infix 30 _[_]

  _[_] : Increasing-sequence → ℕ → Type
  _[_] s n = proj₁ s n

  increasing : (s : Increasing-sequence) →
               ∀ n → (s [ n ]) ⊑ (s [ suc n ])
  increasing = proj₂

  -- Upper bounds.

  Is-upper-bound : Increasing-sequence → Type → Set q
  Is-upper-bound s x = ∀ n → (s [ n ]) ⊑ x

  field
    -- Type "constructors".

    never        : Type
    now          : A → Type
    ⨆            : Increasing-sequence → Type
    antisymmetry : ∀ {x y} → x ⊑ y → y ⊑ x → x ≡ y

    -- We have chosen to explicitly make the type set-truncated.
    -- However, this "constructor" is not used anywhere in the
    -- development.
    Type-UIP-unused : Uniqueness-of-identity-proofs Type

    -- _⊑_ "constructors".

    ⊑-refl             : ∀ x → x ⊑ x
    ⊑-trans            : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
    never⊑             : ∀ x → never ⊑ x
    upper-bound        : ∀ s → Is-upper-bound s (⨆ s)
    least-upper-bound  : ∀ s ub → Is-upper-bound s ub → ⨆ s ⊑ ub
    ⊑-proof-irrelevant : ∀ {x y} → Proof-irrelevant (x ⊑ y)

  ----------------------------------------------------------------------
  -- Some simple consequences

  -- _⊑_ is propositional.

  ⊑-propositional : ∀ {x y} → Is-proposition (x ⊑ y)
  ⊑-propositional =
    _⇔_.from propositional⇔irrelevant ⊑-proof-irrelevant

  private

    -- A lemma.

    Type-is-set-and-equality-characterisation : Is-set Type × _
    Type-is-set-and-equality-characterisation =
      Eq.propositional-identity≃≡
        (λ x y → x ⊑ y × y ⊑ x)
        (λ _ _ → ×-closure 1 ⊑-propositional ⊑-propositional)
        (λ x → ⊑-refl x , ⊑-refl x)
        (λ x y → uncurry {B = λ _ → y ⊑ x} antisymmetry)

  -- Type is a set. (This lemma is analogous to Theorem 11.3.9 in
  -- "Homotopy Type Theory: Univalent Foundations of Mathematics"
  -- (first edition).)

  Type-is-set : Is-set Type
  Type-is-set = proj₁ Type-is-set-and-equality-characterisation

  -- Equality characterisation lemma for Type.

  equality-characterisation-Type :
    ∀ {x y} → (x ⊑ y × y ⊑ x) ≃ (x ≡ y)
  equality-characterisation-Type =
    proj₂ Type-is-set-and-equality-characterisation ext

  -- Equality characterisation lemma for increasing sequences.

  equality-characterisation-increasing :
    ∀ {s₁ s₂} → (∀ n → s₁ [ n ] ≡ s₂ [ n ]) ↔ s₁ ≡ s₂
  equality-characterisation-increasing {s₁} {s₂} =
    (∀ n → s₁ [ n ] ≡ s₂ [ n ])  ↔⟨ Eq.extensionality-isomorphism ext ⟩
    proj₁ s₁ ≡ proj₁ s₂          ↝⟨ ignore-propositional-component
                                      (Π-closure ext 1 λ _ →
                                       ⊑-propositional) ⟩□
    s₁ ≡ s₂                      □

-- Partiality algebras for certain universe levels and types.

record Partiality-algebra {a} p q (A : Set a) :
                          Set (a ⊔ lsuc (p ⊔ q)) where
  constructor ⟨_⟩
  field
    -- A type.

    {Type} : Set p

    -- A partiality-algebra with that type as the underlying type.

    partiality-algebra-with : Partiality-algebra-with Type q A

  open Partiality-algebra-with partiality-algebra-with public

------------------------------------------------------------------------
-- Eliminators

-- I (NAD) have tried to follow the spirit of the rules for HITs
-- specified in the HoTT-Agda library
-- (https://github.com/HoTT/HoTT-Agda/blob/master/core/lib/types/HIT_README.txt).
-- However, at the time of writing those rules don't apply to indexed
-- types.

-- A specification of a given partiality algebra's eliminator
-- arguments (for given motive sizes).

record Arguments {a p′ q′} {A : Set a} p q
                 (PA : Partiality-algebra p′ q′ A) :
                 Set (a ⊔ lsuc (p ⊔ q) ⊔ p′ ⊔ q′) where

  open Partiality-algebra PA

  -- Predicate transformer related to increasing sequences.

  Inc : (P : Type → Set p)
        (Q : ∀ {x y} → P x → P y → x ⊑ y → Set q) →
        Increasing-sequence → Set (p ⊔ q)
  Inc P Q s =
    ∃ λ (p : ∀ n → P (s [ n ])) →
      ∀ n → Q (p n) (p (suc n)) (increasing s n)

  field
    P  : Type → Set p
    Q  : ∀ {x y} → P x → P y → x ⊑ y → Set q
    pe : P never
    po : ∀ x → P (now x)
    pl : ∀ s (pq : Inc P Q s) → P (⨆ s)
    pa : ∀ {x y} (x⊑y : x ⊑ y) (x⊒y : x ⊒ y)
         (p-x : P x) (p-y : P y)
         (q-x⊑y : Q p-x p-y x⊑y) (q-x⊒y : Q p-y p-x x⊒y) →
         subst P (antisymmetry x⊑y x⊒y) p-x ≡ p-y
    pp : ∀ {x} → Uniqueness-of-identity-proofs (P x)
    qr : ∀ x (p : P x) → Q p p (⊑-refl x)
    qt : ∀ {x y z} (x⊑y : x ⊑ y) (y⊑z : y ⊑ z) →
         (px : P x) (py : P y) (pz : P z) →
         Q px py x⊑y → Q py pz y⊑z → Q px pz (⊑-trans x⊑y y⊑z)
    qe : ∀ x (p : P x) → Q pe p (never⊑ x)
    qu : ∀ s (pq : Inc P Q s) n →
         Q (proj₁ pq n) (pl s pq) (upper-bound s n)
    ql : ∀ s ub is-ub (pq : Inc P Q s) (pu : P ub)
         (qu : ∀ n → Q (proj₁ pq n) pu (is-ub n)) →
         Q (pl s pq) pu (least-upper-bound s ub is-ub)
    qp : ∀ {x y} (p-x : P x) (p-y : P y) (x⊑y : x ⊑ y) →
         Proof-irrelevant (Q p-x p-y x⊑y)

-- A specification of a given partiality algebra's eliminators.

record Eliminators {a p q p′ q′} {A : Set a}
                   {PA : Partiality-algebra p′ q′ A}
                   (args : Arguments p q PA) :
                   Set (a ⊔ p ⊔ q ⊔ p′ ⊔ q′) where
  open Partiality-algebra PA
  open Arguments args

  field
    ⊥-rec : (x : Type) → P x
    ⊑-rec : ∀ {x y} (x⊑y : x ⊑ y) → Q (⊥-rec x) (⊥-rec y) x⊑y

  inc-rec : (s : Increasing-sequence) → Inc P Q s
  inc-rec = λ { (s , inc) → ( (λ n → ⊥-rec (s   n))
                            , (λ n → ⊑-rec (inc n))
                            ) }

  field

    -- Some "computation" rules.

    ⊥-rec-never : ⊥-rec never ≡ pe
    ⊥-rec-now   : ∀ x → ⊥-rec (now x) ≡ po x
    ⊥-rec-⨆     : ∀ s → ⊥-rec (⨆ s) ≡ pl s (inc-rec s)

-- A specification of the elimination principle for a given partiality
-- algebra (for motives of certain sizes).

Elimination-principle :
  ∀ {a p′ q′} {A : Set a} →
  ∀ p q → Partiality-algebra p′ q′ A → Set (a ⊔ lsuc (p ⊔ q) ⊔ p′ ⊔ q′)
Elimination-principle p q P =
  (args : Arguments p q P) → Eliminators args

------------------------------------------------------------------------
-- Equality characterisation lemmas for Partiality-algebra-with

abstract

  -- An equality characterisation lemma for Partiality-algebra-with.

  equality-characterisation-Partiality-algebra-with₁ :
    ∀ {a p q} {A : Set a} {Type : Set p}
      {P₁ P₂ : Partiality-algebra-with Type q A} →
    let module P₁ = Partiality-algebra-with P₁
        module P₂ = Partiality-algebra-with P₂
    in
    (∃ λ (⊑≡⊑ : ∀ x y → (x P₁.⊑ y) ≡ (x P₂.⊑ y)) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡ P₂.⨆ (Σ-map Prelude.id (≡⇒→ (⊑≡⊑ _ _) ⊚_) s))
      ↔
    P₁ ≡ P₂
  equality-characterisation-Partiality-algebra-with₁
    {q = q} {A} {Type} {P₁} {P₂} =

    (∃ λ (⊑≡⊑ : ∀ x y → (x P₁.⊑ y) ≡ (x P₂.⊑ y)) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡ P₂.⨆ (Σ-map Prelude.id (≡⇒→ (⊑≡⊑ _ _) ⊚_) s))      ↔⟨ ∃-cong (λ ⊑≡⊑ → ∃-cong λ _ → ∃-cong λ _ → Eq.∀-preserves ext λ s →
                                                                              ≡⇒↝ _ $ cong (λ (p : {f : ℕ → Type} → _) →
                                                                                              P₁.⨆ s ≡ P₂.⨆ (Σ-map Prelude.id p s)) $
                                                                                _⇔_.to propositional⇔irrelevant
                                                                                  (implicit-Π-closure ext 1 λ _ →
                                                                                   Π-closure          ext 1 λ _ →
                                                                                   Π-closure          ext 1 λ _ →
                                                                                   P₂.⊑-propositional)
                                                                                  (≡⇒→ (⊑≡⊑ _ _) ⊚_)
                                                                                  (λ {f} → ≡⇒→ (cong (λ _⊑_ → ∀ n → f n ⊑ f (suc n))
                                                                                                     (Eq.good-ext ext (Eq.good-ext ext ⊚ ⊑≡⊑))))) ⟩
    (∃ λ (⊑≡⊑ : ∀ x y → (x P₁.⊑ y) ≡ (x P₂.⊑ y)) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡
             P₂.⨆ (Σ-map Prelude.id
                         (λ {f} →
                            ≡⇒→ (cong (λ _⊑_ → ∀ n → f n ⊑ f (suc n))
                                      (Eq.good-ext ext
                                         (Eq.good-ext ext ⊚ ⊑≡⊑))))
                         s))                                             ↝⟨ Σ-cong (Eq.∀-preserves ext λ _ →
                                                                                    Eq.extensionality-isomorphism ext) (λ _ → F.id) ⟩
    (∃ λ (⊑≡⊑ : ∀ x → P₁._⊑_ x ≡ P₂._⊑_ x) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡
             P₂.⨆ (Σ-map Prelude.id
                         (λ {f} →
                            ≡⇒→ (cong (λ _⊑_ → ∀ n → f n ⊑ f (suc n))
                                      (Eq.good-ext ext ⊑≡⊑)))
                         s))                                             ↝⟨ Σ-cong (Eq.extensionality-isomorphism ext) (λ _ → F.id) ⟩

    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡
             P₂.⨆ (Σ-map Prelude.id
                         (λ {f} →
                            ≡⇒→ (cong (λ _⊑_ → ∀ n → f n ⊑ f (suc n))
                                      ⊑≡⊑))
                         s))                                             ↔⟨⟩

    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡
             P₂.⨆ ( proj₁ s
                  , ≡⇒→ (cong (λ _⊑_ →
                                 ∀ n → proj₁ s n ⊑ proj₁ s (suc n))
                              ⊑≡⊑)
                        (proj₂ s)
                  ))                                                     ↔⟨ ∃-cong (λ ⊑≡⊑ → ∃-cong λ _ → ∃-cong λ _ → Eq.∀-preserves ext λ _ →
                                                                              ≡⇒↝ _ $ cong (λ eq → _ ≡ P₂.⨆ (_ , ≡⇒→ eq _)) $ sym $
                                                                                cong-∘ _ _ ⊑≡⊑) ⟩
    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡
             P₂.⨆ ( proj₁ s
                  , ≡⇒→ (cong (uncurry λ _⊑_ (f : ℕ → Type) →
                                         ∀ n → f n ⊑ f (suc n))
                              (cong (_, _) ⊑≡⊑))
                        (proj₂ s)
                  ))                                                     ↔⟨ ∃-cong (λ ⊑≡⊑ → ∃-cong λ _ → ∃-cong λ _ → Eq.∀-preserves ext λ _ →
                                                                              ≡⇒↝ _ $ cong (λ inc → _ ≡ P₂.⨆ (_ , inc)) $ sym $
                                                                                subst-in-terms-of-≡⇒↝ equivalence (cong (_, _) ⊑≡⊑) _ _) ⟩
    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡
             P₂.⨆ ( proj₁ s
                  , subst (uncurry λ _⊑_ (f : ℕ → Type) →
                                     ∀ n → f n ⊑ f (suc n))
                          (cong (_, _) ⊑≡⊑)
                          (proj₂ s)
                  ))                                                     ↔⟨ ∃-cong (λ ⊑≡⊑ → ∃-cong λ _ → ∃-cong λ _ → Eq.∀-preserves ext λ _ →
                                                                              ≡⇒↝ _ $ cong (λ eq → _ ≡
                                                                                                   P₂.⨆ (_ , subst (uncurry λ _⊑_ (f : ℕ → Type) →
                                                                                                                              ∀ n → f n ⊑ f (suc n))
                                                                                                                   eq _)) $ sym $
                                                                                Σ-≡,≡→≡-subst-const ⊑≡⊑ refl) ⟩
    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡
             P₂.⨆ ( proj₁ s
                  , subst (uncurry λ _⊑_ (f : ℕ → Type) →
                                     ∀ n → f n ⊑ f (suc n))
                          (Σ-≡,≡→≡ ⊑≡⊑ (subst-const ⊑≡⊑))
                          (proj₂ s)
                  ))                                                     ↔⟨ ∃-cong (λ ⊑≡⊑ → ∃-cong λ _ → ∃-cong λ _ → Eq.∀-preserves ext λ _ →
                                                                              ≡⇒↝ _ $ cong (λ s → _ ≡ P₂.⨆ s) $ sym $
                                                                                push-subst-pair′ {y≡z = ⊑≡⊑} _ _ (subst-const ⊑≡⊑)) ⟩
    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡
             P₂.⨆ (subst (λ _⊑_ → ∃ λ f → ∀ n → f n ⊑ f (suc n))
                         ⊑≡⊑ s))                                         ↔⟨ ∃-cong (λ ⊑≡⊑ → ∃-cong λ _ → ∃-cong λ _ → Eq.∀-preserves ext λ _ →
                                                                              ≡⇒↝ _ $ cong (λ eq → _ ≡
                                                                                                   P₂.⨆ (subst (λ _⊑_ → ∃ λ f → ∀ n →
                                                                                                                          f n ⊑ f (suc n)) eq _)) $
                                                                                sym $ sym-sym ⊑≡⊑) ⟩
    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡
             P₂.⨆ (subst (λ _⊑_ → ∃ λ f → ∀ n → f n ⊑ f (suc n))
                         (sym (sym ⊑≡⊑)) s))                             ↔⟨ ∃-cong (λ ⊑≡⊑ → ∃-cong λ _ → ∃-cong λ _ → Eq.∀-preserves ext λ _ →
                                                                              ≡⇒↝ _ $ cong (λ f → _ ≡ f _) $ sym $
                                                                                subst-→-domain _ (sym ⊑≡⊑)) ⟩
    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡
             subst (λ _⊑_ → ∃ (λ f → ∀ n → f n ⊑ f (suc n)) → Type)
                   (sym ⊑≡⊑) P₂.⨆ s)                                     ↔⟨ ∃-cong (λ _ → ∃-cong λ _ →
                                                                              Eq.extensionality-isomorphism ext
                                                                                ×-cong
                                                                              Eq.extensionality-isomorphism ext) ⟩
    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       P₁.never ≡ P₂.never
         ×
       P₁.now ≡ P₂.now
         ×
       P₁.⨆ ≡ subst _ (sym ⊑≡⊑) P₂.⨆)                                    ↝⟨ ∃-cong (λ ⊑≡⊑ → ∃-cong λ _ → ∃-cong λ _ →
                                                                              ≡⇒↝ _ $ elim (λ ⊑≡⊑ → ∀ {⨆₁ ⨆₂} →
                                                                                              (⨆₁ ≡ subst _ (sym ⊑≡⊑) ⨆₂) ≡
                                                                                              (subst _ ⊑≡⊑ ⨆₁ ≡ ⨆₂))
                                                                                           (λ _ → refl) ⊑≡⊑) ⟩
    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       P₁.never ≡ P₂.never
         ×
       P₁.now ≡ P₂.now
         ×
       subst _ ⊑≡⊑ P₁.⨆ ≡ P₂.⨆)                                          ↝⟨ ∃-cong (λ ⊑≡⊑ →
                                                                              ≡⇒↝ _ (cong (_≡ _) $ sym $ subst-const ⊑≡⊑)
                                                                                ×-cong
                                                                              ≡⇒↝ _ (cong (_≡ _) $ sym $ subst-const ⊑≡⊑)
                                                                                ×-cong
                                                                              F.id) ⟩
    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       subst _ ⊑≡⊑ P₁.never ≡ P₂.never
         ×
       subst _ ⊑≡⊑ P₁.now ≡ P₂.now
         ×
       subst _ ⊑≡⊑ P₁.⨆ ≡ P₂.⨆)                                          ↝⟨ ∃-cong (λ _ → ∃-cong λ _ → ≡×≡↔≡) ⟩

    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       subst _ ⊑≡⊑ P₁.never ≡ P₂.never
         ×
       (subst _ ⊑≡⊑ P₁.now , subst _ ⊑≡⊑ P₁.⨆) ≡
       (P₂.now , P₂.⨆))                                                  ↝⟨ ∃-cong (λ _ → ≡×≡↔≡) ⟩

    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       (subst _ ⊑≡⊑ P₁.never , subst _ ⊑≡⊑ P₁.now , subst _ ⊑≡⊑ P₁.⨆) ≡
       (P₂.never , P₂.now , P₂.⨆))                                       ↝⟨ ∃-cong (λ ⊑≡⊑ → ≡⇒↝ _ $ cong (λ x → (subst _ ⊑≡⊑ P₁.never , x) ≡ _) $
                                                                              sym $ push-subst-, {y≡z = ⊑≡⊑} _
                                                                                                 (λ _⊑_ → (∃ λ f → ∀ n → f n ⊑ f (suc n)) → _)) ⟩
    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       (subst _ ⊑≡⊑ P₁.never , subst _ ⊑≡⊑ (P₁.now , P₁.⨆)) ≡
       (P₂.never , P₂.now , P₂.⨆))                                       ↝⟨ ∃-cong (λ ⊑≡⊑ → ≡⇒↝ _ $ cong (_≡ _) $ sym $
                                                                              push-subst-, {y≡z = ⊑≡⊑} _ _) ⟩
    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       subst _ ⊑≡⊑ (P₁.never , P₁.now , P₁.⨆) ≡
       (P₂.never , P₂.now , P₂.⨆))                                       ↔⟨⟩

    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       subst _ ⊑≡⊑ (proj₂ (proj₁ (_↔_.to rearrange P₁))) ≡
       proj₂ (proj₁ (_↔_.to rearrange P₂)))                              ↝⟨ Bijection.Σ-≡,≡↔≡ ⟩

    proj₁ (_↔_.to rearrange P₁) ≡ proj₁ (_↔_.to rearrange P₂)            ↝⟨ ignore-propositional-component
                                                                              (×-closure 1 (implicit-Π-closure ext 1 λ _ →
                                                                                            implicit-Π-closure ext 1 λ _ →
                                                                                            Π-closure ext 1 λ _ →
                                                                                            Π-closure ext 1 λ _ →
                                                                                            P₂.Type-is-set _ _) $
                                                                               ×-closure 1 (UIP-propositional ext) $
                                                                               ×-closure 1 (Π-closure ext 1 λ _ →
                                                                                            P₂.⊑-propositional) $
                                                                               ×-closure 1 (implicit-Π-closure ext 1 λ _ →
                                                                                            implicit-Π-closure ext 1 λ _ →
                                                                                            implicit-Π-closure ext 1 λ _ →
                                                                                            Π-closure ext 1 λ _ →
                                                                                            Π-closure ext 1 λ _ →
                                                                                            P₂.⊑-propositional) $
                                                                               ×-closure 1 (Π-closure ext 1 λ _ →
                                                                                            P₂.⊑-propositional) $
                                                                               ×-closure 1 (Π-closure ext 1 λ _ →
                                                                                            Π-closure ext 1 λ _ →
                                                                                            P₂.⊑-propositional) $
                                                                               ×-closure 1 (Π-closure ext 1 λ _ →
                                                                                            Π-closure ext 1 λ _ →
                                                                                            Π-closure ext 1 λ _ →
                                                                                            P₂.⊑-propositional)
                                                                                           (implicit-Π-closure ext 1 λ _ →
                                                                                            implicit-Π-closure ext 1 λ _ →
                                                                                            Proof-irrelevant-propositional ext)) ⟩
    _↔_.to rearrange P₁ ≡ _↔_.to rearrange P₂                            ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ rearrange) ⟩□

    P₁ ≡ P₂                                                              □
    where
    module P₁ = Partiality-algebra-with P₁
    module P₂ = Partiality-algebra-with P₂

    rearrange :
      Partiality-algebra-with Type q A
        ↔
      ∃ λ R →
        let _⊑_ : Type → Type → Set q
            _⊑_ = proj₁ R

            never : Type
            never = proj₁ (proj₂ R)

            now : A → Type
            now = proj₁ (proj₂ (proj₂ R))

            ⨆ : (∃ λ (f : ℕ → Type) → ∀ n → f n ⊑ f (suc n)) → Type
            ⨆ = proj₂ (proj₂ (proj₂ R))
        in
        (∀ {x y} → x ⊑ y → y ⊑ x → x ≡ y)
          ×
        Uniqueness-of-identity-proofs Type
          ×
        (∀ x → x ⊑ x)
          ×
        (∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z)
          ×
        (∀ x → never ⊑ x)
          ×
        (∀ s → ∀ n → proj₁ s n ⊑ ⨆ s)
          ×
        (∀ s ub → (∀ n → proj₁ s n ⊑ ub) → ⨆ s ⊑ ub)
          ×
        (∀ {x y} → Proof-irrelevant (x ⊑ y))
    rearrange = record
      { surjection = record
        { logical-equivalence = record
          { to   = λ P → let open Partiality-algebra-with P in
                    ( _⊑_
                    , never
                    , now
                    , ⨆
                    )
                  , antisymmetry
                  , Type-UIP-unused
                  , ⊑-refl
                  , ⊑-trans
                  , never⊑
                  , upper-bound
                  , least-upper-bound
                  , ⊑-proof-irrelevant
          ; from = λ where
              ((LE , ne , n , l) , a , u , r , t , le , ub , lub , p) →
                record
                  { _⊑_                = LE
                  ; never              = ne
                  ; now                = n
                  ; ⨆                  = l
                  ; antisymmetry       = a
                  ; Type-UIP-unused    = u
                  ; ⊑-refl             = r
                  ; ⊑-trans            = t
                  ; never⊑             = le
                  ; upper-bound        = ub
                  ; least-upper-bound  = lub
                  ; ⊑-proof-irrelevant = p
                  }
          }
        ; right-inverse-of = λ _ → refl
        }
      ; left-inverse-of = λ _ → refl
      }

  -- Another equality characterisation lemma for
  -- Partiality-algebra-with.

  equality-characterisation-Partiality-algebra-with₂ :
    ∀ {a p q} {A : Set a} {Type : Set p}
      {P₁ P₂ : Partiality-algebra-with Type q A} →

    Propositional-extensionality q →

    let module P₁ = Partiality-algebra-with P₁
        module P₂ = Partiality-algebra-with P₂
    in
    (∃ λ (⊑⇔⊑ : ∀ x y → x P₁.⊑ y ⇔ x P₂.⊑ y) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡ P₂.⨆ (Σ-map Prelude.id (_⇔_.to (⊑⇔⊑ _ _) ⊚_) s))
      ↔
    P₁ ≡ P₂
  equality-characterisation-Partiality-algebra-with₂
    {q = q} {A} {Type} {P₁} {P₂} prop-ext =

    (∃ λ (⊑⇔⊑ : ∀ x y → x P₁.⊑ y ⇔ x P₂.⊑ y) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡ P₂.⨆ (Σ-map Prelude.id (_⇔_.to (⊑⇔⊑ _ _) ⊚_) s))  ↝⟨ Σ-cong (Eq.∀-preserves ext λ _ → Eq.∀-preserves ext λ _ →
                                                                                     Eq.↔⇒≃ $ Eq.⇔↔≃ ext P₁.⊑-propositional P₂.⊑-propositional)
                                                                                  (λ _ → F.id) ⟩
    (∃ λ (⊑≃⊑ : ∀ x y → (x P₁.⊑ y) ≃ (x P₂.⊑ y)) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡ P₂.⨆ (Σ-map Prelude.id (_≃_.to (⊑≃⊑ _ _) ⊚_) s))  ↝⟨ inverse $ Σ-cong
                                                                             (Eq.∀-preserves ext λ _ → Eq.∀-preserves ext λ _ →
                                                                                ≡≃≃ (_≃_.to
                                                                                       (Propositional-extensionality-is-univalence-for-propositions
                                                                                          ext)
                                                                                       prop-ext
                                                                                       P₁.⊑-propositional
                                                                                       P₂.⊑-propositional))
                                                                             (λ _ → F.id) ⟩
    (∃ λ (⊑≡⊑ : ∀ x y → (x P₁.⊑ y) ≡ (x P₂.⊑ y)) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡ P₂.⨆ (Σ-map Prelude.id (≡⇒→ (⊑≡⊑ _ _) ⊚_) s))     ↝⟨ equality-characterisation-Partiality-algebra-with₁ ⟩□

    P₁ ≡ P₂                                                             □
    where
    module P₁ = Partiality-algebra-with P₁
    module P₂ = Partiality-algebra-with P₂

------------------------------------------------------------------------
-- Partiality algebra morphisms

-- Morphisms from one partiality algebra to another.

record Morphism {a p₁ p₂ q₁ q₂} {A : Set a}
                (P₁ : Partiality-algebra p₁ q₁ A)
                (P₂ : Partiality-algebra p₂ q₂ A) :
                Set (a ⊔ p₁ ⊔ p₂ ⊔ q₁ ⊔ q₂) where

  private
    module P₁ = Partiality-algebra P₁
    module P₂ = Partiality-algebra P₂

  field
    function : P₁.Type → P₂.Type
    monotone : ∀ {x y} → x P₁.⊑ y → function x P₂.⊑ function y

  sequence-function : P₁.Increasing-sequence → P₂.Increasing-sequence
  sequence-function = Σ-map (function ⊚_) (monotone ⊚_)

  field
    strict       : function P₁.never ≡ P₂.never
    now-to-now   : ∀ x → function (P₁.now x) ≡ P₂.now x
    ω-continuous : ∀ s → function (P₁.⨆ s) ≡ P₂.⨆ (sequence-function s)

-- An identity morphism.

id : ∀ {a p q} {A : Set a} {P : Partiality-algebra p q A} → Morphism P P
id = record
  { function     = Prelude.id
  ; monotone     = Prelude.id
  ; strict       = refl
  ; now-to-now   = λ _ → refl
  ; ω-continuous = λ _ → refl
  }

-- Composition of morphisms.

_∘_ : ∀ {a p₁ p₂ p₃ q₁ q₂ q₃} {A : Set a}
        {P₁ : Partiality-algebra p₁ q₁ A}
        {P₂ : Partiality-algebra p₂ q₂ A}
        {P₃ : Partiality-algebra p₃ q₃ A} →
      Morphism P₂ P₃ → Morphism P₁ P₂ → Morphism P₁ P₃
_∘_ {P₁ = P₁} {P₂} {P₃} m₁ m₂ = record
  { function     = function m₁ ⊚ function m₂
  ; monotone     = monotone m₁ ⊚ monotone m₂
  ; strict       = function m₁ (function m₂ (never P₁))  ≡⟨ cong (function m₁) (strict m₂) ⟩
                   function m₁ (never P₂)                ≡⟨ strict m₁ ⟩∎
                   never P₃                              ∎
  ; now-to-now   = λ x →
                     function m₁ (function m₂ (now P₁ x))  ≡⟨ cong (function m₁) (now-to-now m₂ x) ⟩
                     function m₁ (now P₂ x)                ≡⟨ now-to-now m₁ x ⟩∎
                     now P₃ x                              ∎
  ; ω-continuous = λ s →
      function m₁ (function m₂ (⨆ P₁ s))                    ≡⟨ cong (function m₁) (ω-continuous m₂ s) ⟩
      function m₁ (⨆ P₂ (sequence-function m₂ s))           ≡⟨ ω-continuous m₁ (sequence-function m₂ s) ⟩∎
      ⨆ P₃ (sequence-function m₁ (sequence-function m₂ s))  ∎
  }
  where
  open Morphism
  open Partiality-algebra

-- Is-morphism-with P Q f holds if f is a morphism from P to Q.

Is-morphism-with :
  ∀ {a p₁ p₂ q₁ q₂} {Type₁ : Set p₁} {Type₂ : Set p₂} {A : Set a}
  (P₁ : Partiality-algebra-with Type₁ q₁ A)
  (P₂ : Partiality-algebra-with Type₂ q₂ A) →
  (Type₁ → Type₂) → Set _
Is-morphism-with P₁ P₂ f =
  ∃ λ (m : ∀ {x y} → x P₁.⊑ y → f x P₂.⊑ f y) →
  f P₁.never ≡ P₂.never
    ×
  (∀ x → f (P₁.now x) ≡ P₂.now x)
    ×
  (∀ s → f (P₁.⨆ s) ≡ P₂.⨆ (Σ-map (f ⊚_) (m ⊚_) s))
  where
  module P₁ = Partiality-algebra-with P₁
  module P₂ = Partiality-algebra-with P₂

-- Is-morphism P Q f holds if f is a morphism from P to Q.

Is-morphism :
  let open Partiality-algebra in
  ∀ {a p₁ p₂ q₁ q₂} {A : Set a}
  (P₁ : Partiality-algebra p₁ q₁ A) (P₂ : Partiality-algebra p₂ q₂ A) →
  (Type P₁ → Type P₂) → Set _
Is-morphism P₁ P₂ =
  Is-morphism-with P₁.partiality-algebra-with
                   P₂.partiality-algebra-with
  where
  module P₁ = Partiality-algebra P₁
  module P₂ = Partiality-algebra P₂

-- An alternative definition of morphisms.

Morphism-as-Σ :
  ∀ {a p₁ p₂ q₁ q₂} {A : Set a} →
  Partiality-algebra p₁ q₁ A → Partiality-algebra p₂ q₂ A → Set _
Morphism-as-Σ P₁ P₂ =
  ∃ λ (f : P₁.Type → P₂.Type) → Is-morphism P₁ P₂ f
  where
  module P₁ = Partiality-algebra P₁
  module P₂ = Partiality-algebra P₂

-- The two definitions are isomorphic.

Morphism↔Morphism-as-Σ :
  ∀ {a p₁ p₂ q₁ q₂} {A : Set a}
    {P₁ : Partiality-algebra p₁ q₁ A}
    {P₂ : Partiality-algebra p₂ q₂ A} →
  Morphism P₁ P₂ ↔ Morphism-as-Σ P₁ P₂
Morphism↔Morphism-as-Σ = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ m → function m
                   , monotone m
                   , strict m
                   , now-to-now m
                   , ω-continuous m
      ; from = λ { (f , m , s , n , ω) → record
                   { function     = f
                   ; monotone     = m
                   ; strict       = s
                   ; now-to-now   = n
                   ; ω-continuous = ω
                   }
                 }
      }
    ; right-inverse-of = λ _ → refl
    }
  ; left-inverse-of = λ _ → refl
  }
  where
  open Morphism

abstract

  -- Is-morphism-with is pointwise propositional.

  Is-morphism-with-propositional :
    let open Partiality-algebra in
    ∀ {a p₁ p₂ q₁ q₂} {Type₁ : Set p₁} {Type₂ : Set p₂} {A : Set a}
      (P₁ : Partiality-algebra-with Type₁ q₁ A)
      (P₂ : Partiality-algebra-with Type₂ q₂ A)
      {f : Type₁ → Type₂} →
    Is-proposition (Is-morphism-with P₁ P₂ f)
  Is-morphism-with-propositional _ P₂ =
    Σ-closure 1 (implicit-Π-closure ext 1 λ _ →
                 implicit-Π-closure ext 1 λ _ →
                 Π-closure ext 1 λ _ →
                 P₂.⊑-propositional) λ _ →
    ×-closure 1 (P₂.Type-is-set _ _) $
    ×-closure 1 (Π-closure ext 1 λ _ →
                 P₂.Type-is-set _ _) $
    Π-closure ext 1 λ _ →
    P₂.Type-is-set _ _
    where
    module P₂ = Partiality-algebra-with P₂

  -- Is-morphism is pointwise propositional.

  Is-morphism-propositional :
    let open Partiality-algebra in
    ∀ {a p₁ p₂ q₁ q₂} {A : Set a}
      (P₁ : Partiality-algebra p₁ q₁ A)
      (P₂ : Partiality-algebra p₂ q₂ A)
      {f : Type P₁ → Type P₂} →
    Is-proposition (Is-morphism P₁ P₂ f)
  Is-morphism-propositional P₁ P₂ =
    Is-morphism-with-propositional
      P₁.partiality-algebra-with
      P₂.partiality-algebra-with
    where
    module P₁ = Partiality-algebra P₁
    module P₂ = Partiality-algebra P₂

  -- An equality characterisation lemma for morphisms.

  equality-characterisation-Morphism :
    ∀ {a p₁ p₂ q₁ q₂} {A : Set a}
      {P₁ : Partiality-algebra p₁ q₁ A}
      {P₂ : Partiality-algebra p₂ q₂ A} →
      {m₁ m₂ : Morphism P₁ P₂} →

    Morphism.function m₁ ≡ Morphism.function m₂
      ↔
    m₁ ≡ m₂
  equality-characterisation-Morphism {P₁ = P₁} {P₂} {m₁} {m₂} =
    function m₁ ≡ function m₂                                            ↝⟨ ignore-propositional-component (Is-morphism-propositional P₁ P₂) ⟩
    _↔_.to Morphism↔Morphism-as-Σ m₁ ≡ _↔_.to Morphism↔Morphism-as-Σ m₂  ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ Morphism↔Morphism-as-Σ) ⟩□
    m₁ ≡ m₂                                                              □
    where
    open Morphism

  -- The type of morphisms is a set.

  Morphism-set :
    ∀  {a p₁ p₂ q₁ q₂} {A : Set a}
       {P₁ : Partiality-algebra p₁ q₁ A}
       {P₂ : Partiality-algebra p₂ q₂ A} →
    Is-set (Morphism P₁ P₂)
  Morphism-set {P₂ = P₂} _ _ =
    H-level.respects-surjection
      (_↔_.surjection equality-characterisation-Morphism)
      1
      ((Π-closure ext 2 λ _ → Type-is-set P₂) _ _)
    where
    open Partiality-algebra

------------------------------------------------------------------------
-- Partiality algebra categories

-- Partiality algebras form precategories.

precategory :
  ∀ {a} p q (A : Set a) → Precategory (a ⊔ lsuc (p ⊔ q)) (a ⊔ p ⊔ q)
Precategory.precategory (precategory p q A) =
    Partiality-algebra p q A
  , (λ P Q → Morphism P Q , Morphism-set)
  , id
  , _∘_
  , _↔_.to equality-characterisation-Morphism refl
  , _↔_.to equality-characterisation-Morphism refl
  , _↔_.to equality-characterisation-Morphism refl

-- A "standard notion of structure" built using
-- Partiality-algebra-with (and propositional extensionality).

standard-notion-of-structure :
  ∀ {a} p {q} (A : Set a) →
  Propositional-extensionality q →
  Standard-notion-of-structure _ _ (precategory-Set p ext)
standard-notion-of-structure p {q} A prop-ext = record
  { P               = λ B → Partiality-algebra-with (proj₁ B) q A
  ; H               = Is-morphism-with
  ; H-prop          = λ { {p = P} {q = Q} _ →
                          Is-morphism-with-propositional P Q
                        }
  ; H-id            = λ { {p = P} →
                          proj₂ $
                            _↔_.to Morphism↔Morphism-as-Σ
                              (id {P = ⟨ P ⟩})
                        }
  ; H-∘             = λ { {p = P} {q = Q} {r = R}
                          f-morphism g-morphism →
                          proj₂ $
                            _↔_.to Morphism↔Morphism-as-Σ
                              (_↔_.from
                                 (Morphism↔Morphism-as-Σ
                                    {P₁ = ⟨ Q ⟩} {P₂ = ⟨ R ⟩})
                                 (_ , g-morphism)
                                 ∘
                               _↔_.from
                                 (Morphism↔Morphism-as-Σ {P₁ = ⟨ P ⟩})
                                 (_ , f-morphism))
                        }
  ; H-antisymmetric = λ P Q id-morphism-P→Q id-morphism-Q→P →
      _↔_.to
        (equality-characterisation-Partiality-algebra-with₂ prop-ext)
        ( (λ x y → record { to   = proj₁ id-morphism-P→Q
                          ; from = proj₁ id-morphism-Q→P
                          })
        , proj₁ (proj₂ id-morphism-P→Q)
        , proj₁ (proj₂ (proj₂ id-morphism-P→Q))
        , proj₂ (proj₂ (proj₂ id-morphism-P→Q))
        )
  }

abstract

  -- The precategory obtained from the standard notion of structure is
  -- equal to the direct definition above (assuming univalence).

  precategories-equal :
    ∀ {a p q} {A : Set a} →
    Univalence (a ⊔ lsuc (p ⊔ q)) →
    Univalence (a ⊔ p ⊔ q) →
    (prop-ext : Propositional-extensionality q) →
    Standard-notion-of-structure.Str
      (standard-notion-of-structure p A prop-ext)
      ≡
    precategory p q A
  precategories-equal {p = p} {q} {A} univ₁ univ₂ prop-ext =
    _↔_.to (equality-characterisation-Precategory ext univ₁ univ₂)
      ( ≃Partiality-algebra
      , (λ _ _ → Eq.↔⇒≃ $ inverse $ Morphism↔Morphism-as-Σ)
      , (λ _ → refl)
      , (λ _ _ _ _ _ → refl)
      )
    where
    ≃Partiality-algebra :
      (∃ λ (Type : SET p) → Partiality-algebra-with (proj₁ Type) q A)
        ≃
      Partiality-algebra p q A
    ≃Partiality-algebra =
      (∃ λ (Type : SET p) → Partiality-algebra-with (proj₁ Type) q A)  ↔⟨ inverse Σ-assoc ⟩

      (∃ λ (Type : Set p) →
         Is-set Type × Partiality-algebra-with Type q A)               ↔⟨ ∃-cong (λ _ → drop-⊤-left-× λ P → inverse $ _⇔_.to contractible⇔⊤↔ $
                                                                            propositional⇒inhabited⇒contractible
                                                                              (H-level-propositional ext 2)
                                                                              (Partiality-algebra-with.Type-is-set P)) ⟩
      (∃ λ (Type : Set p) → Partiality-algebra-with Type q A)          ↝⟨ Eq.↔⇒≃ record
                                                                            { surjection = record
                                                                              { logical-equivalence = record
                                                                                { to   = uncurry λ _ P → ⟨ P ⟩
                                                                                ; from = λ P → Type P , partiality-algebra-with P
                                                                                }
                                                                              ; right-inverse-of = λ _ → refl
                                                                              }
                                                                            ; left-inverse-of = λ _ → refl
                                                                            } ⟩□
      Partiality-algebra p q A                                         □
      where
      open Partiality-algebra

-- Thus the precategory is a category (assuming univalence and
-- propositional extensionality).

category :
  ∀ {a p q} (A : Set a) →
  Univalence (a ⊔ lsuc (p ⊔ q)) →
  Univalence (a ⊔ p ⊔ q) →
  Univalence p →
  Propositional-extensionality q →
  Category (a ⊔ lsuc (p ⊔ q)) (a ⊔ p ⊔ q)
Category.category (category A univ₁ univ₂ univ₃ prop-ext) =
    precategory _ _ A
  , subst (λ C → ∀ {P Q} → Eq.Is-equivalence
                             (Precategory.≡→≅ C {P} {Q}))
          (precategories-equal univ₁ univ₂ prop-ext)
          (structure-identity-principle
             ext
             (category-Set _ ext (λ _ _ → univ₃))
             (standard-notion-of-structure _ A prop-ext))

private

  precategory-category :
    ∀ {a p} {q} {A : Set a}
      {univ₁ : Univalence (a ⊔ lsuc (p ⊔ q))}
      {univ₂ : Univalence (a ⊔ p ⊔ q)}
      {univ₃ : Univalence p}
      {prop-ext : Propositional-extensionality q} →
    Category.precategory (category A univ₁ univ₂ univ₃ prop-ext) ≡
    precategory p q A
  precategory-category = refl

------------------------------------------------------------------------
-- Initiality

-- The statement that a given partiality algebra is homotopy-initial.

Initial : ∀ {a p q} p′ q′ {A : Set a} → Partiality-algebra p q A →
          Set (a ⊔ p ⊔ q ⊔ lsuc (p′ ⊔ q′))
Initial p′ q′ {A} P =
  (P′ : Partiality-algebra p′ q′ A) → Contractible (Morphism P P′)

-- If a partiality algebra is initial at certain sizes, then it is
-- also initial at smaller sizes.

lower-initiality :
  ∀ {a p q p₁ q₁} p₂ q₂ {A : Set a}
  (P : Partiality-algebra p q A)
  (initial : Initial (p₁ ⊔ p₂) (q₁ ⊔ q₂) P) →
  Initial p₁ q₁ P
lower-initiality {p₁ = p₁} {q₁} p₂ q₂ {A} P initial P′ =
  Σ-map lower-morphism lemma (initial P″)
  where
  open Partiality-algebra P′

  P″ : Partiality-algebra (p₁ ⊔ p₂) (q₁ ⊔ q₂) A
  P″ = record
    { Type                    = ↑ p₂ Type
    ; partiality-algebra-with = record
      { _⊑_                = λ x y → ↑ q₂ (lower x ⊑ lower y)
      ; never              = lift never
      ; now                = lift ⊚ now
      ; ⨆                  = lift ⊚ ⨆ ⊚ Σ-map (lower ⊚_) (lower ⊚_)
      ; antisymmetry       = λ x⊑y y⊑x →
                               cong lift (antisymmetry (lower x⊑y)
                                                       (lower y⊑x))
      ; Type-UIP-unused    = λ _ _ →
                               _⇔_.to set⇔UIP
                                 (↑-closure 2 Type-is-set) _ _
      ; ⊑-refl             = lift ⊚ ⊑-refl ⊚ lower
      ; ⊑-trans            = λ x⊑y y⊑z →
                               lift (⊑-trans (lower x⊑y)
                                             (lower y⊑z))
      ; never⊑             = lift ⊚ never⊑ ⊚ lower
      ; upper-bound        = λ _ → lift ⊚ upper-bound _
      ; least-upper-bound  = λ _ _ →
                               lift ⊚
                               least-upper-bound _ _ ⊚
                               (lower ⊚_)
      ; ⊑-proof-irrelevant = _⇔_.to propositional⇔irrelevant
                               (↑-closure 1 ⊑-propositional)
      }
    }

  lower-morphism : Morphism P P″ → Morphism P P′
  lower-morphism m = record
    { function     = lower ⊚ function
    ; monotone     = lower ⊚ monotone
    ; strict       = cong lower strict
    ; now-to-now   = cong lower ⊚ now-to-now
    ; ω-continuous = cong lower ⊚ ω-continuous
    }
    where
    open Morphism m

  lift-morphism : Morphism P P′ → Morphism P P″
  lift-morphism m = record
    { function     = lift ⊚ function
    ; monotone     = lift ⊚ monotone
    ; strict       = cong lift strict
    ; now-to-now   = cong lift ⊚ now-to-now
    ; ω-continuous = cong lift ⊚ ω-continuous
    }
    where
    open Morphism m

  lemma : {m : Morphism P P″} →
          (∀ m′ → m ≡ m′) →
          (∀ m′ → lower-morphism m ≡ m′)
  lemma {m} hyp m′ = _↔_.to equality-characterisation-Morphism
    (lower ⊚ Morphism.function m  ≡⟨ cong ((lower ⊚_) ⊚ Morphism.function) (hyp (lift-morphism m′)) ⟩∎
     Morphism.function m′         ∎)

------------------------------------------------------------------------
-- Specifying the partiality monad using eliminators is logically
-- equivalent (at the meta-level) to specifying it using initiality

-- Any partiality algebra with eliminators (at certain sizes) is
-- initial (at the same sizes).

eliminators→initiality :
  ∀ {a p q p′ q′} {A : Set a} →
  (P : Partiality-algebra p′ q′ A) →
  Elimination-principle p q P →
  Initial p q P
eliminators→initiality {p = p} {q} P elims P′ = morphism , unique
  where
  module P  = Partiality-algebra P
  module P′ = Partiality-algebra P′

  args : Arguments p q P
  args = record
    { P  = λ _ → P′.Type
    ; Q  = λ x y _ → x P′.⊑ y
    ; pe = P′.never
    ; po = P′.now
    ; pl = λ _ → P′.⨆
    ; pa = λ x⊑y y⊑x u v u⊑v v⊑u →
             let eq = Partiality-algebra.antisymmetry P x⊑y y⊑x in

             subst (const P′.Type) eq u  ≡⟨ subst-const eq ⟩
             u                           ≡⟨ P′.antisymmetry u⊑v v⊑u ⟩∎
             v                           ∎
    ; pp = _⇔_.to set⇔UIP P′.Type-is-set
    ; qr = λ _ → P′.⊑-refl
    ; qt = λ _ _ _ _ _ → P′.⊑-trans
    ; qe = λ _ → P′.never⊑
    ; qu = λ _ → P′.upper-bound
    ; ql = λ _ _ _ → P′.least-upper-bound
    ; qp = λ _ _ _ → _⇔_.to propositional⇔irrelevant P′.⊑-propositional
           -- If the expression above is replaced by
           -- P′.⊑-proof-irrelevant, then
           -- Partiality-monad.Inductive.Monad.Adjunction.join-correct
           -- no longer type-checks.
    }

  module E = Eliminators (elims args)

  morphism : Morphism P P′
  morphism = record
    { function     = E.⊥-rec
    ; monotone     = E.⊑-rec
    ; strict       = E.⊥-rec-never
    ; now-to-now   = E.⊥-rec-now
    ; ω-continuous = E.⊥-rec-⨆
    }

  open Morphism

  function-unique : (f : Morphism P P′) →
                    E.⊥-rec ≡ function f
  function-unique f = sym $ ext $ Eliminators.⊥-rec (elims (record
    { Q  = λ _ _ _ → ↑ _ ⊤
    ; pe = function f P.never  ≡⟨ strict f ⟩
           P′.never            ≡⟨ sym $ E.⊥-rec-never ⟩∎
           E.⊥-rec P.never     ∎
    ; po = λ x →
             function f (P.now x)  ≡⟨ now-to-now f x ⟩
             P′.now x              ≡⟨ sym $ E.⊥-rec-now x ⟩∎
             E.⊥-rec (P.now x)     ∎
    ; pl = λ s hyp →
             function f (P.⨆ s)            ≡⟨ ω-continuous f s ⟩
             P′.⨆ (sequence-function f s)  ≡⟨ cong P′.⨆ $ _↔_.to P′.equality-characterisation-increasing (proj₁ hyp) ⟩
             P′.⨆ (E.inc-rec s)            ≡⟨ sym $ E.⊥-rec-⨆ s ⟩
             E.⊥-rec (P.⨆ s)               ∎
    ; pa = λ _ _ _ _ _ _ → _⇔_.to set⇔UIP P′.Type-is-set _ _
    ; pp = λ _ _ → _⇔_.to set⇔UIP (mono₁ 1 (P′.Type-is-set _ _)) _ _
    ; qp = λ _ _ _ _ _ → refl
    }))

  unique : ∀ f → morphism ≡ f
  unique f =
    _↔_.to equality-characterisation-Morphism (function-unique f)

-- Any partiality algebra with initiality (at certain sufficiently
-- large sizes) has eliminators (at certain sizes).

initiality→eliminators :
  ∀ {a p q p′ q′} {A : Set a} {P : Partiality-algebra p′ q′ A}
  (initial : Initial (p ⊔ p′) (q ⊔ q′) P) →
  Elimination-principle p q P
initiality→eliminators {p = p} {q} {p′} {q′} {A} {PA} initial args =
  record
    { ⊥-rec       = ⊥-rec
    ; ⊑-rec       = ⊑-rec
    ; ⊥-rec-never = ⊥-rec-never
    ; ⊥-rec-now   = ⊥-rec-now
    ; ⊥-rec-⨆     = ⊥-rec-⨆
    }
  where
  open Partiality-algebra PA

  open Arguments args

  private

    -- A partiality algebra with ∃ P as the carrier type.

    ∃PA : Partiality-algebra (p ⊔ p′) (q ⊔ q′) A
    ∃PA = record
      { Type                    = ∃ P
      ; partiality-algebra-with = record
        { _⊑_                = λ { (_ , p) (_ , q) → ∃ (Q p q) }
        ; never              = never , pe
        ; now                = λ x → now x , po x
        ; ⨆                  = λ s → ⨆ (Σ-map (proj₁ ⊚_) (proj₁ ⊚_) s)
                                   , pl _ ( proj₂ ⊚ proj₁ s
                                          , proj₂ ⊚ proj₂ s
                                          )
        ; antisymmetry       = λ { {x = (x , p)} {y = (y , q)}
                                   (x⊑y , Qx⊑y) (y⊑x , Qy⊑x) →
                                   Σ-≡,≡→≡
                                     (antisymmetry x⊑y y⊑x)
                                     (pa x⊑y y⊑x p q Qx⊑y Qy⊑x)
                                 }
        ; Type-UIP-unused    = _⇔_.to propositional⇔irrelevant
                                 (Σ-closure 2
                                    Type-is-set
                                    (λ _ → _⇔_.from set⇔UIP pp)
                                    _ _)
        ; ⊑-refl             = λ _ → _ , qr _ _
        ; ⊑-trans            = Σ-zip ⊑-trans (qt _ _ _ _ _)
        ; never⊑             = λ _ → _ , qe _ _
        ; upper-bound        = λ _ _ → upper-bound _ _ , qu _ _ _
        ; least-upper-bound  = λ _ _ ⊑qs →
                                   least-upper-bound _ _ (proj₁ ⊚ ⊑qs)
                                 , ql _ _ _ _ _ (proj₂ ⊚ ⊑qs)
        ; ⊑-proof-irrelevant = _⇔_.to propositional⇔irrelevant
                                 (Σ-closure 1 ⊑-propositional λ _ →
                                    _⇔_.from propositional⇔irrelevant
                                      (qp _ _ _))
        }
      }

    -- Initiality gives us a morphism from PA to ∃PA.

    eliminator-morphism : Morphism PA ∃PA
    eliminator-morphism = proj₁ (initial ∃PA)

    open Morphism eliminator-morphism

    -- We can construct a morphism from ∃PA to PA directly.

    proj₁-morphism : Morphism ∃PA PA
    proj₁-morphism = record
      { function     = proj₁
      ; monotone     = proj₁
      ; strict       = refl
      ; now-to-now   = λ _ → refl
      ; ω-continuous = λ _ → refl
      }

    -- By composing the two morphisms we get an endomorphism on PA.

    id′ : Morphism PA PA
    id′ = proj₁-morphism ∘ eliminator-morphism

    -- Due to initiality this morphism must be equal to id.

    id′≡id : id′ ≡ id
    id′≡id =
      let m , unique = lower-initiality p q PA initial PA in

      id′  ≡⟨ sym $ unique id′ ⟩
      m    ≡⟨ unique id ⟩∎
      id   ∎

    abstract

      -- This provides us with a key lemma used to define the
      -- eliminators.

      lemma : ∀ x → proj₁ (function x) ≡ x
      lemma x = cong (λ m → Morphism.function m x) id′≡id

    -- As an aside this means that there is a split surjection from
    -- ∃ P to Type.

    ↠Type : ∃ P ↠ Type
    ↠Type = record
      { logical-equivalence = record
        { to   = Morphism.function proj₁-morphism
        ; from = function
        }
      ; right-inverse-of = lemma
      }

  -- The eliminators.

  ⊥-rec : ∀ x → P x
  ⊥-rec x =                 $⟨ proj₂ (function x) ⟩
    P (proj₁ (function x))  ↝⟨ subst P (lemma x) ⟩□
    P x                     □

  ⊑-rec : ∀ {x y} (x⊑y : x ⊑ y) → Q (⊥-rec x) (⊥-rec y) x⊑y
  ⊑-rec {x} {y} x⊑y =                                                   $⟨ proj₂ (monotone x⊑y) ⟩
    Q (proj₂ (function x)) (proj₂ (function y)) (proj₁ (monotone x⊑y))  ↝⟨ subst Q′ $
                                                                             Σ-≡,≡→≡ (cong₂ _,_ (lemma x) (lemma y)) (
        subst (λ xy → P (proj₁ xy) × P (proj₂ xy) ×
                      proj₁ xy ⊑ proj₂ xy)
              (cong₂ _,_ (lemma x) (lemma y))
              ( proj₂ (function x)
              , proj₂ (function y)
              , proj₁ (monotone x⊑y)
              )                                                                 ≡⟨ push-subst-, {y≡z = cong₂ _,_ (lemma x) (lemma y)}
                                                                                                (λ xy → P (proj₁ xy))
                                                                                                (λ xy → P (proj₂ xy) × proj₁ xy ⊑ proj₂ xy)
                                                                                                {p = ( proj₂ (function x)
                                                                                                     , proj₂ (function y)
                                                                                                     , proj₁ (monotone x⊑y)
                                                                                                     )} ⟩
        ( subst (λ xy → P (proj₁ xy))
                (cong₂ _,_ (lemma x) (lemma y))
                (proj₂ (function x))
        , subst (λ xy → P (proj₂ xy) × proj₁ xy ⊑ proj₂ xy)
                (cong₂ _,_ (lemma x) (lemma y))
                ( proj₂ (function y)
                , proj₁ (monotone x⊑y)
                )
        )                                                                       ≡⟨ cong₂ _,_
                                                                                     (subst-∘ P proj₁ (cong₂ _,_ (lemma x) (lemma y))
                                                                                              {p = proj₂ (function x)})
                                                                                     (push-subst-, {y≡z = cong₂ _,_ (lemma x) (lemma y)}
                                                                                                   (λ xy → P (proj₂ xy))
                                                                                                   (λ xy → proj₁ xy ⊑ proj₂ xy)
                                                                                                   {p = ( proj₂ (function y)
                                                                                                        , proj₁ (monotone x⊑y)
                                                                                                        )}) ⟩
        ( subst P (cong proj₁ $ cong₂ _,_ (lemma x) (lemma y))
                (proj₂ (function x))
        , subst (λ xy → P (proj₂ xy))
                (cong₂ _,_ (lemma x) (lemma y))
                (proj₂ (function y))
        , subst (λ xy → proj₁ xy ⊑ proj₂ xy)
                (cong₂ _,_ (lemma x) (lemma y))
                (proj₁ (monotone x⊑y))
        )                                                                       ≡⟨ cong₂ _,_
                                                                                     (cong (λ p → subst P p (proj₂ (function x))) $
                                                                                        cong-proj₁-cong₂-, (lemma x) (lemma y))
                                                                                     (cong₂ _,_
                                                                                        (subst-∘ P proj₂ (cong₂ _,_ (lemma x) (lemma y))
                                                                                                 {p = proj₂ (function y)})
                                                                                        (_⇔_.to propositional⇔irrelevant
                                                                                           ⊑-propositional
                                                                                           _ _)) ⟩
        ( subst P (lemma x) (proj₂ (function x))
        , subst P (cong proj₂ $ cong₂ _,_ (lemma x) (lemma y))
                (proj₂ (function y))
        , x⊑y
        )                                                                       ≡⟨ cong (λ p → ⊥-rec x , subst P p (proj₂ (function y)) , x⊑y) $
                                                                                     cong-proj₂-cong₂-, (lemma x) (lemma y) ⟩∎
        (⊥-rec x , ⊥-rec y , x⊑y)                                               ∎) ⟩□

    Q (⊥-rec x) (⊥-rec y) x⊑y                                           □
    where
    Q′ :
      (∃ λ xy → P (proj₁ xy) × P (proj₂ xy) × proj₁ xy ⊑ proj₂ xy) →
      Set q
    Q′ (_ , px , py , x⊑y) = Q px py x⊑y

  inc-rec : ∀ s → Inc P Q s
  inc-rec (s , inc) = ⊥-rec ⊚ s , ⊑-rec ⊚ inc

  -- "Computation" rules.

  private

    -- A lemma.

    ⊥-rec-lemma′ :
      ∀ {a b} {A : Set a} {B : A → Set b} {x y : Σ A B} →
      Is-set A →
      x ≡ y → (p : proj₁ x ≡ proj₁ y) →
      subst B p (proj₂ x) ≡ proj₂ y
    ⊥-rec-lemma′ {B = B} A-set =
      elim (λ {x y} _ → (p : proj₁ x ≡ proj₁ y) →
                        subst B p (proj₂ x) ≡ proj₂ y)
           (λ { (_ , x₂) p →
                subst B p x₂     ≡⟨ cong (λ p → subst B p _) $
                                      _⇔_.to set⇔UIP A-set p refl ⟩
                subst B refl x₂  ≡⟨⟩

                x₂               ∎
              })

    -- A specific instance of the lemma above.

    ⊥-rec-lemma : ∀ {x y} → function x ≡ (x , y) → ⊥-rec x ≡ y
    ⊥-rec-lemma {x} {y} eq =
      ⊥-rec x                                 ≡⟨⟩
      subst P (lemma x) (proj₂ (function x))  ≡⟨ ⊥-rec-lemma′ Type-is-set eq (lemma x) ⟩∎
      y                                       ∎

  ⊥-rec-never : ⊥-rec never ≡ pe
  ⊥-rec-never = ⊥-rec-lemma strict

  ⊥-rec-now : ∀ x → ⊥-rec (now x) ≡ po x
  ⊥-rec-now x = ⊥-rec-lemma (now-to-now x)

  ⊥-rec-⨆ : ∀ s → ⊥-rec (⨆ s) ≡ pl s (inc-rec s)
  ⊥-rec-⨆ s = ⊥-rec-lemma
    (function (⨆ s)                                           ≡⟨ ω-continuous s ⟩

     ⨆ (Σ-map (proj₁ ⊚_) (proj₁ ⊚_) (sequence-function s)) ,
     pl _ ( proj₂ ⊚ proj₁ (sequence-function s)
          , proj₂ ⊚ proj₂ (sequence-function s)
          )                                                   ≡⟨⟩

     ⨆ ( proj₁ ⊚ function ⊚ proj₁ s
       , proj₁ ⊚ monotone ⊚ proj₂ s
       ) ,
     pl _ ( proj₂ ⊚ function ⊚ proj₁ s
          , proj₂ ⊚ monotone ⊚ proj₂ s
          )                                                   ≡⟨ Σ-≡,≡→≡ (cong ⨆ lemma₁) lemma₂ ⟩

     ⨆ s , pl s ( ⊥-rec ⊚ proj₁ s
                , ⊑-rec ⊚ proj₂ s
                )                                             ≡⟨⟩

     ⨆ s , pl s (inc-rec s)                                   ∎)
     where
     lemma₁ =
       ( proj₁ ⊚ function ⊚ proj₁ s
       , proj₁ ⊚ monotone ⊚ proj₂ s
       )                             ≡⟨ _↔_.to equality-characterisation-increasing (λ n →
                                          lemma (s [ n ])) ⟩∎
       s                             ∎

     lemma₂ =
       subst P (cong ⨆ lemma₁)
         (pl _ ( proj₂ ⊚ function ⊚ proj₁ s
               , proj₂ ⊚ monotone ⊚ proj₂ s
               ))                                                 ≡⟨ sym $ subst-∘ P ⨆ lemma₁ ⟩

       subst (P ⊚ ⨆) lemma₁
         (pl _ ( proj₂ ⊚ function ⊚ proj₁ s
               , proj₂ ⊚ monotone ⊚ proj₂ s
               ))                                                 ≡⟨ elim
                                                                       (λ {s′ s} eq → ∀ {i′ i} →
                                                                                      subst (λ s → ∀ n → P (s [ n ])) eq (proj₁ i′) ≡ proj₁ i →
                                                                                      subst (P ⊚ ⨆) eq (pl s′ i′) ≡ pl s i)
                                                                       (λ s {i′ i} eq →
                                                                          pl s i′  ≡⟨ cong (pl s) (Σ-≡,≡→≡ eq (ext λ _ → qp _ _ _ _ _)) ⟩∎
                                                                          pl s i   ∎)
                                                                       lemma₁
                                                                       (ext λ n →
           let lemma₃ =
                 cong _[ n ] lemma₁                                       ≡⟨ sym $ cong-∘ (_$ n) proj₁ lemma₁ ⟩

                 cong (_$ n) (cong proj₁ lemma₁)                          ≡⟨ cong (cong (_$ n)) $
                                                                               proj₁-Σ-≡,≡→≡ (Eq.good-ext ext (lemma ⊚ proj₁ s)) _ ⟩
                 cong (_$ n) (Eq.good-ext ext (lemma ⊚ proj₁ s))          ≡⟨ Eq.cong-good-ext ext (lemma ⊚ proj₁ s) ⟩∎

                 lemma (s [ n ])                                          ∎
           in
           subst (λ s → ∀ n → P (s [ n ])) lemma₁
                 (proj₂ ⊚ function ⊚ proj₁ s) n                           ≡⟨ sym $ push-subst-application lemma₁ (λ s n → P (s [ n ])) ⟩

           subst (λ s → P (s [ n ])) lemma₁
                 (proj₂ (function (s [ n ])))                             ≡⟨ subst-∘ P _[ n ] lemma₁ ⟩

           subst P (cong _[ n ] lemma₁)
                 (proj₂ (function (s [ n ])))                             ≡⟨ cong (λ eq → subst P eq (proj₂ (function (s [ n ])))) lemma₃ ⟩∎

           subst P (lemma (s [ n ]))
                 (proj₂ (function (s [ n ])))                             ∎) ⟩

       pl s ( (λ n → subst P (lemma (s [ n ]))
                           (proj₂ (function (s [ n ]))))
            , ⊑-rec ⊚ proj₂ s
            )                                                     ≡⟨⟩

       pl s ( ⊥-rec ⊚ proj₁ s
            , ⊑-rec ⊚ proj₂ s
            )                                                     ∎

-- For any partiality algebra (with certain levels) initiality (at
-- possibly larger levels) is logically equivalent to having
-- eliminators (at the same possibly larger levels).

initiality⇔eliminators :
  ∀ {a p q p′ q′} {A : Set a} →
  (P : Partiality-algebra p′ q′ A) →
  Initial (p ⊔ p′) (q ⊔ q′) P
    ⇔
  Elimination-principle (p ⊔ p′) (q ⊔ q′) P
initiality⇔eliminators P = record
  { to   = initiality→eliminators
  ; from = eliminators→initiality P
  }

-- For any partiality algebra initiality at all levels is logically
-- equivalent (at the meta-level) to having eliminators at all levels.

∀initiality→∀eliminators :
  ∀ {a p q} {A : Set a} →
  (P : Partiality-algebra p q A) →
  (∀ p q → Initial p q P) →
  (∀ p q → Elimination-principle p q P)
∀initiality→∀eliminators {p = p′} {q = q′} P initial p q =
  initiality→eliminators (initial (p ⊔ p′) (q ⊔ q′))

∀eliminators→∀initiality :
  ∀ {a p q} {A : Set a} →
  (P : Partiality-algebra p q A) →
  (∀ p q → Elimination-principle p q P) →
  (∀ p q → Initial p q P)
∀eliminators→∀initiality P elim p q =
  eliminators→initiality P (elim p q)