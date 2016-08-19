------------------------------------------------------------------------
-- A partial inductive-recursive definition of the partiality monad,
-- without path or truncation constructors, in order to get the basics
-- right
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Partiality-monad.Inductive.Preliminary-sketch where

open import Prelude hiding (⊥)

-- The partiality monad _⊥ and the information ordering _⊑_ are
-- defined as a single inductive family D. A boolean index is used to
-- separate the two types. I (NAD) think that Conor McBride once
-- pointed out that inductive-inductive types can be encoded as
-- inductive-recursive types in (roughly) the following way.

I : ∀ {a} → Set a → Bool → Set a

data D {a} (A : Set a) : (b : Bool) → I A b → Set a

infix 10 _⊥
infix  4 _⊑_

_⊥  : ∀ {a} → Set a → Set a
_⊑_ : ∀ {a} {A : Set a} → A ⊥ → A ⊥ → Set a

-- _⊥ is not indexed, but _⊑_ is indexed by two values of type A ⊥
-- (for some A).

I A true  = ↑ _ ⊤
I A false = A ⊥ × A ⊥

A ⊥ = D A true _

x ⊑ y = D _ false (x , y)

-- Increasing sequences.

Increasing-sequence : ∀ {a} → Set a → Set a
Increasing-sequence A = ∃ λ (f : ℕ → A ⊥) → ∀ n → f n ⊑ f (suc n)

-- Projection functions for Increasing-sequence.

infix 30 _[_]

_[_] : ∀ {a} {A : Set a} → Increasing-sequence A → ℕ → A ⊥
s [ n ] = proj₁ s n

increasing : ∀ {a} {A : Set a}
             (s : Increasing-sequence A) →
             ∀ n → s [ n ] ⊑ s [ suc n ]
increasing = proj₂

-- Upper bounds.

Is-upper-bound : ∀ {a} {A : Set a} →
                 Increasing-sequence A → A ⊥ → Set a
Is-upper-bound s x = ∀ n → s [ n ] ⊑ x

-- _⊥ and _⊑_.

data D {a} (A : Set a) where
  never : A ⊥
  now   : (x : A) → A ⊥
  ⨆     : (s : Increasing-sequence A) → A ⊥

  ⊑-refl            : (x : A ⊥) → x ⊑ x
  never⊑            : (x : A ⊥) → never ⊑ x
  upper-bound′      : (s : Increasing-sequence A) (ub : A ⊥)
                      (is-ub : ⨆ s ⊑ ub) → Is-upper-bound s ub
  least-upper-bound : (s : Increasing-sequence A) (ub : A ⊥)
                      (is-ub : Is-upper-bound s ub) → ⨆ s ⊑ ub

-- Some examples.

-- ⨆ s is an upper bound for the sequence s.

upper-bound : ∀ {a} {A : Set a}
              (s : Increasing-sequence A) →
              Is-upper-bound s (⨆ s)
upper-bound s = upper-bound′ s (⨆ s) (⊑-refl (⨆ s))

-- Transitivity.

⊑-trans : ∀ {a} {A : Set a} {x y z : A ⊥} → x ⊑ y → y ⊑ z → x ⊑ z
⊑-trans (⊑-refl y)                  y⊑z  = y⊑z
⊑-trans (never⊑ y)                  y⊑z  = never⊑ _
⊑-trans (upper-bound′ s ub is-ub n) ub⊑z =
  ⊑-trans (proj₂ s n) (upper-bound′ s _ (⊑-trans is-ub ub⊑z) (suc n))
⊑-trans (least-upper-bound s ub is-ub) ub⊑z =
  least-upper-bound s _ (λ n → ⊑-trans (is-ub n) ub⊑z)

-- A monotone map function.

I-map : ∀ {a b} {A : Set a} {B : Set b} →
        (f : A → B) → ∀ {b} → I A b → I B b

Increasing-sequence-map :
  ∀ {a b} {A : Set a} {B : Set b} →
  (f : A → B) → Increasing-sequence A → Increasing-sequence B

D-map : ∀ {a b} {A : Set a} {B : Set b} →
        (f : A → B) → ∀ {i b} → D A i b → D B i (I-map f b)

I-map f {b = true}  _       = _
I-map f {b = false} (x , y) = D-map f x , D-map f y

Increasing-sequence-map f (s , inc) =
  (λ n → D-map f (s   n)) ,
  (λ n → D-map f (inc n))

D-map f never                          = never
D-map f (now x)                        = now (f x)
D-map f (⨆ s)                          = ⨆ (Increasing-sequence-map f s)
D-map f (⊑-refl x)                     = ⊑-refl (D-map f x)
D-map f (never⊑ x)                     = never⊑ (D-map f x)
D-map f (upper-bound′ s ub is-ub n)    = upper-bound′
                                           (Increasing-sequence-map f s)
                                           (D-map f ub)
                                           (D-map f is-ub)
                                           n
D-map f (least-upper-bound s ub is-ub) = least-upper-bound
                                           (Increasing-sequence-map f s)
                                           (D-map f ub)
                                           (λ n → D-map f (is-ub n))

-- Predicate transformer related to increasing sequences.

Inc : ∀ {a p q} {A : Set a}
      (P : A ⊥ → Set p) →
      (∀ {x y} → P x → P y → x ⊑ y → Set q) →
      Increasing-sequence A → Set (p ⊔ q)
Inc P Q s =
  ∃ λ (p : ∀ n → P (s [ n ])) →
    ∀ n → Q (p n) (p (suc n)) (increasing s n)

-- Record wrapping up the eliminators' arguments.

record Rec-args
         {a p q} {A : Set a}
         (P : A ⊥ → Set p)
         (Q : ∀ {x y} → P x → P y → x ⊑ y → Set q) :
         Set (a ⊔ p ⊔ q) where
  field
    pe : P never
    po : ∀ x → P (now x)
    pl : ∀ s (pq : Inc P Q s) → P (⨆ s)
    qr : ∀ x (p : P x) → Q p p (⊑-refl x)
    qe : ∀ x (p : P x) → Q pe p (never⊑ x)
    qu : ∀ s ub is-ub n (pq : Inc P Q s) (pu : P ub)
         (qu : Q (pl s pq) pu is-ub) →
         Q (proj₁ pq n) pu (upper-bound′ s ub is-ub n)
    ql : ∀ s ub is-ub (pq : Inc P Q s) (pu : P ub)
         (qu : ∀ n → Q (proj₁ pq n) pu (is-ub n)) →
         Q (pl s pq) pu (least-upper-bound s ub is-ub)

-- Mutually defined dependent eliminators.

module _
  {a p q} {A : Set a}
  {P : A ⊥ → Set p}
  {Q : ∀ {x y} → P x → P y → x ⊑ y → Set q}
  (args : Rec-args P Q)
  where

  open Rec-args args

  ⊥-rec   : (x : A ⊥) → P x
  inc-rec : (s : Increasing-sequence A) → Inc P Q s
  ⊑-rec   : ∀ {x y} (x⊑y : x ⊑ y) → Q (⊥-rec x) (⊥-rec y) x⊑y

  ⊥-rec never   = pe
  ⊥-rec (now x) = po x
  ⊥-rec (⨆ s)   = pl s (inc-rec s)

  inc-rec (s , inc) = ( (λ n → ⊥-rec (s   n))
                      , (λ n → ⊑-rec (inc n))
                      )

  ⊑-rec (⊑-refl x)                     = qr x (⊥-rec x)
  ⊑-rec (never⊑ x)                     = qe x (⊥-rec x)
  ⊑-rec (upper-bound′ s ub is-ub n)    = qu s ub is-ub n
                                            (inc-rec s) (⊥-rec ub)
                                            (⊑-rec is-ub)
  ⊑-rec (least-upper-bound s ub is-ub) = ql s ub is-ub
                                            (inc-rec s) (⊥-rec ub)
                                            (λ n → ⊑-rec (is-ub n))

-- These dependent eliminators can be used to define a monotone map
-- function.

module _ {a b} {A : Set a} {B : Set b} (f : A → B) where

  private

    map-args : Rec-args (λ (_ : A ⊥) → B ⊥) (λ u v _ → u ⊑ v)
    map-args = record
      { pe = never
      ; po = now ∘ f
      ; pl = λ _ → ⨆
      ; qr = λ _ → ⊑-refl
      ; qe = λ _ → never⊑
      ; qu = λ _ _ _ n pq pu pu-is-ub →
               upper-bound′ pq pu pu-is-ub n
      ; ql = λ _ _ _ → least-upper-bound
      }

  map : A ⊥ → B ⊥
  map = ⊥-rec map-args

  map-monotone : ∀ {x y} → x ⊑ y → map x ⊑ map y
  map-monotone = ⊑-rec map-args
