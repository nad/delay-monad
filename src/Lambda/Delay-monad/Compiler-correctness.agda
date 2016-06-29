------------------------------------------------------------------------
-- Compiler correctness
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Lambda.Delay-monad.Compiler-correctness where

open import Equality.Propositional
open import Interval using (ext)
open import Prelude

open import Maybe equality-with-J
open import Monad equality-with-J

open import Delay-monad.Monad
open import Delay-monad.Strong-bisimilarity
open import Delay-monad.Weak-bisimilarity

open import Lambda.Compiler
open import Lambda.Delay-monad.Interpreter
open import Lambda.Delay-monad.Virtual-machine
open import Lambda.Syntax hiding ([_])
open import Lambda.Virtual-machine

private
  module C = Closure Code
  module T = Closure Tm

-- Bind preserves strong bisimilarity.

infixl 5 _>>=-congM_

_>>=-congM_ :
  ∀ {i ℓ} {A B : Set ℓ} {x y : M ∞ A} {f g : A → M ∞ B} →
  Strongly-bisimilar i (run x) (run y) →
  (∀ z → Strongly-bisimilar i (run (f z)) (run (g z))) →
  Strongly-bisimilar i (run (x >>= f)) (run (y >>= g))
p >>=-congM q = p >>=-cong-∼ [ (λ _ → run fail ∎∼) , q ]

-- Bind is associative.

associativityM :
  ∀ {ℓ} {A B C : Set ℓ} (x : M ∞ A) (f : A → M ∞ B) (g : B → M ∞ C) →
  run (x >>= (λ x → f x >>= g)) ∼ run (x >>= f >>= g)
associativityM x f g =
  run (x >>= λ x → f x >>= g)                                       ∼⟨⟩

  run x >>=′ maybe (λ x → run (f x >>= g)) (return nothing)         ∼⟨ (run x ∎∼) >>=-cong-∼ [ (λ _ → run fail ∎∼) , (λ x → run (f x >>= g) ∎∼) ] ⟩

  run x >>=′ (λ x → maybe (MaybeT.run ∘ f) (return nothing) x >>=′
                    maybe (MaybeT.run ∘ g) (return nothing))        ∼⟨ associativity′ (run x) _ _ ⟩

  run x >>=′ maybe (MaybeT.run ∘ f) (return nothing)
        >>=′ maybe (MaybeT.run ∘ g) (return nothing)                ∼⟨⟩

  run (x >>= f >>= g)                                               ∎∼

-- Compiler correctness.

mutual

  ⟦⟧-correct :
    ∀ {i n} t {ρ : T.Env n} {c s} {k : T.Value → M ∞ C.Value} →
    (∀ v → Weakly-bisimilar i
             (run (exec ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩))
             (run (k v))) →
    Weakly-bisimilar i
      (run (exec ⟨ comp t c , s , comp-env ρ ⟩))
      (run (⟦ t ⟧ ρ >>= k))

  ⟦⟧-correct (con i) {ρ} {c} {s} {k} hyp =
    run (exec ⟨ con i ∷ c , s , comp-env ρ ⟩)                     ≳⟨⟩
    run (exec ⟨ c , val (comp-val (T.con i)) ∷ s , comp-env ρ ⟩)  ≈⟨ hyp (T.con i) ⟩
    run (k (T.con i))                                             ∼⟨⟩
    run (⟦ con i ⟧ ρ >>= k)                                       ∎∼

  ⟦⟧-correct (var x) {ρ} {c} {s} {k} hyp =
    run (exec ⟨ var x ∷ c , s , comp-env ρ ⟩)                 ≳⟨⟩
    run (exec ⟨ c , val (comp-val (ρ x)) ∷ s , comp-env ρ ⟩)  ≈⟨ hyp (ρ x) ⟩
    run (k (ρ x))                                             ∼⟨⟩
    run (⟦ var x ⟧ ρ >>= k)                                   ∎∼

  ⟦⟧-correct (ƛ t) {ρ} {c} {s} {k} hyp =
    run (exec ⟨ clo (comp t (ret ∷ [])) ∷ c , s , comp-env ρ ⟩)   ≳⟨⟩
    run (exec ⟨ c , val (comp-val (T.ƛ t ρ)) ∷ s , comp-env ρ ⟩)  ≈⟨ hyp (T.ƛ t ρ) ⟩
    run (k (T.ƛ t ρ))                                             ∼⟨⟩
    run (⟦ ƛ t ⟧ ρ >>= k)                                         ∎∼

  ⟦⟧-correct (t₁ · t₂) {ρ} {c} {s} {k} hyp =
    run (exec ⟨ comp t₁ (comp t₂ (app ∷ c)) , s , comp-env ρ ⟩)    ≈⟨ (⟦⟧-correct t₁ λ v₁ → ⟦⟧-correct t₂ λ v₂ → ∙-correct v₁ v₂ hyp) ⟩

    run (⟦ t₁ ⟧ ρ >>= λ v₁ → ⟦ t₂ ⟧ ρ >>= λ v₂ → v₁ ∙ v₂ >>= k)    ∼⟨ (run (⟦ t₁ ⟧ ρ) ∎∼) >>=-congM (λ _ → associativityM (⟦ t₂ ⟧ ρ) _ _) ⟩

    run (⟦ t₁ ⟧ ρ >>= λ v₁ → (⟦ t₂ ⟧ ρ >>= λ v₂ → v₁ ∙ v₂) >>= k)  ∼⟨ associativityM (⟦ t₁ ⟧ ρ) _ _ ⟩

    run (⟦ t₁ · t₂ ⟧ ρ >>= k)                                      ∎∼

  ∙-correct :
    ∀ {i n} v₁ v₂ {ρ : T.Env n} {c s} {k : T.Value → M ∞ C.Value} →
    (∀ v → Weakly-bisimilar i
             (run (exec ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩))
             (run (k v))) →
    Weakly-bisimilar i
      (run (exec ⟨ app ∷ c
                 , val (comp-val v₂) ∷ val (comp-val v₁) ∷ s
                 , comp-env ρ
                 ⟩))
      (run (v₁ ∙ v₂ >>= k))
  ∙-correct (T.con i) v₂ {ρ} {c} {s} {k} hyp =
    run (exec ⟨ app ∷ c
              , val (comp-val v₂) ∷ val (C.con i) ∷ s
              , comp-env ρ
              ⟩)                                       ≈⟨⟩

    run fail                                           ≈⟨⟩

    run (T.con i ∙ v₂ >>= k)                           ∎≈

  ∙-correct (T.ƛ t₁ ρ₁) v₂ {ρ} {c} {s} {k} hyp =
    run (exec ⟨ app ∷ c
              , val (comp-val v₂) ∷ val (comp-val (T.ƛ t₁ ρ₁)) ∷ s
              , comp-env ρ
              ⟩)                                                    ≈⟨ later-cong (

      run (exec ⟨ comp t₁ (ret ∷ [])
                , ret c (comp-env ρ) ∷ s
                , snoc (comp-env ρ₁) (comp-val v₂)
             ⟩)                                                          ≡⟨ cong (λ ρ′ →
                                                                                    run (exec ⟨ comp t₁ (ret ∷ []) , ret c (comp-env ρ) ∷ s , ρ′ ⟩))
                                                                                 (ext [ (λ _ → refl) , (λ _ → refl) ]) ⟩∞≈
      run (exec ⟨ comp t₁ (ret ∷ [])
                , ret c (comp-env ρ) ∷ s
                , comp-env (snoc ρ₁ v₂)
                ⟩)                                                       ≈⟨ ∞⟦⟧-correct t₁ (λ v →

        run (exec ⟨ ret ∷ []
                  , val (comp-val v) ∷ ret c (comp-env ρ) ∷ s
                  , comp-env (snoc ρ₁ v₂)
                  ⟩)                                                          ≳⟨⟩

        run (exec ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩)                  ≈⟨ hyp v ⟩∎

        run (k v)                                                             ∎) ⟩∞

      run (⟦ t₁ ⟧ (snoc ρ₁ v₂) >>= k)                                    ∎∼) ⟩∎

    run (T.ƛ t₁ ρ₁ ∙ v₂ >>= k)                                      ∎

  ∞⟦⟧-correct :
    ∀ {i n} t {ρ : T.Env n} {c s} {k : T.Value → M ∞ C.Value} →
    (∀ v → Weakly-bisimilar i
             (run (exec ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩))
             (run (k v))) →
    ∞Weakly-bisimilar i
      (run (exec ⟨ comp t c , s , comp-env ρ ⟩))
      (run (⟦ t ⟧ ρ >>= k))
  force (∞⟦⟧-correct t hyp) = ⟦⟧-correct t hyp

-- Note that the equality that is used here is syntactic.

correct :
  ∀ t →
  exec ⟨ comp t [] , [] , empty ⟩ ≈M
  ⟦ t ⟧ empty >>= λ v → return (comp-val v)
correct t =
  run (exec ⟨ comp t [] , [] , empty ⟩)            ≡⟨ cong (λ ρ → run (exec ⟨ comp t [] , [] , ρ ⟩)) (ext λ()) ⟩≈
  run (exec ⟨ comp t [] , [] , comp-env empty ⟩)   ≈⟨ ⟦⟧-correct t (λ v → return (just (comp-val v)) ∎≈) ⟩∎
  run (⟦ t ⟧ empty >>= λ v → return (comp-val v))  ∎