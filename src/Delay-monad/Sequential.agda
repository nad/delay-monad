------------------------------------------------------------------------
-- A combinator for running two (independent) computations in sequence
------------------------------------------------------------------------

{-# OPTIONS --safe --sized-types #-}

module Delay-monad.Sequential where

open import Equality.Propositional as Eq using (_≡_)
open import Prelude hiding (_+_)
open import Prelude.Size

open import Conat Eq.equality-with-J as Conat
  using (zero; suc; force; _+_)

open import Delay-monad
open import Delay-monad.Bisimilarity
open import Delay-monad.Bisimilarity.Kind
open import Delay-monad.Monad

private

  variable
    a               : Level
    A B C           : Type a
    i               : Size
    k               : Kind
    f₁ f₂           : Delay (A → B) ∞
    x x₁ x₂ y y₁ y₂ : Delay A ∞
    f′              : Delay′ (A → B) ∞
    x′              : Delay′ A ∞
    h               : A → B
    z               : A

------------------------------------------------------------------------
-- The _⊛_ operator

-- Sequential composition of computations.

infixl 6 _⊛_

_⊛_ : Delay (A → B) i → Delay A i → Delay B i
f ⊛ x = f >>=′ λ f → x >>=′ λ x → now (f x)

-- The number of later constructors in f ⊛ x is bisimilar to the sum
-- of the number of later constructors in f and the number of later
-- constructors in x.

steps-⊛∼steps-+-steps :
  (f : Delay (A → B) ∞) →
  Conat.[ i ] steps (f ⊛ x) ∼ steps f + steps x
steps-⊛∼steps-+-steps {x = now _}   (now _)   = zero
steps-⊛∼steps-+-steps {x = later _} (now _)   = suc λ { .force → steps-⊛∼steps-+-steps (now _)    }
steps-⊛∼steps-+-steps               (later f) = suc λ { .force → steps-⊛∼steps-+-steps (f .force) }

-- A rearrangement lemma for _⊛_.

later-⊛∼⊛-later :
  [ i ] later f′ ⊛ x′ .force ∼ f′ .force ⊛ later x′
later-⊛∼⊛-later = lemma _ Eq.refl
  where
  lemma :
    ∀ f → f′ .force ≡ f → [ i ] later f′ ⊛ x′ .force ∼ f ⊛ later x′
  lemma {f′ = f′} {x′ = x′} (now f) eq = later λ { .force →
    f′ .force ⊛ x′ .force  ≡⟨ Eq.cong (_⊛ x′ .force) eq ⟩
    now f ⊛ x′ .force      ∎ }
  lemma {f′ = f′} {x′ = x′} (later f) eq = later λ { .force →
    f′ .force ⊛ x′ .force  ≡⟨ Eq.cong (_⊛ x′ .force) eq ⟩
    later f ⊛ x′ .force    ∼⟨ later-⊛∼⊛-later ⟩∼
    f .force ⊛ later x′    ∎ }

-- The _⊛_ operator preserves strong and weak bisimilarity and
-- expansion.

infixl 6 _⊛-cong_

_⊛-cong_ :
  [ i ] f₁ ⟨ k ⟩ f₂ →
  [ i ] x₁ ⟨ k ⟩ x₂ →
  [ i ] f₁ ⊛ x₁ ⟨ k ⟩ f₂ ⊛ x₂
p ⊛-cong q = p >>=-cong λ _ → q >>=-cong λ _ → now

-- The _⊛_ operator is (kind of) commutative.

⊛-comm :
  (f : Delay (A → B) ∞) (x : Delay A ∞) →
  [ i ] f ⊛ x ∼ map′ (flip _$_) x ⊛ f
⊛-comm (now f)   (now x)   = reflexive _
⊛-comm (now f)   (later x) = later λ { .force → ⊛-comm (now f) (x .force) }
⊛-comm (later f) (now x)   = later λ { .force → ⊛-comm (f .force) (now x) }
⊛-comm (later f) (later x) = later λ { .force →
  f .force ⊛ later x                    ∼⟨ symmetric later-⊛∼⊛-later ⟩
  later f ⊛ x .force                    ∼⟨ ⊛-comm (later f) (x .force) ⟩∼
  map′ (flip _$_) (x .force) ⊛ later f  ∎ }

-- The function map′ can be expressed using _⊛_.

map∼now-⊛ : (x : Delay A ∞) → [ i ] map′ h x ∼ now h ⊛ x
map∼now-⊛ {h = h} x =
  map′ h x                           ∼⟨ map∼>>=-now _ ⟩
  (x >>=′ now ∘ h)                   ∼⟨⟩
  (now h >>=′ λ h → x >>=′ now ∘ h)  ∼⟨⟩
  now h ⊛ x                          ∎

-- The applicative functor laws hold up to strong bisimilarity.

now-id-⊛ : [ i ] now id ⊛ x ∼ x
now-id-⊛ {x = now x}   = now
now-id-⊛ {x = later x} = later λ { .force → now-id-⊛ }

now-∘-⊛-⊛-⊛ :
  (f : Delay (B → C) ∞) (g : Delay (A → B) ∞) (x : Delay A ∞) →
  [ i ] now (λ f → f ∘_) ⊛ f ⊛ g ⊛ x ∼ f ⊛ (g ⊛ x)
now-∘-⊛-⊛-⊛ (now _)   (now _)   (now _)   = now
now-∘-⊛-⊛-⊛ (now _)   (now _)   (later x) = later λ { .force → now-∘-⊛-⊛-⊛ (now _)    (now _)    (x .force) }
now-∘-⊛-⊛-⊛ (now _)   (later g) x         = later λ { .force → now-∘-⊛-⊛-⊛ (now _)    (g .force) x          }
now-∘-⊛-⊛-⊛ (later f) g         x         = later λ { .force → now-∘-⊛-⊛-⊛ (f .force) g          x          }

now-⊛-now : [ i ] now h ⊛ now z ∼ now (h z)
now-⊛-now = now

⊛-now :
  (f : Delay (A → B) ∞) →
  [ i ] f ⊛ now z ∼ now (λ f → f z) ⊛ f
⊛-now (now f)   = now
⊛-now (later f) = later λ { .force → ⊛-now (f .force) }

------------------------------------------------------------------------
-- The _∣_ operator

-- Sequential composition of computations.

infix 10 _∣_

_∣_ : Delay A i → Delay B i → Delay (A × B) i
x ∣ y = map′ _,_ x ⊛ y

-- The number of later constructors in x ∣ y is bisimilar to the sum
-- of the number of later constructors in x and the number of later
-- constructors in y.

steps-∣∼max-steps-steps :
  Conat.[ i ] steps (x ∣ y) ∼ steps x + steps y
steps-∣∼max-steps-steps {x = x} {y = y} =
  steps (x ∣ y)                 Conat.∼⟨ Conat.reflexive-∼ _ ⟩
  steps (map′ _,_ x ⊛ y)        Conat.∼⟨ steps-⊛∼steps-+-steps (map′ _,_ x) ⟩
  steps (map′ _,_ x) + steps y  Conat.∼⟨ steps-map′ x Conat.+-cong Conat.reflexive-∼ _ ⟩∎
  steps x + steps y             ∎∼

-- The _∣_ operator preserves strong and weak bisimilarity and
-- expansion.

infix 10 _∣-cong_

_∣-cong_ :
  [ i ] x₁ ⟨ k ⟩ x₂ →
  [ i ] y₁ ⟨ k ⟩ y₂ →
  [ i ] x₁ ∣ y₁ ⟨ k ⟩ x₂ ∣ y₂
p ∣-cong q = map-cong _,_ p ⊛-cong q

-- The _∣_ operator is commutative (up to swapping of results).

∣-comm : [ i ] x ∣ y ∼ map′ swap (y ∣ x)
∣-comm {x = x} {y = y} =
  x ∣ y                                                          ∼⟨⟩
  map′ _,_ x ⊛ y                                                 ∼⟨ ⊛-comm (map′ _,_ x) y ⟩
  map′ (flip _$_) y ⊛ map′ _,_ x                                 ∼⟨ map∼now-⊛ y ⊛-cong map∼now-⊛ x ⟩
  now (flip _$_) ⊛ y ⊛ (now _,_ ⊛ x)                             ∼⟨ symmetric (now-∘-⊛-⊛-⊛ (now _ ⊛ y) (now _) x) ⟩
  now (λ f → f ∘_) ⊛ (now (flip _$_) ⊛ y) ⊛ now _,_ ⊛ x          ∼⟨ symmetric (now-∘-⊛-⊛-⊛ (now _) (now _) y) ⊛-cong (now _ ∎) ⊛-cong (x ∎) ⟩
  now _∘_ ⊛ now (λ f → f ∘_) ⊛ now (flip _$_) ⊛ y ⊛ now _,_ ⊛ x  ∼⟨⟩
  now (λ x f y → f y x) ⊛ y ⊛ now _,_ ⊛ x                        ∼⟨ ⊛-now (now (λ x f y → f y x) ⊛ y) ⊛-cong (x ∎) ⟩
  now (_$ _,_) ⊛ (now (λ x f y → f y x) ⊛ y) ⊛ x                 ∼⟨ symmetric (now-∘-⊛-⊛-⊛ (now _) (now _) y) ⊛-cong (x ∎) ⟩
  now _∘_ ⊛ now (_$ _,_) ⊛ now (λ x f y → f y x) ⊛ y ⊛ x         ∼⟨⟩
  now (curry swap) ⊛ y ⊛ x                                       ∼⟨⟩
  now _∘_ ⊛ now (swap ∘_) ⊛ now _,_ ⊛ y ⊛ x                      ∼⟨ now-∘-⊛-⊛-⊛ (now _) (now _) y ⊛-cong (x ∎) ⟩
  now (swap ∘_) ⊛ (now _,_ ⊛ y) ⊛ x                              ∼⟨ (now _ ∎) ⊛-cong symmetric (map∼now-⊛ y) ⊛-cong (x ∎) ⟩
  now (swap ∘_) ⊛ map′ _,_ y ⊛ x                                 ∼⟨⟩
  now _∘_ ⊛ now swap ⊛ map′ _,_ y ⊛ x                            ∼⟨ now-∘-⊛-⊛-⊛ (now _) (map′ _,_ y) x ⟩
  now swap ⊛ (map′ _,_ y ⊛ x)                                    ∼⟨ symmetric (map∼now-⊛ _) ⟩
  map′ swap (map′ _,_ y ⊛ x)                                     ∼⟨⟩
  map′ swap (y ∣ x)                                              ∎

-- The _∣_ operator can be expressed using other functions.

∣-∼ : [ i ] x ∣ y ∼ (x >>=′ λ x → y >>=′ λ y → now (x , y))
∣-∼ {x = x} {y = y} =
  (map′ _,_ x >>=′ λ f → y >>=′ λ y → now (f y))                 ∼⟨ (map∼>>=-now x >>=-cong λ _ → _ ∎) ⟩
  ((x >>=′ λ x → now (x ,_)) >>=′ λ f → y >>=′ λ y → now (f y))  ∼⟨ symmetric $ associativity′ x (λ x → now (x ,_)) (λ f → y >>=′ λ y → now (f y)) ⟩
  (x >>=′ λ x → now (x ,_) >>=′ λ f → y >>=′ λ y → now (f y))    ∼⟨⟩
  (x >>=′ λ x → y >>=′ λ y → now (x , y))                        ∎
