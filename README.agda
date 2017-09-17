------------------------------------------------------------------------
-- Code related to the delay monad
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module README where

-- The concept referred to as the delay monad here is the monad
-- presented by Capretta in "General Recursion via Coinductive Types".

------------------------------------------------------------------------
-- The delay monad

-- The delay monad, defined coinductively.

import Delay-monad

-- Strong bisimilarity.

import Delay-monad.Strong-bisimilarity

-- Weak bisimilarity.

import Delay-monad.Weak-bisimilarity

-- An example showing that transitivity-like proofs that are not
-- size-preserving can sometimes be used in a compositional way.

import Delay-monad.Transitivity-constructor

-- The expansion relation.

import Delay-monad.Expansion

-- A partial order.

import Delay-monad.Partial-order

-- Least upper bounds.

import Delay-monad.Least-upper-bound

-- The delay monad is a monad up to strong bisimilarity.

import Delay-monad.Monad

-- The "always true" predicate, □.

import Delay-monad.Always

------------------------------------------------------------------------
-- A variant of the delay monad with a sized type parameter

-- The delay monad, defined coinductively, with a sized type
-- parameter.

import Delay-monad.Sized

-- Strong bisimilarity.

import Delay-monad.Sized.Strong-bisimilarity

-- Weak bisimilarity.

import Delay-monad.Sized.Weak-bisimilarity

-- A partial order.

import Delay-monad.Sized.Partial-order

-- Least upper bounds.

import Delay-monad.Sized.Least-upper-bound

-- A monad-like structure.

import Delay-monad.Sized.Monad

-- The "always true" predicate, □.

import Delay-monad.Sized.Always
