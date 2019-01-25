------------------------------------------------------------------------
-- Code related to the delay monad
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module README where

-- The concept referred to as the delay monad here is the monad
-- presented by Capretta in "General Recursion via Coinductive Types".

------------------------------------------------------------------------
-- The delay monad

-- The delay monad, defined coinductively.

import Delay-monad

-- A type used to index a combined definition of strong and weak
-- bisimilarity and expansion.

import Delay-monad.Bisimilarity.Kind

-- A combined definition of strong and weak bisimilarity and
-- expansion, along with various properties.

import Delay-monad.Bisimilarity

-- A variant of weak bisimilarity that can be used to relate the
-- number of steps in two computations.

import Delay-monad.Quantitative-weak-bisimilarity

-- Termination.

import Delay-monad.Termination

-- Alternative definitions of weak bisimilarity.

import Delay-monad.Bisimilarity.Alternative

-- Some negative results related to weak bisimilarity and expansion.

import Delay-monad.Bisimilarity.Negative

-- An example showing that transitivity-like proofs that are not
-- size-preserving can sometimes be used in a compositional way.

import Delay-monad.Bisimilarity.Transitivity-constructor

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

-- A combined definition of strong and weak bisimilarity and
-- expansion, along with various properties.

import Delay-monad.Sized.Bisimilarity

-- Termination.

import Delay-monad.Sized.Termination

-- Alternative definitions of weak bisimilarity.

import Delay-monad.Sized.Bisimilarity.Alternative

-- Some negative results related to weak bisimilarity and expansion.

import Delay-monad.Sized.Bisimilarity.Negative

-- A partial order.

import Delay-monad.Sized.Partial-order

-- Least upper bounds.

import Delay-monad.Sized.Least-upper-bound

-- A monad-like structure.

import Delay-monad.Sized.Monad

-- The "always true" predicate, □.

import Delay-monad.Sized.Always
