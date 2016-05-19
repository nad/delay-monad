------------------------------------------------------------------------
-- Code related to the paper "Partiality, Revisited"
-- Thorsten Altenkirch and Nils Anders Danielsson
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module README where

------------------------------------------------------------------------
-- The partiality monad

-- The code is heavily inspired by the section on Cauchy reals in the
-- HoTT book (first edition).

-- A partial inductive definition of the partiality monad, without
-- path or truncation constructors, in order to get the basics right.

import Partiality-monad.Inductive.Preliminary-sketch

-- A higher inductive-inductive definition of the partiality monad.

import Partiality-monad.Inductive

-- Specialised eliminators.

import Partiality-monad.Inductive.Eliminators

-- Some definitions and properties.

import Partiality-monad.Inductive.Properties

-- An alternative characterisation of the information ordering, along
-- with related results.

import Partiality-monad.Inductive.Alternative-order

-- Monotone functions.

import Partiality-monad.Inductive.Monotone

-- ω-continuous functions.

import Partiality-monad.Inductive.Omega-continuous

-- The partiality monad's monad instance.

import Partiality-monad.Inductive.Monad

-- Strict ω-continuous functions.

import Partiality-monad.Inductive.Strict-omega-continuous

-- Fixpoint combinators.

import Partiality-monad.Inductive.Fixpoints

------------------------------------------------------------------------
-- An example

-- Some developments from "Operational Semantics Using the Partiality
-- Monad" by Danielsson, ported to the present setting.
--
-- These developments to a large extent mirror developments in
-- "Coinductive big-step operational semantics" by Leroy and Grall.

-- The syntax of, and a type system for, the untyped λ-calculus with
-- constants.

import Lambda.Syntax

-- A definitional interpreter.

import Lambda.Interpreter

-- A type soundness result.

import Lambda.Type-soundness

-- A virtual machine.

import Lambda.Virtual-machine

-- A correct compiler.

import Lambda.Compiler
