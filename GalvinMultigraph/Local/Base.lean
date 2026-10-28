/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Bipartite multigraphs: matchings and degrees in edge sets

A bipartite multigraph is an edge type `E` together with endpoint maps `left : E → U` and
`right : E → R`; parallel edges are distinct `e ≠ f` with `left e = left f` and `right e = right f`.

These modules come from the author's Erdős #81 Paper V formalization (proofs produced by Harmonic's
Aristotle, then integrated and checked); only names, imports and documentation were changed here.
-/

@[expose] public section

-- The statements keep the finiteness and decidability instances of the section variables, which
-- the proofs use.
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false


namespace GalvinMultigraph.Local

variable {U R E : Type*} [Fintype U] [Fintype R] [Fintype E]
  [DecidableEq U] [DecidableEq R] [DecidableEq E]

/-- `M` is a matching of the multigraph: distinct edges of `M` share no endpoint. -/
def IsMatchingOn (left : E → U) (right : E → R) (M : Finset E) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → left e ≠ left f ∧ right e ≠ right f

/-- The number of edges of `S` incident to the left vertex `u`. -/
def degLOn (left : E → U) (S : Finset E) (u : U) : ℕ := (S.filter fun e => left e = u).card

/-- The number of edges of `S` incident to the right vertex `r`. -/
def degROn (right : E → R) (S : Finset E) (r : R) : ℕ := (S.filter fun e => right e = r).card

end GalvinMultigraph.Local
