/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
PROVENANCE (Paper V). Returned by Aristotle, project `c2f11738-cc7c-4694-9186-da436d43ee7f`
(gate GALVIN-BKW-LOCAL, 2026-09-14), homed into the Erdős #81 Paper V formalization, then into this library
(`GalvinMultigraph/Local/`) with namespaces and imports renamed and
no other change; re-verified against the pinned Mathlib by the Paper V build and aggregate gate.
Provenance is not correctness: only the gates below certify these declarations.
-/
/-
Paper V, gate GALVIN-BKW-LOCAL — shared vocabulary for bipartite MULTIGRAPHS.

A bipartite multigraph is an edge type `E` together with endpoint maps `left : E → U` and
`right : E → R`; parallel edges are distinct `e ≠ f` with `left e = left f` and `right e = right f`.
-/

module

public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

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
