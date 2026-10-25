/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

import Solution

/-! Axiom audit and boundary cases for the multigraph extension. -/

#print axioms ListEdgeColouring.gale_shapley
#print axioms ListEdgeColouring.galvin
#print axioms ListEdgeColouring.dinitz
#print axioms GalvinMultigraph.galvin_of_degree_bound
#print axioms GalvinMultigraph.galvin
#print axioms GalvinMultigraph.konig
#print axioms GalvinMultigraph.degree_bounds_of_proper
#print axioms GalvinMultigraph.maxDegree_le_of_proper
#print axioms GalvinMultigraph.colorable_iff

-- Distinct identifiers with the same endpoints are genuine parallel edges.
example : GalvinMultigraph.maxDegree (fun _ : Fin 2 => ()) (fun _ : Fin 2 => ()) = 2 := by
  simp [GalvinMultigraph.maxDegree, Nat.card_eq_fintype_card, Fintype.card_subtype]

example : ¬ ∃ c : Fin 2 → Fin 1,
    GalvinMultigraph.Proper (fun _ => ()) (fun _ => ()) c := by
  rw [GalvinMultigraph.colorable_iff]
  simp [GalvinMultigraph.maxDegree, Nat.card_eq_fintype_card, Fintype.card_subtype]

-- Empty multigraphs allow an empty palette and empty vertex types.
example : ∃ c : Fin 0 → Fin 0,
    GalvinMultigraph.Proper (fun e : Fin 0 => e) (fun e : Fin 0 => e) c := by
  apply (GalvinMultigraph.colorable_iff _ _ 0).mpr
  simp [GalvinMultigraph.maxDegree]
