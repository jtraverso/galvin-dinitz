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
#print axioms GalvinMultigraph.galvin_local

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

-- Local lists (Borodin–Kostochka–Woodall): two parallel edges `0, 1` between `a = 0` and `b = 0`,
-- and a pendant edge `2` from `a = 1` to `b = 0`. Each edge needs a list as long as the larger
-- degree of its ends, here 2 for the parallel edges and 3 for the edge at the degree-3 vertex `b = 0`.
example : ∃ c : Fin 3 → ℕ, (∀ e, c e ∈ ({0, 1, 2} : Finset ℕ)) ∧
    GalvinMultigraph.Proper (fun e : Fin 3 => if e = 2 then (1 : Fin 2) else 0)
      (fun _ : Fin 3 => ()) c :=
  GalvinMultigraph.galvin_local _ _ (fun _ => ({0, 1, 2} : Finset ℕ)) fun e => by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide +revert

