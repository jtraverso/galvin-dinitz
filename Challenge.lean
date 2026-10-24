/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph

/-!
# Galvin's theorem, the Dinitz problem and stable matchings

* `ListEdgeColouring.gale_shapley`: **Gale–Shapley (1962).** Let `E` be a bipartite acceptability
relation
  between finite sets `M` and `W`, and let every element rank its potential partners by an
  injective rank function (smaller rank = preferred). Then there is a *stable matching*: a
  matching `μ ⊆ E` such that every acceptable pair `(m, w)` outside `μ` is blocked, i.e. `m` is
  matched to someone it prefers to `w`, or `w` is matched to someone it prefers to `m`.
* `ListEdgeColouring.galvin`: **Galvin (1995).** The list chromatic index of a finite bipartite
graph equals
  its maximum degree: if every edge `e` of a bipartite graph `G` has a list of at least `Δ(G)`
  colours, there is a proper edge colouring (a colouring of Mathlib's `SimpleGraph.lineGraph`)
  choosing the colour of every edge from its list.
* `ListEdgeColouring.dinitz`: **the Dinitz problem.** If every cell of an `n × n` array has a list
of at least
  `n` symbols, one can choose a symbol from each list so that the symbols in every row and in every
  column are distinct.

The Mathlib definitions used in these statements are reproduced verbatim, with file and line at the
pinned Mathlib revision, in `MATHLIB_DEFINITIONS.md` at the root of this repository.
-/

@[expose] public section

namespace ListEdgeColouring

/-- **Gale–Shapley (1962).** For a bipartite acceptability relation `E` between finite sets `M`
and `W`, with strict preferences given by injective rank functions (`rm m w < rm m w'` means that
`m` prefers `w` to `w'`), there is a stable matching. -/
theorem gale_shapley {M W : Type*} [Finite M] [Finite W] (E : M → W → Prop)
    (rm : M → W → ℕ) (rw : W → M → ℕ) (hrm : ∀ m, Function.Injective (rm m))
    (hrw : ∀ w, Function.Injective (rw w)) :
    ∃ μ : M → W → Prop, (∀ m w, μ m w → E m w) ∧
      (∀ m w w', μ m w → μ m w' → w = w') ∧ (∀ m m' w, μ m w → μ m' w → m = m') ∧
      ∀ m w, E m w → ¬ μ m w →
        (∃ w', μ m w' ∧ rm m w' < rm m w) ∨ (∃ m', μ m' w ∧ rw w m' < rw w m) := by
  sorry

/-- **Galvin's theorem (1995).** If every edge of a finite bipartite graph `G` has a list of at
least `Δ(G)` colours, then `G` has a proper edge colouring choosing every colour from the list of
its edge. -/
theorem galvin {V Color : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Colorable 2) (lists : G.edgeSet → Finset Color)
    (hLists : ∀ e, G.maxDegree ≤ (lists e).card) :
    ∃ coloring : G.lineGraph.Coloring Color, ∀ e, coloring e ∈ lists e := by
  sorry

/-- **The Dinitz problem** (Galvin 1995). If every cell of an `n × n` array has a list of at least
`n` symbols, there is a choice of one symbol from each list with all symbols in each row distinct
and all symbols in each column distinct. -/
theorem dinitz {Symbol : Type*} (n : ℕ) (lists : Fin n → Fin n → Finset Symbol)
    (hLists : ∀ i j, n ≤ (lists i j).card) :
    ∃ f : Fin n → Fin n → Symbol, (∀ i j, f i j ∈ lists i j) ∧
      (∀ i j j', j ≠ j' → f i j ≠ f i j') ∧ (∀ i i' j, i ≠ i' → f i j ≠ f i' j) := by
  sorry

end ListEdgeColouring


namespace GalvinMultigraph

open Finset

variable {A B E Color : Type*}

/-- Distinct edges meeting at either endpoint must receive different colors. -/
def Proper (a : E → A) (b : E → B) (c : E → Color) : Prop :=
  ∀ e f, e ≠ f → a e = a f ∨ b e = b f → c e ≠ c f

/-- Maximum incidence degree, with each parallel edge counted separately. -/
noncomputable def maxDegree [Fintype A] [Fintype B] (a : E → A) (b : E → B) : ℕ :=
  max (univ.sup fun x => Nat.card {e // a e = x})
      (univ.sup fun y => Nat.card {e // b e = y})

/-- Galvin's list-edge-coloring theorem, allowing any common degree bound k. -/
theorem galvin_of_degree_bound [Finite A] [Finite B] [Finite E]
    (a : E → A) (b : E → B) (k : ℕ)
    (ha : ∀ x, Nat.card {e // a e = x} ≤ k)
    (hb : ∀ y, Nat.card {e // b e = y} ≤ k)
    (L : E → Finset Color) (hL : ∀ e, k ≤ (L e).card) :
    ∃ c : E → Color, (∀ e, c e ∈ L e) ∧ Proper a b c := by
  sorry

/-- Galvin (1995): every list assignment of size at least the maximum degree
admits a proper edge coloring of the finite bipartite multigraph. -/
theorem galvin [Fintype A] [Fintype B] [Finite E]
    (a : E → A) (b : E → B) (L : E → Finset Color)
    (hL : ∀ e, maxDegree a b ≤ (L e).card) :
    ∃ c : E → Color, (∀ e, c e ∈ L e) ∧ Proper a b c := by
  sorry

/-- Kőnig's edge-coloring theorem for bipartite multigraphs. -/
theorem konig [Fintype A] [Fintype B] [Finite E] (a : E → A) (b : E → B) :
    ∃ c : E → Fin (maxDegree a b), Proper a b c := by
  sorry

/-- Every proper finite-palette edge coloring has at least as many colors as
each incidence degree. -/
theorem degree_bounds_of_proper [Finite E] [Fintype Color]
    (a : E → A) (b : E → B) (c : E → Color) (hc : Proper a b c) :
    (∀ x, Nat.card {e // a e = x} ≤ Fintype.card Color) ∧
    (∀ y, Nat.card {e // b e = y} ≤ Fintype.card Color) := by
  sorry

/-- The palette size is bounded below by the actual multigraph maximum degree. -/
theorem maxDegree_le_of_proper [Fintype A] [Fintype B] [Finite E] [Fintype Color]
    (a : E → A) (b : E → B) (c : E → Color) (hc : Proper a b c) :
    maxDegree a b ≤ Fintype.card Color := by
  sorry

/-- Exact ordinary chromatic-index threshold, including empty edge sets. -/
theorem colorable_iff [Fintype A] [Fintype B] [Finite E]
    (a : E → A) (b : E → B) (k : ℕ) :
    (∃ c : E → Fin k, Proper a b c) ↔ maxDegree a b ≤ k := by
  sorry

end GalvinMultigraph
