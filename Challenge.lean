/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Galvin's theorem, the Dinitz problem and stable matchings

* `ListEdgeColouring.gale_shapley`: **Gale–Shapley (1962).** Let `E` be a bipartite acceptability relation
  between finite sets `M` and `W`, and let every element rank its potential partners by an
  injective rank function (smaller rank = preferred). Then there is a *stable matching*: a
  matching `μ ⊆ E` such that every acceptable pair `(m, w)` outside `μ` is blocked, i.e. `m` is
  matched to someone it prefers to `w`, or `w` is matched to someone it prefers to `m`.
* `ListEdgeColouring.galvin`: **Galvin (1995).** The list chromatic index of a finite bipartite graph equals
  its maximum degree: if every edge `e` of a bipartite graph `G` has a list of at least `Δ(G)`
  colours, there is a proper edge colouring (a colouring of Mathlib's `SimpleGraph.lineGraph`)
  choosing the colour of every edge from its list.
* `ListEdgeColouring.dinitz`: **the Dinitz problem.** If every cell of an `n × n` array has a list of at least
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
