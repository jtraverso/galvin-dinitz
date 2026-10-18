/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import GalvinLib.Galvin

/-!
# Proofs of the statements in `Challenge.lean`

The theorems are proved in `GalvinLib/` (namespace `Galvin`). `GaleShapley.lean` proves the
existence of stable matchings by strong induction on the number of acceptable pairs (if two
men share a favourite woman, delete the pair she likes less). `Kernel.lean` proves the kernel
lemma: if every set of vertices of a digraph has a kernel and every list is longer than the
out-degree, there is a proper list colouring. `Orientation.lean` orients the line graph of a
bipartite graph using a proper `Δ`-edge-colouring from Kőnig's theorem (`Konig/Basic.lean`, from
the registered entry PALOMAR-2026-10-15-000019, included unchanged): every out-degree is below
`Δ`, and every set of edges has a kernel, given by a stable matching. The Dinitz problem is the
case of `K_{n,n}`.
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
        (∃ w', μ m w' ∧ rm m w' < rm m w) ∨ (∃ m', μ m' w ∧ rw w m' < rw w m) :=
  Galvin.gale_shapley E rm rw hrm hrw

/-- **Galvin's theorem (1995).** If every edge of a finite bipartite graph `G` has a list of at
least `Δ(G)` colours, then `G` has a proper edge colouring choosing every colour from the list of
its edge. -/
theorem galvin {V Color : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Colorable 2) (lists : G.edgeSet → Finset Color)
    (hLists : ∀ e, G.maxDegree ≤ (lists e).card) :
    ∃ coloring : G.lineGraph.Coloring Color, ∀ e, coloring e ∈ lists e :=
  Galvin.galvin G hG lists hLists

/-- **The Dinitz problem** (Galvin 1995). If every cell of an `n × n` array has a list of at least
`n` symbols, there is a choice of one symbol from each list with all symbols in each row distinct
and all symbols in each column distinct. -/
theorem dinitz {Symbol : Type*} (n : ℕ) (lists : Fin n → Fin n → Finset Symbol)
    (hLists : ∀ i j, n ≤ (lists i j).card) :
    ∃ f : Fin n → Fin n → Symbol, (∀ i j, f i j ∈ lists i j) ∧
      (∀ i j j', j ≠ j' → f i j ≠ f i j') ∧ (∀ i i' j, i ≠ i' → f i j ≠ f i' j) :=
  Galvin.dinitz n lists hLists

end ListEdgeColouring
