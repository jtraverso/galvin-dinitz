# Galvin's theorem, the Dinitz problem and stable matchings in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

All statements are in the namespace `ListEdgeColouring`:

1. `gale_shapley`, **Gale–Shapley (1962)**. For finite sets `M`, `W`, an acceptability relation
   `E ⊆ M × W` and strict preferences (injective rank functions), there is a *stable matching*: a
   matching `μ ⊆ E` such that every acceptable pair `(m, w)` outside `μ` is blocked, i.e. `m` is
   matched to someone it prefers to `w`, or `w` is matched to someone it prefers to `m`.
2. `galvin`, **Galvin's theorem (1995)**. The list chromatic index of a finite bipartite graph is
   its maximum degree: if every edge has a list of at least `Δ(G)` colours, there is a proper edge
   colouring (a colouring of Mathlib's `SimpleGraph.lineGraph`) choosing every colour from the list
   of its edge.
3. `dinitz`, **the Dinitz problem** (solved by Galvin). If every cell of an `n × n` array has a
   list of at least `n` symbols, one can choose a symbol from each list so that the symbols in each
   row and in each column are distinct.

Mathlib has line graphs, colourings and Hall's theorem, but none of these results.

## Files

- [`Challenge.lean`](Challenge.lean): the audited statements. It imports only Mathlib.
- [`Solution.lean`](Solution.lean) and [`GalvinLib/`](GalvinLib): the proofs.
- [`Konig/Basic.lean`](Konig/Basic.lean) and [`LeanPool/`](LeanPool): Kőnig's edge-colouring
  theorem `χ′ = Δ` for bipartite graphs (and the Vizing machinery it uses), reused unchanged from
  the registered entry
  [PALOMAR-2026-10-15-000019](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-15-000019&version=1)
  ([jtraverso/konig-edge-colouring](https://github.com/jtraverso/konig-edge-colouring) @ 7c60f7e).
- [`comparator.json`](comparator.json): the theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## How the proofs go

* **Gale–Shapley** (`GaleShapley.lean`), by strong induction on the number of acceptable pairs.
  If no two elements of `M` have the same favourite, matching each to its favourite is stable.
  Otherwise two of them share a favourite `w`; delete the pair that `w` likes less and take a
  stable matching of the smaller instance, which remains stable for the original one.
* **Kernel lemma** (`Kernel.lean`). If every set of vertices of a digraph has a kernel (an
  independent set into which every other vertex of the set has an arc), and every list is longer
  than the out-degree of its vertex, there is a proper colouring from the lists: colour a kernel
  of the vertices whose list contains a given colour, remove it, and induct.
* **Galvin** (`Orientation.lean`). Take a proper `Δ`-edge-colouring `φ` (Kőnig) and a bipartition
  `A ∪ B`. Orient two edges meeting at `w` from the larger colour to the smaller one if `w ∈ A`,
  and from the smaller to the larger if `w ∈ B`. Each out-degree is at most `Δ − 1`, and every set
  of edges has a kernel: a stable matching in which `A`-vertices prefer smaller colours and
  `B`-vertices prefer larger ones.
* **Dinitz.** Apply Galvin's theorem to `K_{n,n}`, whose maximum degree is `n`.

## Sources

* F. Galvin, *The list chromatic index of a bipartite multigraph*, J. Combin. Theory Ser. B 63
  (1995) 153–158, doi:10.1006/jctb.1995.1011.
* D. Gale, L. S. Shapley, *College admissions and the stability of marriage*, Amer. Math. Monthly
  69 (1962) 9–15, doi:10.1080/00029890.1962.11989827.

## Authorship and use of AI

The author chose the results. The statements and proof plan were written with Claude in Claude
Code. Harmonic's Aristotle produced the proofs, which were audited and rebuilt locally. Lean
checks everything mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
