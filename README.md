# Galvin's theorem for bipartite multigraphs, Dinitz and stable matchings

Author and maintainer: **Juan Pablo Traverso Gianini**. License: Apache-2.0.

This extension removes the simple-graph restriction from the Galvin development
registered as [PALOMAR-2026-10-18-000029, version 1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-18-000029&version=1).
The previous Gale–Shapley, simple-graph Galvin and Dinitz statements and their
proofs are retained. The multigraph extension has not yet been registered.

Galvin's classical theorem says that finite bipartite multigraphs can be
properly edge-colored from arbitrary finite lists of at least the maximum
degree. In particular their list chromatic index and ordinary chromatic index
both equal their maximum degree. This resolves the bipartite case of the list
edge-coloring conjecture and the Dinitz problem. The research audience includes
graph coloring, matching theory and combinatorics. No new mathematics or
priority among formalizations is claimed.

## Multigraph interface

The edge type `E` contains **edge identifiers**. The endpoint maps `a : E → A`
and `b : E → B` locate each edge on its two sides. The vertex set is understood
as the disjoint union `A ⊕ B`, so loops are excluded. Neither the endpoint maps
nor their pairing is required to be injective. Distinct identifiers with the
same two endpoints are parallel edges and must receive distinct colors.

`GalvinMultigraph.Proper a b c` says that distinct edges sharing either endpoint
have different colors. `GalvinMultigraph.maxDegree` is the maximum of the
cardinalities of the endpoint fibers, counting all parallel edges. These
definitions appear in full in the independent `Challenge.lean`. `Nat.card`
counts a finite subtype; every compared statement using these counts assumes
finiteness of `E`. Both sides may contain isolated vertices or be empty.

## Compared results

The original declarations remain in namespace `ListEdgeColouring`:

- `gale_shapley`: stable matchings with strict preferences and incomplete acceptability.
- `galvin`: list edge coloring of finite bipartite simple graphs.
- `dinitz`: choosing symbols with distinct rows and columns from an n × n array of lists.

Six additional declarations are in namespace `GalvinMultigraph`:

| Declaration | Content |
| --- | --- |
| `galvin_of_degree_bound` | Lists of size at least k suffice when every incidence degree is at most k. |
| `galvin` | Lists of size at least the actual maximum multidegree suffice. |
| `konig` | A proper ordinary edge coloring with exactly Δ available colors exists. |
| `degree_bounds_of_proper` | Any finite palette supporting a proper coloring has size at least each incidence degree. |
| `maxDegree_le_of_proper` | Any such palette has size at least Δ. |
| `colorable_iff` | A proper edge coloring into `Fin k` exists exactly when Δ ≤ k. |

The list colors may belong to an arbitrary type. Empty edge sets and Δ = 0 are
included. The lower bounds plus the list-coloring theorem establish optimality
of the list-size threshold; no separate numerical definition of the list
chromatic index is introduced. The interface uses endpoint maps rather than
Mathlib's newer `Graph` structure. No restriction on parallel multiplicities
is imposed.

## Proof and reuse

The original proof library is retained from commit
`0aa98fc17e1e96ec408f7bad3198ce37a08d26fc`. Its proof bodies are unchanged;
aggregate Mathlib imports in three Galvin modules are narrowed and the finite
interval import is made explicit. The Kőnig/Vizing library is retained as well.

The extension reduces to the existing simple-graph theorem. First shrink each
edge list to a palette of exactly k colors. For every edge identifier insert
a separate copy of `K_{k,k}` with its `(0,0)` edge removed, and connect the two
deficient vertices to the original endpoints. Original degrees are unchanged
and every inserted degree is at most k. Apply the existing Galvin theorem to
this simple bipartite graph, giving every gadget edge its original edge's palette.

The decisive lemma is `Gadget.terminal_agreement`: the two terminal edges of a
gadget have the same color. To prove it, complete its k × k array at `(0,0)`
with one terminal color. Every row uses the entire k-element palette, and each
column other than zero has distinct colors. If the two terminal colors differed,
locating the other terminal color in each row would give an injective map from
`Fin k` to itself avoiding zero, contradicting finite surjectivity. Terminal
colors therefore descend to a proper coloring of the original multigraph.
Empty edge sets are handled before constructing gadgets, covering k = 0.

This is a reduction built on the existing formalization, not a claim that the
multigraph proof follows the original paper line by line. The retained simple
case uses stable matchings, the kernel lemma, Galvin's orientation and Kőnig's theorem.

## Build and check

Lean `v4.35.0-rc3`; Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`.

```sh
lake exe cache get
lake build --wfail
lake build Challenge
lake env lean Audit.lean
lake comparator --config comparator.json
```

`Challenge.lean` imports only Mathlib and has nine intentional statement
placeholders. `Solution.lean` never imports it. Comparator compares all nine
theorems and their transitive definitions, rejects `sorryAx` in the proofs,
and requires both Lean and NanoDa kernel acceptance. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted. See `VERIFICATION.md`.

## Sources and production

- F. Galvin, *The list chromatic index of a bipartite multigraph*, JCTB 63 (1995),
  153–158, [doi:10.1006/jctb.1995.1011](https://doi.org/10.1006/jctb.1995.1011).
- D. Gale and L. S. Shapley, *College admissions and the stability of marriage*,
  American Mathematical Monthly 69 (1962), 9–15,
  [doi:10.1080/00029890.1962.11989827](https://doi.org/10.1080/00029890.1962.11989827).

The previous development reports proofs produced by Harmonic's Aristotle with
planning, integration and review in Claude Code. OpenAI Codex developed the
multigraph reduction, proofs, boundary checks and updated packaging under the
author's direction. No new Aristotle run was used for the extension. Its
checks and self-assessment were performed in the same session that wrote it;
no independent human mathematical review of the extension has been performed.
The detailed structured provenance is in `formalization.yaml`.
