/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import GalvinLib.Kernel

/-!
# The kernel lemma, in the form used by the rank engine

`kernel_coloring` restates the registered kernel lemma `Galvin.exists_listColoring` for a digraph
`A` on a finite vertex type with lists of natural numbers: if every finite vertex set has a kernel
and every list is longer than the out-degree, there is a list colouring that separates the ends of
every arc.
-/

@[expose] public section

namespace GalvinMultigraph.Local

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `K` is a kernel of the sub-digraph induced by `S`: independent, and every vertex
of `S ∖ K` has an out-neighbour in `K`. -/
def IsKernelOn (A : V → V → Prop) (S K : Finset V) : Prop :=
  K ⊆ S ∧ (∀ x ∈ K, ∀ y ∈ K, ¬ A x y) ∧ ∀ x ∈ S, x ∉ K → ∃ y ∈ K, A x y

/-- **Kernel colouring lemma.** If every induced subdigraph of `A` has a kernel and
`|L(v)| ≥ d⁺(v) + 1`, the underlying graph is `L`-colourable. -/
theorem kernel_coloring (A : V → V → Prop) [DecidableRel A]
    (hirr : ∀ v, ¬ A v v)
    (hker : ∀ S : Finset V, ∃ K, IsKernelOn A S K)
    (L : V → Finset ℕ)
    (hL : ∀ v, (Finset.univ.filter fun u => A v u).card + 1 ≤ (L v).card) :
    ∃ φ : V → ℕ, (∀ v, φ v ∈ L v) ∧ ∀ u v, A u v → φ u ≠ φ v := by
  have hK : Galvin.HasKernels (SimpleGraph.fromRel A) A := by
    intro S
    obtain ⟨K, hKS, hKind, hKabs⟩ := hker S
    refine ⟨K, hKS, fun x hx y hy hxy => ?_, hKabs⟩
    rcases ((SimpleGraph.fromRel_adj _ _ _).1 hxy).2 with h | h
    · exact hKind x hx y hy h
    · exact hKind y hy x hx h
  obtain ⟨c, hc⟩ := Galvin.exists_listColoring (SimpleGraph.fromRel A) A hK L
    fun x => Nat.lt_of_succ_le (hL x)
  refine ⟨c, hc, fun u v huv => c.valid ?_⟩
  exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨fun h => hirr u (h ▸ huv), Or.inl huv⟩

end GalvinMultigraph.Local
