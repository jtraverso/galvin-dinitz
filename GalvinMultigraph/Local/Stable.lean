/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import GalvinMultigraph.Local.Base

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Push
import Mathlib.Tactic.Set

/-!
# Stable matchings in bipartite multigraphs

This is the multigraph analogue of `Galvin.exists_isStable` (registered) from `Galvin.lean` (which
    is stated
for simple graphs encoded as `Finset (U × R)` and therefore cannot see parallel edges).  Stable
matchings are exactly the kernels of the Galvin orientation of the line graph, so this lemma is what
makes the kernel method applicable to multigraphs.

The proof is a finite deferred-acceptance argument organised as an induction on the number of
edges: if the best edge `e` at some left vertex is not the worst edge at its right endpoint, the
edges that right endpoint likes less than `e` can be deleted (they are dominated in any stable
matching of the smaller edge set); otherwise the set of locally best edges is itself stable.

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

omit [Fintype U] [Fintype R] in
/-- **Stable matchings for bipartite multigraphs.**  If every vertex ranks its incident edges
injectively (`pu` at the left endpoints, `pr` at the right endpoints, larger = better), then any set
`S` of edges has a stable matching: a matching `M ⊆ S` such that every edge of `S` outside `M` is
beaten, at one of its two endpoints, by an edge of `M`. -/
theorem stable_matching_multi (left : E → U) (right : E → R) (pu pr : E → ℕ)
    (hu : ∀ e f, left e = left f → pu e = pu f → e = f)
    (hr : ∀ e f, right e = right f → pr e = pr f → e = f) (S : Finset E) :
    ∃ M : Finset E, M ⊆ S ∧ IsMatchingOn left right M ∧
      ∀ g ∈ S, g ∉ M → (∃ f ∈ M, left f = left g ∧ pu g < pu f) ∨
        (∃ f ∈ M, right f = right g ∧ pr g < pr f) := by
  classical
  induction S using Finset.strongInduction with
  | _ S ih =>
    by_cases hcase : ∃ e ∈ S, (∀ f ∈ S, left f = left e → pu f ≤ pu e) ∧
        ∃ g ∈ S, right g = right e ∧ pr g < pr e
    · -- Deferred acceptance step: the right endpoint of `e` rejects everything it likes less.
      obtain ⟨e, heS, hetop, g, hgS, hgright, hgpr⟩ := hcase
      set D : Finset E := S.filter (fun x => right x = right e ∧ pr x < pr e) with hDdef
      have hgD : g ∈ D := by simp [hDdef, hgS, hgright, hgpr]
      have heD : e ∉ D := by simp [hDdef]
      have hsub : S \ D ⊂ S := by
        refine Finset.ssubset_iff_of_subset Finset.sdiff_subset |>.2 ⟨g, hgS, ?_⟩
        simp [Finset.mem_sdiff, hgD]
      obtain ⟨M, hMsub, hMmatch, hMstab⟩ := ih (S \ D) hsub
      refine ⟨M, hMsub.trans Finset.sdiff_subset, hMmatch, ?_⟩
      intro x hxS hxM
      by_cases hxD : x ∈ D
      · -- `x` is rejected by `right e`; the edge occupying `right e` in `M` beats it.
        have hxr : right x = right e ∧ pr x < pr e := by
          have := Finset.mem_filter.mp hxD; exact this.2
        by_cases heM : e ∈ M
        · exact Or.inr ⟨e, heM, hxr.1 ▸ rfl, hxr.2⟩
        · have heSD : e ∈ S \ D := Finset.mem_sdiff.mpr ⟨heS, heD⟩
          rcases hMstab e heSD heM with ⟨f, hfM, hfl, hfp⟩ | ⟨f, hfM, hfr, hfp⟩
          · exact absurd (hetop f (hMsub hfM |> fun h => (Finset.mem_sdiff.mp h).1) hfl)
              (by omega)
          · exact Or.inr ⟨f, hfM, by rw [hfr, hxr.1], by omega⟩
      · exact hMstab x (Finset.mem_sdiff.mpr ⟨hxS, hxD⟩) hxM
    · -- No proposal is ever rejected: the locally best edges form a stable matching.
      push Not at hcase
      refine ⟨S.filter (fun x => ∀ f ∈ S, left f = left x → pu f ≤ pu x), Finset.filter_subset _ _,
        ?_, ?_⟩
      · intro a ha b hb hab
        obtain ⟨haS, hatop⟩ := Finset.mem_filter.mp ha
        obtain ⟨hbS, hbtop⟩ := Finset.mem_filter.mp hb
        constructor
        · intro hl
          exact hab (hu a b hl (le_antisymm (hbtop a haS hl) (hatop b hbS hl.symm)))
        · intro hrr
          rcases lt_trichotomy (pr a) (pr b) with h | h | h
          · exact absurd (hcase b hbS hbtop a haS hrr) (by omega)
          · exact hab (hr a b hrr h)
          · exact absurd (hcase a haS hatop b hbS hrr.symm) (by omega)
      · intro g hgS hgM
        obtain ⟨f, hf, hfmax⟩ :=
          Finset.exists_max_image (S.filter (fun x => left x = left g)) pu
            ⟨g, Finset.mem_filter.mpr ⟨hgS, rfl⟩⟩
        obtain ⟨hfS, hfl⟩ := Finset.mem_filter.mp hf
        have hfM : f ∈ S.filter (fun x => ∀ f' ∈ S, left f' = left x → pu f' ≤ pu x) := by
          refine Finset.mem_filter.mpr ⟨hfS, ?_⟩
          intro f' hf' hf'l
          exact hfmax f' (Finset.mem_filter.mpr ⟨hf', by rw [hf'l, hfl]⟩)
        refine Or.inl ⟨f, hfM, hfl, ?_⟩
        have hle : pu g ≤ pu f := hfmax g (Finset.mem_filter.mpr ⟨hgS, rfl⟩)
        rcases lt_or_eq_of_le hle with h | h
        · exact h
        · exact absurd (hu g f hfl.symm h ▸ hfM) hgM

end GalvinMultigraph.Local
