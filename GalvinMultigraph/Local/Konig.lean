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
Paper V, gate GALVIN-BKW-LOCAL — Kőnig's edge colouring theorem for bipartite MULTIGRAPHS.

Multigraph analogue of Kőnig's edge colouring theorem: a set of edges with all degrees at most
`Δ` decomposes into `Δ` matchings.  The proof follows the simple-graph one: Hall's theorem produces
a matching saturating the left vertices of degree `Δ` and one saturating the right vertices of
degree `Δ`, the two are merged (Mendelsohn–Dulmage, via stable matchings), and the resulting
matching is removed as one colour class.
-/
module

public import GalvinMultigraph.Local.Stable

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Set

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Group.Action.Defs

@[expose] public section

namespace GalvinMultigraph.Local

variable {U R E : Type*} [Fintype U] [Fintype R] [Fintype E]
  [DecidableEq U] [DecidableEq R] [DecidableEq E]

omit [Fintype U] [Fintype E] [DecidableEq E] in
/-- Edges of `S` whose left endpoint lies in `A`, counted fibrewise. -/
lemma card_filter_left_mem (left : E → U) (S : Finset E) (A : Finset U) :
    (S.filter fun e => left e ∈ A).card = ∑ u ∈ A, degLOn left S u := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := left) (t := A)
    (by intro x hx; exact (Finset.mem_filter.mp hx).2)]
  refine Finset.sum_congr rfl fun u hu => ?_
  unfold degLOn
  congr 1
  ext e
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2 ▸ hu⟩, h.2⟩⟩

omit [Fintype R] [Fintype E] [DecidableEq E] in
/-- Edges of `S` whose right endpoint lies in `B`, counted fibrewise. -/
lemma card_filter_right_mem (right : E → R) (S : Finset E) (B : Finset R) :
    (S.filter fun e => right e ∈ B).card = ∑ r ∈ B, degROn right S r := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := right) (t := B)
    (by intro x hx; exact (Finset.mem_filter.mp hx).2)]
  refine Finset.sum_congr rfl fun r hr => ?_
  unfold degROn
  congr 1
  ext e
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2 ▸ hr⟩, h.2⟩⟩

omit [Fintype R] [Fintype E] in
/-- Hall's theorem: a matching of `S` saturating every left vertex of maximal degree `Δ`. -/
lemma saturating_matching_left (left : E → U) (right : E → R) (S : Finset E) (Δ : ℕ) (hΔ : 0 < Δ)
    (hR : ∀ r, degROn right S r ≤ Δ) :
    ∃ M : Finset E, M ⊆ S ∧ IsMatchingOn left right M ∧
      ∀ u, degLOn left S u = Δ → ∃ e ∈ M, left e = u := by
  classical
  set T0 : Finset U := Finset.univ.filter (fun u => degLOn left S u = Δ) with hT0
  set nbr : U → Finset R := fun u => (S.filter fun e => left e = u).image right with hnbr
  have hall : ∀ A : Finset ↥T0, A.card ≤ (A.biUnion (fun u => nbr u.val)).card := by
    intro A
    set AU : Finset U := A.image Subtype.val with hAU
    set B : Finset R := A.biUnion (fun u => nbr u.val) with hB
    have hAUcard : AU.card = A.card := Finset.card_image_of_injective _ Subtype.val_injective
    have h1 : (S.filter fun e => left e ∈ AU).card = Δ * A.card := by
      rw [card_filter_left_mem left S AU]
      have : ∀ u ∈ AU, degLOn left S u = Δ := by
        intro u hu
        obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hu
        exact (Finset.mem_filter.mp v.2).2
      rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, hAUcard, mul_comm]
    have hsub : (S.filter fun e => left e ∈ AU) ⊆ (S.filter fun e => right e ∈ B) := by
      intro e he
      simp only [Finset.mem_filter] at he ⊢
      refine ⟨he.1, ?_⟩
      obtain ⟨u, huA, hu⟩ := Finset.mem_image.mp he.2
      exact Finset.mem_biUnion.mpr ⟨u, huA,
        Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he.1, hu.symm⟩, rfl⟩⟩
    have h2 : (S.filter fun e => right e ∈ B).card ≤ Δ * B.card := by
      rw [card_filter_right_mem right S B]
      calc ∑ r ∈ B, degROn right S r ≤ ∑ _r ∈ B, Δ := Finset.sum_le_sum fun r _ => hR r
        _ = Δ * B.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have : Δ * A.card ≤ Δ * B.card := by
      calc Δ * A.card = (S.filter fun e => left e ∈ AU).card := h1.symm
        _ ≤ (S.filter fun e => right e ∈ B).card := Finset.card_le_card hsub
        _ ≤ Δ * B.card := h2
    exact Nat.le_of_mul_le_mul_left this hΔ
  obtain ⟨f, hfinj, hf⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective (fun u : ↥T0 => nbr u.val)).mp hall
  have hex : ∀ u : ↥T0, ∃ e, e ∈ S ∧ left e = u.val ∧ right e = f u := by
    intro u
    obtain ⟨e, he, hre⟩ := Finset.mem_image.mp (hf u)
    exact ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2, hre⟩
  choose g hgS hgl hgr using hex
  refine ⟨Finset.image g Finset.univ, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he
    exact hgS u
  · intro e he e' he' hne
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp he'
    have huv : u ≠ v := fun h => hne (by rw [h])
    refine ⟨?_, ?_⟩
    · rw [hgl u, hgl v]
      exact fun h => huv (Subtype.ext h)
    · rw [hgr u, hgr v]
      exact fun h => huv (hfinj h)
  · intro u hu
    have huT : u ∈ T0 := Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩
    exact ⟨g ⟨u, huT⟩, Finset.mem_image.mpr ⟨⟨u, huT⟩, Finset.mem_univ _, rfl⟩, hgl ⟨u, huT⟩⟩

omit [Fintype U] [Fintype E] in
/-- Hall's theorem: a matching of `S` saturating every right vertex of maximal degree `Δ`. -/
lemma saturating_matching_right (left : E → U) (right : E → R) (S : Finset E) (Δ : ℕ) (hΔ : 0 < Δ)
    (hL : ∀ u, degLOn left S u ≤ Δ) :
    ∃ M : Finset E, M ⊆ S ∧ IsMatchingOn left right M ∧
      ∀ r, degROn right S r = Δ → ∃ e ∈ M, right e = r := by
  obtain ⟨M, hMS, hM, hsat⟩ := saturating_matching_left right left S Δ hΔ (fun u => hL u)
  exact ⟨M, hMS, fun e he f hf hne => ⟨(hM e he f hf hne).2, (hM e he f hf hne).1⟩, hsat⟩

omit [Fintype U] [Fintype R] in
/-- Mendelsohn–Dulmage: two matchings can be merged into a single matching saturating the left
vertices covered by the first and the right vertices covered by the second. -/
lemma merge_matchings (left : E → U) (right : E → R) (S ML MR : Finset E)
    (hMLS : ML ⊆ S) (hMRS : MR ⊆ S)
    (hML : IsMatchingOn left right ML) (hMR : IsMatchingOn left right MR) :
    ∃ M : Finset E, M ⊆ S ∧ IsMatchingOn left right M ∧
      (∀ u, (∃ e ∈ ML, left e = u) → ∃ e ∈ M, left e = u) ∧
      (∀ r, (∃ e ∈ MR, right e = r) → ∃ e ∈ M, right e = r) := by
  classical
  -- Left vertices prefer the edges of `MR`, right vertices prefer the edges of `ML`; a stable
  -- matching for these preferences must cover every vertex covered by the corresponding matching.
  set n : ℕ := Fintype.card E with hn
  set idx : E → ℕ := fun e => ((Fintype.equivFin E) e : ℕ) with hidx
  have hidxlt : ∀ e, idx e < n := fun e => (Fintype.equivFin E e).isLt
  have hidxinj : Function.Injective idx := by
    intro e f h
    exact (Fintype.equivFin E).injective (Fin.ext h)
  set pu : E → ℕ := fun e => (if e ∈ ML then 0 else n) + idx e with hpu
  set pr : E → ℕ := fun e => (if e ∈ MR then 0 else n) + idx e with hpr
  have hpuinj : ∀ e f, pu e = pu f → e = f := by
    intro e f h
    by_cases he : e ∈ ML <;> by_cases hf : f ∈ ML <;>
      simp only [hpu, he, hf, if_true, if_false] at h <;>
      first
        | exact hidxinj (by omega)
        | (exfalso; have := hidxlt e; have := hidxlt f; omega)
  have hprinj : ∀ e f, pr e = pr f → e = f := by
    intro e f h
    by_cases he : e ∈ MR <;> by_cases hf : f ∈ MR <;>
      simp only [hpr, he, hf, if_true, if_false] at h <;>
      first
        | exact hidxinj (by omega)
        | (exfalso; have := hidxlt e; have := hidxlt f; omega)
  obtain ⟨M, hMsub, hMmatch, hMstab⟩ :=
    stable_matching_multi left right pu pr (fun e f _ h => hpuinj e f h)
      (fun e f _ h => hprinj e f h) (ML ∪ MR)
  refine ⟨M, hMsub.trans (Finset.union_subset hMLS hMRS), hMmatch, ?_, ?_⟩
  · rintro u ⟨e, heML, rfl⟩
    by_cases heM : e ∈ M
    · exact ⟨e, heM, rfl⟩
    · rcases hMstab e (Finset.mem_union_left _ heML) heM with ⟨f, hfM, hfl, _⟩ | ⟨f, hfM, hfr, hfp⟩
      · exact ⟨f, hfM, hfl⟩
      · exfalso
        have hfne : f ≠ e := fun h => heM (h ▸ hfM)
        rcases Finset.mem_union.mp (hMsub hfM) with hfML | hfMR
        · exact (hML f hfML e heML hfne).2 hfr
        · have hfnotML : f ∉ ML := fun h => (hML f h e heML hfne).2 hfr
          have hlt : pr e < pr f := hfp
          have h1 : pr f = idx f := by simp [hpr, hfMR]
          have heMR : e ∈ MR := by
            by_contra hcon
            have : pr e = n + idx e := by simp [hpr, hcon]
            have := hidxlt f
            omega
          exact hfne (hMR f hfMR e heMR hfne |>.2 hfr |>.elim)
  · rintro r ⟨e, heMR, rfl⟩
    by_cases heM : e ∈ M
    · exact ⟨e, heM, rfl⟩
    · rcases hMstab e (Finset.mem_union_right _ heMR) heM with ⟨f, hfM, hfl, hfp⟩ | ⟨f, hfM, hfr, _⟩
      · exfalso
        have hfne : f ≠ e := fun h => heM (h ▸ hfM)
        rcases Finset.mem_union.mp (hMsub hfM) with hfML | hfMR
        · have h1 : pu f = idx f := by simp [hpu, hfML]
          have heML : e ∈ ML := by
            by_contra hcon
            have : pu e = n + idx e := by simp [hpu, hcon]
            have := hidxlt f
            omega
          exact (hML f hfML e heML hfne).1 hfl
        · exact (hMR f hfMR e heMR hfne).1 hfl
      · exact ⟨f, hfM, hfr⟩

/-- A matching of `S` meeting every vertex of degree exactly `Δ`, on both sides. -/
lemma saturated_matching (left : E → U) (right : E → R) (S : Finset E) (Δ : ℕ) (hΔ : 0 < Δ)
    (hL : ∀ u, degLOn left S u ≤ Δ) (hR : ∀ r, degROn right S r ≤ Δ) :
    ∃ M : Finset E, M ⊆ S ∧ IsMatchingOn left right M ∧
      (∀ u, degLOn left S u = Δ → ∃ e ∈ M, left e = u) ∧
      (∀ r, degROn right S r = Δ → ∃ e ∈ M, right e = r) := by
  obtain ⟨ML, hMLS, hML, hLsat⟩ := saturating_matching_left left right S Δ hΔ hR
  obtain ⟨MR, hMRS, hMR, hRsat⟩ := saturating_matching_right left right S Δ hΔ hL
  obtain ⟨M, hMS, hM, hcovL, hcovR⟩ := merge_matchings left right S ML MR hMLS hMRS hML hMR
  exact ⟨M, hMS, hM, fun u hu => hcovL u (hLsat u hu), fun r hr => hcovR r (hRsat r hr)⟩

/-- **Kőnig's edge colouring theorem for bipartite multigraphs.**  A set `S` of edges with all
degrees at most `Δ` has a proper edge colouring with colours `< Δ`. -/
theorem konig_multigraph (left : E → U) (right : E → R) (S : Finset E) (Δ : ℕ)
    (hL : ∀ u, degLOn left S u ≤ Δ) (hR : ∀ r, degROn right S r ≤ Δ) :
    ∃ φ : E → ℕ, (∀ e ∈ S, φ e < Δ) ∧
      ∀ e ∈ S, ∀ f ∈ S, e ≠ f → (left e = left f ∨ right e = right f) → φ e ≠ φ f := by
  classical
  induction Δ generalizing S with
  | zero =>
    have hS : S = ∅ := by
      by_contra hcon
      obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hcon
      have : 1 ≤ degLOn left S (left e) :=
        Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, rfl⟩⟩
      have := hL (left e)
      omega
    subst hS
    exact ⟨fun _ => 0, by simp, by simp⟩
  | succ Δ ih =>
    obtain ⟨M, hMS, hM, hLsat, hRsat⟩ := saturated_matching left right S (Δ + 1) (by omega) hL hR
    have hmono : ∀ (u : U), degLOn left (S \ M) u ≤ degLOn left S u := by
      intro u
      exact Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)
    have hmonoR : ∀ (r : R), degROn right (S \ M) r ≤ degROn right S r := by
      intro r
      exact Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)
    have hL' : ∀ u, degLOn left (S \ M) u ≤ Δ := by
      intro u
      by_cases hu : degLOn left S u = Δ + 1
      · obtain ⟨e, heM, heu⟩ := hLsat u hu
        have hss : (S \ M).filter (fun x => left x = u) ⊂ S.filter (fun x => left x = u) := by
          refine Finset.ssubset_iff_of_subset (Finset.filter_subset_filter _ Finset.sdiff_subset)
            |>.2 ⟨e, Finset.mem_filter.mpr ⟨hMS heM, heu⟩, ?_⟩
          simp [Finset.mem_filter, Finset.mem_sdiff, heM]
        have := Finset.card_lt_card hss
        unfold degLOn at hu ⊢
        omega
      · have := hL u; have := hmono u; omega
    have hR' : ∀ r, degROn right (S \ M) r ≤ Δ := by
      intro r
      by_cases hr : degROn right S r = Δ + 1
      · obtain ⟨e, heM, her⟩ := hRsat r hr
        have hss : (S \ M).filter (fun x => right x = r) ⊂ S.filter (fun x => right x = r) := by
          refine Finset.ssubset_iff_of_subset (Finset.filter_subset_filter _ Finset.sdiff_subset)
            |>.2 ⟨e, Finset.mem_filter.mpr ⟨hMS heM, her⟩, ?_⟩
          simp [Finset.mem_filter, Finset.mem_sdiff, heM]
        have := Finset.card_lt_card hss
        unfold degROn at hr ⊢
        omega
      · have := hR r; have := hmonoR r; omega
    obtain ⟨φ', hφ'lt, hφ'⟩ := ih (S \ M) hL' hR'
    refine ⟨fun e => if e ∈ M then Δ else φ' e, ?_, ?_⟩
    · intro e he
      by_cases heM : e ∈ M
      · simp [heM]
      · have := hφ'lt e (Finset.mem_sdiff.mpr ⟨he, heM⟩)
        simp [heM]
        omega
    · intro e he f hf hne hadj
      by_cases heM : e ∈ M <;> by_cases hfM : f ∈ M
      · exfalso
        rcases hadj with h | h
        · exact (hM e heM f hfM hne).1 h
        · exact (hM e heM f hfM hne).2 h
      · have := hφ'lt f (Finset.mem_sdiff.mpr ⟨hf, hfM⟩)
        simp only [heM, hfM, if_true, if_false]
        omega
      · have := hφ'lt e (Finset.mem_sdiff.mpr ⟨he, heM⟩)
        simp only [heM, hfM, if_true, if_false]
        omega
      · simp only [heM, hfM, if_false]
        exact hφ' e (Finset.mem_sdiff.mpr ⟨he, heM⟩) f (Finset.mem_sdiff.mpr ⟨hf, hfM⟩) hne hadj

end GalvinMultigraph.Local
