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
Paper V, gate GALVIN-BKW-LOCAL — the rank construction behind Borodin–Kostochka–Woodall.

Galvin's method needs, at every vertex of the bipartite multigraph, a linear order of the incident
edges.  For the *local* list sizes `max (d u) (d v)` the orders must be chosen so that for every
edge `e = uv` the number of edges above `e` at `u` plus the number of edges below `e` at `v` is at
most `max (d u) (d v) - 1`.  Writing `p u e` for the position of `e` at `u` (a bijection onto
`{0, …, d u - 1}`) this is exactly

  `p v e ≤ p u e + (max (d u) (d v) - d u)`.

The construction is by peeling matchings.  `matching_dichotomy` provides the matching to peel: a
nonempty matching which either covers *every* left vertex, or whose covered left vertices have all
their neighbours covered.  In the first case the matching is placed at the *bottom* of the order at
both of its endpoints, in the second case at the *top*; either way the required inequality is
preserved.  `ranks_exist` runs the induction in the generality needed for it to go through: each
vertex is given an arbitrary starting position `a`, and the invariant is that both the bottom and
the top of the two intervals of an edge are correctly related.
-/
module

public import GalvinMultigraph.Local.Konig

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Set

@[expose] public section

namespace GalvinMultigraph.Local

variable {U R E : Type*} [Fintype U] [Fintype R] [Fintype E]
  [DecidableEq U] [DecidableEq R] [DecidableEq E]

/-! ### Degrees after deleting a matching -/

omit [Fintype U] [Fintype E] [DecidableEq E] in
lemma degLOn_le_of_subset (left : E → U) {S T : Finset E} (h : S ⊆ T) (u : U) :
    degLOn left S u ≤ degLOn left T u :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

omit [Fintype R] [Fintype E] [DecidableEq E] in
lemma degROn_le_of_subset (right : E → R) {S T : Finset E} (h : S ⊆ T) (r : R) :
    degROn right S r ≤ degROn right T r :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

omit [Fintype U] [Fintype R] [Fintype E] [DecidableEq R] in
/-- Deleting a matching drops the left degree of a covered vertex by exactly one. -/
lemma degLOn_sdiff_covered (left : E → U) (right : E → R) (S M : Finset E)
    (hM : IsMatchingOn left right M) (hMS : M ⊆ S) {m : E} (hm : m ∈ M) :
    degLOn left S (left m) = degLOn left (S \ M) (left m) + 1 := by
  classical
  have hkey : (S \ M).filter (fun e => left e = left m)
      = (S.filter (fun e => left e = left m)).erase m := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_erase]
    constructor
    · rintro ⟨⟨hxS, hxM⟩, hx⟩
      exact ⟨fun h => hxM (h ▸ hm), hxS, hx⟩
    · rintro ⟨hxm, hxS, hx⟩
      refine ⟨⟨hxS, ?_⟩, hx⟩
      intro hxM
      exact (hM x hxM m hm hxm).1 (by rw [hx])
  have hmem : m ∈ S.filter (fun e => left e = left m) := Finset.mem_filter.mpr ⟨hMS hm, rfl⟩
  have hpos : 0 < (S.filter (fun e => left e = left m)).card := Finset.card_pos.mpr ⟨m, hmem⟩
  unfold degLOn
  rw [hkey, Finset.card_erase_of_mem hmem]
  omega

omit [Fintype U] [Fintype R] [Fintype E] [DecidableEq U] in
/-- Deleting a matching drops the right degree of a covered vertex by exactly one. -/
lemma degROn_sdiff_covered (left : E → U) (right : E → R) (S M : Finset E)
    (hM : IsMatchingOn left right M) (hMS : M ⊆ S) {m : E} (hm : m ∈ M) :
    degROn right S (right m) = degROn right (S \ M) (right m) + 1 := by
  classical
  have hkey : (S \ M).filter (fun e => right e = right m)
      = (S.filter (fun e => right e = right m)).erase m := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_erase]
    constructor
    · rintro ⟨⟨hxS, hxM⟩, hx⟩
      exact ⟨fun h => hxM (h ▸ hm), hxS, hx⟩
    · rintro ⟨hxm, hxS, hx⟩
      refine ⟨⟨hxS, ?_⟩, hx⟩
      intro hxM
      exact (hM x hxM m hm hxm).2 (by rw [hx])
  have hmem : m ∈ S.filter (fun e => right e = right m) := Finset.mem_filter.mpr ⟨hMS hm, rfl⟩
  have hpos : 0 < (S.filter (fun e => right e = right m)).card := Finset.card_pos.mpr ⟨m, hmem⟩
  unfold degROn
  rw [hkey, Finset.card_erase_of_mem hmem]
  omega

omit [Fintype U] [Fintype E] in
lemma degLOn_sdiff_uncovered (left : E → U) (S M : Finset E) (u : U)
    (h : ∀ m ∈ M, left m ≠ u) : degLOn left (S \ M) u = degLOn left S u := by
  unfold degLOn
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1, fun hxM => h x hxM hx.2⟩, hx.2⟩⟩

omit [Fintype R] [Fintype E] in
lemma degROn_sdiff_uncovered (right : E → R) (S M : Finset E) (v : R)
    (h : ∀ m ∈ M, right m ≠ v) : degROn right (S \ M) v = degROn right S v := by
  unfold degROn
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1, fun hxM => h x hxM hx.2⟩, hx.2⟩⟩

omit [Fintype U] [Fintype E] [DecidableEq E] in
lemma degLOn_pos (left : E → U) {S : Finset E} {e : E} (he : e ∈ S) :
    0 < degLOn left S (left e) :=
  Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, rfl⟩⟩

omit [Fintype R] [Fintype E] [DecidableEq E] in
lemma degROn_pos (right : E → R) {S : Finset E} {e : E} (he : e ∈ S) :
    0 < degROn right S (right e) :=
  Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, rfl⟩⟩

/-! ### The matching to be peeled -/

omit [Fintype U] [Fintype R] [Fintype E] in
/-- Hall's theorem, in the form used below: if every subset of `A` has at least as many
neighbours as elements, then `S` contains a matching covering `A` on the left and nothing else,
whose right endpoints exhaust `A`'s neighbourhood as far as cardinality permits. -/
lemma hall_matching (left : E → U) (right : E → R) (S : Finset E) (A : Finset U)
    (hAne : A.Nonempty)
    (hall : ∀ B ⊆ A,
      B.card ≤ (B.biUnion (fun u => (S.filter fun e => left e = u).image right)).card) :
    ∃ M : Finset E, M ⊆ S ∧ M.Nonempty ∧ IsMatchingOn left right M ∧
      (∀ u ∈ A, ∃ e ∈ M, left e = u) ∧ (∀ e ∈ M, left e ∈ A) ∧
      M.image right ⊆ A.biUnion (fun u => (S.filter fun e => left e = u).image right) ∧
      A.card ≤ (M.image right).card := by
  classical
  set nbr : U → Finset R := fun u => (S.filter fun e => left e = u).image right with hnbr
  have hall' : ∀ B : Finset ↥A, B.card ≤ (B.biUnion fun u => nbr u.val).card := by
    intro B
    have h1 : (B.image Subtype.val).card = B.card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    have h2 : (B.image Subtype.val).biUnion nbr = B.biUnion fun u => nbr u.val := by
      ext r
      simp only [Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨u, ⟨v, hv, rfl⟩, hr⟩
        exact ⟨v, hv, hr⟩
      · rintro ⟨v, hv, hr⟩
        exact ⟨v.val, ⟨v, hv, rfl⟩, hr⟩
    have hsub : B.image Subtype.val ⊆ A := by
      intro u hu
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hu
      exact v.2
    have := hall _ hsub
    rw [h1, h2] at this
    exact this
  obtain ⟨f, hfinj, hf⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective (fun u : ↥A => nbr u.val)).mp hall'
  have hex : ∀ u : ↥A, ∃ e, e ∈ S ∧ left e = u.val ∧ right e = f u := by
    intro u
    obtain ⟨e, he, hre⟩ := Finset.mem_image.mp (hf u)
    exact ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2, hre⟩
  choose g hgS hgl hgr using hex
  refine ⟨Finset.image g Finset.univ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he
    exact hgS u
  · obtain ⟨u, hu⟩ := hAne
    exact ⟨g ⟨u, hu⟩, Finset.mem_image.mpr ⟨⟨u, hu⟩, Finset.mem_univ _, rfl⟩⟩
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
    exact ⟨g ⟨u, hu⟩, Finset.mem_image.mpr ⟨⟨u, hu⟩, Finset.mem_univ _, rfl⟩, hgl ⟨u, hu⟩⟩
  · intro e he
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he
    rw [hgl u]
    exact u.2
  · intro r hr
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_biUnion.mpr ⟨u.val, u.2, by rw [hgr u]; exact hf u⟩
  · have himg : (Finset.image g Finset.univ).image right = Finset.univ.image f := by
      rw [Finset.image_image]
      exact Finset.image_congr (fun u _ => hgr u)
    rw [himg, Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_coe]

omit [Fintype R] [Fintype E] in
/-- **The peeling dichotomy.**  A nonempty set of edges contains a nonempty matching which either
covers every left vertex that carries an edge, or is such that every neighbour of a covered left
vertex is covered on the right. -/
lemma matching_dichotomy (left : E → U) (right : E → R) (S : Finset E) (hS : S.Nonempty) :
    ∃ M : Finset E, M ⊆ S ∧ M.Nonempty ∧ IsMatchingOn left right M ∧
      ((∀ e ∈ S, ∃ f ∈ M, left f = left e) ∨
       (∀ e ∈ S, (∃ f ∈ M, left f = left e) → ∃ f ∈ M, right f = right e)) := by
  classical
  set nbr : U → Finset R := fun u => (S.filter fun e => left e = u).image right with hnbr
  by_cases hall : ∀ B ⊆ S.image left, B.card ≤ (B.biUnion nbr).card
  · -- Hall's condition holds: a matching covering all left vertices.
    obtain ⟨e0, he0⟩ := hS
    obtain ⟨M, hMS, hMne, hM, hcov, _, _, _⟩ :=
      hall_matching left right S (S.image left) ⟨left e0, Finset.mem_image_of_mem _ he0⟩ hall
    exact ⟨M, hMS, hMne, hM, Or.inl fun e he => hcov (left e) (Finset.mem_image_of_mem _ he)⟩
  · -- Hall's condition fails: a minimal violating set minus one vertex is tight.
    push_neg at hall
    obtain ⟨B0, hB0sub, hB0⟩ := hall
    set bad : Finset (Finset U) :=
      (Finset.univ : Finset (Finset U)).filter
        (fun B => B ⊆ S.image left ∧ (B.biUnion nbr).card < B.card) with hbad
    have hbadne : bad.Nonempty := ⟨B0, by simp [hbad, hB0sub, hB0]⟩
    obtain ⟨A, hAbad, hAmin⟩ := Finset.exists_min_image bad Finset.card hbadne
    obtain ⟨hAsub, hAcard⟩ : A ⊆ S.image left ∧ (A.biUnion nbr).card < A.card := by
      have := Finset.mem_filter.mp hAbad
      exact this.2
    have hA2 : 2 ≤ A.card := by
      by_contra hlt
      interval_cases h : A.card
      · omega
      · obtain ⟨x, hAx⟩ := Finset.card_eq_one.mp h
        subst hAx
        have hxim : x ∈ S.image left := hAsub (Finset.mem_singleton_self x)
        obtain ⟨e, heS, hex⟩ := Finset.mem_image.mp hxim
        have : (nbr x).Nonempty :=
          ⟨right e, Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨heS, hex⟩, rfl⟩⟩
        have hcard : 1 ≤ (({x} : Finset U).biUnion nbr).card := by
          rw [Finset.singleton_biUnion]
          exact Finset.card_pos.mpr this
        omega
    obtain ⟨x, hx⟩ : A.Nonempty := Finset.card_pos.mp (by omega)
    set A' : Finset U := A.erase x with hA'
    have hA'card : A'.card = A.card - 1 := Finset.card_erase_of_mem hx
    have hA'sub : A' ⊆ A := Finset.erase_subset _ _
    have hA'ne : A'.Nonempty := Finset.card_pos.mp (by omega)
    have hall' : ∀ B ⊆ A', B.card ≤ (B.biUnion nbr).card := by
      intro B hB
      by_contra hlt
      push_neg at hlt
      have hBbad : B ∈ bad := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hB.trans hA'sub).trans hAsub, hlt⟩
      have := hAmin B hBbad
      have hBcard : B.card ≤ A'.card := Finset.card_le_card hB
      omega
    obtain ⟨M, hMS, hMne, hM, hcov, hleftmem, himgsub, hcardge⟩ :=
      hall_matching left right S A' hA'ne hall'
    have hNsub : A'.biUnion nbr ⊆ A.biUnion nbr := Finset.biUnion_subset_biUnion_of_subset_left _ hA'sub
    have hNcard : (A'.biUnion nbr).card ≤ (M.image right).card := by
      have := Finset.card_le_card hNsub
      omega
    have heq : M.image right = A'.biUnion nbr :=
      Finset.eq_of_subset_of_card_le himgsub hNcard
    refine ⟨M, hMS, hMne, hM, Or.inr ?_⟩
    rintro e heS ⟨f, hfM, hfl⟩
    have hxA' : left e ∈ A' := hfl ▸ hleftmem f hfM
    have : right e ∈ A'.biUnion nbr :=
      Finset.mem_biUnion.mpr ⟨left e, hxA',
        Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨heS, rfl⟩, rfl⟩⟩
    rw [← heq] at this
    obtain ⟨f', hf', hf'r⟩ := Finset.mem_image.mp this
    exact ⟨f', hf', hf'r⟩

/-! ### The rank construction -/

omit [Fintype R] [Fintype E] in
/-- **The rank construction.**  Each left vertex `u` is given a starting position `aL u` and each
right vertex `v` a starting position `aR v`.  Under the two displayed hypotheses — the bottoms and
the tops of the two position intervals of every edge are related by the edge constant `c e` — the
edges of `S` can be numbered at each vertex, consecutively from the starting position, so that for
every edge `e = uv` the position of `e` at `v` exceeds its position at `u` by at most `c e`.

Applied with `aL = aR = 0` and `c e = max (d u) (d v) - d u` this is exactly the ordering needed
for the Galvin orientation in the Borodin–Kostochka–Woodall theorem. -/
theorem ranks_exist (left : E → U) (right : E → R) (c : E → ℕ) (S : Finset E) :
    ∀ aL : U → ℕ, ∀ aR : R → ℕ,
    (∀ e ∈ S, aR (right e) ≤ aL (left e) + c e) →
    (∀ e ∈ S, aR (right e) + degROn right S (right e)
        ≤ aL (left e) + degLOn left S (left e) + c e) →
    ∃ pL pR : E → ℕ,
      (∀ e ∈ S, aL (left e) ≤ pL e ∧ pL e < aL (left e) + degLOn left S (left e)) ∧
      (∀ e ∈ S, aR (right e) ≤ pR e ∧ pR e < aR (right e) + degROn right S (right e)) ∧
      (∀ e ∈ S, ∀ f ∈ S, left e = left f → pL e = pL f → e = f) ∧
      (∀ e ∈ S, ∀ f ∈ S, right e = right f → pR e = pR f → e = f) ∧
      (∀ e ∈ S, pR e ≤ pL e + c e) := by
  classical
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro aL aR h1 h2
    rcases S.eq_empty_or_nonempty with rfl | hS
    · exact ⟨fun _ => 0, fun _ => 0, by simp, by simp, by simp, by simp, by simp⟩
    obtain ⟨M, hMS, hMne, hM, hcase⟩ := matching_dichotomy left right S hS
    obtain ⟨m0, hm0⟩ := hMne
    have hssub : S \ M ⊂ S := by
      refine Finset.ssubset_iff_of_subset Finset.sdiff_subset |>.2 ⟨m0, hMS hm0, ?_⟩
      simp [Finset.mem_sdiff, hm0]
    -- degree bookkeeping
    have hdL1 : ∀ m ∈ M, degLOn left S (left m) = degLOn left (S \ M) (left m) + 1 :=
      fun m hm => degLOn_sdiff_covered left right S M hM hMS hm
    have hdR1 : ∀ m ∈ M, degROn right S (right m) = degROn right (S \ M) (right m) + 1 :=
      fun m hm => degROn_sdiff_covered left right S M hM hMS hm
    have hdL0 : ∀ u, (∀ m ∈ M, left m ≠ u) → degLOn left (S \ M) u = degLOn left S u :=
      fun u h => degLOn_sdiff_uncovered left S M u h
    have hdR0 : ∀ v, (∀ m ∈ M, right m ≠ v) → degROn right (S \ M) v = degROn right S v :=
      fun v h => degROn_sdiff_uncovered right S M v h
    have hdLle : ∀ u, degLOn left (S \ M) u ≤ degLOn left S u :=
      fun u => degLOn_le_of_subset left Finset.sdiff_subset u
    have hdRle : ∀ v, degROn right (S \ M) v ≤ degROn right S v :=
      fun v => degROn_le_of_subset right Finset.sdiff_subset v
    -- the covered-degree identities in the form used repeatedly below
    have hdLcov : ∀ u, (∃ m ∈ M, left m = u) →
        degLOn left S u = degLOn left (S \ M) u + 1 := by
      rintro u ⟨m, hm, rfl⟩; exact hdL1 m hm
    have hdRcov : ∀ v, (∃ m ∈ M, right m = v) →
        degROn right S v = degROn right (S \ M) v + 1 := by
      rintro v ⟨m, hm, rfl⟩; exact hdR1 m hm
    rcases hcase with hA | hB
    · -- Case A: `M` covers every left vertex; place it at the bottom of both orders.
      set aL' : U → ℕ := fun u => aL u + (if (∃ m ∈ M, left m = u) then 1 else 0) with haL'
      set aR' : R → ℕ := fun v => aR v + (if (∃ m ∈ M, right m = v) then 1 else 0) with haR'
      have hcovL : ∀ e ∈ S \ M, (∃ m ∈ M, left m = left e) := by
        intro e he
        exact hA e (Finset.mem_sdiff.mp he).1
      have h1' : ∀ e ∈ S \ M, aR' (right e) ≤ aL' (left e) + c e := by
        intro e he
        have hx : (∃ m ∈ M, left m = left e) := hcovL e he
        have := h1 e (Finset.mem_sdiff.mp he).1
        simp only [haL', haR', hx, if_true]
        split <;> omega
      have h2' : ∀ e ∈ S \ M, aR' (right e) + degROn right (S \ M) (right e)
          ≤ aL' (left e) + degLOn left (S \ M) (left e) + c e := by
        intro e he
        have hx : (∃ m ∈ M, left m = left e) := hcovL e he
        have hxd := hdLcov (left e) hx
        have hb := h2 e (Finset.mem_sdiff.mp he).1
        simp only [haL', haR', hx, if_true]
        by_cases hy : (∃ m ∈ M, right m = right e)
        · have hyd := hdRcov (right e) hy
          simp only [hy, if_true]
          omega
        · have hyd := hdR0 (right e) (by push_neg at hy; intro m hm; exact hy m hm)
          simp only [hy, if_false]
          omega
      obtain ⟨pL', pR', hbL', hbR', hiL', hiR', hc'⟩ := ih (S \ M) hssub aL' aR' h1' h2'
      refine ⟨fun e => if e ∈ M then aL (left e) else pL' e,
              fun e => if e ∈ M then aR (right e) else pR' e, ?_, ?_, ?_, ?_, ?_⟩
      · intro e he
        by_cases hem : e ∈ M
        · simp only [hem, if_true]
          have := degLOn_pos left he
          omega
        · have heS : e ∈ S \ M := Finset.mem_sdiff.mpr ⟨he, hem⟩
          have hx : (∃ m ∈ M, left m = left e) := hcovL e heS
          have hxd := hdLcov (left e) hx
          have := hbL' e heS
          simp only [hem, if_false, haL', hx, if_true] at this ⊢
          omega
      · intro e he
        by_cases hem : e ∈ M
        · simp only [hem, if_true]
          have := degROn_pos right he
          omega
        · have heS : e ∈ S \ M := Finset.mem_sdiff.mpr ⟨he, hem⟩
          have hb := hbR' e heS
          simp only [hem, if_false]
          by_cases hy : (∃ m ∈ M, right m = right e)
          · have hyd := hdRcov (right e) hy
            simp only [haR', hy, if_true] at hb
            omega
          · have hyd := hdR0 (right e) (by push_neg at hy; intro m hm; exact hy m hm)
            simp only [haR', hy, if_false] at hb
            omega
      · intro e he f hf hlef hval
        by_cases hem : e ∈ M <;> by_cases hfm : f ∈ M
        · by_contra hne
          exact (hM e hem f hfm hne).1 hlef
        · exfalso
          have hfS : f ∈ S \ M := Finset.mem_sdiff.mpr ⟨hf, hfm⟩
          have hx : (∃ m ∈ M, left m = left f) := hcovL f hfS
          have hb := (hbL' f hfS).1
          simp only [hem, if_true, hfm, if_false] at hval
          simp only [haL', hx, if_true] at hb
          rw [hlef] at hval
          omega
        · exfalso
          have heS : e ∈ S \ M := Finset.mem_sdiff.mpr ⟨he, hem⟩
          have hx : (∃ m ∈ M, left m = left e) := hcovL e heS
          have hb := (hbL' e heS).1
          simp only [hem, if_false, hfm, if_true] at hval
          simp only [haL', hx, if_true] at hb
          rw [← hlef] at hval
          omega
        · simp only [hem, if_false, hfm, if_false] at hval
          exact hiL' e (Finset.mem_sdiff.mpr ⟨he, hem⟩) f (Finset.mem_sdiff.mpr ⟨hf, hfm⟩) hlef hval
      · intro e he f hf hlef hval
        by_cases hem : e ∈ M <;> by_cases hfm : f ∈ M
        · by_contra hne
          exact (hM e hem f hfm hne).2 hlef
        · exfalso
          have hfS : f ∈ S \ M := Finset.mem_sdiff.mpr ⟨hf, hfm⟩
          have hy : (∃ m ∈ M, right m = right f) := ⟨e, hem, hlef⟩
          have hb := (hbR' f hfS).1
          simp only [hem, if_true, hfm, if_false] at hval
          simp only [haR', hy, if_true] at hb
          rw [hlef] at hval
          omega
        · exfalso
          have heS : e ∈ S \ M := Finset.mem_sdiff.mpr ⟨he, hem⟩
          have hy : (∃ m ∈ M, right m = right e) := ⟨f, hfm, hlef.symm⟩
          have hb := (hbR' e heS).1
          simp only [hem, if_false, hfm, if_true] at hval
          simp only [haR', hy, if_true] at hb
          rw [← hlef] at hval
          omega
        · simp only [hem, if_false, hfm, if_false] at hval
          exact hiR' e (Finset.mem_sdiff.mpr ⟨he, hem⟩) f (Finset.mem_sdiff.mpr ⟨hf, hfm⟩) hlef hval
      · intro e he
        by_cases hem : e ∈ M
        · simp only [hem, if_true]
          exact h1 e he
        · simp only [hem, if_false]
          exact hc' e (Finset.mem_sdiff.mpr ⟨he, hem⟩)
    · -- Case B: neighbours of covered left vertices are covered; place `M` at the top.
      have h1' : ∀ e ∈ S \ M, aR (right e) ≤ aL (left e) + c e :=
        fun e he => h1 e (Finset.mem_sdiff.mp he).1
      have h2' : ∀ e ∈ S \ M, aR (right e) + degROn right (S \ M) (right e)
          ≤ aL (left e) + degLOn left (S \ M) (left e) + c e := by
        intro e he
        have heS := (Finset.mem_sdiff.mp he).1
        have hb := h2 e heS
        by_cases hx : (∃ m ∈ M, left m = left e)
        · have hy := hB e heS hx
          have hxd := hdLcov (left e) hx
          have hyd := hdRcov (right e) hy
          omega
        · have hxd := hdL0 (left e) (by push_neg at hx; intro m hm; exact hx m hm)
          have hyd := hdRle (right e)
          omega
      obtain ⟨pL', pR', hbL', hbR', hiL', hiR', hc'⟩ := ih (S \ M) hssub aL aR h1' h2'
      refine ⟨fun e => if e ∈ M then aL (left e) + degLOn left S (left e) - 1 else pL' e,
              fun e => if e ∈ M then aR (right e) + degROn right S (right e) - 1 else pR' e,
              ?_, ?_, ?_, ?_, ?_⟩
      · intro e he
        by_cases hem : e ∈ M
        · simp only [hem, if_true]
          have := degLOn_pos left he
          omega
        · have := hbL' e (Finset.mem_sdiff.mpr ⟨he, hem⟩)
          have hle := hdLle (left e)
          simp only [hem, if_false]
          omega
      · intro e he
        by_cases hem : e ∈ M
        · simp only [hem, if_true]
          have := degROn_pos right he
          omega
        · have := hbR' e (Finset.mem_sdiff.mpr ⟨he, hem⟩)
          have hle := hdRle (right e)
          simp only [hem, if_false]
          omega
      · intro e he f hf hlef hval
        by_cases hem : e ∈ M <;> by_cases hfm : f ∈ M
        · by_contra hne
          exact (hM e hem f hfm hne).1 hlef
        · exfalso
          have hfS : f ∈ S \ M := Finset.mem_sdiff.mpr ⟨hf, hfm⟩
          have hx : (∃ m ∈ M, left m = left f) := ⟨e, hem, hlef⟩
          have hxd := hdLcov (left f) hx
          have := (hbL' f hfS).2
          simp only [hem, if_true, hfm, if_false] at hval
          rw [hlef] at hval
          omega
        · exfalso
          have heS : e ∈ S \ M := Finset.mem_sdiff.mpr ⟨he, hem⟩
          have hx : (∃ m ∈ M, left m = left e) := ⟨f, hfm, hlef.symm⟩
          have hxd := hdLcov (left e) hx
          have := (hbL' e heS).2
          simp only [hem, if_false, hfm, if_true] at hval
          rw [← hlef] at hval
          omega
        · simp only [hem, if_false, hfm, if_false] at hval
          exact hiL' e (Finset.mem_sdiff.mpr ⟨he, hem⟩) f (Finset.mem_sdiff.mpr ⟨hf, hfm⟩) hlef hval
      · intro e he f hf hlef hval
        by_cases hem : e ∈ M <;> by_cases hfm : f ∈ M
        · by_contra hne
          exact (hM e hem f hfm hne).2 hlef
        · exfalso
          have hfS : f ∈ S \ M := Finset.mem_sdiff.mpr ⟨hf, hfm⟩
          have hy : (∃ m ∈ M, right m = right f) := ⟨e, hem, hlef⟩
          have hyd := hdRcov (right f) hy
          have := (hbR' f hfS).2
          simp only [hem, if_true, hfm, if_false] at hval
          rw [hlef] at hval
          omega
        · exfalso
          have heS : e ∈ S \ M := Finset.mem_sdiff.mpr ⟨he, hem⟩
          have hy : (∃ m ∈ M, right m = right e) := ⟨f, hfm, hlef.symm⟩
          have hyd := hdRcov (right e) hy
          have := (hbR' e heS).2
          simp only [hem, if_false, hfm, if_true] at hval
          rw [← hlef] at hval
          omega
        · simp only [hem, if_false, hfm, if_false] at hval
          exact hiR' e (Finset.mem_sdiff.mpr ⟨he, hem⟩) f (Finset.mem_sdiff.mpr ⟨hf, hfm⟩) hlef hval
      · intro e he
        by_cases hem : e ∈ M
        · simp only [hem, if_true]
          have hb := h2 e he
          have := degLOn_pos left he
          have := degROn_pos right he
          omega
        · simp only [hem, if_false]
          exact hc' e (Finset.mem_sdiff.mpr ⟨he, hem⟩)

end GalvinMultigraph.Local
