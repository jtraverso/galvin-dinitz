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
TARGET FILE for Aristotle (Paper V, gate GALVIN-BKW-LOCAL).

Context: `Galvin.lean` (same directory) proves, for SIMPLE bipartite graphs encoded as `Finset (U × R)`:
  * `kernel_coloring` (from the registered kernel lemma)   — kernel-perfect digraph + lists of size ≥ d⁺ + 1 ⟹ proper list colouring
  * `Galvin.exists_isStable` (registered)      — stable matchings exist for injective rank preferences
  * Kőnig's edge colouring theorem — bipartite Δ-edge-colouring
  * `Galvin.galvin` (registered) — Galvin: |L(e)| ≥ Δ ⟹ proper list edge colouring
Reuse these (or their proof patterns) freely; do not modify `Galvin.lean`.

Encoding of a bipartite MULTIGRAPH: an edge type `E` with endpoint maps `left : E → U`, `right : E → R`
(parallel edges are distinct `e ≠ f` with `left e = left f ∧ right e = right f`). Degrees:
  d(u) = #{e : left e = u},  d(r) = #{e : right e = r}.
Two distinct edges are adjacent iff they share an endpoint (`left e = left f ∨ right e = right f`).

Both theorems must be proved free of incomplete declarations with `#print axioms` = [propext, Classical.choice, Quot.sound].
Theorem B implies Theorem A; if B is out of reach, prove A (the direct multigraph adaptation of
`galvin_max_degree`: Kőnig colouring of the multigraph, Galvin orientation, kernel via Gale–Shapley).
For B (Borodin–Kostochka–Woodall 1997, bipartite multigraphs: χ'_list ≤ max_{uv} max(d(u), d(v))) the
classical proof is Galvin's orientation of the line graph with the stronger out-degree bound obtained by
choosing the Kőnig colouring appropriately / or by the BKW induction; any correct proof is acceptable.
-/
module

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Set
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Interval.Finset.Nat
public import GalvinMultigraph.Local.Kernel
public import GalvinMultigraph.Local.Ranks

@[expose] public section

namespace GalvinMultigraph.Local

variable {U R E : Type*} [Fintype U] [Fintype R] [Fintype E] [DecidableEq U] [DecidableEq R] [DecidableEq E]

/-- Left degree of the vertex `u`. -/
def degL (left : E → U) (u : U) : ℕ := (Finset.univ.filter fun e => left e = u).card

/-- Right degree of the vertex `r`. -/
def degR (right : E → R) (r : R) : ℕ := (Finset.univ.filter fun e => right e = r).card

/-! ### Multigraph infrastructure

The simple-graph development in `Galvin.lean` encodes edges as pairs, which cannot express parallel
edges.  We redevelop the three ingredients of Galvin's proof for an abstract edge type `E`:
stable matchings (kernels of the Galvin orientation), Kőnig's edge colouring, and the Galvin
orientation itself.  The kernel colouring lemma `kernel_coloring` is stated for an arbitrary finite
vertex type and is reused verbatim, with the line graph of the multigraph as its vertex type. -/

omit [Fintype U] [Fintype R] in
/-- **The Galvin engine.**  Given injective rankings of the edges at each vertex (`ru` at the left
endpoints, `rv` at the right endpoints), the line graph of the multigraph, oriented towards the
larger `ru` at left vertices and towards the smaller `rv` at right vertices, is kernel perfect;
hence lists strictly larger than the out-degree suffice. -/
theorem galvin_engine (left : E → U) (right : E → R) (ru rv : E → ℕ)
    (hru : ∀ e f, left e = left f → ru e = ru f → e = f)
    (hrv : ∀ e f, right e = right f → rv e = rv f → e = f)
    (L : E → Finset ℕ)
    (hL : ∀ e, (Finset.univ.filter fun f =>
        (left e = left f ∧ ru e < ru f) ∨ (right e = right f ∧ rv f < rv e)).card < (L e).card) :
    ∃ φ : E → ℕ, (∀ e, φ e ∈ L e) ∧
      ∀ e f, e ≠ f → (left e = left f ∨ right e = right f) → φ e ≠ φ f := by
  classical
  set A : E → E → Prop := fun e f =>
    (left e = left f ∧ ru e < ru f) ∨ (right e = right f ∧ rv f < rv e) with hAdef
  have hirr : ∀ e, ¬ A e e := by intro e; simp [hAdef]
  -- Kernels of the Galvin orientation are exactly stable matchings.
  have hker : ∀ S : Finset E, ∃ K, IsKernelOn A S K := by
    intro S
    set C : ℕ := Finset.univ.sup rv with hC
    have hle : ∀ e, rv e ≤ C := fun e => Finset.le_sup (Finset.mem_univ e)
    obtain ⟨M, hMsub, hMmatch, hMstab⟩ :=
      stable_matching_multi left right ru (fun e => C - rv e) hru
        (by
          intro e f hrr hpp
          have hpp' : C - rv e = C - rv f := hpp
          exact hrv e f hrr (by have := hle e; have := hle f; omega)) S
    refine ⟨M, hMsub, ?_, ?_⟩
    · intro x hx y hy hxy
      rcases eq_or_ne x y with rfl | hne
      · exact hirr x hxy
      · obtain ⟨hl, hr⟩ := hMmatch x hx y hy hne
        rcases hxy with ⟨h, _⟩ | ⟨h, _⟩
        · exact hl h
        · exact hr h
    · intro x hxS hxK
      rcases hMstab x hxS hxK with ⟨f, hfM, hfl, hfp⟩ | ⟨f, hfM, hfr, hfp⟩
      · exact ⟨f, hfM, Or.inl ⟨hfl.symm, hfp⟩⟩
      · refine ⟨f, hfM, Or.inr ⟨hfr.symm, ?_⟩⟩
        have := hle x; have := hle f; omega
  obtain ⟨φ, hφmem, hφ⟩ := kernel_coloring A hirr hker L (fun e => hL e)
  refine ⟨φ, hφmem, ?_⟩
  intro e f hef hadj
  rcases hadj with hl | hr
  · rcases lt_trichotomy (ru e) (ru f) with h | h | h
    · exact hφ e f (Or.inl ⟨hl, h⟩)
    · exact absurd (hru e f hl h) hef
    · exact (hφ f e (Or.inl ⟨hl.symm, h⟩)).symm
  · rcases lt_trichotomy (rv e) (rv f) with h | h | h
    · exact (hφ f e (Or.inr ⟨hr.symm, h⟩)).symm
    · exact absurd (hrv e f hr h) hef
    · exact hφ e f (Or.inr ⟨hr, h⟩)

/-- **Theorem A (Galvin, multigraph, maximum degree).** Bipartite multigraph with all degrees ≤ Δ and lists of
size ≥ Δ has a proper list edge colouring. -/
theorem galvin_multigraph_max_degree (left : E → U) (right : E → R) (Δ : ℕ)
    (hdegU : ∀ u, degL left u ≤ Δ) (hdegR : ∀ r, degR right r ≤ Δ)
    (L : E → Finset ℕ) (hL : ∀ e, Δ ≤ (L e).card) :
    ∃ φ : E → ℕ, (∀ e, φ e ∈ L e) ∧
      ∀ e f, e ≠ f → (left e = left f ∨ right e = right f) → φ e ≠ φ f := by
  classical
  rcases Nat.eq_zero_or_pos Δ with rfl | hΔ
  · -- With `Δ = 0` the multigraph has no edges at all.
    have hempty : ∀ e : E, False := by
      intro e
      have h1 : 1 ≤ degL left (left e) := by
        refine Finset.card_pos.mpr ⟨e, ?_⟩
        simp
      have := hdegU (left e); omega
    exact ⟨fun _ => 0, fun e => (hempty e).elim, fun e => (hempty e).elim⟩
  · obtain ⟨φ0, hφ0lt, hφ0⟩ :=
      konig_multigraph left right Finset.univ Δ (fun u => hdegU u) (fun r => hdegR r)
    have hφ0lt' : ∀ e, φ0 e < Δ := fun e => hφ0lt e (Finset.mem_univ e)
    have hproper : ∀ e f, e ≠ f → (left e = left f ∨ right e = right f) → φ0 e ≠ φ0 f :=
      fun e f h h' => hφ0 e (Finset.mem_univ e) f (Finset.mem_univ f) h h'
    refine galvin_engine left right φ0 φ0 ?_ ?_ L ?_
    · intro e f hlf hcol
      by_contra hne
      exact hproper e f hne (Or.inl hlf) hcol
    · intro e f hrf hcol
      by_contra hne
      exact hproper e f hne (Or.inr hrf) hcol
    · intro e
      have hA : (Finset.univ.filter fun f => left e = left f ∧ φ0 e < φ0 f).card ≤ Δ - 1 - φ0 e := by
        have hinj : Set.InjOn φ0 ↑(Finset.univ.filter fun f => left e = left f ∧ φ0 e < φ0 f) := by
          intro x hx y hy hxy
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
          by_contra hne
          exact hproper x y hne (Or.inl (hx.2.1.symm.trans hy.2.1)) hxy
        have hsub : (Finset.univ.filter fun f => left e = left f ∧ φ0 e < φ0 f).image φ0 ⊆
            Finset.Icc (φ0 e + 1) (Δ - 1) := by
          intro c hc
          simp only [Finset.mem_image, Finset.mem_filter] at hc
          obtain ⟨f, hf, rfl⟩ := hc
          have := hφ0lt' f
          exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        calc (Finset.univ.filter fun f => left e = left f ∧ φ0 e < φ0 f).card
              = ((Finset.univ.filter fun f => left e = left f ∧ φ0 e < φ0 f).image φ0).card :=
              (Finset.card_image_of_injOn hinj).symm
          _ ≤ (Finset.Icc (φ0 e + 1) (Δ - 1)).card := Finset.card_le_card hsub
          _ = Δ - 1 - φ0 e := by rw [Nat.card_Icc]; omega
      have hB : (Finset.univ.filter fun f => right e = right f ∧ φ0 f < φ0 e).card ≤ φ0 e := by
        have hinj : Set.InjOn φ0 ↑(Finset.univ.filter fun f => right e = right f ∧ φ0 f < φ0 e) := by
          intro x hx y hy hxy
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
          by_contra hne
          exact hproper x y hne (Or.inr (hx.2.1.symm.trans hy.2.1)) hxy
        have hsub : (Finset.univ.filter fun f => right e = right f ∧ φ0 f < φ0 e).image φ0 ⊆
            Finset.range (φ0 e) := by
          intro c hc
          simp only [Finset.mem_image, Finset.mem_filter] at hc
          obtain ⟨f, hf, rfl⟩ := hc
          exact Finset.mem_range.mpr hf.2.2
        calc (Finset.univ.filter fun f => right e = right f ∧ φ0 f < φ0 e).card
              = ((Finset.univ.filter fun f => right e = right f ∧ φ0 f < φ0 e).image φ0).card :=
              (Finset.card_image_of_injOn hinj).symm
          _ ≤ (Finset.range (φ0 e)).card := Finset.card_le_card hsub
          _ = φ0 e := Finset.card_range _
      have hsplit : (Finset.univ.filter fun f =>
          (left e = left f ∧ φ0 e < φ0 f) ∨ (right e = right f ∧ φ0 f < φ0 e)).card ≤
          (Finset.univ.filter fun f => left e = left f ∧ φ0 e < φ0 f).card +
            (Finset.univ.filter fun f => right e = right f ∧ φ0 f < φ0 e).card := by
        rw [Finset.filter_or]
        exact Finset.card_union_le _ _
      have hlt := hφ0lt' e
      have hLe := hL e
      omega

/-- **Theorem B (Borodin–Kostochka–Woodall, local lists).** Bipartite multigraph; if every edge `e = uv` has a
list of size ≥ max(d(u), d(v)), there is a proper list edge colouring. -/
theorem galvin_bkw_local (left : E → U) (right : E → R)
    (L : E → Finset ℕ) (hL : ∀ e, max (degL left (left e)) (degR right (right e)) ≤ (L e).card) :
    ∃ φ : E → ℕ, (∀ e, φ e ∈ L e) ∧
      ∀ e f, e ≠ f → (left e = left f ∨ right e = right f) → φ e ≠ φ f := by
  classical
  -- The local slack of an edge: how much its right degree exceeds its left degree.
  set c : E → ℕ := fun e =>
    max (degL left (left e)) (degR right (right e)) - degL left (left e) with hc
  have hdegL : ∀ u, degLOn left Finset.univ u = degL left u := fun _ => rfl
  have hdegR : ∀ v, degROn right Finset.univ v = degR right v := fun _ => rfl
  have hmaxL : ∀ e : E, degL left (left e) ≤ max (degL left (left e)) (degR right (right e)) :=
    fun e => le_max_left _ _
  have hmaxR : ∀ e : E, degR right (right e) ≤ max (degL left (left e)) (degR right (right e)) :=
    fun e => le_max_right _ _
  obtain ⟨pL, pR, hbL, hbR, hiL, hiR, hcle⟩ :=
    ranks_exist left right c Finset.univ (fun _ => 0) (fun _ => 0)
      (fun e _ => Nat.zero_le _)
      (by
        intro e _
        have h1 := hmaxL e
        have h2 := hmaxR e
        simp only [hdegL, hdegR, hc, Nat.zero_add]
        omega)
  refine galvin_engine left right pL pR (fun e f hlf hval => hiL e (Finset.mem_univ e) f
      (Finset.mem_univ f) hlf hval)
    (fun e f hrf hval => hiR e (Finset.mem_univ e) f (Finset.mem_univ f) hrf hval) L ?_
  intro e
  have hbLe := hbL e (Finset.mem_univ e)
  have hbRe := hbR e (Finset.mem_univ e)
  rw [hdegL] at hbLe
  rw [hdegR] at hbRe
  -- The edges above `e` at its left endpoint.
  have hA : (Finset.univ.filter fun f => left e = left f ∧ pL e < pL f).card
      ≤ degL left (left e) - 1 - pL e := by
    have hinj : Set.InjOn pL ↑(Finset.univ.filter fun f => left e = left f ∧ pL e < pL f) := by
      intro x hx y hy hxy
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
      exact hiL x (Finset.mem_univ x) y (Finset.mem_univ y) (hx.2.1.symm.trans hy.2.1) hxy
    have hsub : (Finset.univ.filter fun f => left e = left f ∧ pL e < pL f).image pL ⊆
        Finset.Ico (pL e + 1) (degL left (left e)) := by
      intro k hk
      simp only [Finset.mem_image, Finset.mem_filter] at hk
      obtain ⟨f, hf, rfl⟩ := hk
      have := hbL f (Finset.mem_univ f)
      rw [hdegL, ← hf.2.1] at this
      obtain ⟨_, hup⟩ := this
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    calc (Finset.univ.filter fun f => left e = left f ∧ pL e < pL f).card
          = ((Finset.univ.filter fun f => left e = left f ∧ pL e < pL f).image pL).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Ico (pL e + 1) (degL left (left e))).card := Finset.card_le_card hsub
      _ = degL left (left e) - 1 - pL e := by rw [Nat.card_Ico]; omega
  -- The edges below `e` at its right endpoint.
  have hB : (Finset.univ.filter fun f => right e = right f ∧ pR f < pR e).card ≤ pR e := by
    have hinj : Set.InjOn pR ↑(Finset.univ.filter fun f => right e = right f ∧ pR f < pR e) := by
      intro x hx y hy hxy
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
      exact hiR x (Finset.mem_univ x) y (Finset.mem_univ y) (hx.2.1.symm.trans hy.2.1) hxy
    have hsub : (Finset.univ.filter fun f => right e = right f ∧ pR f < pR e).image pR ⊆
        Finset.range (pR e) := by
      intro k hk
      simp only [Finset.mem_image, Finset.mem_filter] at hk
      obtain ⟨f, hf, rfl⟩ := hk
      exact Finset.mem_range.mpr hf.2.2
    calc (Finset.univ.filter fun f => right e = right f ∧ pR f < pR e).card
          = ((Finset.univ.filter fun f => right e = right f ∧ pR f < pR e).image pR).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range (pR e)).card := Finset.card_le_card hsub
      _ = pR e := Finset.card_range _
  have hsplit : (Finset.univ.filter fun f =>
      (left e = left f ∧ pL e < pL f) ∨ (right e = right f ∧ pR f < pR e)).card ≤
      (Finset.univ.filter fun f => left e = left f ∧ pL e < pL f).card +
        (Finset.univ.filter fun f => right e = right f ∧ pR f < pR e).card := by
    rw [Finset.filter_or]
    exact Finset.card_union_le _ _
  have hcl := hcle e (Finset.mem_univ e)
  have hLe := hL e
  have h1 := hmaxL e
  have h2 := hmaxR e
  have hcval : c e = max (degL left (left e)) (degR right (right e)) - degL left (left e) := rfl
  omega

end GalvinMultigraph.Local
