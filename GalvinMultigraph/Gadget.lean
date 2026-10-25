/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# A simple bipartite replacement for parallel edges

For each edge identifier e, insert K_{k,k} with its (0,0) edge removed.
The two missing incidences connect to the original endpoints of e. Original
vertices have their original multidegrees; every inserted vertex has degree k.
-/

@[expose] public section

namespace GalvinMultigraph.Gadget

open Finset SimpleGraph

variable {A B E Color : Type*} {k : ℕ} [NeZero k]

abbrev Left (A E : Type*) (k : ℕ) := A ⊕ (E × Fin k)
abbrev Right (B E : Type*) (k : ℕ) := B ⊕ (E × Fin k)
abbrev Vertex (A B E : Type*) (k : ℕ) := Left A E k ⊕ Right B E k

/-- Cross-part incidences in the replacement graph. -/
def cross (a : E → A) (b : E → B) : Left A E k → Right B E k → Prop
  | .inl _, .inl _ => False
  | .inl x, .inr (e, j) => a e = x ∧ j = 0
  | .inr (e, i), .inl y => b e = y ∧ i = 0
  | .inr (e, i), .inr (f, j) => e = f ∧ (i ≠ 0 ∨ j ≠ 0)

/-- The simple bipartite replacement graph. -/
def graph (a : E → A) (b : E → B) : SimpleGraph (Vertex A B E k) where
  Adj
    | .inl u, .inr v => cross a b u v
    | .inr v, .inl u => cross a b u v
    | _, _ => False
  symm := ⟨by rintro (u | u) (v | v) h <;> exact h⟩
  loopless := ⟨by rintro (v | v) h <;> exact h⟩

noncomputable instance (a : E → A) (b : E → B) :
    DecidableRel (graph (k := k) a b).Adj := Classical.decRel _

def coloring (a : E → A) (b : E → B) : (graph (k := k) a b).Coloring (Fin 2) :=
  Coloring.mk (Sum.elim (fun _ => 0) (fun _ => 1)) (by
    rintro (u | u) (v | v) h <;> simp_all [graph])

/-- The original left endpoint and its terminal edge. -/
def aEdge (a : E → A) (b : E → B) (e : E) : (graph (k := k) a b).edgeSet :=
  ⟨s(Sum.inl (Sum.inl (a e)), Sum.inr (Sum.inr (e, 0))), by simp [graph, cross]⟩

/-- The original right endpoint and its terminal edge. -/
def bEdge (a : E → A) (b : E → B) (e : E) : (graph (k := k) a b).edgeSet :=
  ⟨s(Sum.inl (Sum.inr (e, 0)), Sum.inr (Sum.inl (b e))), by simp [graph, cross]⟩

def innerEdge (a : E → A) (b : E → B) (e : E) (i j : Fin k)
    (h : i ≠ 0 ∨ j ≠ 0) : (graph (k := k) a b).edgeSet :=
  ⟨s(Sum.inl (Sum.inr (e, i)), Sum.inr (Sum.inr (e, j))), by simp [graph, cross, h]⟩

def rowEdge (a : E → A) (b : E → B) (e : E) (i j : Fin k) :
    (graph (k := k) a b).edgeSet :=
  if h : i = 0 ∧ j = 0 then bEdge a b e
  else innerEdge a b e i j (by tauto)

def tag : Vertex A B E k → Option E
  | .inl (.inr (e, _)) => some e
  | .inr (.inr (e, _)) => some e
  | _ => none

open Classical in
noncomputable def tagList (P : E → Finset Color) : Option E → Option E → Finset Color
  | none, none => ∅
  | some e, none => P e
  | none, some e => P e
  | some e, some f => if e = f then P e else ∅

theorem tagList_symm (P : E → Finset Color) (x y : Option E) :
    tagList P x y = tagList P y x := by
  classical
  cases x with
  | none => cases y <;> rfl
  | some e =>
    cases y with
    | none => rfl
    | some f =>
      by_cases h : e = f
      · subst f; rfl
      · simp [tagList, h, Ne.symm h]

noncomputable def lists (a : E → A) (b : E → B) (P : E → Finset Color)
    (e : (graph (k := k) a b).edgeSet) : Finset Color :=
  Sym2.lift ⟨fun u v => tagList P (tag u) (tag v), fun _ _ => tagList_symm P _ _⟩ e.1

@[simp] theorem lists_aEdge (a : E → A) (b : E → B) (P : E → Finset Color) (e : E) :
    lists a b P (aEdge (k := k) a b e) = P e := rfl

@[simp] theorem lists_bEdge (a : E → A) (b : E → B) (P : E → Finset Color) (e : E) :
    lists a b P (bEdge (k := k) a b e) = P e := rfl

@[simp] theorem lists_innerEdge (a : E → A) (b : E → B) (P : E → Finset Color)
    (e : E) (i j : Fin k) (h : i ≠ 0 ∨ j ≠ 0) :
    lists a b P (innerEdge a b e i j h) = P e := by
  classical
  simp [lists, innerEdge, tag, tagList, Sym2.lift_mk]

@[simp] theorem lists_rowEdge (a : E → A) (b : E → B) (P : E → Finset Color)
    (e : E) (i j : Fin k) : lists a b P (rowEdge a b e i j) = P e := by
  classical
  unfold rowEdge
  split <;> simp

theorem rowEdge_injective (a : E → A) (b : E → B) (e : E) (i : Fin k) :
    Function.Injective (rowEdge a b e i) := by
  intro j j' h
  have hval := congrArg Subtype.val h
  unfold rowEdge at hval
  split_ifs at hval with h h'
  · exact h.2.trans h'.2.symm
  · simp [bEdge, innerEdge] at hval
  · simp [bEdge, innerEdge] at hval
  · simpa [innerEdge] using hval

theorem rowEdge_mem (a : E → A) (b : E → B) (e : E) (i j : Fin k) :
    Sum.inl (Sum.inr (e, i)) ∈ (rowEdge a b e i j).val := by
  unfold rowEdge
  split_ifs with h
  · simp [bEdge, h.1]
  · simp [innerEdge]

theorem columnEdge_injective (a : E → A) (b : E → B) (e : E) (j : Fin k) (hj : j ≠ 0) :
    Function.Injective (fun i => rowEdge a b e i j) := by
  intro i i' h
  have hval := congrArg Subtype.val h
  simpa [rowEdge, hj, innerEdge] using hval

theorem columnEdge_mem (a : E → A) (b : E → B) (e : E) (i j : Fin k) (hj : j ≠ 0) :
    Sum.inr (Sum.inr (e, j)) ∈ (rowEdge a b e i j).val := by
  simp [rowEdge, hj, innerEdge]

theorem neighbor_a_iff (a : E → A) (b : E → B) (x : A) (v : Vertex A B E k) :
    (graph a b).Adj (Sum.inl (Sum.inl x)) v ↔
      ∃ e, a e = x ∧ v = Sum.inr (Sum.inr (e, 0)) := by
  rcases v with (y | ⟨e, i⟩) | (y | ⟨e, i⟩) <;>
    simp [graph, cross, eq_comm]

theorem neighbor_b_iff (a : E → A) (b : E → B) (y : B) (v : Vertex A B E k) :
    (graph a b).Adj (Sum.inr (Sum.inl y)) v ↔
      ∃ e, b e = y ∧ v = Sum.inl (Sum.inr (e, 0)) := by
  rcases v with (x | ⟨e, i⟩) | (x | ⟨e, i⟩) <;>
    simp [graph, cross, eq_comm]

/-- At an inserted vertex, an incident edge is determined by the opposite index. -/
def index : Vertex A B E k → Fin k
  | .inl (.inr (_, i)) => i
  | .inr (.inr (_, i)) => i
  | _ => 0

theorem index_injective_left (a : E → A) (b : E → B) (e : E) (i : Fin k) :
    Function.Injective (fun v : (graph a b).neighborSet (Sum.inl (Sum.inr (e, i))) =>
      index v.val) := by
  rintro ⟨v, hv⟩ ⟨w, hw⟩ h
  apply Subtype.ext
  rcases v with (x | ⟨f, j⟩) | (y | ⟨f, j⟩) <;>
    rcases w with (x' | ⟨g, l⟩) | (y' | ⟨g, l⟩) <;>
    simp only [graph, cross] at hv hw <;>
    simp only [index] at h <;> aesop

theorem index_injective_right (a : E → A) (b : E → B) (e : E) (j : Fin k) :
    Function.Injective (fun v : (graph a b).neighborSet (Sum.inr (Sum.inr (e, j))) =>
      index v.val) := by
  rintro ⟨v, hv⟩ ⟨w, hw⟩ h
  apply Subtype.ext
  rcases v with (x | ⟨f, i⟩) | (y | ⟨f, i⟩) <;>
    rcases w with (x' | ⟨g, l⟩) | (y' | ⟨g, l⟩) <;>
    simp only [graph, cross] at hv hw <;>
    simp only [index] at h <;> aesop

theorem degree_a [Fintype A] [Fintype B] [Fintype E]
    (a : E → A) (b : E → B) (x : A) :
    (graph (k := k) a b).degree (Sum.inl (Sum.inl x)) ≤
      Nat.card {e // a e = x} := by
  classical
  let f : (graph (k := k) a b).neighborSet (Sum.inl (Sum.inl x)) → {e // a e = x} :=
    fun v => ⟨((neighbor_a_iff a b x v.val).mp v.property).choose,
      ((neighbor_a_iff a b x v.val).mp v.property).choose_spec.1⟩
  have hf : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    have hv := ((neighbor_a_iff a b x v.val).mp v.property).choose_spec.2
    have hw := ((neighbor_a_iff a b x w.val).mp w.property).choose_spec.2
    have he : (f v).val = (f w).val := congrArg Subtype.val h
    change v.val = Sum.inr (Sum.inr ((f v).val, 0)) at hv
    change w.val = Sum.inr (Sum.inr ((f w).val, 0)) at hw
    rw [hv, hw, he]
  rw [← card_neighborSet_eq_degree, Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_injective f hf

theorem degree_b [Fintype A] [Fintype B] [Fintype E]
    (a : E → A) (b : E → B) (y : B) :
    (graph (k := k) a b).degree (Sum.inr (Sum.inl y)) ≤
      Nat.card {e // b e = y} := by
  classical
  let f : (graph (k := k) a b).neighborSet (Sum.inr (Sum.inl y)) → {e // b e = y} :=
    fun v => ⟨((neighbor_b_iff a b y v.val).mp v.property).choose,
      ((neighbor_b_iff a b y v.val).mp v.property).choose_spec.1⟩
  have hf : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    have hv := ((neighbor_b_iff a b y v.val).mp v.property).choose_spec.2
    have hw := ((neighbor_b_iff a b y w.val).mp w.property).choose_spec.2
    have he : (f v).val = (f w).val := congrArg Subtype.val h
    change v.val = Sum.inl (Sum.inr ((f v).val, 0)) at hv
    change w.val = Sum.inl (Sum.inr ((f w).val, 0)) at hw
    rw [hv, hw, he]
  rw [← card_neighborSet_eq_degree, Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_injective f hf

theorem maxDegree_le [Fintype A] [Fintype B] [Fintype E]
    (a : E → A) (b : E → B)
    (ha : ∀ x, Nat.card {e // a e = x} ≤ k)
    (hb : ∀ y, Nat.card {e // b e = y} ≤ k) : (graph (k := k) a b).maxDegree ≤ k := by
  classical
  apply (graph (k := k) a b).maxDegree_le_of_forall_degree_le k
  rintro ((x | ⟨e, i⟩) | (y | ⟨e, j⟩))
  · exact (degree_a a b x).trans (ha x)
  · rw [← card_neighborSet_eq_degree]
    simpa using Fintype.card_le_of_injective _ (index_injective_left a b e i)
  · exact (degree_b a b y).trans (hb y)
  · rw [← card_neighborSet_eq_degree]
    simpa using Fintype.card_le_of_injective _ (index_injective_right a b e j)

theorem lists_card (a : E → A) (b : E → B) (P : E → Finset Color)
    (hP : ∀ e, (P e).card = k) (f : (graph (k := k) a b).edgeSet) :
    (lists a b P f).card = k := by
  classical
  obtain ⟨f, hf⟩ := f
  induction f using Sym2.ind with
  | _ u v =>
    change (graph a b).Adj u v at hf
    change (tagList P (tag u) (tag v)).card = k
    rcases u with (x | ⟨e, i⟩) | (y | ⟨e, i⟩) <;>
      rcases v with (x' | ⟨f, j⟩) | (y' | ⟨f, j⟩) <;>
      simp_all [graph, cross, tagList, tag]

theorem edge_eq_of_color_eq {V : Type*} {H : SimpleGraph V}
    (col : H.lineGraph.Coloring Color) {f g : H.edgeSet} {v : V}
    (hf : v ∈ f.val) (hg : v ∈ g.val) (hc : col f = col g) : f = g := by
  by_contra hne
  exact col.valid (SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hne, v, hf, hg⟩) hc

theorem rowColor_injective (a : E → A) (b : E → B)
    (col : (graph (k := k) a b).lineGraph.Coloring Color) (e : E) (i : Fin k) :
    Function.Injective (fun j => col (rowEdge a b e i j)) := by
  intro j j' h
  exact rowEdge_injective a b e i (edge_eq_of_color_eq col
    (rowEdge_mem a b e i j) (rowEdge_mem a b e i j') h)

theorem columnColor_injective (a : E → A) (b : E → B)
    (col : (graph (k := k) a b).lineGraph.Coloring Color) (e : E) (j : Fin k) (hj : j ≠ 0) :
    Function.Injective (fun i => col (rowEdge a b e i j)) := by
  intro i i' h
  exact columnEdge_injective a b e j hj (edge_eq_of_color_eq col
    (columnEdge_mem a b e i j hj) (columnEdge_mem a b e i' j hj) h)

/-- A k-element palette forces the two terminal edges to have equal colors. -/
theorem terminal_agreement (a : E → A) (b : E → B) (P : E → Finset Color)
    (col : (graph (k := k) a b).lineGraph.Coloring Color)
    (hcol : ∀ f, col f ∈ lists a b P f) (e : E) (hP : (P e).card = k) :
    col (aEdge a b e) = col (bEdge a b e) := by
  classical
  have hm (i j : Fin k) : col (rowEdge a b e i j) ∈ P e := by
    simpa using hcol (rowEdge a b e i j)
  have hrow (i : Fin k) : ∃ j, col (rowEdge a b e i j) = col (aEdge a b e) := by
    let f : Fin k → {c // c ∈ P e} := fun j => ⟨col (rowEdge a b e i j), hm i j⟩
    have hf : Function.Injective f := by
      intro j j' h
      exact rowColor_injective a b col e i (congrArg Subtype.val h)
    have hcard : Fintype.card (Fin k) = Fintype.card {c // c ∈ P e} := by simp [hP]
    have hsurj := (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcard)).mp hf
    have ha : col (aEdge a b e) ∈ P e := by simpa using hcol (aEdge a b e)
    obtain ⟨j, hj⟩ := hsurj ⟨col (aEdge a b e), ha⟩
    exact ⟨j, congrArg Subtype.val hj⟩
  choose g hg using hrow
  by_contra hne
  have hg0 (i : Fin k) : g i ≠ 0 := by
    intro hzero
    have h := hg i
    rw [hzero] at h
    by_cases hi : i = 0
    · subst i
      exact hne (by simpa [rowEdge] using h.symm)
    · have hbad : rowEdge a b e i 0 ≠ aEdge a b e := by
        intro heq
        have heq' := congrArg Subtype.val heq
        simp [rowEdge, hi, innerEdge, aEdge] at heq'
      apply hbad
      apply edge_eq_of_color_eq col (v := Sum.inr (Sum.inr (e, 0))) _ _ h
      · simp [rowEdge, hi, innerEdge]
      · simp [aEdge]
  have hginj : Function.Injective g := by
    intro i i' h
    apply columnColor_injective a b col e (g i) (hg0 i)
    calc col (rowEdge a b e i (g i)) = col (aEdge a b e) := hg i
      _ = col (rowEdge a b e i' (g i)) := by rw [h, hg i']
  obtain ⟨i, hi⟩ := Finite.surjective_of_injective hginj 0
  exact hg0 i hi

theorem aEdge_injective (a : E → A) (b : E → B) :
    Function.Injective (aEdge (k := k) a b) := by
  intro e f h
  have hval : a e = a f ∧ e = f := by
    simpa [aEdge] using congrArg Subtype.val h
  exact hval.2

/-- Terminal colors are proper at both original endpoints. -/
theorem terminal_proper (a : E → A) (b : E → B)
    (col : (graph (k := k) a b).lineGraph.Coloring Color)
    (heq : ∀ e, col (aEdge a b e) = col (bEdge a b e)) :
    ∀ e f, e ≠ f → a e = a f ∨ b e = b f → col (aEdge a b e) ≠ col (aEdge a b f) := by
  intro e f hne hends hcol
  rcases hends with ha | hb
  · have h := edge_eq_of_color_eq col (v := Sum.inl (Sum.inl (a e)))
      (by simp [aEdge]) (by simp [aEdge, ha]) hcol
    exact hne (aEdge_injective a b h)
  · rw [heq e, heq f] at hcol
    have h := edge_eq_of_color_eq col (v := Sum.inr (Sum.inl (b e)))
      (by simp [bEdge]) (by simp [bEdge, hb]) hcol
    have hval : e = f ∧ b e = b f := by
      simpa [bEdge] using congrArg Subtype.val h
    exact hne hval.1

end GalvinMultigraph.Gadget
