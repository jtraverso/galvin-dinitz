/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import GalvinMultigraph.Gadget
public import GalvinLib.Galvin

/-!
# Galvin's theorem for finite bipartite multigraphs

Edges have independent identifiers in E and endpoint maps a : E → A and b : E → B.
The pair (a,b) need not be injective: parallel edges remain distinct and must
receive distinct colors. Degrees count identifiers, including multiplicity.
-/

@[expose] public section

namespace GalvinMultigraph

open Finset

variable {A B E Color : Type*}

/-- Distinct edges meeting at either endpoint must receive different colors. -/
def Proper (a : E → A) (b : E → B) (c : E → Color) : Prop :=
  ∀ e f, e ≠ f → a e = a f ∨ b e = b f → c e ≠ c f

/-- Maximum incidence degree, with each parallel edge counted separately. -/
noncomputable def maxDegree [Fintype A] [Fintype B] (a : E → A) (b : E → B) : ℕ :=
  max (univ.sup fun x => Nat.card {e // a e = x})
      (univ.sup fun y => Nat.card {e // b e = y})

theorem degreeA_le_maxDegree [Fintype A] [Fintype B] (a : E → A) (b : E → B) (x : A) :
    Nat.card {e // a e = x} ≤ maxDegree a b :=
  (Finset.le_sup (f := fun x => Nat.card {e // a e = x}) (mem_univ x)).trans
    (le_max_left _ _)

theorem degreeB_le_maxDegree [Fintype A] [Fintype B] (a : E → A) (b : E → B) (y : B) :
    Nat.card {e // b e = y} ≤ maxDegree a b :=
  (Finset.le_sup (f := fun y => Nat.card {e // b e = y}) (mem_univ y)).trans
    (le_max_right _ _)

/-- Galvin's list-edge-coloring theorem, allowing any common degree bound k. -/
theorem galvin_of_degree_bound [Finite A] [Finite B] [Finite E]
    (a : E → A) (b : E → B) (k : ℕ)
    (ha : ∀ x, Nat.card {e // a e = x} ≤ k)
    (hb : ∀ y, Nat.card {e // b e = y} ≤ k)
    (L : E → Finset Color) (hL : ∀ e, k ≤ (L e).card) :
    ∃ c : E → Color, (∀ e, c e ∈ L e) ∧ Proper a b c := by
  classical
  let _ := Fintype.ofFinite A
  let _ := Fintype.ofFinite B
  let _ := Fintype.ofFinite E
  cases isEmpty_or_nonempty E with
  | inl hE =>
    exact ⟨isEmptyElim, fun e => isEmptyElim e, fun e => isEmptyElim e⟩
  | inr hE =>
    have hk : k ≠ 0 := by
      intro hk
      obtain ⟨e⟩ := hE
      have h := ha (a e)
      have : Nonempty {f : E // a f = a e} := ⟨⟨e, rfl⟩⟩
      rw [hk, Nat.card_eq_fintype_card] at h
      have := Fintype.card_pos (α := {f : E // a f = a e})
      omega
    have : NeZero k := ⟨hk⟩
    choose P hsub hP using fun e => Finset.exists_subset_card_eq (hL e)
    let G := Gadget.graph (k := k) a b
    have hdeg : G.maxDegree ≤ k := Gadget.maxDegree_le a b ha hb
    obtain ⟨col, hcol⟩ := Galvin.galvin G ⟨Gadget.coloring a b⟩ (Gadget.lists a b P)
      (fun f => by rw [Gadget.lists_card a b P hP f]; exact hdeg)
    refine ⟨fun e => col (Gadget.aEdge a b e), ?_, ?_⟩
    · intro e
      apply hsub e
      simpa using hcol (Gadget.aEdge a b e)
    · exact Gadget.terminal_proper a b col
        (fun e => Gadget.terminal_agreement a b P col hcol e (hP e))

/-- Galvin (1995): every list assignment of size at least the maximum degree
admits a proper edge coloring of the finite bipartite multigraph. -/
theorem galvin [Fintype A] [Fintype B] [Finite E]
    (a : E → A) (b : E → B) (L : E → Finset Color)
    (hL : ∀ e, maxDegree a b ≤ (L e).card) :
    ∃ c : E → Color, (∀ e, c e ∈ L e) ∧ Proper a b c :=
  galvin_of_degree_bound a b (maxDegree a b)
    (degreeA_le_maxDegree a b) (degreeB_le_maxDegree a b) L hL

/-- Kőnig's edge-coloring theorem for bipartite multigraphs. -/
theorem konig [Fintype A] [Fintype B] [Finite E] (a : E → A) (b : E → B) :
    ∃ c : E → Fin (maxDegree a b), Proper a b c := by
  obtain ⟨c, _, hc⟩ := galvin a b (fun _ => (univ : Finset (Fin (maxDegree a b))))
    (by intro e; simp)
  exact ⟨c, hc⟩

/-- Every proper finite-palette edge coloring has at least as many colors as
each incidence degree. -/
theorem degree_bounds_of_proper [Finite E] [Fintype Color]
    (a : E → A) (b : E → B) (c : E → Color) (hc : Proper a b c) :
    (∀ x, Nat.card {e // a e = x} ≤ Fintype.card Color) ∧
    (∀ y, Nat.card {e // b e = y} ≤ Fintype.card Color) := by
  classical
  let _ := Fintype.ofFinite E
  constructor
  · intro x
    rw [Nat.card_eq_fintype_card]
    apply Fintype.card_le_of_injective (fun e : {e // a e = x} => c e.val)
    intro e f h
    apply Subtype.ext
    by_contra hne
    exact hc e.val f.val hne (Or.inl (e.property.trans f.property.symm)) h
  · intro y
    rw [Nat.card_eq_fintype_card]
    apply Fintype.card_le_of_injective (fun e : {e // b e = y} => c e.val)
    intro e f h
    apply Subtype.ext
    by_contra hne
    exact hc e.val f.val hne (Or.inr (e.property.trans f.property.symm)) h

/-- The palette size is bounded below by the actual multigraph maximum degree. -/
theorem maxDegree_le_of_proper [Fintype A] [Fintype B] [Finite E] [Fintype Color]
    (a : E → A) (b : E → B) (c : E → Color) (hc : Proper a b c) :
    maxDegree a b ≤ Fintype.card Color := by
  have h := degree_bounds_of_proper a b c hc
  exact max_le (Finset.sup_le fun x _ => h.1 x) (Finset.sup_le fun y _ => h.2 y)

/-- Exact ordinary chromatic-index threshold, including empty edge sets. -/
theorem colorable_iff [Fintype A] [Fintype B] [Finite E]
    (a : E → A) (b : E → B) (k : ℕ) :
    (∃ c : E → Fin k, Proper a b c) ↔ maxDegree a b ≤ k := by
  constructor
  · rintro ⟨c, hc⟩
    simpa using maxDegree_le_of_proper a b c hc
  · intro hk
    obtain ⟨c, _, hc⟩ := galvin a b (fun _ => (univ : Finset (Fin k))) (by intro e; simpa using hk)
    exact ⟨c, hc⟩

end GalvinMultigraph
