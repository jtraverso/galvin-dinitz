/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import GalvinMultigraph.Main
public import GalvinMultigraph.Local.Main

/-!
# The Borodin–Kostochka–Woodall theorem in the form of `GalvinMultigraph`

`galvin_bkw_local` colours from lists of natural numbers, with degrees counted by filtering. Here
the colours of the lists are numbered (all of them lie in the finite set `⋃ₑ L e`), the lists are
transported to `ℕ`, and the colouring is decoded back.
-/

@[expose] public section

namespace GalvinMultigraph

open Finset

variable {A B E Color : Type*}

/-- **Borodin–Kostochka–Woodall (1997).** In a finite bipartite multigraph, lists whose size at
each edge is at least the larger degree of its two ends admit a proper list edge colouring. -/
theorem galvin_local [Finite A] [Finite B] [Finite E]
    (a : E → A) (b : E → B) (L : E → Finset Color)
    (hL : ∀ e, max (Nat.card {f // a f = a e}) (Nat.card {f // b f = b e}) ≤ (L e).card) :
    ∃ c : E → Color, (∀ e, c e ∈ L e) ∧ Proper a b c := by
  classical
  let _ := Fintype.ofFinite A
  let _ := Fintype.ofFinite B
  let _ := Fintype.ofFinite E
  -- number the colours occurring in the lists
  set S : Finset Color := univ.biUnion L with hS
  let num : S ≃ Fin S.card := S.equivFin
  let enc : Color → ℕ := fun x => if h : x ∈ S then (num ⟨x, h⟩ : ℕ) else 0
  have hLS : ∀ e, L e ⊆ S := fun e x hx => mem_biUnion.2 ⟨e, mem_univ e, hx⟩
  have henc : ∀ x ∈ S, ∀ y ∈ S, enc x = enc y → x = y := by
    intro x hx y hy h
    simp only [enc, dif_pos hx, dif_pos hy] at h
    exact congrArg Subtype.val (num.injective (Fin.ext h))
  let L' : E → Finset ℕ := fun e => (L e).image enc
  have hcard : ∀ e, (L' e).card = (L e).card := fun e =>
    card_image_of_injOn fun x hx y hy h => henc x (hLS e hx) y (hLS e hy) h
  have hdA : ∀ x, Local.degL a x = Nat.card {f // a f = x} := fun x => by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  have hdB : ∀ y, Local.degR b y = Nat.card {f // b f = y} := fun y => by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  obtain ⟨φ, hφL, hφ⟩ := Local.galvin_bkw_local a b L' fun e => by
    rw [hcard, hdA, hdB]
    exact hL e
  have hdec : ∀ e, ∃ x ∈ L e, enc x = φ e := fun e => mem_image.1 (hφL e)
  choose c hcL hce using hdec
  refine ⟨c, hcL, fun e f hef hab hc => hφ e f hef hab ?_⟩
  rw [← hce e, ← hce f, hc]

end GalvinMultigraph
