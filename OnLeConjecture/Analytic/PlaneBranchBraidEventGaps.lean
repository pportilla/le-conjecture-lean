/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchBraidEventIntervals

/-!
# Event-free intervals between successive braid replacements

A cut in the ordered event list treats the initial, intermediate and
final gap uniformly. The empty list has no additional boundary case.
-/

public section

open Set

namespace OnLeConjecture.Analytic

theorem mem_braid_event_iff_of_sorted_enumeration {N : ℕ}
    (event : Fin N → ℝ) (E : Finset ℝ)
    (hevent : List.ofFn event = E.sort (· ≤ ·)) (t : ℝ) :
    t ∈ E ↔ ∃ j, event j = t := by
  rw [← Finset.mem_sort (α := ℝ) (· ≤ ·), ← hevent, List.mem_ofFn]

/-- If every completed event is before `u` and every remaining event is
after `v`, the whole closed gap is event free. -/
theorem braid_event_gap_of_cut {N : ℕ}
    (event : Fin N → ℝ) (E : Finset ℝ)
    (hevent : List.ofFn event = E.sort (· ≤ ·)) (i : Fin (N + 1)) (u v : ℝ)
    (hprev : ∀ j, j.val < i.val → event j < u)
    (hnext : ∀ j, i.val ≤ j.val → v < event j) :
    ∀ t ∈ Icc u v, t ∉ E := by
  intro t ht htE
  obtain ⟨j, rfl⟩ := (mem_braid_event_iff_of_sorted_enumeration event E hevent t).mp htE
  rcases lt_or_ge j.val i.val with h | h
  · exact (not_lt_of_ge ht.1) (hprev j h)
  · exact (not_lt_of_ge ht.2) (hnext j h)

/-- Only the adjacent events need to be bounded to exclude every event
from a gap. The quantified bounds also cover the two endpoint gaps. -/
theorem braid_event_gap_of_adjacent_cut {N : ℕ}
    (event : Fin N → ℝ) (E : Finset ℝ)
    (hevent : List.ofFn event = E.sort (· ≤ ·)) (hmono : StrictMono event)
    (i : Fin (N + 1)) (u v : ℝ)
    (hprev : ∀ j : Fin N, j.val + 1 = i.val → event j < u)
    (hnext : ∀ j : Fin N, j.val = i.val → v < event j) :
    ∀ t ∈ Icc u v, t ∉ E := by
  apply braid_event_gap_of_cut event E hevent i u v
  · intro j hj
    let p : Fin N := ⟨i.val - 1, by have := i.isLt; have := j.isLt; omega⟩
    have hjp : j ≤ p := by change j.val ≤ i.val - 1; omega
    exact (hmono.monotone hjp).trans_lt (hprev p (by dsimp [p]; omega))
  · intro j hj
    let q : Fin N := ⟨i.val, by have := j.isLt; omega⟩
    have hqj : q ≤ j := hj
    exact (hnext q rfl).trans_le (hmono.monotone hqj)

end OnLeConjecture.Analytic
