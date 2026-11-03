/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusFirstClass

/-!
# The second weighted bound in the range covered by the first representative

The second numerical estimate only uses the parameter `t = 2/m`. At this
parameter, the second staircase level is at least the first whenever
`n+1 ≤ 2*m`. The explicitly constructed first representative therefore
already supplies the second hypothesis in this range. A new representative
is needed only when `2*m < n+1`.

This is a weighted-filtration result. It does not assert the second
bifiltration-coordinate bound for the first cycle.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer

namespace Staircase

/-- The exact difference of the two levels used by the final numerical argument. -/
theorem consecutiveWeight_two_sub_one (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
    consecutiveWeight n t ⟨2, by omega⟩ - consecutiveWeight n t ⟨1, by omega⟩ =
      2 - t * ((n : ℝ) + 1) / 2 := by
  simp only [consecutiveWeight, consecutiveFirst, consecutiveSecond,
    Nat.cast_ofNat, Nat.cast_one]
  ring

/-- The precise parameter range in which the first weighted level is sufficient. -/
theorem consecutiveWeight_one_le_two_iff (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
    consecutiveWeight n t ⟨1, by omega⟩ ≤ consecutiveWeight n t ⟨2, by omega⟩ ↔
      t * ((n : ℝ) + 1) ≤ 4 := by
  have h := consecutiveWeight_two_sub_one n hn t
  constructor <;> intro ht <;> linarith

end Staircase

namespace GridFull

open TauCeti Staircase

variable (n : ℕ) (R : Type*) [CommRing R] [CharP R 2]

/-- The first native cycle also represents the corner class at the second
weighted level throughout the stated parameter range. -/
theorem reflectedTorusAnchorClass_representedBelow_second_vertex_of_parameter
    (hn : 2 ≤ n) (t : ℝ) (ht : t * ((n : ℝ) + 1) ≤ 4) :
    ((laurentMaslovBifiltration (reflectedTorusGrid n) R).weighted t).RepresentedBelow 0
      (reflectedTorusAnchorClass n R)
      (consecutiveWeight n t ⟨2, by omega⟩) :=
  (reflectedTorusAnchorClass_representedBelow_first_vertex n R (by omega) t).mono
    ((consecutiveWeight_one_le_two_iff n hn t).mpr ht)

/-- At the only parameter required by the comparison, no new cycle is needed
when the staircase size is at most twice the denominator. -/
theorem reflectedTorusAnchorClass_representedBelow_second_vertex_of_le
    (m : ℕ) (hn : 2 ≤ n) (hm : 0 < m) (hS : n + 1 ≤ 2 * m) :
    ((laurentMaslovBifiltration (reflectedTorusGrid n) R).weighted
      (2 / (m : ℝ))).RepresentedBelow 0 (reflectedTorusAnchorClass n R)
      (consecutiveWeight n (2 / (m : ℝ)) ⟨2, by omega⟩) := by
  apply reflectedTorusAnchorClass_representedBelow_second_vertex_of_parameter n R hn
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hSR : (n : ℝ) + 1 ≤ 2 * (m : ℝ) := by exact_mod_cast hS
  rw [div_mul_eq_mul_div, div_le_iff₀ hmR]
  nlinarith

end GridFull

end OnLeConjecture.KnotFloer
