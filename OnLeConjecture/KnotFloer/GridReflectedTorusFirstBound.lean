/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusFirstSupport
public import OnLeConjecture.KnotFloer.GridReflectedTorusThreeCycleGrading
public import OnLeConjecture.KnotFloer.GridReflectedTorusAnchorAlexander
public import OnLeConjecture.KnotFloer.GridWeightedDeformation

/-!
# The first torus representative satisfies both filtration bounds

The explicit representative `x₀+U⁻¹D(H₁)` has degree zero, is homologous
to the corner cycle, and lies in coordinates `(1,A(x₀)-n)`. Its support
has been computed using the full rectangle differential. This proves the
first of the two representative bounds required for the numerical estimate.
Nonvanishing and geometric positive-torus identification are separate.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable (n : ℕ) (R : Type*) [CommRing R] [CharP R 2]

/-- Nonzero coefficients have Alexander grading at least `n+1` below the corner. -/
theorem alexander_le_of_firstTorusCycle_apply_ne_zero (hn : 0 < n)
    {y : GridState (consecutiveTorusGridSize n)} (hy : firstTorusCycle n R y ≠ 0) :
    (reflectedTorusGrid n).alexander y ≤
      (reflectedTorusGrid n).alexander (reflectedTorusAnchor n) - (n + 1 : ℚ) := by
  obtain ⟨a, b, c, hab, hbc, hyc⟩ :=
    exists_ordered_threeCycle_of_firstTorusCycle_ne_zero n R hn hy
  have hya : y ≠ reflectedTorusAnchor n := by
    intro h
    rw [h, firstTorusCycle_anchor_eq_zero n R hn] at hy
    exact hy rfl
  have hd : laurentDifferential (reflectedTorusGrid n) R (firstTorusTriangle n R) y ≠ 0 := by
    intro h
    apply hy
    rw [firstTorusCycle, Finsupp.add_apply, Finsupp.single_eq_of_ne hya,
      Finsupp.smul_apply, h, smul_zero, add_zero]
  have hcount : (firstTorusTriangleEdgeCount n a b c : LaurentPolynomial R) ≠ 0 := by
    intro h
    apply hd
    rcases hyc with hcy | hcy
    · rw [hcy, laurentDifferential_firstTorusTriangle_threeCycle n R a b c hab hbc, h]
    · rw [hcy, laurentDifferential_firstTorusTriangle_threeCycle_reverse n R a b c hab hbc, h]
  have hodd : Odd (firstTorusTriangleEdgeCount n a b c) := by
    rcases Nat.even_or_odd (firstTorusTriangleEdgeCount n a b c) with he | ho
    · obtain ⟨k, hk⟩ := he
      apply (hcount ?_).elim
      rw [hk, Nat.cast_add, CharTwo.add_self_eq_zero]
    · exact ho
  obtain ⟨hg₁, hg₂, hg₃⟩ :=
    cyclic_gaps_le_of_odd_firstTorusTriangleEdgeCount n a b c hab hbc hodd
  have hA := alexander_reflectedTorus_three_cycle_bounds n a b c hab hbc hg₁ hg₂ hg₃
  rcases hyc with rfl | rfl
  · exact hA.1
  · exact hA.2

/-- The representative's second filtration coordinate is at most `A(x₀)-n`. -/
theorem firstTorusCycle_second_coordinate_le (hn : 0 < n)
    {y : GridState (consecutiveTorusGridSize n)} {k : ℤ}
    (hk : k ∈ (firstTorusCycle n R y).coeff.support) :
    ((reflectedTorusGrid n).alexander y : ℝ) - k ≤
      ((reflectedTorusGrid n).alexander (reflectedTorusAnchor n) : ℝ) - n := by
  have hy : firstTorusCycle n R y ≠ 0 := by
    intro h
    simp only [h, AddMonoidAlgebra.coeff_zero, Finsupp.support_zero, Finset.notMem_empty] at hk
  have hA := alexander_le_of_firstTorusCycle_apply_ne_zero n R hn hy
  have hAr : ((reflectedTorusGrid n).alexander y : ℝ) ≤
      ((reflectedTorusGrid n).alexander (reflectedTorusAnchor n) : ℝ) - (n + 1 : ℝ) := by
    exact_mod_cast hA
  have hi := firstTorusCycle_first_coordinate_le_one n R hk
  linarith

/-- The fully computed representative lies in both specified filtration sublevels. -/
theorem firstTorusCycle_mem_bifiltration (hn : 0 < n) :
    firstTorusCycle n R ∈ laurentBifiltrationLevel (reflectedTorusGrid n) R 1
      (((reflectedTorusGrid n).alexander (reflectedTorusAnchor n) : ℝ) - n) := by
  intro y k hk
  exact ⟨firstTorusCycle_first_coordinate_le_one n R hk,
    firstTorusCycle_second_coordinate_le n R hn hk⟩

/-- The first representative has the exact first staircase vertex bounds. -/
theorem firstTorusCycle_mem_first_staircase_vertex (hn : 0 < n) :
    firstTorusCycle n R ∈ laurentBifiltrationLevel (reflectedTorusGrid n) R 1
      ((n : ℝ) * ((n : ℝ) - 1) / 2) := by
  have h := firstTorusCycle_mem_bifiltration n R hn
  have heq : ((reflectedTorusGrid n).alexander (reflectedTorusAnchor n) : ℝ) - n =
      (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    rw [alexander_reflectedTorusAnchor]
    push_cast
    ring
  simpa only [heq] using h

end OnLeConjecture.KnotFloer.GridFull
