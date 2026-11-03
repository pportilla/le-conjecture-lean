/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CanonicalCriticalReduction
public import OnLeConjecture.Analytic.CriticalSupportNonempty
public import OnLeConjecture.KnotFloer.ConsecutiveStaircase

/-!
# Reduction to one staircase comparison at the critical breakpoint

The final numerical estimates follow from the upper comparison for the
explicit consecutive staircase. Zero differential proves that the square
sum is at least four. Nonempty critical support proves that the denominator
is at least two, so its breakpoint belongs to the required rational unit
interval. Only one weak-transform tree with the comparison is needed.

This module gives an alternative endpoint. Its upper comparison is not proved in this
repository, and the final theorem `leConjecture_native` does not use it: it goes through
`leConjecture_of_criticalJacobian_floer_data`. The final proof uses only the auxiliary bounds of
this module.
-/

public noncomputable section

open scoped BigOperators

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ KnotFloer.Staircase

namespace RawProjectiveWeakBlowupTree

/-- Zero differential forces root multiplicity at least two in every
tree of the actual coordinate ideal. -/
theorem two_le_root_multiplicity_of_differential_eq_zero
    {g : PointedMapGerm 2 3} (T : RawProjectiveWeakBlowupTree g.1.component)
    (hd : g.differential = 0) : 2 ≤ T.multiplicity T.root := by
  have hp := T.multiplicity_pos T.root
  by_contra h
  have he : T.multiplicity T.root = 1 := by omega
  obtain ⟨i, hi⟩ := T.generator_exact T.root
  rw [T.generators_root, he] at hi
  exact hi ((g.differential_eq_zero_iff_coordinateIdeal_le_sq.mp hd)
    (g.1.component_mem_coordinateIdeal i))

/-- The staircase index is never one of the exceptional sizes zero or one. -/
theorem four_le_square_sum_of_differential_eq_zero
    {g : PointedMapGerm 2 3} (T : RawProjectiveWeakBlowupTree g.1.component)
    (hd : g.differential = 0) : 4 ≤ ∑ p, (T.multiplicity p) ^ 2 := by
  have hr := T.two_le_root_multiplicity_of_differential_eq_zero hd
  have hs : (T.multiplicity T.root) ^ 2 ≤ ∑ p, (T.multiplicity p) ^ 2 :=
    Finset.single_le_sum (f := fun p => (T.multiplicity p) ^ 2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ T.root)
  nlinarith

end RawProjectiveWeakBlowupTree

/-- The common-Jacobian breakpoint is a rational point of the unit interval. -/
theorem criticalJacobian_breakpoint_rational_unitInterval
    (g : PointedMapGerm 2 3) (hi : g.HasInjectiveRepresentative)
    (hd : g.differential = 0) :
    ∃ q : ℚ, q ∈ Set.Icc 0 1 ∧
      (q : ℝ) = 2 / ((g.criticalJacobianFactorization hi).maxMultiplicity : ℝ) := by
  have hm := (g.criticalJacobianFactorization hi).two_le_maxMultiplicity_of_differential_eq_zero
    hi hd
  have hmr : (2 : ℚ) ≤ ((g.criticalJacobianFactorization hi).maxMultiplicity : ℚ) := by
    exact_mod_cast hm
  refine ⟨2 / ((g.criticalJacobianFactorization hi).maxMultiplicity : ℚ),
    ⟨div_nonneg (by norm_num) (by linarith), (div_le_one (by linarith)).mpr hmr⟩, ?_⟩
  push_cast
  rfl

/-- The sole numerical comparison still required for a specified tree. -/
@[expose] def CriticalJacobianStaircaseComparison
    (g : PointedMapGerm 2 3) (hi : g.HasInjectiveRepresentative)
    (T : RawProjectiveWeakBlowupTree g.1.component) : Prop :=
  consecutiveShiftedValue ((∑ p, (T.multiplicity p) ^ 2) - 1)
      (2 / ((g.criticalJacobianFactorization hi).maxMultiplicity : ℝ)) ≤
    2 * (((∑ p, (T.multiplicity p) ^ 2 : ℕ) : ℝ) -
      ((∑ p, T.multiplicity p : ℕ) : ℝ)) /
        ((g.criticalJacobianFactorization hi).maxMultiplicity : ℝ)

/-- The single comparison discharges both inequalities in the canonical
critical-divisor reduction, with its size and positivity conditions proved. -/
theorem criticalJacobian_bounds_of_staircase_comparison
    (g : PointedMapGerm 2 3) (hd : g.differential = 0)
    (hi : g.HasInjectiveRepresentative) (T : RawProjectiveWeakBlowupTree g.1.component)
    (hupper : CriticalJacobianStaircaseComparison g hi T) :
    (∑ p, T.multiplicity p) ≤ (g.criticalJacobianFactorization hi).maxMultiplicity ∧
      (∑ p, (T.multiplicity p) ^ 2) + (∑ p, T.multiplicity p) ≤
        3 * (g.criticalJacobianFactorization hi).maxMultiplicity := by
  have hS := T.four_le_square_sum_of_differential_eq_zero hd
  have hm := (g.criticalJacobianFactorization hi).two_le_maxMultiplicity_of_differential_eq_zero
    hi hd
  have hpred : (∑ p, (T.multiplicity p) ^ 2) - 1 + 1 = ∑ p, (T.multiplicity p) ^ 2 :=
    Nat.sub_add_cancel (by omega)
  have h := estimates_of_consecutive_staircase_comparison
    ((∑ p, (T.multiplicity p) ^ 2) - 1) (∑ p, T.multiplicity p)
    (g.criticalJacobianFactorization hi).maxMultiplicity (by omega) (by omega) ?_
  · simpa only [hpred] using h
  · have hc : (((∑ p, (T.multiplicity p) ^ 2) - 1 : ℕ) : ℝ) + 1 =
        ((∑ p, (T.multiplicity p) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hpred
    simpa only [hc] using (show consecutiveShiftedValue
      ((∑ p, (T.multiplicity p) ^ 2) - 1)
      (2 / ((g.criticalJacobianFactorization hi).maxMultiplicity : ℝ)) ≤ _ from hupper)

end OnLeConjecture.Analytic

namespace OnLeConjecture

open Analytic Analytic.Germ

/-- Conditional reduction of the entire conjecture to one explicit upper
comparison for one tree per injective zero-differential germ. No exceptional
staircase case or zero denominator remains as an extra hypothesis. -/
theorem leConjecture_of_criticalJacobian_staircase_comparison
    (hcomparison : ∀ (g : PointedMapGerm 2 3), g.differential = 0 →
      ∀ hi : g.HasInjectiveRepresentative,
        ∃ T : RawProjectiveWeakBlowupTree g.1.component,
          CriticalJacobianStaircaseComparison g hi T) :
    LeConjecture := by
  apply leConjecture_of_general_resolution_reduction
  intro g hd hi
  obtain ⟨T, hupper⟩ := hcomparison g hd hi
  obtain ⟨hM, hglobal⟩ := criticalJacobian_bounds_of_staircase_comparison g hd hi T hupper
  obtain ⟨q₀, _, hq₀⟩ := T.exists_exact_coefficients Set.univ isOpen_univ Set.univ_nonempty
  obtain ⟨R⟩ := exists_constructedResolutionRemainingData_of_criticalJacobian_bounds
    g hd hi T q₀ hq₀ hM hglobal
  exact R.exists_generalResolutionReductionData

end OnLeConjecture
