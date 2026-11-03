/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# The estimates at the first breakpoint

This file formalizes the arithmetic deduction in `thm:estimates` of the
article *On Lê's conjecture*.
-/

public section

namespace OnLeConjecture.Numerical

/-- The arithmetic step in `thm:estimates` of the paper.

The real number `Φ` abstracts the value of the normalized Upsilon expression at the
breakpoint `2 / m`. The three inequalities are precisely the two torus knot lower bounds
and the cobordism upper bound used in the paper. -/
theorem estimates_of_breakpoint_bounds
    (M S m : ℕ) (Φ : ℝ) (hm : 0 < m)
    (h_lower_one : 2 * (M : ℝ) / (m : ℝ) - 2 ≤ Φ)
    (h_lower_two : 4 * (M : ℝ) / (m : ℝ) - 6 ≤ Φ)
    (h_upper : Φ ≤ 2 * ((M : ℝ) - (S : ℝ)) / (m : ℝ)) :
    S ≤ m ∧ M + S ≤ 3 * m := by
  have hm_real : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast hm
  have h_one :
      2 * (M : ℝ) / (m : ℝ) - 2 ≤
        2 * ((M : ℝ) - (S : ℝ)) / (m : ℝ) :=
    h_lower_one.trans h_upper
  have h_two :
      4 * (M : ℝ) / (m : ℝ) - 6 ≤
        2 * ((M : ℝ) - (S : ℝ)) / (m : ℝ) :=
    h_lower_two.trans h_upper
  have hS_real : (S : ℝ) ≤ (m : ℝ) := by
    have h := mul_le_mul_of_nonneg_right h_one hm_real.le
    field_simp [ne_of_gt hm_real] at h
    linarith
  have hMS_real : (M : ℝ) + (S : ℝ) ≤ 3 * (m : ℝ) := by
    have h := mul_le_mul_of_nonneg_right h_two hm_real.le
    field_simp [ne_of_gt hm_real] at h
    linarith
  constructor
  · exact_mod_cast hS_real
  · exact_mod_cast hMS_real

end OnLeConjecture.Numerical
