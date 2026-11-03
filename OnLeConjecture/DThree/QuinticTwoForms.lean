/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.TwoForms
import Mathlib.Tactic

/-!
# The cubic and quintic constant Jacobian equation

The quintic alternative forces both lower cubic coefficients to be
nonzero. Their relation will make the rational Newton weight integral
and separate the three terminal tangent roots.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial

variable {K : Type*} [Field K] [CharZero K]

@[expose] noncomputable def quintic (c5 c4 c3 c2 c1 c0 : K) : K[X] :=
  C c5 * X ^ 5 + C c4 * X ^ 4 + C c3 * X ^ 3 + C c2 * X ^ 2 + C c1 * X + C c0

/-- The nonzero constant cubic-quintic differential equation forces both
lower cubic coefficients to be nonzero and fixes their ratio. -/
theorem classify_quintic_pair_of_ode
    (A B c5 c4 c3 c2 c1 c0 c : K) (hc : c ≠ 0)
    (hODE : 5 * (cubic A B).derivative * quintic c5 c4 c3 c2 c1 c0 -
      3 * cubic A B * (quintic c5 c4 c3 c2 c1 c0).derivative = C c) :
    c5 ≠ 0 ∧ A ≠ 0 ∧ B ≠ 0 ∧ A ^ 3 = 9 * B ^ 2 ∧
      quintic c5 c4 c3 c2 c1 c0 = C c5 *
        (X ^ 5 + C (5 * A / 3) * X ^ 3 + C (5 * B / 3) * X ^ 2 +
          C (5 * A ^ 2 / 9) * X + C (10 * A * B / 9)) := by
  have hExpansion :
      5 * (cubic A B).derivative * quintic c5 c4 c3 c2 c1 c0 -
        3 * cubic A B * (quintic c5 c4 c3 c2 c1 c0).derivative =
      (3 * C c4) * X ^ 6 + (6 * C c3 - 10 * C A * C c5) * X ^ 5 +
      (9 * C c2 - 7 * C A * C c4 - 15 * C B * C c5) * X ^ 4 +
      (12 * C c1 - 4 * C A * C c3 - 12 * C B * C c4) * X ^ 3 +
      (15 * C c0 - C A * C c2 - 9 * C B * C c3) * X ^ 2 +
      (2 * C A * C c1 - 6 * C B * C c2) * X +
      (5 * C A * C c0 - 3 * C B * C c1) := by
    simp only [cubic, quintic, derivative_add, derivative_mul, derivative_pow,
      derivative_X, derivative_C, zero_mul, add_zero, zero_add, mul_one]
    norm_num
    simp only [C_ofNat]
    ring
  rw [hExpansion] at hODE
  have h4 : c4 = 0 := by
    have h := congrArg (fun q : K[X] ↦ q.coeff 6) hODE
    simpa [coeff_mul_X_pow'] using h
  have h3 : c3 = 5 * A * c5 / 3 := by
    have h := congrArg (fun q : K[X] ↦ q.coeff 5) hODE
    simp [h4, coeff_mul_X_pow'] at h
    linear_combination h / 6
  have h2 : c2 = 5 * B * c5 / 3 := by
    have h := congrArg (fun q : K[X] ↦ q.coeff 4) hODE
    simp [h4, coeff_mul_X_pow'] at h
    linear_combination h / 9
  have h1 : c1 = 5 * A ^ 2 * c5 / 9 := by
    have h := congrArg (fun q : K[X] ↦ q.coeff 3) hODE
    simp [h4, h3, coeff_mul_X_pow'] at h
    linear_combination h / 12
  have h0 : c0 = 10 * A * B * c5 / 9 := by
    have h := congrArg (fun q : K[X] ↦ q.coeff 2) hODE
    simp [h4, h3, h2, coeff_mul_X_pow'] at h
    linear_combination h / 15
  have hc_formula : c = 35 * A ^ 2 * B * c5 / 9 := by
    have h := congrArg (fun q : K[X] ↦ q.coeff 0) hODE
    simp [h4, h1, h0] at h
    linear_combination -h
  have hc5 : c5 ≠ 0 := by
    intro hzero
    apply hc
    simp [hc_formula, hzero]
  have hA : A ≠ 0 := by
    intro hzero
    apply hc
    simp [hc_formula, hzero]
  have hB : B ≠ 0 := by
    intro hzero
    apply hc
    simp [hc_formula, hzero]
  have hrelation : A ^ 3 = 9 * B ^ 2 := by
    apply mul_right_cancel₀ hc5
    have h := congrArg (fun q : K[X] ↦ q.coeff 1) hODE
    simp [h2, h1, coeff_mul_X_pow'] at h
    linear_combination (9 / 10 : K) * h
  refine ⟨hc5, hA, hB, hrelation, ?_⟩
  rw [quintic, h4, h3, h2, h1, h0]
  simp only [map_zero, zero_mul, add_zero, div_eq_mul_inv, map_mul, map_pow]
  ring

omit [CharZero K] in
/-- Writing a polynomial of degree at most five in coefficient form. -/
theorem eq_quintic_of_natDegree_le_five (q : K[X]) (hq : q.natDegree ≤ 5) :
    q = quintic (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0) := by
  ext j
  by_cases hj : j < 6
  · interval_cases j <;> simp [quintic, coeff_mul_X_pow']
  · have hlarge : 5 < j := by omega
    rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    simp [quintic, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C,
      show j ≠ 0 by omega, show 1 ≠ j by omega,
      show j ≠ 2 by omega, show j ≠ 3 by omega, show j ≠ 4 by omega, show j ≠ 5 by omega]

/-- The same coefficient criterion without an explicit coefficient list. -/
theorem lower_coefficients_ne_zero_of_cubic_quintic_constant_ode
    (A B : K) (q : K[X]) (hq : q.natDegree ≤ 5) (c : K) (hc : c ≠ 0)
    (hODE : 5 * (cubic A B).derivative * q - 3 * cubic A B * q.derivative = C c) :
    A ≠ 0 ∧ B ≠ 0 ∧ A ^ 3 = 9 * B ^ 2 := by
  rw [eq_quintic_of_natDegree_le_five q hq] at hODE
  have h := classify_quintic_pair_of_ode A B _ _ _ _ _ _ c hc hODE
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩

end OnLeConjecture.DThree
