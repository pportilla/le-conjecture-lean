/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Order

/-!
# Pole order arithmetic in Lemma `dthree-Horders`

This file formalizes the numerical combination of the local pole estimates for
the derivative

`(-3 [Lambda_Q] + 4 (1 + w) [Lambda_P]) / 12`.

The inputs correspond to the pole bounds for `[Lambda_Q]` and `[Lambda_P]`.
The conclusions are the finite pole bound, the bound at either point at
infinity, the degree of the pole divisor, and the final strict inequality.
-/

public section

namespace OnLeConjecture.DThree

/-- The bound for the degree of the pole divisor of `d[R]/dw`. -/
def hDerivativePoleDegreeBound (N : ℕ) : ℕ :=
  2 * (N - 2) + (N - 2) / 2

/-- The bound for `k_1 + k_2` in Lemma `dthree-Horders`. -/
@[expose]
def hBranchOrderSumBound (N : ℕ) : ℕ :=
  2 * N - 2 + (N - 2) / 2

/-- At `(-1,2)`, the pole order of the derivative numerator is at most
`floor((N - 2)/2)` once the two summands have their expected bounds. -/
theorem h_finite_derivative_pole_order_le
    (N qPole pPole : ℕ) (hN : 4 ≤ N)
    (hq : qPole ≤ (N - 3) / 2)
    (hp : pPole ≤ (N - 4) / 2) :
    max qPole (pPole + 1) ≤ (N - 2) / 2 := by
  omega

/-- At either point at infinity, the pole order of the derivative numerator
is at most `N - 2` once the two summands have their expected bounds. -/
theorem h_infinity_derivative_pole_order_le
    (N qPole pPole : ℕ) (hN : 4 ≤ N)
    (hq : qPole ≤ N - 3) (hp : pPole ≤ N - 4) :
    max qPole (pPole + 2) ≤ N - 2 := by
  omega

/-- Adding the finite pole and the two infinity poles gives the pole divisor
bound in Lemma `dthree-Horders`. -/
theorem h_derivative_pole_degree_le
    (N finitePole infinityPoleOne infinityPoleTwo : ℕ)
    (hfinite : finitePole ≤ (N - 2) / 2)
    (hinfinityOne : infinityPoleOne ≤ N - 2)
    (hinfinityTwo : infinityPoleTwo ≤ N - 2) :
    finitePole + infinityPoleOne + infinityPoleTwo ≤
      hDerivativePoleDegreeBound N := by
  simp only [hDerivativePoleDegreeBound]
  omega

/-- For `N ≥ 2`, adding the two units lost by differentiation converts the
pole divisor bound into the branch order bound. -/
theorem h_derivative_bound_add_two
    (N : ℕ) (hN : 2 ≤ N) :
    hDerivativePoleDegreeBound N + 2 = hBranchOrderSumBound N := by
  simp only [hDerivativePoleDegreeBound, hBranchOrderSumBound]
  omega

/-- If the two zeros of the derivative have orders `k_1 - 1` and `k_2 - 1`,
the pole divisor bound gives the claimed estimate for `k_1 + k_2`. -/
theorem h_branch_order_sum_le
    (N kOne kTwo : ℕ) (hN : 2 ≤ N)
    (hkOne : 1 ≤ kOne) (hkTwo : 1 ≤ kTwo)
    (hzeroPole :
      (kOne - 1) + (kTwo - 1) ≤ hDerivativePoleDegreeBound N) :
    kOne + kTwo ≤ hBranchOrderSumBound N := by
  rw [← h_derivative_bound_add_two N hN]
  omega

/-- Twice the branch order bound is strictly less than `5N` for `N ≥ 5`. -/
theorem two_mul_h_branch_order_sum_bound_lt
    (N : ℕ) (hN : 5 ≤ N) :
    2 * hBranchOrderSumBound N < 5 * N := by
  simp only [hBranchOrderSumBound]
  omega

/-- The final strict inequality in Lemma `dthree-Horders`. -/
theorem h_branch_order_sum_bound_lt_five_halves
    (N : ℕ) (hN : 5 ≤ N) :
    (hBranchOrderSumBound N : ℚ) < 5 * (N : ℚ) / 2 := by
  have hnat := two_mul_h_branch_order_sum_bound_lt N hN
  have hrat :
      (2 * hBranchOrderSumBound N : ℚ) < (5 * N : ℕ) := by
    exact_mod_cast hnat
  norm_num at hrat ⊢
  linarith

end OnLeConjecture.DThree
