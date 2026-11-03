/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HConicLocalData

/-!
# Explicit local order factorizations for the `H` conic

This file records the local parameter and unit factorizations used in Lemma
`dthree-Horders`.  Each asserted order is represented by an identity on a
punctured chart together with a proof that the remaining factor has a nonzero
specialization at the point.

At the points above `X = 1`, the parameter is `X - 1`.  At the point
`(-1,2)`, the parameter is `X + 1`.  At infinity, the parameter is `u = 1/X`.
The point `(-1,-2)` is represented by the regular formulas from
`HConicLocalData`.
-/

public section

namespace OnLeConjecture.DThree

variable {K : Type*} [Field K] [CharZero K]

/-! ## Order one zeros above `X = 1` -/

/-- The partial derivative of the conic equation with respect to `theta` is
nonzero at each point over `X = 1`. -/
theorem h_conic_theta_derivative_at_one_ne_zero
    {theta : K} (htheta : theta ^ 2 = -12) :
    (2 : K) * theta ≠ 0 := by
  apply mul_ne_zero (by norm_num)
  intro hzero
  rw [hzero] at htheta
  norm_num at htheta

/-- At either point over `X = 1`, `w` is `(X - 1)` times a factor whose value
at the point is nonzero. -/
theorem h_conic_w_order_one_factorization
    {theta0 : K} (htheta0 : theta0 ^ 2 = -12) :
    (∀ X theta : K,
      hConicW X theta = (X - 1) * hConicWSlope X theta) ∧
      hConicWSlope 1 theta0 ≠ 0 := by
  constructor
  · intro X theta
    exact (h_conic_functions_factor_at_one X theta).1
  · exact h_conic_w_slope_at_one_ne_zero htheta0

/-- At either point over `X = 1`, `W` is `(X - 1)` times a factor whose value
at the point is nonzero. -/
theorem h_conic_capitalW_order_one_factorization
    {theta0 : K} (htheta0 : theta0 ^ 2 = -12) :
    (∀ X theta : K,
      hConicCapitalW X theta =
        (X - 1) * hConicCapitalWSlope X theta) ∧
      hConicCapitalWSlope 1 theta0 ≠ 0 := by
  constructor
  · intro X theta
    exact (h_conic_functions_factor_at_one X theta).2
  · exact h_conic_capitalW_slope_at_one_ne_zero htheta0

/-! ## Simple poles at `(-1,2)` -/

/-- The factor remaining after multiplication of `w` by `X + 1`. -/
@[expose]
noncomputable def hPlusWPoleUnit (X theta : K) : K :=
  hConicWNumerator X theta / 6

/-- The factor remaining after multiplication of `W` by `X + 1`. -/
@[expose]
noncomputable def hPlusCapitalWPoleUnit (X theta : K) : K :=
  hConicCapitalWNumerator X theta / 6

/-- Away from `X = -1`, multiplication by `X + 1` removes the displayed pole
of `w`. -/
theorem h_conic_w_simple_pole_factorization
    {X theta : K} (hX : X + 1 ≠ 0) :
    (X + 1) * hConicW X theta = hPlusWPoleUnit X theta := by
  simp only [hConicW, hConicWNumerator, hPlusWPoleUnit]
  field_simp [hX]

/-- Away from `X = -1`, multiplication by `X + 1` removes the displayed pole
of `W`. -/
theorem h_conic_capitalW_simple_pole_factorization
    {X theta : K} (hX : X + 1 ≠ 0) :
    (X + 1) * hConicCapitalW X theta =
      hPlusCapitalWPoleUnit X theta := by
  simp only [hConicCapitalW, hConicCapitalWNumerator,
    hPlusCapitalWPoleUnit]
  field_simp [hX]

/-- The pole unit for `w` specializes to `4/3` at `(-1,2)`. -/
theorem h_plus_w_pole_unit_at_point :
    hPlusWPoleUnit (-1 : K) 2 = 4 / 3 ∧
      hPlusWPoleUnit (-1 : K) 2 ≠ 0 := by
  simp only [hPlusWPoleUnit, hConicWNumerator]
  constructor <;> norm_num

/-- The pole unit for `W` specializes to `-4/3` at `(-1,2)`. -/
theorem h_plus_capitalW_pole_unit_at_point :
    hPlusCapitalWPoleUnit (-1 : K) 2 = -4 / 3 ∧
      hPlusCapitalWPoleUnit (-1 : K) 2 ≠ 0 := by
  simp only [hPlusCapitalWPoleUnit, hConicCapitalWNumerator]
  constructor <;> norm_num

/-! ## Regular units at `(-1,-2)` -/

/-- The regular expression for `w` at `(-1,-2)` has nonzero value. -/
theorem h_minus_w_regular_unit_at_point :
    hConicWRegularAtMinusBranch (-1 : K) (-2) = -1 / 3 ∧
      hConicWRegularAtMinusBranch (-1 : K) (-2) ≠ 0 := by
  constructor
  · exact h_conic_w_regular_value_at_minus_branch
  · rw [h_conic_w_regular_value_at_minus_branch]
    norm_num

/-- The regular expression for `W` at `(-1,-2)` has nonzero value. -/
theorem h_minus_capitalW_regular_unit_at_point :
    hConicCapitalWRegularAtMinusBranch (-1 : K) (-2) = -1 / 3 ∧
      hConicCapitalWRegularAtMinusBranch (-1 : K) (-2) ≠ 0 := by
  constructor
  · exact h_conic_capitalW_regular_value_at_minus_branch
  · rw [h_conic_capitalW_regular_value_at_minus_branch]
    norm_num

/-- The partial derivative of the conic equation with respect to `theta` is
nonzero at `(-1,-2)`. -/
theorem h_conic_theta_derivative_at_regular_branch :
    (2 : K) * (-2) = -4 ∧ (-4 : K) ≠ 0 := by
  constructor <;> norm_num

/-! ## Double poles at infinity -/

/-- In the infinity chart, the coordinate `X = 1/u` has a simple pole with
unit factor `1`. -/
theorem h_infinity_x_simple_pole_factorization
    {u : K} (hu : u ≠ 0) :
    u * (1 / u) = 1 ∧ (1 : K) ≠ 0 := by
  constructor
  · field_simp
  · exact one_ne_zero

/-- The factor remaining after multiplication of `w` by `u^2`. -/
@[expose]
noncomputable def hInfinityWPoleUnit (u eta : K) : K :=
  hInfinityWNumerator u eta / hInfinityDenominatorUnit u

/-- The factor remaining after multiplication of `W` by `u^2`. -/
@[expose]
noncomputable def hInfinityCapitalWPoleUnit (u eta : K) : K :=
  hInfinityCapitalWNumerator u eta / hInfinityDenominatorUnit u

/-- Away from `u = 0` and `u = -1`, multiplication by `u^2` removes the
displayed pole of `w`. -/
theorem h_infinity_w_double_pole_factorization
    {u eta : K} (hu : u ≠ 0) (hplus : 1 + u ≠ 0) :
    u ^ 2 * hInfinityW u eta = hInfinityWPoleUnit u eta := by
  simp only [hInfinityW, hInfinityWPoleUnit, hInfinityDenominatorUnit]
  field_simp [hu, hplus]

/-- Away from `u = 0` and `u = -1`, multiplication by `u^2` removes the
displayed pole of `W`. -/
theorem h_infinity_capitalW_double_pole_factorization
    {u eta : K} (hu : u ≠ 0) (hplus : 1 + u ≠ 0) :
    u ^ 2 * hInfinityCapitalW u eta =
      hInfinityCapitalWPoleUnit u eta := by
  simp only [hInfinityCapitalW, hInfinityCapitalWPoleUnit,
    hInfinityDenominatorUnit]
  field_simp [hu, hplus]

/-- At either point at infinity, the pole unit for `w` specializes to
`eta/6` and is nonzero. -/
theorem h_infinity_w_pole_unit_at_point
    {eta : K} (heta : eta ^ 2 = -2) :
    hInfinityWPoleUnit 0 eta = eta / 6 ∧
      hInfinityWPoleUnit 0 eta ≠ 0 := by
  have heta0 := h_infinity_eta_ne_zero heta
  simp only [hInfinityWPoleUnit, hInfinityWNumerator,
    hInfinityDenominatorUnit]
  constructor
  · norm_num
  · norm_num
    exact heta0

/-- At either point at infinity, the pole unit for `W` specializes to
`-1/3` and is nonzero. -/
theorem h_infinity_capitalW_pole_unit_at_point (eta : K) :
    hInfinityCapitalWPoleUnit 0 eta = -1 / 3 ∧
      hInfinityCapitalWPoleUnit 0 eta ≠ 0 := by
  simp only [hInfinityCapitalWPoleUnit, hInfinityCapitalWNumerator,
    hInfinityDenominatorUnit]
  constructor <;> norm_num

end OnLeConjecture.DThree
