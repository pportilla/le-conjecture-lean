/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HResidual

/-!
# Local algebra for the conic in the `H` case

This file verifies the local rational identities used in Lemma
`dthree-Horders`.  At the points over `(X,w) = (1,0)`, it isolates the
nonzero factor relating `w` and `X - 1`.  At the two points with `X = -1`, it
records the nonzero numerators on the pole branch and the cancellation on the
other branch.  In the chart at infinity it writes `w` and `W` with denominator
`u^2` times a factor that is nonzero at `u = 0`.

These are algebraic certificates for the local orders in the article.  The
translation from these identities to orders in the local rings of the conic
requires a general local parameter result and is not asserted here.
-/

public section

namespace OnLeConjecture.DThree

variable {K : Type*} [Field K] [CharZero K]

/-- The affine equation of the conic in Lemma `dthree-Horders`. -/
@[expose]
noncomputable def hConicEquation (X theta : K) : K :=
  theta ^ 2 + 2 * (X ^ 2 + 4 * X + 1)

/-- The numerator of `hConicW` before division by `6 (X + 1)`. -/
@[expose]
noncomputable def hConicWNumerator (X theta : K) : K :=
  (X - 1) * (2 * (2 * X + 1) + X * theta)

/-- The numerator of `hConicCapitalW` before division by `6 (X + 1)`. -/
@[expose]
noncomputable def hConicCapitalWNumerator (X theta : K) : K :=
  -((X - 1) * (2 * X ^ 2 + 4 * X - theta))

omit [CharZero K] in
/-- The conic equation is equivalent to the form used in `HResidual`. -/
theorem h_conic_equation_eq_zero_iff {X theta : K} :
    hConicEquation X theta = 0 ↔
      theta ^ 2 = -2 * (X ^ 2 + 4 * X + 1) := by
  simp only [hConicEquation]
  constructor <;> intro h
  · linear_combination h
  · linear_combination h

omit [CharZero K] in
/-- The two displayed rational functions have the stated numerators. -/
theorem h_conic_functions_eq_numerator_div (X theta : K) :
    hConicW X theta = hConicWNumerator X theta / (6 * (X + 1)) ∧
      hConicCapitalW X theta =
        hConicCapitalWNumerator X theta / (6 * (X + 1)) := by
  constructor <;> rfl

/-- The rational inverse obtained by solving the displayed formula for `w`
for the conic coordinate `theta`. -/
@[expose]
noncomputable def hConicThetaOfGamma (X w : K) : K :=
  (6 * (X + 1) * w / (X - 1) - 2 * (2 * X + 1)) / X

/-- Substitution of the rational inverse recovers `w` away from its displayed
denominators. -/
theorem h_conic_w_of_theta_of_gamma
    (X w : K) (hX : X ≠ 0) (hdiag : X ≠ 1) (hplus : X + 1 ≠ 0) :
    hConicW X (hConicThetaOfGamma X w) = w := by
  simp only [hConicW, hConicThetaOfGamma]
  field_simp [hX, sub_ne_zero.mpr hdiag, hplus]
  ring

/-- Substitution of the conic formula for `w` in the rational inverse
recovers `theta`. -/
theorem h_theta_of_gamma_of_conic_w
    (X theta : K) (hX : X ≠ 0) (hdiag : X ≠ 1)
    (hplus : X + 1 ≠ 0) :
    hConicThetaOfGamma X (hConicW X theta) = theta := by
  simp only [hConicThetaOfGamma, hConicW]
  field_simp [hX, sub_ne_zero.mpr hdiag, hplus]
  ring

omit [CharZero K] in
/-- After clearing denominators, the conic equation of the rational inverse
is `2 (X + 1) Gamma`. -/
theorem h_conic_equation_of_theta_of_gamma
    (X w : K) (hX : X ≠ 0) (hdiag : X ≠ 1) :
    X ^ 2 * (X - 1) ^ 2 *
        hConicEquation X (hConicThetaOfGamma X w) =
      2 * (X + 1) * hGamma X w := by
  simp only [hConicEquation, hConicThetaOfGamma, hGamma]
  field_simp [hX, sub_ne_zero.mpr hdiag]
  ring

/-- On the open chart `X ≠ 0, 1, -1`, the rational inverse carries
`Gamma = 0` precisely to the conic. -/
theorem h_gamma_eq_zero_iff_conic_theta_of_gamma
    (X w : K) (hX : X ≠ 0) (hdiag : X ≠ 1) (hplus : X + 1 ≠ 0) :
    hGamma X w = 0 ↔
      hConicEquation X (hConicThetaOfGamma X w) = 0 := by
  have hidentity := h_conic_equation_of_theta_of_gamma X w hX hdiag
  have hleft : X ^ 2 * (X - 1) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hX)
      (pow_ne_zero 2 (sub_ne_zero.mpr hdiag))
  have hright : (2 : K) * (X + 1) ≠ 0 :=
    mul_ne_zero (by norm_num) hplus
  constructor
  · intro hgamma
    rw [hgamma, mul_zero] at hidentity
    exact (mul_eq_zero.mp hidentity).resolve_left hleft
  · intro hconic
    rw [hconic, mul_zero] at hidentity
    exact (mul_eq_zero.mp hidentity.symm).resolve_left hright

/-- The conic formula for `W` becomes the collapsed first fibre equation
under the rational inverse. -/
theorem h_conic_capitalW_of_theta_of_gamma
    (X w : K) (hX : X ≠ 0) (hdiag : X ≠ 1) (hplus : X + 1 ≠ 0) :
    hConicCapitalW X (hConicThetaOfGamma X w) = hCollapsedW X w := by
  have hfirst :=
    h_conic_first_fibre_equation X (hConicThetaOfGamma X w) hplus
  rw [h_conic_w_of_theta_of_gamma X w hX hdiag hplus] at hfirst
  exact (h_first_fibre_equation_iff hX).mp hfirst

/-! ## The two points over `(X,w) = (1,0)` -/

/-- The factor relating `w` to `X - 1` on the conic. -/
@[expose]
noncomputable def hConicWSlope (X theta : K) : K :=
  (2 * (2 * X + 1) + X * theta) / (6 * (X + 1))

/-- The corresponding factor for `W`. -/
@[expose]
noncomputable def hConicCapitalWSlope (X theta : K) : K :=
  -(2 * X ^ 2 + 4 * X - theta) / (6 * (X + 1))

omit [CharZero K] in
/-- The functions `w` and `W` factor by `X - 1`. -/
theorem h_conic_functions_factor_at_one (X theta : K) :
    hConicW X theta = (X - 1) * hConicWSlope X theta ∧
      hConicCapitalW X theta =
        (X - 1) * hConicCapitalWSlope X theta := by
  simp only [hConicW, hConicCapitalW, hConicWSlope,
    hConicCapitalWSlope, div_eq_mul_inv]
  constructor <;> ring

/-- At `X = 1`, the factor relating `w` to `X - 1` is `(6 + theta) / 12`. -/
theorem h_conic_w_slope_at_one (theta : K) :
    hConicWSlope 1 theta = (6 + theta) / 12 := by
  simp only [hConicWSlope]
  field_simp
  ring

/-- At `X = 1`, the factor relating `W` to `X - 1` is `(theta - 6) / 12`. -/
theorem h_conic_capitalW_slope_at_one (theta : K) :
    hConicCapitalWSlope 1 theta = (theta - 6) / 12 := by
  simp only [hConicCapitalWSlope]
  field_simp
  ring

/-- The factor relating `w` to `X - 1` is nonzero at either point of the
conic over `X = 1`. -/
theorem h_conic_w_slope_at_one_ne_zero
    {theta : K} (htheta : theta ^ 2 = -12) :
    hConicWSlope 1 theta ≠ 0 := by
  rw [h_conic_w_slope_at_one]
  intro h
  have hlinear : theta = -6 := by
    field_simp at h
    linear_combination h
  rw [hlinear] at htheta
  norm_num at htheta

/-- The factor relating `W` to `X - 1` is nonzero at either point of the
conic over `X = 1`. -/
theorem h_conic_capitalW_slope_at_one_ne_zero
    {theta : K} (htheta : theta ^ 2 = -12) :
    hConicCapitalWSlope 1 theta ≠ 0 := by
  rw [h_conic_capitalW_slope_at_one]
  intro h
  have hlinear : theta = 6 := by
    field_simp at h
    linear_combination h
  rw [hlinear] at htheta
  norm_num at htheta

omit [CharZero K] in
/-- Over `X = 1`, the conic equation is equivalent to `theta^2 = -12`. -/
theorem h_conic_equation_at_one_iff (theta : K) :
    hConicEquation 1 theta = 0 ↔ theta ^ 2 = -12 := by
  rw [h_conic_equation_eq_zero_iff]
  constructor <;> intro h
  · linear_combination h
  · linear_combination h

/-! ## The two points with `X = -1` -/

omit [CharZero K] in
/-- The conic contains the point `(-1,2)`. -/
theorem h_conic_equation_at_minus_one_two :
    hConicEquation (-1 : K) 2 = 0 := by
  simp only [hConicEquation]
  ring

omit [CharZero K] in
/-- The conic contains the point `(-1,-2)`. -/
theorem h_conic_equation_at_minus_one_minus_two :
    hConicEquation (-1 : K) (-2) = 0 := by
  simp only [hConicEquation]
  ring

/-- At `(-1,2)`, the numerator of `w` equals `8` and is nonzero. -/
theorem h_conic_w_numerator_at_pole :
    hConicWNumerator (-1 : K) 2 = 8 ∧
      hConicWNumerator (-1 : K) 2 ≠ 0 := by
  simp only [hConicWNumerator]
  constructor <;> norm_num

/-- At `(-1,2)`, the numerator of `W` equals `-8` and is nonzero. -/
theorem h_conic_capitalW_numerator_at_pole :
    hConicCapitalWNumerator (-1 : K) 2 = -8 ∧
      hConicCapitalWNumerator (-1 : K) 2 ≠ 0 := by
  simp only [hConicCapitalWNumerator]
  constructor <;> norm_num

/-- The derivative of the conic equation with respect to `theta` is nonzero
at `(-1,2)`. -/
theorem h_conic_theta_derivative_at_pole :
    (2 : K) * 2 = 4 ∧ (4 : K) ≠ 0 := by
  constructor <;> norm_num

omit [CharZero K] in
/-- On the conic, the two factors above `X = -1` satisfy the identity used to
cancel the apparent pole at `theta = -2`. -/
theorem h_conic_factor_at_minus_one
    {X theta : K} (hconic : hConicEquation X theta = 0) :
    (theta - 2) * (theta + 2) =
      -2 * (X + 1) * (X + 3) := by
  simp only [hConicEquation] at hconic
  linear_combination hconic

/-- A formula for `w` in which the apparent pole at `(-1,-2)` has
cancelled. -/
@[expose]
noncomputable def hConicWRegularAtMinusBranch (X theta : K) : K :=
  (X - 1) / 6 * (2 - 2 * X * (X + 3) / (theta - 2))

/-- A formula for `W` in which the apparent pole at `(-1,-2)` has
cancelled. -/
@[expose]
noncomputable def hConicCapitalWRegularAtMinusBranch
    (X theta : K) : K :=
  -(X - 1) / 6 *
    (2 * (X + 1) + 2 * (X + 3) / (theta - 2))

/-- On the conic, the regular formula for `w` equals the original rational
formula away from its two displayed denominators. -/
theorem h_conic_w_eq_regular_at_minus_branch
    {X theta : K} (hX : X + 1 ≠ 0) (htheta : theta - 2 ≠ 0)
    (hconic : hConicEquation X theta = 0) :
    hConicW X theta = hConicWRegularAtMinusBranch X theta := by
  simp only [hConicW, hConicWRegularAtMinusBranch, hConicEquation] at *
  field_simp [hX, htheta]
  linear_combination X * (X - 1) * hconic

/-- On the conic, the regular formula for `W` equals the original rational
formula away from its two displayed denominators. -/
theorem h_conic_capitalW_eq_regular_at_minus_branch
    {X theta : K} (hX : X + 1 ≠ 0) (htheta : theta - 2 ≠ 0)
    (hconic : hConicEquation X theta = 0) :
    hConicCapitalW X theta =
      hConicCapitalWRegularAtMinusBranch X theta := by
  simp only [hConicCapitalW, hConicCapitalWRegularAtMinusBranch,
    hConicEquation] at *
  field_simp [hX, htheta]
  linear_combination (X - 1) * hconic

/-- The regular formula for `w` takes the value `-1/3` at `(-1,-2)`. -/
theorem h_conic_w_regular_value_at_minus_branch :
    hConicWRegularAtMinusBranch (-1 : K) (-2) = -1 / 3 := by
  simp only [hConicWRegularAtMinusBranch]
  norm_num

/-- The regular formula for `W` takes the value `-1/3` at `(-1,-2)`. -/
theorem h_conic_capitalW_regular_value_at_minus_branch :
    hConicCapitalWRegularAtMinusBranch (-1 : K) (-2) = -1 / 3 := by
  simp only [hConicCapitalWRegularAtMinusBranch]
  norm_num

/-! ## The chart at infinity -/

/-- The conic equation after setting `u = 1 / X` and `eta = theta / X`. -/
@[expose]
noncomputable def hInfinityConicEquation (u eta : K) : K :=
  eta ^ 2 + 2 * (1 + 4 * u + u ^ 2)

/-- The numerator of `w` in the chart at infinity. -/
@[expose]
noncomputable def hInfinityWNumerator (u eta : K) : K :=
  (1 - u) * (eta + 4 * u + 2 * u ^ 2)

/-- The numerator of `W` in the chart at infinity. -/
@[expose]
noncomputable def hInfinityCapitalWNumerator (u eta : K) : K :=
  -(1 - u) * (2 + (4 - eta) * u)

/-- The factor in the denominators at infinity that is nonzero at `u = 0`. -/
@[expose]
noncomputable def hInfinityDenominatorUnit (u : K) : K :=
  6 * (1 + u)

/-- The formula for `w` in the chart at infinity. -/
@[expose]
noncomputable def hInfinityW (u eta : K) : K :=
  hInfinityWNumerator u eta /
    (u ^ 2 * hInfinityDenominatorUnit u)

/-- The formula for `W` in the chart at infinity. -/
@[expose]
noncomputable def hInfinityCapitalW (u eta : K) : K :=
  hInfinityCapitalWNumerator u eta /
    (u ^ 2 * hInfinityDenominatorUnit u)

omit [CharZero K] in
/-- The affine conic equation transforms to the equation in the infinity
chart after clearing `u^2`. -/
theorem h_conic_equation_in_infinity_chart
    (u eta : K) (hu : u ≠ 0) :
    u ^ 2 * hConicEquation (1 / u) (eta / u) =
      hInfinityConicEquation u eta := by
  simp only [hConicEquation, hInfinityConicEquation]
  field_simp [hu]

/-- The formula for `w` transforms to `hInfinityW` in the infinity chart. -/
theorem h_conic_w_in_infinity_chart
    (u eta : K) (hu : u ≠ 0) (hplus : 1 + u ≠ 0) :
    hConicW (1 / u) (eta / u) = hInfinityW u eta := by
  simp only [hConicW, hInfinityW, hInfinityWNumerator,
    hInfinityDenominatorUnit]
  field_simp [hu, hplus]
  ring

/-- The formula for `W` transforms to `hInfinityCapitalW` in the infinity
chart. -/
theorem h_conic_capitalW_in_infinity_chart
    (u eta : K) (hu : u ≠ 0) (hplus : 1 + u ≠ 0) :
    hConicCapitalW (1 / u) (eta / u) = hInfinityCapitalW u eta := by
  simp only [hConicCapitalW, hInfinityCapitalW,
    hInfinityCapitalWNumerator, hInfinityDenominatorUnit]
  field_simp [hu, hplus]
  ring

omit [CharZero K] in
/-- At `u = 0`, the infinity equation reduces to `eta^2 + 2 = 0`. -/
theorem h_infinity_conic_equation_at_zero (eta : K) :
    hInfinityConicEquation 0 eta = eta ^ 2 + 2 := by
  simp only [hInfinityConicEquation]
  ring

omit [CharZero K] in
/-- Over `u = 0`, the infinity conic equation is equivalent to
`eta^2 = -2`. -/
theorem h_infinity_conic_equation_at_zero_iff (eta : K) :
    hInfinityConicEquation 0 eta = 0 ↔ eta ^ 2 = -2 := by
  rw [h_infinity_conic_equation_at_zero]
  constructor <;> intro h
  · linear_combination h
  · linear_combination h

/-- At a point of the conic over `u = 0`, the coordinate `eta` is nonzero. -/
theorem h_infinity_eta_ne_zero
    {eta : K} (heta : eta ^ 2 = -2) : eta ≠ 0 := by
  intro hzero
  rw [hzero] at heta
  norm_num at heta

omit [CharZero K] in
/-- The numerator of `w` at `u = 0` equals `eta`. -/
theorem h_infinity_w_numerator_at_zero (eta : K) :
    hInfinityWNumerator 0 eta = eta := by
  simp only [hInfinityWNumerator]
  ring

/-- The numerator of `w` is nonzero at either point over `u = 0`. -/
theorem h_infinity_w_numerator_at_zero_ne_zero
    {eta : K} (heta : eta ^ 2 = -2) :
    hInfinityWNumerator 0 eta ≠ 0 := by
  rw [h_infinity_w_numerator_at_zero]
  exact h_infinity_eta_ne_zero heta

/-- The numerator of `W` at `u = 0` equals `-2` and is nonzero. -/
theorem h_infinity_capitalW_numerator_at_zero :
    ∀ eta : K,
      hInfinityCapitalWNumerator 0 eta = -2 ∧
        hInfinityCapitalWNumerator 0 eta ≠ 0 := by
  intro eta
  simp only [hInfinityCapitalWNumerator]
  constructor <;> norm_num

/-- The remaining denominator factor at `u = 0` equals `6` and is nonzero. -/
theorem h_infinity_denominator_unit_at_zero :
    hInfinityDenominatorUnit (0 : K) = 6 ∧
      hInfinityDenominatorUnit (0 : K) ≠ 0 := by
  simp only [hInfinityDenominatorUnit]
  constructor <;> norm_num

/-- The derivative of the infinity conic equation with respect to `eta` is
nonzero at every point over `u = 0`. -/
theorem h_infinity_eta_derivative_ne_zero
    {eta : K} (heta : eta ^ 2 = -2) : (2 : K) * eta ≠ 0 := by
  exact mul_ne_zero (by norm_num) (h_infinity_eta_ne_zero heta)

end OnLeConjecture.DThree
