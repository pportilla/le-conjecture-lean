/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# The residual fibre product for the `H` pair

This file formalizes the affine algebra in Lemmas `dthree-Hcomponents` and
`dthree-Horders`.  After the substitutions `w = t^2` and `W = T^2`, it proves
the collapsed first fibre equation, the residual equation `Gamma`, its
discriminant, and the identities satisfied by the rational conic formulas in
equation `dthree-conic-functions`.

The geometric assertions about irreducibility, normalization, poles, and local
orders are not included here.
-/

public section

namespace OnLeConjecture.DThree

variable {K : Type*} [Field K] [CharZero K]

/-- The cubic coordinate of the `H` pair after writing `w = t^2`. -/
@[expose]
noncomputable def hP (x w : K) : K :=
  x ^ 3 + 3 * x * w

/-- The quartic coordinate of the `H` pair after writing `w = t^2`. -/
@[expose]
noncomputable def hQ (x w : K) : K :=
  x ^ 4 + 4 * x ^ 2 * w + 2 * w ^ 2

/-- The value of `W` obtained from the first fibre equation in the chart
`x = 1`, provided that `X` is nonzero. -/
@[expose]
noncomputable def hCollapsedW (X w : K) : K :=
  (1 + 3 * w - X ^ 3) / (3 * X)

/-- The residual equation in the chart `x = 1` from equation `dthree-G`. -/
@[expose]
noncomputable def hGamma (X w : K) : K :=
  18 * (X + 1) * w ^ 2 -
    12 * (X - 1) * (2 * X + 1) * w +
    (X - 1) ^ 2 * (X ^ 3 + 3 * X ^ 2 + 6 * X + 2)

/-- The first fibre equation is equivalent to the collapsed formula for `W`
when `X` is nonzero. -/
theorem h_first_fibre_equation_iff
    {X w W : K} (hX : X ≠ 0) :
    hP 1 w = hP X W ↔ W = hCollapsedW X w := by
  simp only [hP, hCollapsedW]
  constructor
  · intro h
    field_simp [hX]
    linear_combination -h
  · intro h
    rw [h]
    field_simp [hX]
    ring

/-- Substitution of the collapsed first equation factors the second coordinate
difference by the diagonal equation and `hGamma`. -/
theorem h_second_difference_on_collapsed
    (X w : K) (hX : X ≠ 0) :
    9 * X ^ 2 *
        (hQ 1 w - hQ X (hCollapsedW X w)) =
      (X - 1) * hGamma X w := by
  simp only [hQ, hCollapsedW, hGamma]
  field_simp [hX]
  ring

/-- Away from `X = 0` and the diagonal `X = 1`, the two fibre equations in
the chart `x = 1` are equivalent to the collapsed formula and `Gamma = 0`. -/
theorem h_fibre_iff_collapsed_gamma
    {X w W : K} (hX : X ≠ 0) (hdiag : X ≠ 1) :
    (hP 1 w = hP X W ∧ hQ 1 w = hQ X W) ↔
      (W = hCollapsedW X w ∧ hGamma X w = 0) := by
  constructor
  · rintro ⟨hfirst, hsecond⟩
    have hW := (h_first_fibre_equation_iff hX).mp hfirst
    subst W
    refine ⟨rfl, ?_⟩
    have hproduct : (X - 1) * hGamma X w = 0 := by
      rw [← h_second_difference_on_collapsed X w hX]
      rw [sub_eq_zero.mpr hsecond]
      ring
    exact (mul_eq_zero.mp hproduct).resolve_left (sub_ne_zero.mpr hdiag)
  · rintro ⟨rfl, hgamma⟩
    constructor
    · exact (h_first_fibre_equation_iff hX).mpr rfl
    · apply sub_eq_zero.mp
      have hscale : (9 : K) * X ^ 2 ≠ 0 :=
        mul_ne_zero (by norm_num) (pow_ne_zero 2 hX)
      apply (mul_eq_zero.mp ?_).resolve_left hscale
      rw [h_second_difference_on_collapsed X w hX, hgamma]
      ring

omit [CharZero K] in
/-- The discriminant of `hGamma`, viewed as a quadratic polynomial in `w`. -/
theorem h_gamma_discriminant (X : K) :
    (-12 * (X - 1) * (2 * X + 1)) ^ 2 -
        4 * (18 * (X + 1)) *
          ((X - 1) ^ 2 * (X ^ 3 + 3 * X ^ 2 + 6 * X + 2)) =
      -72 * X ^ 2 * (X - 1) ^ 2 * (X ^ 2 + 4 * X + 1) := by
  ring

omit [CharZero K] in
/-- On the diagonal `X = 1`, the residual equation is `36 w^2 = 0`. -/
theorem h_gamma_on_diagonal (w : K) :
    hGamma 1 w = 36 * w ^ 2 := by
  simp only [hGamma]
  ring

/-- In characteristic zero, the residual equation on the diagonal forces
`w = 0`. -/
theorem h_gamma_eq_zero_on_diagonal_iff (w : K) :
    hGamma 1 w = 0 ↔ w = 0 := by
  rw [h_gamma_on_diagonal]
  constructor
  · intro h
    have hw2 : w ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_left (by norm_num)
    simpa using hw2
  · rintro rfl
    ring

/-- The function `w` on the conic used in equation
`dthree-conic-functions`. -/
@[expose]
noncomputable def hConicW (X theta : K) : K :=
  (X - 1) * (2 * (2 * X + 1) + X * theta) / (6 * (X + 1))

/-- The function `W` on the conic used in equation
`dthree-conic-functions`. -/
@[expose]
noncomputable def hConicCapitalW (X theta : K) : K :=
  -((X - 1) * (2 * X ^ 2 + 4 * X - theta)) / (6 * (X + 1))

/-- The two rational functions on the conic satisfy the collapsed first fibre
equation wherever their displayed denominators are nonzero. -/
theorem h_conic_first_fibre_equation
    (X theta : K) (hden : X + 1 ≠ 0) :
    hP 1 (hConicW X theta) =
      hP X (hConicCapitalW X theta) := by
  simp only [hP, hConicW, hConicCapitalW]
  field_simp [hden]
  ring

/-- When `X` is nonzero, the conic formula for `W` equals the value obtained
by solving the first fibre equation. -/
theorem h_conic_capitalW_eq_collapsed
    (X theta : K) (hX : X ≠ 0) (hden : X + 1 ≠ 0) :
    hConicCapitalW X theta = hCollapsedW X (hConicW X theta) :=
  (h_first_fibre_equation_iff hX).mp
    (h_conic_first_fibre_equation X theta hden)

/-- Substitution of the first rational conic function in `hGamma` vanishes
under the conic equation from Lemma `dthree-Horders`. -/
theorem h_gamma_on_conic
    {X theta : K} (hden : X + 1 ≠ 0)
    (htheta : theta ^ 2 = -2 * (X ^ 2 + 4 * X + 1)) :
    hGamma X (hConicW X theta) = 0 := by
  simp only [hGamma, hConicW]
  field_simp [hden]
  linear_combination 18 * X ^ 2 * (X - 1) ^ 2 * htheta

/-- The two rational functions on the conic satisfy the second fibre equation
under the conic equation from Lemma `dthree-Horders`. -/
theorem h_conic_second_fibre_equation
    {X theta : K} (hden : X + 1 ≠ 0)
    (htheta : theta ^ 2 = -2 * (X ^ 2 + 4 * X + 1)) :
    hQ 1 (hConicW X theta) =
      hQ X (hConicCapitalW X theta) := by
  simp only [hQ, hConicW, hConicCapitalW]
  field_simp [hden]
  linear_combination 2 * (X - 1) ^ 3 * (X + 1) * htheta

/-- The rational conic formulas determine two points in one fibre of the
`H` pair. -/
theorem h_conic_parametrizes_fibre
    {X theta : K} (hden : X + 1 ≠ 0)
    (htheta : theta ^ 2 = -2 * (X ^ 2 + 4 * X + 1)) :
    hP 1 (hConicW X theta) = hP X (hConicCapitalW X theta) ∧
      hQ 1 (hConicW X theta) = hQ X (hConicCapitalW X theta) :=
  ⟨h_conic_first_fibre_equation X theta hden,
    h_conic_second_fibre_equation hden htheta⟩

omit [CharZero K] in
/-- Equation `J(P,Q) = 12 w^2` for the `H` pair, written using the four
partial derivatives. -/
theorem h_jacobian_identity (x w : K) :
    (3 * x ^ 2 + 3 * w) * (4 * x ^ 2 + 4 * w) -
        (3 * x) * (4 * x ^ 3 + 8 * x * w) =
      12 * w ^ 2 := by
  ring

end OnLeConjecture.DThree
