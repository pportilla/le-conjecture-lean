/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.OrbitJacobianCongruence
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Cubic normalization for the quadratic orbit pair

This module proves the coefficient calculation used when a squarefree
quadratic jet has been normalized to `Phi`. A homogeneous cubic whose
Jacobian with `Phi` is divisible by `lambda ^ 3` is a scalar multiple of
`Psi`.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Polynomial

set_option linter.flexible false in
theorem orbitJacobian_coeff_zero_of_three_le
    (R : OrbitSourceForm) (r : ℕ) (hr : 3 ≤ r) :
    MvPolynomial.coeff (orbitExponent r 0)
        (jacobian (orbitPolynomialPhi ℂ) R) =
      2 * orbitLowCoefficient R r 1 := by
  have hr0 : r ≠ 0 := by omega
  have hexponent :
      (orbitExponent r 0 - Finsupp.single (0 : Fin 2) 1) +
          Finsupp.single (1 : Fin 2) 1 =
        orbitExponent (r - 1) 1 := by
    ext i
    fin_cases i
    · simp
    · simp
  rw [orbitJacobian_formula]
  simp only [mul_assoc]
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_C_mul]
  simp only [orbitPolynomialS, orbitPolynomialLambda]
  rw [MvPolynomial.coeff_X_mul', MvPolynomial.coeff_X_mul']
  simp [orbitExponent_zero, hr0, MvPolynomial.coeff_pderiv]
  rw [hexponent]
  rfl

set_option linter.flexible false in
theorem orbitJacobian_coeff_one_of_three_le
    (R : OrbitSourceForm) (r : ℕ) (hr : 3 ≤ r) :
    MvPolynomial.coeff (orbitExponent (r - 1) 1)
        (jacobian (orbitPolynomialPhi ℂ) R) =
      4 * orbitLowCoefficient R r 2 +
        2 * r * orbitLowCoefficient R r 0 := by
  have hr1 : r - 1 ≠ 0 := by omega
  have hfirstExponent :
      (orbitExponent (r - 1) 1 - Finsupp.single (0 : Fin 2) 1) +
          Finsupp.single (1 : Fin 2) 1 =
        orbitExponent (r - 2) 2 := by
    ext i
    fin_cases i
    · simp
      omega
    · simp
  have hsecondExponent :
      (orbitExponent (r - 1) 1 - Finsupp.single (1 : Fin 2) 1) +
          Finsupp.single (0 : Fin 2) 1 =
        orbitExponent r 0 := by
    ext i
    fin_cases i
    · simp
      omega
    · simp
  rw [orbitJacobian_formula]
  simp only [mul_assoc]
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_C_mul]
  simp only [orbitPolynomialS, orbitPolynomialLambda]
  rw [MvPolynomial.coeff_X_mul', MvPolynomial.coeff_X_mul']
  simp [orbitExponent_zero, orbitExponent_one, hr1,
    MvPolynomial.coeff_pderiv]
  rw [hfirstExponent, hsecondExponent]
  simp only [orbitLowCoefficient]
  rw [Nat.cast_sub (by omega : 1 ≤ r)]
  simp only [Nat.sub_zero]
  ring_nf

set_option linter.flexible false in
theorem orbitJacobian_coeff_two_of_three_le
    (R : OrbitSourceForm) (r : ℕ) (hr : 3 ≤ r) :
    MvPolynomial.coeff (orbitExponent (r - 2) 2)
        (jacobian (orbitPolynomialPhi ℂ) R) =
      6 * orbitLowCoefficient R r 3 +
        2 * (r - 1) * orbitLowCoefficient R r 1 := by
  have hr2 : r - 2 ≠ 0 := by omega
  have hfirstExponent :
      (orbitExponent (r - 2) 2 - Finsupp.single (0 : Fin 2) 1) +
          Finsupp.single (1 : Fin 2) 1 =
        orbitExponent (r - 3) 3 := by
    ext i
    fin_cases i
    · simp
      omega
    · simp
  have hsecondExponent :
      (orbitExponent (r - 2) 2 - Finsupp.single (1 : Fin 2) 1) +
          Finsupp.single (0 : Fin 2) 1 =
        orbitExponent (r - 1) 1 := by
    ext i
    fin_cases i
    · simp
      omega
    · simp
  rw [orbitJacobian_formula]
  simp only [mul_assoc]
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_C_mul]
  simp only [orbitPolynomialS, orbitPolynomialLambda]
  rw [MvPolynomial.coeff_X_mul', MvPolynomial.coeff_X_mul']
  simp [orbitExponent_zero, orbitExponent_one, hr2,
    MvPolynomial.coeff_pderiv]
  rw [hfirstExponent, hsecondExponent]
  simp only [orbitLowCoefficient]
  rw [Nat.cast_sub (by omega : 2 ≤ r)]
  ring_nf

theorem orbitLowCoefficient_relations_of_jacobian_dvd_of_three_le
    {R : OrbitSourceForm} {r : ℕ} (hr : 3 ≤ r)
    (hdivides : orbitPolynomialLambda ℂ ^ 3 ∣
      jacobian (orbitPolynomialPhi ℂ) R) :
    orbitLowCoefficient R r 1 = 0 ∧
      2 * orbitLowCoefficient R r 2 =
        -(r : ℂ) * orbitLowCoefficient R r 0 ∧
      orbitLowCoefficient R r 3 = 0 := by
  have hzero := orbitJacobian_coefficient_eq_zero_of_lambda_cube_dvd
    hdivides r 0 (by omega)
  have hone := orbitJacobian_coefficient_eq_zero_of_lambda_cube_dvd
    hdivides (r - 1) 1 (by omega)
  have htwo := orbitJacobian_coefficient_eq_zero_of_lambda_cube_dvd
    hdivides (r - 2) 2 (by omega)
  rw [orbitJacobian_coeff_zero_of_three_le R r hr] at hzero
  rw [orbitJacobian_coeff_one_of_three_le R r hr] at hone
  rw [orbitJacobian_coeff_two_of_three_le R r hr] at htwo
  constructor
  · linear_combination (1 / 2 : ℂ) * hzero
  constructor
  · linear_combination (1 / 2 : ℂ) * hone
  · have honeCoefficient : orbitLowCoefficient R r 1 = 0 := by
      linear_combination (1 / 2 : ℂ) * hzero
    rw [honeCoefficient] at htwo
    linear_combination (1 / 6 : ℂ) * htwo

theorem orbitLowForm_eq_of_same_lead_and_jacobian_dvd_of_three_le
    {R B : OrbitSourceForm} {r : ℕ} (hr : 3 ≤ r)
    (hRdivides : orbitPolynomialLambda ℂ ^ 3 ∣
      jacobian (orbitPolynomialPhi ℂ) R)
    (hBdivides : orbitPolynomialLambda ℂ ^ 3 ∣
      jacobian (orbitPolynomialPhi ℂ) B)
    (hlead : orbitLowCoefficient R r 0 =
      orbitLowCoefficient B r 0) :
    orbitLowForm R r = orbitLowForm B r := by
  obtain ⟨hRone, hRtwo, hRthree⟩ :=
    orbitLowCoefficient_relations_of_jacobian_dvd_of_three_le
      hr hRdivides
  obtain ⟨hBone, hBtwo, hBthree⟩ :=
    orbitLowCoefficient_relations_of_jacobian_dvd_of_three_le
      hr hBdivides
  have hcoefficients : ∀ i < 4,
      orbitLowCoefficient R r i = orbitLowCoefficient B r i := by
    intro i hi
    interval_cases i
    · exact hlead
    · rw [hRone, hBone]
    · rw [hlead] at hRtwo
      linear_combination (1 / 2 : ℂ) * (hRtwo - hBtwo)
    · rw [hRthree, hBthree]
  rw [orbitLowForm, orbitLowForm, orbitLowIterated, orbitLowIterated]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi4 : i < 4 := Finset.mem_range.mp hi
  rw [hcoefficients i hi4]

theorem orbitLambda_four_dvd_sub_of_same_lead_and_jacobian_dvd_of_three_le
    {R B : OrbitSourceForm} {r : ℕ} (hr : 3 ≤ r)
    (hR : R.IsHomogeneous r) (hB : B.IsHomogeneous r)
    (hRdivides : orbitPolynomialLambda ℂ ^ 3 ∣
      jacobian (orbitPolynomialPhi ℂ) R)
    (hBdivides : orbitPolynomialLambda ℂ ^ 3 ∣
      jacobian (orbitPolynomialPhi ℂ) B)
    (hlead : orbitLowCoefficient R r 0 =
      orbitLowCoefficient B r 0) :
    orbitPolynomialLambda ℂ ^ 4 ∣ R - B := by
  have hRlow := orbitLambda_four_dvd_sub_lowForm hR
  have hBlow := orbitLambda_four_dvd_sub_lowForm hB
  have hlow :=
    orbitLowForm_eq_of_same_lead_and_jacobian_dvd_of_three_le
      hr hRdivides hBdivides hlead
  have hdifference := dvd_sub hRlow hBlow
  have hequality :
      (R - orbitLowForm R r) - (B - orbitLowForm B r) = R - B := by
    rw [hlow]
    ring_nf
  rw [← hequality]
  exact hdifference

/-- A cubic satisfying the polar divisibility condition is a scalar
multiple of the normalized cubic orbit form. -/
theorem exists_eq_C_mul_orbitPolynomialPsi_of_cubic_jacobian_dvd
    {R : OrbitSourceForm} (hR : R.IsHomogeneous 3)
    (hdivides : orbitPolynomialLambda ℂ ^ 3 ∣
      jacobian (orbitPolynomialPhi ℂ) R) :
    ∃ coefficient : ℂ,
      R = MvPolynomial.C coefficient * orbitPolynomialPsi ℂ := by
  let lead := orbitLowCoefficient R 3 0
  let B := MvPolynomial.C (lead / 2) * orbitPolynomialPsi ℂ *
    orbitPolynomialPhi ℂ ^ 0
  have hB : B.IsHomogeneous 3 := by
    simpa only [B, Nat.mul_zero, add_zero] using
      orbitOddBase_isHomogeneous lead 0
  have hBdivides : orbitPolynomialLambda ℂ ^ 3 ∣
      jacobian (orbitPolynomialPhi ℂ) B := by
    simpa only [B] using orbitOddBase_jacobian_lambda_cube_dvd lead 0
  have hlead : orbitLowCoefficient R 3 0 =
      orbitLowCoefficient B 3 0 := by
    change lead = orbitLowCoefficient B 3 0
    symm
    simpa only [B, Nat.mul_zero, add_zero] using
      orbitLowCoefficient_oddBase_zero lead 0
  have hfour : orbitPolynomialLambda ℂ ^ 4 ∣ R - B :=
    orbitLambda_four_dvd_sub_of_same_lead_and_jacobian_dvd_of_three_le
      (by omega) hR hB hdivides hBdivides hlead
  have hsubHomogeneous : (R - B).IsHomogeneous 3 := hR.sub hB
  have hsubZero : R - B = 0 := by
    by_contra hsubNonzero
    have hdegreeSub : (R - B).totalDegree = 3 :=
      hsubHomogeneous.totalDegree hsubNonzero
    have hlambdaHomogeneous :
        (orbitPolynomialLambda ℂ ^ 4).IsHomogeneous 4 := by
      exact (MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2)).pow 4
    have hlambdaNonzero : orbitPolynomialLambda ℂ ^ 4 ≠ 0 := by
      exact pow_ne_zero 4 (MvPolynomial.X_ne_zero (R := ℂ) (1 : Fin 2))
    have hdegreeLambda :
        (orbitPolynomialLambda ℂ ^ 4).totalDegree = 4 :=
      hlambdaHomogeneous.totalDegree hlambdaNonzero
    have hdegreeLe := MvPolynomial.totalDegree_le_of_dvd_of_isDomain
      hfour hsubNonzero
    rw [hdegreeLambda, hdegreeSub] at hdegreeLe
    omega
  refine ⟨lead / 2, ?_⟩
  simpa only [B, pow_zero, mul_one] using sub_eq_zero.mp hsubZero

end OnLeConjecture.DTwo
