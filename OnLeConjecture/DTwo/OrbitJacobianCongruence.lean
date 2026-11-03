/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.OrbitDifferenceDescent
public import OnLeConjecture.DThree.EThetaHomogeneous
public import OnLeConjecture.Polynomial.WeightedJacobian

/-!
# The Jacobian congruence for the quadratic orbit pair

This module proves the congruence used in the quadratic orbit case. If a
homogeneous form `R` of degree at least four satisfies
`lambda ^ 3 ∣ J(Phi,R)`, then there is a homogeneous element `B` of
`C[Phi,Psi]` such that `lambda ^ 4 ∣ R - B`.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.DThree
open OnLeConjecture.Polynomial

noncomputable def orbitExponent (a b : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b

@[simp]
theorem orbitExponent_zero (a b : ℕ) : orbitExponent a b 0 = a := by
  simp [orbitExponent]

@[simp]
theorem orbitExponent_one (a b : ℕ) : orbitExponent a b 1 = b := by
  simp [orbitExponent]

theorem orbitExponent_eq_eFormExponent (a b : ℕ) :
    orbitExponent a b = eFormExponent a b := by
  ext i
  fin_cases i <;> simp

theorem orbitFormToIterated_coeff (R : OrbitSourceForm) (a b : ℕ) :
    ((eFormToIterated R).coeff b).coeff a =
      MvPolynomial.coeff (orbitExponent a b) R := by
  have hback : eIteratedToForm (eFormToIterated R) = R := by
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
      AlgHom.congr_fun eIteratedToForm_comp_formToIterated R
  have hcoefficient := eIteratedToForm_coeff (eFormToIterated R) a b
  rw [hback, ← orbitExponent_eq_eFormExponent] at hcoefficient
  exact hcoefficient.symm

@[expose]
noncomputable def orbitLowCoefficient
    (R : OrbitSourceForm) (r i : ℕ) : ℂ :=
  MvPolynomial.coeff (orbitExponent (r - i) i) R

theorem orbitFormToIterated_outerCoeff_of_homogeneous
    {R : OrbitSourceForm} {r : ℕ} (hR : R.IsHomogeneous r)
    (i : ℕ) :
    (eFormToIterated R).coeff i =
      Polynomial.monomial (r - i) (orbitLowCoefficient R r i) := by
  ext j
  rw [Polynomial.coeff_monomial]
  by_cases hji : j = r - i
  · subst j
    rw [if_pos rfl]
    exact orbitFormToIterated_coeff R (r - i) i
  · rw [if_neg (Ne.symm hji)]
    by_contra hnonzero
    have hsource :
        MvPolynomial.coeff (orbitExponent j i) R ≠ 0 := by
      rw [← orbitFormToIterated_coeff]
      exact hnonzero
    have hdegree := hR hsource
    have hsum : j + i = r := by
      simpa [orbitExponent, Finsupp.degree_eq_weight_one,
        Finsupp.weight_apply, Finsupp.sum_fintype,
        Fin.sum_univ_two] using hdegree
    exact hji (by omega)

@[expose]
noncomputable def orbitLowIterated
    (R : OrbitSourceForm) (r : ℕ) : Polynomial (Polynomial ℂ) :=
  ∑ i ∈ Finset.range 4,
    Polynomial.monomial i
      (Polynomial.monomial (r - i) (orbitLowCoefficient R r i))

@[expose]
noncomputable def orbitLowForm
    (R : OrbitSourceForm) (r : ℕ) : OrbitSourceForm :=
  eIteratedToForm (orbitLowIterated R r)

theorem orbitFormToIterated_sub_low_X_four_dvd
    {R : OrbitSourceForm} {r : ℕ} (hR : R.IsHomogeneous r) :
    Polynomial.X ^ 4 ∣ eFormToIterated R - orbitLowIterated R r := by
  rw [Polynomial.X_pow_dvd_iff]
  intro i hi
  rw [Polynomial.coeff_sub,
    orbitFormToIterated_outerCoeff_of_homogeneous hR]
  simp [orbitLowIterated, Polynomial.coeff_monomial, hi]

theorem orbitLambda_four_dvd_sub_lowForm
    {R : OrbitSourceForm} {r : ℕ} (hR : R.IsHomogeneous r) :
    orbitPolynomialLambda ℂ ^ 4 ∣ R - orbitLowForm R r := by
  obtain ⟨Q, hQ⟩ := orbitFormToIterated_sub_low_X_four_dvd hR
  refine ⟨eIteratedToForm Q, ?_⟩
  have hback : eIteratedToForm (eFormToIterated R) = R := by
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
      AlgHom.congr_fun eIteratedToForm_comp_formToIterated R
  have hvariable : eIteratedToForm Polynomial.X =
      orbitPolynomialLambda ℂ := by
    rw [eIteratedToForm_outerX, orbitPolynomialLambda]
    rfl
  calc
    R - orbitLowForm R r =
        eIteratedToForm (eFormToIterated R - orbitLowIterated R r) := by
      simp only [map_sub, hback, orbitLowForm]
    _ = eIteratedToForm (Polynomial.X ^ 4 * Q) := by rw [hQ]
    _ = orbitPolynomialLambda ℂ ^ 4 * eIteratedToForm Q := by
      rw [map_mul, map_pow, hvariable]

theorem orbitJacobian_formula (R : OrbitSourceForm) :
    jacobian (orbitPolynomialPhi ℂ) R =
      MvPolynomial.C 2 * orbitPolynomialS ℂ *
          MvPolynomial.pderiv (1 : Fin 2) R +
        MvPolynomial.C 2 * orbitPolynomialLambda ℂ *
          MvPolynomial.pderiv (0 : Fin 2) R := by
  have hC2 : MvPolynomial.C (2 : ℂ) =
      (2 : OrbitSourceForm) := map_ofNat _ 2
  simp only [jacobian, orbitPolynomialPhi, orbitPolynomialS,
    orbitPolynomialLambda, map_sub,
    MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0),
    MvPolynomial.pderiv_X_of_ne (by decide : (0 : Fin 2) ≠ 1)]
  rw [hC2]
  ring_nf

set_option linter.flexible false in
theorem orbitJacobian_coeff_zero (R : OrbitSourceForm) (r : ℕ) (hr : 4 ≤ r) :
    MvPolynomial.coeff (orbitExponent r 0)
        (jacobian (orbitPolynomialPhi ℂ) R) =
      2 * orbitLowCoefficient R r 1 := by
  have hr0 : r ≠ 0 := by omega
  have hexponent :
      (orbitExponent r 0 - Finsupp.single (0 : Fin 2) 1) +
          Finsupp.single (1 : Fin 2) 1 =
        orbitExponent (r - 1) 1 := by
    ext i
    fin_cases i <;> simp [orbitExponent]
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
theorem orbitJacobian_coeff_one (R : OrbitSourceForm) (r : ℕ) (hr : 4 ≤ r) :
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
    · simp [orbitExponent]
      omega
    · simp [orbitExponent]
  have hsecondExponent :
      (orbitExponent (r - 1) 1 - Finsupp.single (1 : Fin 2) 1) +
          Finsupp.single (0 : Fin 2) 1 =
        orbitExponent r 0 := by
    ext i
    fin_cases i
    · simp [orbitExponent]
      omega
    · simp [orbitExponent]
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
theorem orbitJacobian_coeff_two (R : OrbitSourceForm) (r : ℕ) (hr : 4 ≤ r) :
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
    · simp [orbitExponent]
      omega
    · simp [orbitExponent]
  have hsecondExponent :
      (orbitExponent (r - 2) 2 - Finsupp.single (1 : Fin 2) 1) +
          Finsupp.single (0 : Fin 2) 1 =
        orbitExponent (r - 1) 1 := by
    ext i
    fin_cases i
    · simp [orbitExponent]
      omega
    · simp [orbitExponent]
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

theorem orbitJacobian_coefficient_eq_zero_of_lambda_cube_dvd
    {R : OrbitSourceForm}
    (hdivides : orbitPolynomialLambda ℂ ^ 3 ∣
      jacobian (orbitPolynomialPhi ℂ) R)
    (a b : ℕ) (hb : b < 3) :
    MvPolynomial.coeff (orbitExponent a b)
        (jacobian (orbitPolynomialPhi ℂ) R) = 0 := by
  have hmapped := map_dvd eFormToIterated hdivides
  have hlambda : eFormToIterated (orbitPolynomialLambda ℂ) =
      Polynomial.X := by
    rw [orbitPolynomialLambda]
    exact eFormToIterated_t
  rw [map_pow, hlambda] at hmapped
  have houter := (Polynomial.X_pow_dvd_iff.mp hmapped) b hb
  rw [← orbitFormToIterated_coeff]
  rw [houter]
  simp

theorem orbitLowCoefficient_relations_of_jacobian_dvd
    {R : OrbitSourceForm} {r : ℕ} (hr : 4 ≤ r)
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
  rw [orbitJacobian_coeff_zero R r hr] at hzero
  rw [orbitJacobian_coeff_one R r hr] at hone
  rw [orbitJacobian_coeff_two R r hr] at htwo
  constructor
  · linear_combination (1 / 2 : ℂ) * hzero
  constructor
  · linear_combination (1 / 2 : ℂ) * hone
  · have honeCoefficient : orbitLowCoefficient R r 1 = 0 := by
      linear_combination (1 / 2 : ℂ) * hzero
    rw [honeCoefficient] at htwo
    linear_combination (1 / 6 : ℂ) * htwo

noncomputable def orbitLambdaZeroRingHom :
    OrbitSourceForm →+* Polynomial ℂ :=
  Polynomial.constantCoeff.comp eFormToIterated.toRingHom

@[simp]
theorem orbitLambdaZeroRingHom_s :
    orbitLambdaZeroRingHom (orbitPolynomialS ℂ) = Polynomial.X := by
  change Polynomial.constantCoeff
      (eFormToIterated (formX : Form ℂ)) = Polynomial.X
  rw [eFormToIterated_x]
  simp

@[simp]
theorem orbitLambdaZeroRingHom_lambda :
    orbitLambdaZeroRingHom (orbitPolynomialLambda ℂ) = 0 := by
  change Polynomial.constantCoeff
      (eFormToIterated (formT : Form ℂ)) = 0
  rw [eFormToIterated_t]
  simp

@[simp]
theorem orbitLambdaZeroRingHom_C (coefficient : ℂ) :
    orbitLambdaZeroRingHom (MvPolynomial.C coefficient) =
      Polynomial.C coefficient := by
  change Polynomial.constantCoeff
      (eFormToIterated ((algebraMap ℂ (Form ℂ)) coefficient)) =
        Polynomial.C coefficient
  rw [eFormToIterated.commutes]
  simp

theorem orbitLambdaZeroRingHom_phi :
    orbitLambdaZeroRingHom (orbitPolynomialPhi ℂ) =
      Polynomial.X ^ 2 := by
  simp only [orbitPolynomialPhi, map_sub, map_pow,
    orbitLambdaZeroRingHom_s, orbitLambdaZeroRingHom_lambda]
  ring_nf

theorem orbitLambdaZeroRingHom_psi :
    orbitLambdaZeroRingHom (orbitPolynomialPsi ℂ) =
      Polynomial.C 2 * Polynomial.X ^ 3 := by
  simp only [orbitPolynomialPsi, map_sub, map_mul, map_pow,
    orbitLambdaZeroRingHom_s, orbitLambdaZeroRingHom_lambda,
    orbitLambdaZeroRingHom_C]
  ring_nf

theorem orbitLowCoefficient_zero_eq_lambdaZero_coeff
    (R : OrbitSourceForm) (r : ℕ) :
    orbitLowCoefficient R r 0 =
      (orbitLambdaZeroRingHom R).coeff r := by
  rw [orbitLowCoefficient, Nat.sub_zero,
    ← orbitFormToIterated_coeff R r 0]
  rfl

theorem orbitLowCoefficient_evenBase_zero
    (coefficient : ℂ) (n : ℕ) :
    orbitLowCoefficient
        (MvPolynomial.C coefficient * orbitPolynomialPhi ℂ ^ n)
        (2 * n) 0 = coefficient := by
  rw [orbitLowCoefficient_zero_eq_lambdaZero_coeff]
  simp only [map_mul, map_pow, orbitLambdaZeroRingHom_phi]
  rw [← pow_mul]
  simp

theorem orbitLowCoefficient_oddBase_zero
    (coefficient : ℂ) (n : ℕ) :
    orbitLowCoefficient
        (MvPolynomial.C (coefficient / 2) * orbitPolynomialPsi ℂ *
          orbitPolynomialPhi ℂ ^ n)
        (3 + 2 * n) 0 = coefficient := by
  rw [orbitLowCoefficient_zero_eq_lambdaZero_coeff]
  simp only [map_mul, map_pow, orbitLambdaZeroRingHom_phi,
    orbitLambdaZeroRingHom_psi, orbitLambdaZeroRingHom_C]
  rw [← pow_mul]
  rw [show Polynomial.C (coefficient / 2) *
        (Polynomial.C 2 * Polynomial.X ^ 3) *
          Polynomial.X ^ (2 * n) =
      Polynomial.C coefficient *
        (Polynomial.X ^ 3 * Polynomial.X ^ (2 * n)) by
    calc
      Polynomial.C (coefficient / 2) *
            (Polynomial.C 2 * Polynomial.X ^ 3) *
          Polynomial.X ^ (2 * n) =
          (Polynomial.C (coefficient / 2) * Polynomial.C 2) *
            (Polynomial.X ^ 3 * Polynomial.X ^ (2 * n)) := by ring_nf
      _ = Polynomial.C coefficient *
            (Polynomial.X ^ 3 * Polynomial.X ^ (2 * n)) := by
        rw [← map_mul]
        congr 1
        ring_nf]
  rw [← pow_add]
  simp

theorem orbitEvenBase_isHomogeneous
    (coefficient : ℂ) (n : ℕ) :
    (MvPolynomial.C coefficient * orbitPolynomialPhi ℂ ^ n).IsHomogeneous
      (2 * n) := by
  change MvPolynomial.IsWeightedHomogeneous (1 : Fin 2 → ℕ)
    (MvPolynomial.C coefficient * orbitPolynomialPhi ℂ ^ n) (2 * n)
  have hphi := orbitPolynomialPhi_isHomogeneous (K := ℂ)
  simpa [mul_comm] using (hphi.pow n).C_mul coefficient

theorem orbitOddBase_isHomogeneous
    (coefficient : ℂ) (n : ℕ) :
    (MvPolynomial.C (coefficient / 2) * orbitPolynomialPsi ℂ *
      orbitPolynomialPhi ℂ ^ n).IsHomogeneous (3 + 2 * n) := by
  change (MvPolynomial.C (coefficient / 2) * orbitPolynomialPsi ℂ *
    orbitPolynomialPhi ℂ ^ n).IsWeightedHomogeneous
      (1 : Fin 2 → ℕ) (3 + 2 * n)
  have hphi := orbitPolynomialPhi_isHomogeneous (K := ℂ)
  have hpsi := orbitPolynomialPsi_isHomogeneous (K := ℂ)
  have hproduct := hpsi.mul (hphi.pow n)
  simpa [nsmul_eq_mul, mul_comm, mul_assoc] using
    hproduct.C_mul (coefficient / 2)

theorem orbitEvenBase_jacobian_lambda_cube_dvd
    (coefficient : ℂ) (n : ℕ) :
    orbitPolynomialLambda ℂ ^ 3 ∣
      jacobian (orbitPolynomialPhi ℂ)
        (MvPolynomial.C coefficient * orbitPolynomialPhi ℂ ^ n) := by
  refine ⟨0, ?_⟩
  simp [jacobian, orbitPolynomialPhi, orbitPolynomialS,
    orbitPolynomialLambda]
  ring_nf

set_option linter.flexible false in
theorem orbitOddBase_jacobian_lambda_cube_dvd
    (coefficient : ℂ) (n : ℕ) :
    orbitPolynomialLambda ℂ ^ 3 ∣
      jacobian (orbitPolynomialPhi ℂ)
        (MvPolynomial.C (coefficient / 2) * orbitPolynomialPsi ℂ *
          orbitPolynomialPhi ℂ ^ n) := by
  have hC2 : MvPolynomial.C (2 : ℂ) =
      (2 : OrbitSourceForm) := map_ofNat _ 2
  have hC3 : MvPolynomial.C (3 : ℂ) =
      (3 : OrbitSourceForm) := map_ofNat _ 3
  refine ⟨-(MvPolynomial.C (coefficient / 2) *
      MvPolynomial.C 2 * MvPolynomial.C 3 *
        orbitPolynomialPhi ℂ ^ n), ?_⟩
  simp [jacobian, orbitPolynomialPhi, orbitPolynomialPsi,
    orbitPolynomialS, orbitPolynomialLambda]
  rw [hC2, hC3]
  ring_nf

theorem orbitLowForm_eq_of_same_lead_and_jacobian_dvd
    {R B : OrbitSourceForm} {r : ℕ} (hr : 4 ≤ r)
    (hRdivides : orbitPolynomialLambda ℂ ^ 3 ∣
      jacobian (orbitPolynomialPhi ℂ) R)
    (hBdivides : orbitPolynomialLambda ℂ ^ 3 ∣
      jacobian (orbitPolynomialPhi ℂ) B)
    (hlead : orbitLowCoefficient R r 0 =
      orbitLowCoefficient B r 0) :
    orbitLowForm R r = orbitLowForm B r := by
  obtain ⟨hRone, hRtwo, hRthree⟩ :=
    orbitLowCoefficient_relations_of_jacobian_dvd hr hRdivides
  obtain ⟨hBone, hBtwo, hBthree⟩ :=
    orbitLowCoefficient_relations_of_jacobian_dvd hr hBdivides
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

theorem orbitLambda_four_dvd_sub_of_same_lead_and_jacobian_dvd
    {R B : OrbitSourceForm} {r : ℕ} (hr : 4 ≤ r)
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
  have hlow := orbitLowForm_eq_of_same_lead_and_jacobian_dvd
    hr hRdivides hBdivides hlead
  have hdifference := dvd_sub hRlow hBlow
  have hequality :
      (R - orbitLowForm R r) - (B - orbitLowForm B r) = R - B := by
    rw [hlow]
    ring_nf
  rw [← hequality]
  exact hdifference

theorem orbitEvenBase_mem_range
    (coefficient : ℂ) (n : ℕ) :
    MvPolynomial.C coefficient * orbitPolynomialPhi ℂ ^ n ∈
      Set.range (orbitBaseToSource ℂ) := by
  refine ⟨MvPolynomial.C coefficient * orbitBasePhi ℂ ^ n, ?_⟩
  simp

theorem orbitOddBase_mem_range
    (coefficient : ℂ) (n : ℕ) :
    MvPolynomial.C (coefficient / 2) * orbitPolynomialPsi ℂ *
        orbitPolynomialPhi ℂ ^ n ∈
      Set.range (orbitBaseToSource ℂ) := by
  refine ⟨MvPolynomial.C (coefficient / 2) * orbitBasePsi ℂ *
    orbitBasePhi ℂ ^ n, ?_⟩
  simp [mul_assoc]

theorem exists_orbitBase_congruent_mod_lambda_four
    {R : OrbitSourceForm} {r : ℕ} (hr : 4 ≤ r)
    (hR : R.IsHomogeneous r)
    (hdivides : orbitPolynomialLambda ℂ ^ 3 ∣
      jacobian (orbitPolynomialPhi ℂ) R) :
    ∃ B : OrbitSourceForm,
      B ∈ Set.range (orbitBaseToSource ℂ) ∧
      B.IsHomogeneous r ∧
      orbitPolynomialLambda ℂ ^ 4 ∣ R - B := by
  rcases r.even_or_odd with heven | hodd
  · obtain ⟨n, rfl⟩ := heven
    let coefficient := orbitLowCoefficient R (n + n) 0
    let B := MvPolynomial.C coefficient * orbitPolynomialPhi ℂ ^ n
    have hBhomogeneous : B.IsHomogeneous (n + n) := by
      simpa [B, two_mul] using orbitEvenBase_isHomogeneous coefficient n
    have hBdivides : orbitPolynomialLambda ℂ ^ 3 ∣
        jacobian (orbitPolynomialPhi ℂ) B := by
      exact orbitEvenBase_jacobian_lambda_cube_dvd coefficient n
    have hlead : orbitLowCoefficient R (n + n) 0 =
        orbitLowCoefficient B (n + n) 0 := by
      change coefficient = orbitLowCoefficient B (n + n) 0
      symm
      simpa [B, two_mul] using
        orbitLowCoefficient_evenBase_zero coefficient n
    refine ⟨B, orbitEvenBase_mem_range coefficient n,
      hBhomogeneous, ?_⟩
    exact orbitLambda_four_dvd_sub_of_same_lead_and_jacobian_dvd
      hr hR hBhomogeneous hdivides hBdivides hlead
  · obtain ⟨n, rfl⟩ := hodd
    have hn : 2 ≤ n := by omega
    let q := n - 1
    let coefficient := orbitLowCoefficient R (2 * n + 1) 0
    let B := MvPolynomial.C (coefficient / 2) * orbitPolynomialPsi ℂ *
      orbitPolynomialPhi ℂ ^ q
    have hdegree : 2 * n + 1 = 3 + 2 * q := by
      dsimp only [q]
      omega
    have hBhomogeneous : B.IsHomogeneous (2 * n + 1) := by
      rw [hdegree]
      exact orbitOddBase_isHomogeneous coefficient q
    have hBdivides : orbitPolynomialLambda ℂ ^ 3 ∣
        jacobian (orbitPolynomialPhi ℂ) B := by
      exact orbitOddBase_jacobian_lambda_cube_dvd coefficient q
    have hlead : orbitLowCoefficient R (2 * n + 1) 0 =
        orbitLowCoefficient B (2 * n + 1) 0 := by
      change coefficient = orbitLowCoefficient B (2 * n + 1) 0
      symm
      rw [hdegree]
      simpa [B] using orbitLowCoefficient_oddBase_zero coefficient q
    refine ⟨B, orbitOddBase_mem_range coefficient q,
      hBhomogeneous, ?_⟩
    exact orbitLambda_four_dvd_sub_of_same_lead_and_jacobian_dvd
      hr hR hBhomogeneous hdivides hBdivides hlead

end OnLeConjecture.DTwo
