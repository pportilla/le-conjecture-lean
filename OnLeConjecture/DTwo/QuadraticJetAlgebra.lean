/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.QuadraticJetCubicNormalization

/-!
# Algebra of binary quadratic jets

This module records the coefficient presentation of a homogeneous binary
quadratic and proves that vanishing discriminant is equivalent to being a
nonzero scalar multiple of the square of a nonzero linear form.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.DThree

/-- The binary quadratic with coefficients `a`, `b`, and `c`. -/
@[expose]
noncomputable def binaryQuadraticForm (a b c : ℂ) : OrbitSourceForm :=
  MvPolynomial.C a * orbitPolynomialS ℂ ^ 2 +
    MvPolynomial.C b * orbitPolynomialS ℂ * orbitPolynomialLambda ℂ +
      MvPolynomial.C c * orbitPolynomialLambda ℂ ^ 2

/-- A binary linear form in the orbit coordinates. -/
@[expose]
noncomputable def binaryLinearForm (u v : ℂ) : OrbitSourceForm :=
  MvPolynomial.C u * orbitPolynomialS ℂ +
    MvPolynomial.C v * orbitPolynomialLambda ℂ

/-- The three coefficients of a homogeneous binary quadratic. -/
@[expose]
noncomputable def binaryQuadraticCoefficients
    (Q : OrbitSourceForm) : Fin 3 → ℂ :=
  ![orbitLowCoefficient Q 2 0,
    orbitLowCoefficient Q 2 1,
    orbitLowCoefficient Q 2 2]

/-- The discriminant of the coefficient presentation of a binary
quadratic. -/
@[expose]
noncomputable def binaryQuadraticDiscriminant
    (Q : OrbitSourceForm) : ℂ :=
  binaryQuadraticCoefficients Q 1 ^ 2 -
    4 * binaryQuadraticCoefficients Q 0 *
      binaryQuadraticCoefficients Q 2

theorem binaryLinearForm_isHomogeneous (u v : ℂ) :
    (binaryLinearForm u v).IsHomogeneous 1 := by
  exact ((MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)).C_mul u).add
    ((MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2)).C_mul v)

theorem binaryQuadraticForm_isHomogeneous (a b c : ℂ) :
    (binaryQuadraticForm a b c).IsHomogeneous 2 := by
  have hs := MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)
  have hlambda := MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2)
  simpa [binaryQuadraticForm, orbitPolynomialS,
    orbitPolynomialLambda, mul_assoc] using
    ((hs.pow 2).C_mul a).add
      ((hs.mul hlambda).C_mul b) |>.add ((hlambda.pow 2).C_mul c)

private noncomputable def binaryQuadraticIterated
    (a b c : ℂ) : Polynomial (Polynomial ℂ) :=
  Polynomial.monomial 0 (Polynomial.monomial 2 a) +
    Polynomial.monomial 1 (Polynomial.monomial 1 b) +
      Polynomial.monomial 2 (Polynomial.C c)

private theorem eIteratedToForm_binaryQuadraticIterated
    (a b c : ℂ) :
    eIteratedToForm (binaryQuadraticIterated a b c) =
      binaryQuadraticForm a b c := by
  simp only [binaryQuadraticIterated, map_add,
    ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
    eIteratedToForm_innerX, eIteratedToForm_outerX]
  rw [show eIteratedToForm (Polynomial.C (Polynomial.C a)) =
      MvPolynomial.C a by exact eIteratedToForm.commutes a]
  rw [show eIteratedToForm (Polynomial.C (Polynomial.C b)) =
      MvPolynomial.C b by exact eIteratedToForm.commutes b]
  rw [show eIteratedToForm (Polynomial.C (Polynomial.C c)) =
      MvPolynomial.C c by exact eIteratedToForm.commutes c]
  simp only [pow_zero, mul_one]
  simp [binaryQuadraticForm, orbitPolynomialS,
    orbitPolynomialLambda, formX, formT]

private theorem eFormToIterated_eq_binaryQuadraticIterated
    {Q : OrbitSourceForm} (hQ : Q.IsHomogeneous 2) :
    eFormToIterated Q = binaryQuadraticIterated
      (binaryQuadraticCoefficients Q 0)
      (binaryQuadraticCoefficients Q 1)
      (binaryQuadraticCoefficients Q 2) := by
  ext i j
  rw [orbitFormToIterated_outerCoeff_of_homogeneous hQ]
  simp only [binaryQuadraticIterated, Polynomial.coeff_add,
    Polynomial.coeff_monomial]
  by_cases hi0 : i = 0
  · subst i
    simp [binaryQuadraticCoefficients, Polynomial.coeff_monomial]
  by_cases hi1 : i = 1
  · subst i
    simp [binaryQuadraticCoefficients, Polynomial.coeff_monomial]
  by_cases hi2 : i = 2
  · subst i
    by_cases hj : j = 0
    · subst j
      simp [binaryQuadraticCoefficients]
    · simp [binaryQuadraticCoefficients, Polynomial.coeff_C,
        hj, Ne.symm hj]
  have hi3 : 3 ≤ i := by omega
  have hlow : orbitLowCoefficient Q 2 i = 0 := by
    rw [orbitLowCoefficient]
    apply hQ.coeff_eq_zero
    simp [Finsupp.degree_eq_weight_one,
      Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two]
    omega
  rw [hlow]
  simp [Ne.symm hi0, Ne.symm hi1, Ne.symm hi2]

/-- Every homogeneous binary quadratic is recovered from its three
coefficients. -/
theorem eq_binaryQuadraticForm_of_isHomogeneous
    {Q : OrbitSourceForm} (hQ : Q.IsHomogeneous 2) :
    Q = binaryQuadraticForm
      (binaryQuadraticCoefficients Q 0)
      (binaryQuadraticCoefficients Q 1)
      (binaryQuadraticCoefficients Q 2) := by
  have hback : eIteratedToForm (eFormToIterated Q) = Q := by
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
      AlgHom.congr_fun eIteratedToForm_comp_formToIterated Q
  calc
    Q = eIteratedToForm (eFormToIterated Q) := hback.symm
    _ = eIteratedToForm (binaryQuadraticIterated
        (binaryQuadraticCoefficients Q 0)
        (binaryQuadraticCoefficients Q 1)
        (binaryQuadraticCoefficients Q 2)) := by
      rw [eFormToIterated_eq_binaryQuadraticIterated hQ]
    _ = binaryQuadraticForm
        (binaryQuadraticCoefficients Q 0)
        (binaryQuadraticCoefficients Q 1)
        (binaryQuadraticCoefficients Q 2) :=
      eIteratedToForm_binaryQuadraticIterated _ _ _

private theorem eFormToIterated_binaryQuadraticForm
    (a b c : ℂ) :
    eFormToIterated (binaryQuadraticForm a b c) =
      binaryQuadraticIterated a b c := by
  have hback : eFormToIterated
      (eIteratedToForm (binaryQuadraticIterated a b c)) =
        binaryQuadraticIterated a b c := by
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
      AlgHom.congr_fun eFormToIterated_comp_iteratedToForm
        (binaryQuadraticIterated a b c)
  rw [eIteratedToForm_binaryQuadraticIterated] at hback
  exact hback

@[simp]
theorem binaryQuadraticCoefficients_binaryQuadraticForm_zero
    (a b c : ℂ) :
    binaryQuadraticCoefficients (binaryQuadraticForm a b c) 0 = a := by
  rw [binaryQuadraticCoefficients]
  change orbitLowCoefficient (binaryQuadraticForm a b c) 2 0 = a
  rw [orbitLowCoefficient, ← orbitFormToIterated_coeff,
    eFormToIterated_binaryQuadraticForm]
  simp [binaryQuadraticIterated, Polynomial.coeff_monomial]

@[simp]
theorem binaryQuadraticCoefficients_binaryQuadraticForm_one
    (a b c : ℂ) :
    binaryQuadraticCoefficients (binaryQuadraticForm a b c) 1 = b := by
  rw [binaryQuadraticCoefficients]
  change orbitLowCoefficient (binaryQuadraticForm a b c) 2 1 = b
  rw [orbitLowCoefficient, ← orbitFormToIterated_coeff,
    eFormToIterated_binaryQuadraticForm]
  simp [binaryQuadraticIterated, Polynomial.coeff_monomial]

@[simp]
theorem binaryQuadraticCoefficients_binaryQuadraticForm_two
    (a b c : ℂ) :
    binaryQuadraticCoefficients (binaryQuadraticForm a b c) 2 = c := by
  rw [binaryQuadraticCoefficients]
  change orbitLowCoefficient (binaryQuadraticForm a b c) 2 2 = c
  rw [orbitLowCoefficient, ← orbitFormToIterated_coeff,
    eFormToIterated_binaryQuadraticForm]
  simp [binaryQuadraticIterated, Polynomial.coeff_monomial]

/-- A scalar multiple of a linear square has zero quadratic
discriminant. -/
theorem binaryQuadraticDiscriminant_C_mul_binaryLinearForm_sq
    (scalar u v : ℂ) :
    binaryQuadraticDiscriminant
      (MvPolynomial.C scalar * binaryLinearForm u v ^ 2) = 0 := by
  have hform : MvPolynomial.C scalar * binaryLinearForm u v ^ 2 =
      binaryQuadraticForm (scalar * u ^ 2)
        (2 * scalar * u * v) (scalar * v ^ 2) := by
    simp only [binaryLinearForm, binaryQuadraticForm, map_mul, map_pow,
      map_ofNat]
    ring
  rw [hform, binaryQuadraticDiscriminant]
  simp
  ring

theorem binaryLinearForm_ne_zero_of_coefficients
    {u v : ℂ} (hcoefficients : u ≠ 0 ∨ v ≠ 0) :
    binaryLinearForm u v ≠ 0 := by
  intro hzero
  rcases hcoefficients with hu | hv
  · have heval := congrArg (MvPolynomial.eval ![(1 : ℂ), 0]) hzero
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, binaryLinearForm,
      orbitPolynomialS, Fin.isValue, orbitPolynomialLambda, map_add,
      map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      Matrix.cons_val_zero, mul_one, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, mul_zero, add_zero, map_zero] at heval
    exact hu heval
  · have heval := congrArg (MvPolynomial.eval ![(0 : ℂ), 1]) hzero
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, binaryLinearForm,
      orbitPolynomialS, Fin.isValue, orbitPolynomialLambda, map_add,
      map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      Matrix.cons_val_zero, mul_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, mul_one, zero_add, map_zero] at heval
    exact hv heval

/-- A nonzero homogeneous binary quadratic with zero discriminant is a
nonzero scalar multiple of the square of a nonzero linear form. -/
theorem exists_scalar_mul_linear_sq_of_discriminant_eq_zero
    {Q : OrbitSourceForm} (hQ : Q.IsHomogeneous 2) (hQnonzero : Q ≠ 0)
    (hdiscriminant : binaryQuadraticDiscriminant Q = 0) :
    ∃ scalar u v : ℂ,
      scalar ≠ 0 ∧ (u ≠ 0 ∨ v ≠ 0) ∧
        Q = MvPolynomial.C scalar * binaryLinearForm u v ^ 2 := by
  let a := binaryQuadraticCoefficients Q 0
  let b := binaryQuadraticCoefficients Q 1
  let c := binaryQuadraticCoefficients Q 2
  have hpresentation : Q = binaryQuadraticForm a b c := by
    exact eq_binaryQuadraticForm_of_isHomogeneous hQ
  have hdisc : b ^ 2 - 4 * a * c = 0 := by
    simpa only [binaryQuadraticDiscriminant, a, b, c] using hdiscriminant
  by_cases ha : a = 0
  · rw [ha] at hdisc
    ring_nf at hdisc
    have hbSquare : b ^ 2 = 0 := hdisc
    have hb : b = 0 := sq_eq_zero_iff.mp hbSquare
    have hc : c ≠ 0 := by
      intro hc
      apply hQnonzero
      rw [hpresentation, ha, hb, hc]
      simp [binaryQuadraticForm]
    refine ⟨c, 0, 1, hc, Or.inr one_ne_zero, ?_⟩
    rw [hpresentation, ha, hb]
    simp [binaryQuadraticForm, binaryLinearForm]
  · have hcFormula : c = b ^ 2 / (4 * a) := by
      field_simp
      linear_combination -hdisc
    let v := b / (2 * a)
    have hcross : a * (2 * v) = b := by
      dsimp only [v]
      field_simp
    have hsquare : a * v ^ 2 = b ^ 2 / (4 * a) := by
      dsimp only [v]
      field_simp
      ring
    refine ⟨a, 1, b / (2 * a), ha, Or.inl one_ne_zero, ?_⟩
    rw [hpresentation, hcFormula]
    simp only [binaryQuadraticForm, binaryLinearForm]
    change _ = MvPolynomial.C a *
      (MvPolynomial.C 1 * orbitPolynomialS ℂ +
        MvPolynomial.C v * orbitPolynomialLambda ℂ) ^ 2
    have hcrossC := congrArg
      (MvPolynomial.C : ℂ →+* OrbitSourceForm) hcross
    have hsquareC := congrArg
      (MvPolynomial.C : ℂ →+* OrbitSourceForm) hsquare
    simp only [map_mul, map_ofNat, map_pow] at hcrossC hsquareC
    rw [show MvPolynomial.C (b ^ 2 / (4 * a)) =
        MvPolynomial.C a * MvPolynomial.C v ^ 2 by
      exact hsquareC.symm]
    rw [show MvPolynomial.C b =
        MvPolynomial.C a * (2 * MvPolynomial.C v) by
      exact hcrossC.symm]
    norm_num
    ring

end OnLeConjecture.DTwo
