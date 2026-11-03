/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HNoninvariantReflection
public import OnLeConjecture.DThree.EThetaHomogeneous

/-!
# Homogeneity after quadratic descent

This module recovers weighted homogeneity of a polynomial in `x,w` from
ordinary homogeneity after the substitution `w = t^2`. It also applies the
result to the odd decomposition supplied by reflection on the H line.
-/

public section

noncomputable section

namespace OnLeConjecture.DThree

open _root_.Polynomial

/-- The two inverse iterated presentations use the same two multivariate
variables. -/
theorem hIteratedToWeightedForm_eq_eIteratedToForm :
    hIteratedToWeightedForm (K := ℂ) = eIteratedToForm := by
  apply Polynomial.algHom_ext'
  · apply Polynomial.algHom_ext
    change hIteratedToWeightedForm (K := ℂ) (C X) =
      eIteratedToForm (C X)
    rw [hIteratedToWeightedForm_innerX, eIteratedToForm_innerX]
    rfl
  · change hIteratedToWeightedForm (K := ℂ) X = eIteratedToForm X
    rw [hIteratedToWeightedForm_outerX, eIteratedToForm_outerX]
    rfl

/-- Coefficients in the iterated presentation agree with coefficients in the
two variable weighted presentation. -/
theorem hIteratedToWeightedForm_coeff
    (S : HIteratedWeightedRing ℂ) (a b : ℕ) :
    MvPolynomial.coeff (eFormExponent a b)
        (hIteratedToWeightedForm S) =
      (S.coeff b).coeff a := by
  rw [hIteratedToWeightedForm_eq_eIteratedToForm]
  exact eIteratedToForm_coeff S a b

/-- Ordinary homogeneity after `w = t^2` implies weighted homogeneity with
weights one and two before substitution. -/
theorem isWeightedHomogeneous_of_hQuadraticSubstitutionForm_isHomogeneous
    {Rzero : MvPolynomial (Fin 2) ℂ} {N : ℕ}
    (hhomogeneous :
      (hQuadraticSubstitutionForm Rzero).IsHomogeneous N) :
    Rzero.IsWeightedHomogeneous hFormWeight N := by
  let S : HIteratedWeightedRing ℂ := hWeightedFormToIterated Rzero
  have hback : hIteratedToWeightedForm S = Rzero := by
    simpa only [S, AlgHom.comp_apply, AlgHom.id_apply] using
      AlgHom.congr_fun
        hIteratedToWeightedForm_comp_weightedFormToIterated Rzero
  have hsubstitution :
      eIteratedToForm (Polynomial.expand (Polynomial ℂ) 2 S) =
        hQuadraticSubstitutionForm Rzero := by
    calc
      eIteratedToForm (Polynomial.expand (Polynomial ℂ) 2 S) =
          eIteratedToForm (hIteratedSquareEvaluation S) := by
        change eIteratedToForm (Polynomial.expand (Polynomial ℂ) 2 S) =
          eIteratedToForm (S.eval₂ C (X ^ 2))
        rw [Polynomial.expand_eq_comp_X_pow]
        rfl
      _ = hQuadraticSubstitutionForm (hIteratedToWeightedForm S) :=
        (hQuadraticSubstitution_iteratedToWeightedForm S).symm
      _ = hQuadraticSubstitutionForm Rzero := by rw [hback]
  intro d hd
  have hcoefficientS : (S.coeff (d 1)).coeff (d 0) ≠ 0 := by
    rw [← hIteratedToWeightedForm_coeff S (d 0) (d 1),
      eFormExponent_apply, hback]
    exact hd
  have houter :
      (Polynomial.expand (Polynomial ℂ) 2 S).coeff (d 1 * 2) =
        S.coeff (d 1) :=
    Polynomial.coeff_expand_mul (by norm_num) S (d 1)
  have hcoefficient :
      MvPolynomial.coeff (eFormExponent (d 0) (d 1 * 2))
          (hQuadraticSubstitutionForm Rzero) ≠ 0 := by
    have hformula := eIteratedToForm_coeff
      (Polynomial.expand (Polynomial ℂ) 2 S) (d 0) (d 1 * 2)
    rw [hsubstitution, houter] at hformula
    exact hformula.symm ▸ hcoefficientS
  have hdegree := hhomogeneous hcoefficient
  rw [h_form_weight_apply]
  have hsum :
      (eFormExponent (d 0) (d 1 * 2)).sum (fun _ e ↦ e) = N := by
    simpa [Finsupp.weight_apply] using hdegree
  rw [Finsupp.sum_fintype] at hsum
  · rw [Fin.sum_univ_two, eFormExponent_zero,
      eFormExponent_one] at hsum
    omega
  · intro i
    rfl

/-- In an odd hard decomposition of an ordinarily homogeneous form, the
descended summand is weighted homogeneous of the same degree. -/
theorem hHardOddDecomposition.Rzero_isWeightedHomogeneous
    {R : Form ℂ} {Rzero : MvPolynomial (Fin 2) ℂ}
    {coefficient : ℂ} {N : ℕ}
    (hhomogeneous : R.IsHomogeneous N)
    (hdecomposition :
      R = hQuadraticSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N) :
    Rzero.IsWeightedHomogeneous hFormWeight N := by
  have ht : (formT : Form ℂ).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X ℂ 1
  have hpure :
      (MvPolynomial.C coefficient * formT ^ N).IsHomogeneous N :=
    by simpa using (ht.pow N).C_mul coefficient
  have hsubstitution :
      (hQuadraticSubstitutionForm Rzero).IsHomogeneous N := by
    have hequality :
        hQuadraticSubstitutionForm Rzero =
          R - MvPolynomial.C coefficient * formT ^ N := by
      rw [hdecomposition]
      ring
    rw [hequality]
    exact hhomogeneous.sub hpure
  exact
    isWeightedHomogeneous_of_hQuadraticSubstitutionForm_isHomogeneous
      hsubstitution

end OnLeConjecture.DThree
