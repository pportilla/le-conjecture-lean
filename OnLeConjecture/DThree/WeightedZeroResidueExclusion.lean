/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ResidueZeroPointedMap
public import OnLeConjecture.DThree.WeightedAnalyticRescaling
public import OnLeConjecture.DThree.WeightedPowerJacobianDescent

/-!
# Exclusion of classified forms with zero residue

When the weighted degree is divisible by the first source weight, the third
form is obtained from an ordinary homogeneous form by a power substitution.
Weighted Jacobian divisibility descends to the ordinary fifth power
divisibility. A weighted exclusion from the relevant base ring descends with
it.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- A normalized E weighted map with zero residue is incompatible with an
injective representative under weighted base exclusion and Jacobian
divisibility. -/
theorem eWeightedZeroResiduePointedMap_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3)
    (a D : ℕ) (ha : 0 < a)
    (P : Form ℂ) (hP : P.IsWeightedHomogeneous ![a, 1] D)
    (hresidue : D % a = 0)
    (hdiv : formT ^ (6 * a - 1) ∣
      OnLeConjecture.Polynomial.jacobian
        (weightedCubicPolynomial a 0 3) P)
    (hnotbase : ∀ S : ESourceRing ℂ,
      S ∈ Set.range (eBaseToSource ℂ) →
        weightedPowerSubstitutionForm a
          (eSourceCubeSubstitutionForm S) ≠ P)
    (htailZero :
      g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
          (weightedCubicPolynomial a 0 3) ∈
        Germ.weightedOrderIdeal a (3 * a + 1))
    (htailOne :
      g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
          (weightedQuarticPolynomial a 1 0 0 4 0) ∈
        Germ.weightedOrderIdeal a (4 * a + 1))
    (htailTwo :
      g.1.component 2 - Germ.coordinatePolynomialAlgHom 2 P ∈
        Germ.weightedOrderIdeal a (D + 1)) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨R, hR, hdecomposition⟩ :=
    exists_weightedPowerSubstitutionForm_of_residue_eq_zero
      a D ha P hP hresidue
  have hordinaryDiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian (cubicForm 0 3) R := by
    apply formT_five_dvd_jacobian_of_weighted_substitution_divisibility
      a ha (cubicForm 0 3) R
    rw [← weightedCubicPolynomial_eq_weightedPowerSubstitutionForm,
      ← hdecomposition]
    exact hdiv
  have hordinaryNotbase : ∀ S : ESourceRing ℂ,
      eSourceCubeSubstitutionForm S = R →
        S ∉ Set.range (eBaseToSource ℂ) := by
    intro S hS hSbase
    apply hnotbase S hSbase
    rw [hS]
    exact hdecomposition.symm
  let omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)
  have homega : IsPrimitiveRoot omega 3 :=
    Complex.isPrimitiveRoot_exp 3 (by norm_num)
  apply eResidueZeroPointedMap_not_hasInjectiveRepresentative
    g a (D / a) ha R homega hR hordinaryDiv
      hordinaryNotbase
  intro i
  fin_cases i
  · simpa [eResidueZeroPolynomialMap, eInvariantPolynomialMap,
      eResidueZeroDegrees,
      weightedCubicPolynomial_eq_weightedPowerSubstitutionForm]
      using htailZero
  · simpa [eResidueZeroPolynomialMap, eInvariantPolynomialMap,
      eResidueZeroDegrees,
      weightedQuarticPolynomial_eq_weightedPowerSubstitutionForm]
      using htailOne
  · have hdegree : (D / a) * a = D := by
      calc
        (D / a) * a = a * (D / a) := Nat.mul_comm _ _
        _ = D % a + a * (D / a) := by simp [hresidue]
        _ = D := Nat.mod_add_div D a
    simpa [eResidueZeroPolynomialMap, eInvariantPolynomialMap,
      hdecomposition, eResidueZeroDegrees, hdegree] using htailTwo

/-- A normalized H weighted map with zero residue is incompatible with an
injective representative under weighted base exclusion and the two weighted
Jacobian divisibilities. -/
theorem hWeightedZeroResiduePointedMap_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3)
    (a D : ℕ) (ha : 0 < a) (hdegreeFive : 5 ≤ D / a)
    (P : Form ℂ) (hP : P.IsWeightedHomogeneous ![a, 1] D)
    (hresidue : D % a = 0)
    (hPdiv : formT ^ (6 * a - 1) ∣
      OnLeConjecture.Polynomial.jacobian
        (weightedCubicPolynomial a 3 0) P)
    (hQdiv : formT ^ (6 * a - 1) ∣
      OnLeConjecture.Polynomial.jacobian
        (weightedQuarticPolynomial a 1 0 4 0 2) P)
    (hnotbase : ∀ S : Form ℂ,
      S ∈ Set.range (hBaseToWeightedForm ℂ) →
        weightedPowerSubstitutionForm a
          (hQuadraticSubstitutionForm S) ≠ P)
    (htailZero :
      g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
          (weightedCubicPolynomial a 3 0) ∈
        Germ.weightedOrderIdeal a (3 * a + 1))
    (htailOne :
      g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
          (weightedQuarticPolynomial a 1 0 4 0 2) ∈
        Germ.weightedOrderIdeal a (4 * a + 1))
    (htailTwo :
      g.1.component 2 - Germ.coordinatePolynomialAlgHom 2 P ∈
        Germ.weightedOrderIdeal a (D + 1)) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨R, hR, hdecomposition⟩ :=
    exists_weightedPowerSubstitutionForm_of_residue_eq_zero
      a D ha P hP hresidue
  have hordinaryPDiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian (cubicForm 3 0) R := by
    apply formT_five_dvd_jacobian_of_weighted_substitution_divisibility
      a ha (cubicForm 3 0) R
    rw [← weightedCubicPolynomial_eq_weightedPowerSubstitutionForm,
      ← hdecomposition]
    exact hPdiv
  have hordinaryQDiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (quarticForm 1 0 4 0 2) R := by
    apply formT_five_dvd_jacobian_of_weighted_substitution_divisibility
      a ha (quarticForm 1 0 4 0 2) R
    rw [← weightedQuarticPolynomial_eq_weightedPowerSubstitutionForm,
      ← hdecomposition]
    exact hQdiv
  have hordinaryNotbase : ∀ S : Form ℂ,
      hQuadraticSubstitutionForm S = R →
        S ∉ Set.range (hBaseToWeightedForm ℂ) := by
    intro S hS hSbase
    apply hnotbase S hSbase
    rw [hS]
    exact hdecomposition.symm
  apply hResidueZeroPointedMap_not_hasInjectiveRepresentative
    g a (D / a) ha hdegreeFive R hR hordinaryNotbase
      hordinaryPDiv hordinaryQDiv
  intro i
  fin_cases i
  · simpa [hResidueZeroPolynomialMap, hOrdinaryPolynomialMap,
      hQuadraticWeightedDegrees,
      weightedCubicPolynomial_eq_weightedPowerSubstitutionForm]
      using htailZero
  · simpa [hResidueZeroPolynomialMap, hOrdinaryPolynomialMap,
      hQuadraticWeightedDegrees,
      weightedQuarticPolynomial_eq_weightedPowerSubstitutionForm]
      using htailOne
  · have hdegree : (D / a) * a = D := by
      calc
        (D / a) * a = a * (D / a) := Nat.mul_comm _ _
        _ = D % a + a * (D / a) := by simp [hresidue]
        _ = D := Nat.mod_add_div D a
    simpa [hResidueZeroPolynomialMap, hOrdinaryPolynomialMap,
      hdecomposition, hQuadraticWeightedDegrees, hdegree] using htailTwo

end OnLeConjecture.DThree
