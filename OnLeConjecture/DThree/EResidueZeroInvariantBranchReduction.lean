/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EResidueZeroInvariantExceptional
public import OnLeConjecture.DThree.EResidueZeroInvariantRegular

/-!
# Invariant E residue zero branch

The projective residual zero supplied by the invariant E argument is placed
in either a regular chart or an exceptional chart. The reciprocal symmetry
interchanges the two exceptional orientations.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- The invariant E branch with residue zero and correction terms in the next
weighted order ideals has no injective representative. -/
theorem eInvariantResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
    {omega : ℂ} (a N : ℕ) (ha : 0 < a)
    (R : Form ℂ)
    (homega : IsPrimitiveRoot omega 3)
    (hR : R.IsHomogeneous N)
    (hinvariant : R = eRotateForm omega R)
    (hdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian (cubicForm 0 3) R)
    (hnotbase : ∀ Rzero : ESourceRing ℂ,
      eSourceCubeSubstitutionForm Rzero = R →
        Rzero ∉ Set.range (eBaseToSource ℂ))
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (eResidueZeroPolynomialMap a R i) ∈
        Germ.weightedOrderIdeal a
          (eResidueZeroDegrees a N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨Rzero, c, hdescent, hdecomposition, hThetaHomogeneous,
      _, hThetaNe, x, X, hprojective, hThetaZero, hxX⟩ :=
    exists_e_invariant_nonzero_residual_off_diagonal_projective_zero
      R N homega hR hinvariant hdiv hnotbase
  obtain ⟨z, hzRoot, hzOne⟩ :=
    exists_eThetaPolynomial_affine_root c (N - 1)
      hThetaHomogeneous x X hprojective hThetaZero hxX
  have hp : ePairDehomogenize (eThetaPolynomial ℂ c) ≠ 0 :=
    ePairDehomogenize_ne_zero hThetaHomogeneous hThetaNe
  by_cases hw : eResidualW z 1 = 0
  · have hz : z ≠ 0 := eResidualW_zero_implies_ne_zero z hw
    have hzInvRoot :
        (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot z⁻¹ :=
      eThetaPolynomial_isRoot_inv c (N - 1) z hThetaHomogeneous hz hzRoot
    have hzInvOne : z⁻¹ ≠ 1 := inv_ne_one_of_ne_one z hz hzOne
    have hwInv : eResidualW z⁻¹ 1 ≠ 0 := by
      intro hzeroInv
      have hsecond : eResidualW 1 z = 0 := by
        rw [eResidualW_one_eq_scaled_inv z hz, hzeroInv, mul_zero]
      exact (eResidualW_nonzero_or_swapped_nonzero z hzOne).resolve_left
        (fun hne ↦ hne hw) hsecond
    have hWInv : eResidualW 1 z⁻¹ = 0 := by
      have hproduct : z ^ 3 * eResidualW 1 z⁻¹ = 0 := by
        calc
          z ^ 3 * eResidualW 1 z⁻¹ = eResidualW z 1 :=
            (eResidualW_eq_scaled_one_inv z hz).symm
          _ = 0 := hw
      exact (mul_eq_zero.mp hproduct).resolve_left (pow_ne_zero 3 hz)
    exact
      eInvariantExceptionalResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
        a ha Rzero R c (N - 1) N z⁻¹ hR hdescent hdecomposition
          hThetaHomogeneous hp hzInvRoot hzInvOne hwInv hWInv
            representative hanalytic hzero htail
  · by_cases hW : eResidualW 1 z = 0
    · exact
        eInvariantExceptionalResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
          a ha Rzero R c (N - 1) N z hR hdescent hdecomposition
            hThetaHomogeneous hp hzRoot hzOne hw hW representative
              hanalytic hzero htail
    · exact
        eInvariantRegularResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
          a ha Rzero R c (N - 1) N z hR hdescent hdecomposition
            hThetaHomogeneous hp hzRoot hzOne hw hW representative
              hanalytic hzero htail

end OnLeConjecture.DThree
