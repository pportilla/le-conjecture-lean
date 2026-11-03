/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EInvariantExceptionalNoninjectivity
public import OnLeConjecture.DThree.EInvariantRegularContradiction

/-!
# Reduction of the invariant E branch to exceptional residual roots

The two residual cube coordinates cannot vanish simultaneously away from the
diagonal.  Consequently, the regular persistence argument settles every root
except a root at which exactly one residual coordinate vanishes.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- Away from the diagonal, at least one of the two residual coordinates is
nonzero. -/
theorem eResidualW_nonzero_or_swapped_nonzero
    (z : ℂ) (hz : z ≠ 1) :
    eResidualW z 1 ≠ 0 ∨ eResidualW 1 z ≠ 0 := by
  by_contra hboth
  have hfirstZero : eResidualW z 1 = 0 :=
    not_ne_iff.mp (fun hne ↦ hboth (Or.inl hne))
  have hsecondZero : eResidualW 1 z = 0 :=
    not_ne_iff.mp (fun hne ↦ hboth (Or.inr hne))
  have hfirst := e_residual_first_equation z (1 : ℂ)
  have hsecond := e_residual_second_equation z (1 : ℂ)
  rw [hfirstZero] at hfirst
  rw [hsecondZero] at hsecond
  have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have hquadraticFirst :
      (1 : ℂ) + 2 * z + 3 * z ^ 2 = 0 := by
    exact (mul_eq_zero.mp (by simpa using hfirst)).resolve_left hsub
  have hquadraticSecond :
      (3 : ℂ) + 2 * z + z ^ 2 = 0 := by
    exact (mul_eq_zero.mp (by simpa using hsecond)).resolve_left hsub
  have hone : (1 : ℂ) = 0 := by
    linear_combination
      (z / 12) * hquadraticFirst +
        (1 / 3 - z / 4) * hquadraticSecond
  exact one_ne_zero hone

theorem eResidualW_zero_implies_ne_zero
    (z : ℂ) (hw : eResidualW z 1 = 0) : z ≠ 0 := by
  intro hz
  subst z
  norm_num [eResidualW] at hw

theorem eResidualW_one_eq_scaled_inv
    (z : ℂ) (hz : z ≠ 0) :
    eResidualW 1 z = z ^ 3 * eResidualW z⁻¹ 1 := by
  simpa [hz] using eResidualW_common_scale z z⁻¹ 1

theorem eResidualW_eq_scaled_one_inv
    (z : ℂ) (hz : z ≠ 0) :
    eResidualW z 1 = z ^ 3 * eResidualW 1 z⁻¹ := by
  simpa [hz] using eResidualW_common_scale z 1 z⁻¹

/-- Symmetry and homogeneity transport an affine residual root to its
reciprocal. -/
theorem eThetaPolynomial_isRoot_inv
    (c : Fin 4 → EBaseRing ℂ) (n : ℕ) (z : ℂ)
    (hhomogeneous : EPairIsHomogeneous (eThetaPolynomial ℂ c) n)
    (hz : z ≠ 0)
    (hzRoot :
      (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot z) :
    (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot z⁻¹ := by
  have htheta :
      ePairPointEval ℂ z 1 (eThetaPolynomial ℂ c) = 0 := by
    calc
      ePairPointEval ℂ z 1 (eThetaPolynomial ℂ c) =
          MvPolynomial.eval ![z, 1]
            (eIteratedToForm (eThetaPolynomial ℂ c)) :=
        ePairPointEval_eq_eval_iteratedToForm
          (eThetaPolynomial ℂ c) z 1
      _ = (ePairDehomogenize (eThetaPolynomial ℂ c)).eval z :=
        (ePairDehomogenize_eval (eThetaPolynomial ℂ c) z).symm
      _ = 0 := hzRoot
  have hswap :
      ePairPointEval ℂ 1 z (eThetaPolynomial ℂ c) = 0 :=
    (eThetaPolynomial_pointEval_swap c z 1).trans htheta
  have hscaled := ePairPointEval_scaled_dehomogenize
    hhomogeneous z z⁻¹ hz
  change (ePairDehomogenize (eThetaPolynomial ℂ c)).eval z⁻¹ = 0
  have hproduct :
      z ^ n * (ePairDehomogenize (eThetaPolynomial ℂ c)).eval z⁻¹ =
        0 := by
    rw [← hscaled]
    simpa [hz] using hswap
  exact (mul_eq_zero.mp hproduct).resolve_left (pow_ne_zero n hz)

theorem inv_ne_one_of_ne_one
    (z : ℂ) (hz : z ≠ 0) (hzOne : z ≠ 1) : z⁻¹ ≠ 1 := by
  intro hinverse
  apply hzOne
  have hequal := congrArg (fun w : ℂ ↦ z * w) hinverse
  simpa [hz] using hequal.symm

/-- Under the invariant branch hypotheses, the weighted order contradiction
holds or the selected isolated residual root has exactly one zero residual
coordinate. -/
theorem eInvariantWeightedOrderTails_noninjective_or_exceptional_root
    {omega : ℂ} (R : Form ℂ) (N : ℕ)
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
            (eInvariantPolynomialMap R i) ∈
        Germ.weightedOrderIdeal 1 (eInvariantDegrees N i + 1)) :
    (¬ PointedMapGerm.HasInjectiveRepresentative
        (PointedMapGerm.ofPairFunction representative hanalytic hzero)) ∨
      ∃ Rzero : ESourceRing ℂ, ∃ c : Fin 4 → EBaseRing ℂ,
        ∃ z : ℂ,
          eSourceCubeSubstitutionForm Rzero = R ∧
          Rzero = ∑ i : Fin 4,
            eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ) ∧
          EPairIsHomogeneous (eThetaPolynomial ℂ c) (N - 1) ∧
          ePairDehomogenize (eThetaPolynomial ℂ c) ≠ 0 ∧
          (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot z ∧
          z ≠ 1 ∧
          ((eResidualW z 1 ≠ 0 ∧ eResidualW 1 z = 0) ∨
            (eResidualW z 1 = 0 ∧ eResidualW 1 z ≠ 0)) := by
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
  · right
    exact ⟨Rzero, c, z, hdescent, hdecomposition,
      hThetaHomogeneous, hp, hzRoot, hzOne, Or.inr
        ⟨hw, (eResidualW_nonzero_or_swapped_nonzero z hzOne).resolve_left
          (fun hne ↦ hne hw)⟩⟩
  · by_cases hW : eResidualW 1 z = 0
    · right
      exact ⟨Rzero, c, z, hdescent, hdecomposition,
        hThetaHomogeneous, hp, hzRoot, hzOne, Or.inl ⟨hw, hW⟩⟩
    · left
      exact eInvariantRegularWeightedOrderTails_not_hasInjectiveRepresentative
        Rzero R c (N - 1) N z hR hdescent hdecomposition
          hThetaHomogeneous hp hzRoot hzOne hw hW representative
            hanalytic hzero htail

/-- The invariant `E` branch with correction terms in the next ordinary
order ideals has no injective representative. -/
theorem eInvariantWeightedOrderTails_not_hasInjectiveRepresentative
    {omega : ℂ} (R : Form ℂ) (N : ℕ)
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
            (eInvariantPolynomialMap R i) ∈
        Germ.weightedOrderIdeal 1 (eInvariantDegrees N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  rcases eInvariantWeightedOrderTails_noninjective_or_exceptional_root
      R N homega hR hinvariant hdiv hnotbase representative hanalytic
        hzero htail with hnoninjective |
      ⟨Rzero, c, z, hdescent, hdecomposition, hThetaHomogeneous,
        hp, hzRoot, hzOne, hregular | hexceptional⟩
  · exact hnoninjective
  · exact eInvariantExceptionalWeightedOrderTails_not_hasInjectiveRepresentative
      Rzero R c (N - 1) N z hR hdescent hdecomposition
        hThetaHomogeneous hp hzRoot hzOne hregular.1 hregular.2
          representative hanalytic hzero htail
  · obtain ⟨hw, hW⟩ := hexceptional
    have hz : z ≠ 0 := eResidualW_zero_implies_ne_zero z hw
    have hzInvRoot :
        (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot z⁻¹ :=
      eThetaPolynomial_isRoot_inv c (N - 1) z hThetaHomogeneous hz hzRoot
    have hzInvOne : z⁻¹ ≠ 1 := inv_ne_one_of_ne_one z hz hzOne
    have hwInv : eResidualW z⁻¹ 1 ≠ 0 := by
      intro hzeroInv
      apply hW
      rw [eResidualW_one_eq_scaled_inv z hz, hzeroInv, mul_zero]
    have hWInv : eResidualW 1 z⁻¹ = 0 := by
      have hproduct : z ^ 3 * eResidualW 1 z⁻¹ = 0 := by
        calc
          z ^ 3 * eResidualW 1 z⁻¹ = eResidualW z 1 :=
            (eResidualW_eq_scaled_one_inv z hz).symm
          _ = 0 := hw
      exact (mul_eq_zero.mp hproduct).resolve_left (pow_ne_zero 3 hz)
    exact eInvariantExceptionalWeightedOrderTails_not_hasInjectiveRepresentative
      Rzero R c (N - 1) N z⁻¹ hR hdescent hdecomposition
        hThetaHomogeneous hp hzInvRoot hzInvOne hwInv hWInv
          representative hanalytic hzero htail

/-- Coefficient divisibility of the invariant correction terms implies the
weighted order hypotheses and excludes an injective representative. -/
theorem eInvariantWeightedCoefficientTails_not_hasInjectiveRepresentative
    {omega : ℂ} (R : Form ℂ) (N : ℕ)
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
      Germ.WeightedCoefficientDivisibility 1
        (eInvariantDegrees N i + 1)
        (pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (eInvariantPolynomialMap R i))) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  apply eInvariantWeightedOrderTails_not_hasInjectiveRepresentative
    R N homega hR hinvariant hdiv hnotbase representative hanalytic hzero
  intro i
  exact Germ.mem_weightedOrderIdeal_of_weightedCoefficientDivisibility
    1 (eInvariantDegrees N i + 1) (by simp) _ (htail i)

end OnLeConjecture.DThree
