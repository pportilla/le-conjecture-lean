/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HHardOddNoninjectivity
public import OnLeConjecture.DThree.HResidueZeroOrdinaryBranchPersistence
public import OnLeConjecture.DThree.HResidueZeroZeroSecondPersistence

/-!
# Odd hard H branch with residue zero

The hard norm alternatives produce ordinary analytic source branch data in
one of two affine charts. Both chart types persist after an arbitrary positive
power substitution in the second source coordinate.
-/

public section

noncomputable section

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

/-- An odd hard H decomposition followed by a positive power substitution is
incompatible with an injective representative under the next weighted order
tail conditions. -/
theorem hHardOddResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
    (a : ℕ) (ha : 0 < a)
    (R Rzero : Form ℂ) (coefficient : ℂ) (N : ℕ)
    (hR : R.IsHomogeneous N)
    (hdecomposition :
      R = hQuadraticSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N)
    (hNodd : Odd N) (hcoefficient : coefficient ≠ 0)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (hResidueZeroPolynomialMap a R i) ∈
        Germ.weightedOrderIdeal a
          (hQuadraticWeightedDegrees a N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  have hRzero : Rzero.IsWeightedHomogeneous hFormWeight N :=
    hHardOddDecomposition.Rzero_isWeightedHomogeneous hR hdecomposition
  by_cases hdifference : hConicDifference Rzero = 0
  · obtain ⟨data⟩ :=
      exists_hHardOddOrdinarySourceBranchData_of_reciprocal_norm_zero
        R Rzero coefficient N hR hdecomposition hNodd
          (h_reciprocal_hHardOddNorm_ne_zero_of_conicDifference_eq_zero
            Rzero coefficient N hNodd hcoefficient hdifference)
          (h_reciprocal_hHardOddNorm_eval_zero_of_conicDifference_eq_zero
            Rzero coefficient N hdifference)
    exact
      hOrdinarySourceBranchResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
        a N ha R hR data representative hanalytic hzero htail
  obtain ⟨numerator, hnumerator, _hdegree, hrepresentation,
      hdrop | ⟨z, hzPlus, hzMinus, hroot⟩⟩ :=
    exists_hHardOddNorm_numerator_zero_away_or_degree_drop
      Rzero coefficient N hNodd hcoefficient hRzero hdifference
  · have hdegreeProfile :
        numerator.natDegree < 2 * N + 2 * (4 * N) := by
      omega
    obtain ⟨order, horder, horderInfinity⟩ :=
      h_order_at_infinity_positive_of_pole_profile_degree_drop
        (2 * N) (4 * N) hnumerator hdegreeProfile hrepresentation
    have horderZero :
        hFiniteOrderAt (0 : ℂ)
            (hReciprocalRatFuncRingHom
              (hHardOddNorm Rzero coefficient N)) =
          WithZero.exp (order : ℤ) := by
      rw [h_finite_order_reciprocalRatFuncRingHom]
      exact horderInfinity
    have hnormNe : hReciprocalRatFuncRingHom
        (hHardOddNorm Rzero coefficient N) ≠ 0 :=
      h_ratFunc_ne_zero_of_finite_order horderZero
    have hnormZero : RatFunc.eval (RingHom.id ℂ) 0
        (hReciprocalRatFuncRingHom
          (hHardOddNorm Rzero coefficient N)) = 0 :=
      h_ratFunc_eval_eq_zero_of_finite_order_pos
        0 (hReciprocalRatFuncRingHom
          (hHardOddNorm Rzero coefficient N)) order horder horderZero
    obtain ⟨data⟩ :=
      exists_hHardOddOrdinarySourceBranchData_of_reciprocal_norm_zero
        R Rzero coefficient N hR hdecomposition hNodd hnormNe hnormZero
    exact
      hOrdinarySourceBranchResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
        a N ha R hR data representative hanalytic hzero htail
  by_cases hprofile :
      (hPoleProfileDenominator (K := ℂ) (2 * N) (4 * N)).eval z = 0
  · rcases h_pole_profile_denominator_root_classification
      (2 * N) (4 * N) z hprofile with hpole | hboundary
    · subst z
      exact (not_hHardOddNorm_numerator_isRoot_pole
        Rzero coefficient N hNodd hcoefficient hRzero numerator
          hrepresentation hroot).elim
    · have hz : z ^ 2 + 2 = 0 := by
        simpa [hConicParamDenominator] using hboundary
      obtain ⟨data⟩ :=
        exists_hHardOddOrdinarySourceBranchData_of_finite_boundary_root
          R Rzero coefficient N hR hdecomposition hNodd hRzero numerator
            hnumerator z hz hroot hrepresentation
      exact
        hOrdinarySourceBranchResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
          a N ha R hR data representative hanalytic hzero htail
  have hNpos : 0 < N := hNodd.pos
  obtain ⟨hlinear, hden⟩ := h_pole_profile_factors_ne_zero
    (2 * N) (4 * N) (by omega) (by omega) z hprofile
  have hfunction := h_regular_function_denominator_ne_zero hlinear hden
  have hone := h_conic_one_factor_ne_zero_of_away_from_roots
    hConicOneRootPlus hConicOneRootMinus z
      h_conic_one_roots_equations.1 h_conic_one_roots_equations.2
        h_conic_one_roots_ne hzPlus hzMinus
  have hnotBoth :
      hRegularProfileW z 0 ≠ 0 ∨
        hRegularProfileCapitalW z 0 ≠ 0 := by
    rcases h_conic_param_second_factors_not_both_zero z with
      hWFactor | hCapitalWFactor
    · left
      have hnumeratorW :
          (-hConicParamOneFactor * hConicParamWFactor).eval z ≠ 0 := by
        rw [Polynomial.eval_mul, Polynomial.eval_neg]
        exact mul_ne_zero (neg_ne_zero.mpr hone) hWFactor
      have hquotient := div_ne_zero hnumeratorW hfunction
      simpa [hRegularProfileW, hRegularProfileParameter] using hquotient
    · right
      have hnumeratorCapitalW :
          (-hConicParamOneFactor * hConicParamCapitalWFactor).eval z ≠ 0 := by
        rw [Polynomial.eval_mul, Polynomial.eval_neg]
        exact mul_ne_zero (neg_ne_zero.mpr hone) hCapitalWFactor
      have hquotient := div_ne_zero hnumeratorCapitalW hfunction
      simpa [hRegularProfileCapitalW, hRegularProfileParameter]
        using hquotient
  rcases hnotBoth with hW | hCapitalW
  · by_cases hCapitalWZero : hRegularProfileCapitalW z 0 = 0
    · obtain ⟨data⟩ :=
        exists_hHardOddZeroSecondSourceBranchData_of_capitalW_norm_root
          R Rzero coefficient N hR hdecomposition hNodd numerator hnumerator
            z hroot hlinear hden hprofile hW hCapitalWZero hrepresentation
      exact
        hOrdinaryZeroSecondResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
          a N ha R hR data representative hanalytic hzero htail
    · have hX : hRegularProfileX z 0 ≠ 1 := by
        rw [h_regular_profile_X_eq_eval z 0 (by simpa using hden)]
        simpa using h_conic_param_eval_x_ne_one
          h_conic_one_roots_equations.1 h_conic_one_roots_equations.2
            h_conic_one_roots_ne hzPlus hzMinus hden
      obtain ⟨data⟩ :=
        exists_hHardOddOrdinarySourceBranchData_of_regular_norm_root
          R Rzero coefficient N hR hdecomposition hNodd numerator hnumerator
            z hroot hlinear hden hprofile hW hCapitalWZero hX hrepresentation
      exact
        hOrdinarySourceBranchResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
          a N ha R hR data representative hanalytic hzero htail
  · by_cases hWZero : hRegularProfileW z 0 = 0
    · obtain ⟨data⟩ :=
        exists_hHardOddZeroSecondSourceBranchData_of_W_norm_root
          R Rzero coefficient N hR hdecomposition hNodd numerator hnumerator
            z hroot hlinear hden hprofile hWZero hCapitalW hrepresentation
      exact
        hOrdinaryZeroSecondResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
          a N ha R hR data representative hanalytic hzero htail
    · have hX : hRegularProfileX z 0 ≠ 1 := by
        rw [h_regular_profile_X_eq_eval z 0 (by simpa using hden)]
        simpa using h_conic_param_eval_x_ne_one
          h_conic_one_roots_equations.1 h_conic_one_roots_equations.2
            h_conic_one_roots_ne hzPlus hzMinus hden
      obtain ⟨data⟩ :=
        exists_hHardOddOrdinarySourceBranchData_of_regular_norm_root
          R Rzero coefficient N hR hdecomposition hNodd numerator hnumerator
            z hroot hlinear hden hprofile hWZero hCapitalW hX hrepresentation
      exact
        hOrdinarySourceBranchResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
          a N ha R hR data representative hanalytic hzero htail

end OnLeConjecture.DThree
