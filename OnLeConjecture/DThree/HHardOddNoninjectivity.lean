/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HHardOddExceptionalBranch
public import OnLeConjecture.DThree.HExceptionalProfileNoninjectivity

/-!
# Ordinary noninjectivity for the odd hard H decomposition

The hard norm root count is combined with analytic source branches at every
possible parameter. This includes parameter infinity, the finite boundary,
both regular charts, and both transverse zero coordinate charts.
-/

public section

noncomputable section

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

/-- An odd hard decomposition with nonzero odd coefficient is incompatible
with an injective representative under ordinary maximal ideal tails. -/
theorem hHardOddMaximalIdealTails_not_hasInjectiveRepresentative
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
            (hOrdinaryPolynomialMap R i) ∈
        Germ.maximalIdeal 2 ^ (hOrdinaryDegrees N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  have hRzero : Rzero.IsWeightedHomogeneous hFormWeight N :=
    hHardOddDecomposition.Rzero_isWeightedHomogeneous hR hdecomposition
  by_cases hdifference : hConicDifference Rzero = 0
  · exact
      hHardOddConicDifferenceZeroMaximalIdealTails_not_hasInjectiveRepresentative
        R Rzero coefficient N hR hdecomposition hNodd hcoefficient
          hdifference representative hanalytic hzero htail
  obtain ⟨numerator, hnumerator, _hdegree, hrepresentation,
      hdrop | ⟨z, hzPlus, hzMinus, hroot⟩⟩ :=
    exists_hHardOddNorm_numerator_zero_away_or_degree_drop
      Rzero coefficient N hNodd hcoefficient hRzero hdifference
  · exact
      hHardOddNormDegreeDropMaximalIdealTails_not_hasInjectiveRepresentative
        R Rzero coefficient N hR hdecomposition hNodd numerator hnumerator
          hdrop hrepresentation representative hanalytic hzero htail
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
      exact
        hHardOddFiniteBoundaryMaximalIdealTails_not_hasInjectiveRepresentative
          R Rzero coefficient N hR hdecomposition hNodd hRzero numerator
            hnumerator z hz hroot hrepresentation representative hanalytic
              hzero htail
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
          (-hConicParamOneFactor *
              hConicParamCapitalWFactor).eval z ≠ 0 := by
        rw [Polynomial.eval_mul, Polynomial.eval_neg]
        exact mul_ne_zero (neg_ne_zero.mpr hone) hCapitalWFactor
      have hquotient := div_ne_zero hnumeratorCapitalW hfunction
      simpa [hRegularProfileCapitalW, hRegularProfileParameter]
        using hquotient
  rcases hnotBoth with hW | hCapitalW
  · by_cases hCapitalWZero : hRegularProfileCapitalW z 0 = 0
    · exact
        hHardOddCapitalWZeroNormRootMaximalIdealTails_not_hasInjectiveRepresentative
          R Rzero coefficient N hR hdecomposition hNodd numerator hnumerator
            z hroot hlinear hden hprofile hW hCapitalWZero hrepresentation
              representative hanalytic hzero htail
    · exact
        hHardOddRegularFiniteRootMaximalIdealTails_not_hasInjectiveRepresentative
          R Rzero coefficient N hR hdecomposition hNodd numerator hnumerator
            z hroot hzPlus hzMinus hprofile hW hCapitalWZero
              hrepresentation representative hanalytic hzero htail
  · by_cases hWZero : hRegularProfileW z 0 = 0
    · exact
        hHardOddWZeroNormRootMaximalIdealTails_not_hasInjectiveRepresentative
          R Rzero coefficient N hR hdecomposition hNodd numerator hnumerator
            z hroot hlinear hden hprofile hWZero hCapitalW hrepresentation
              representative hanalytic hzero htail
    · exact
        hHardOddRegularFiniteRootMaximalIdealTails_not_hasInjectiveRepresentative
          R Rzero coefficient N hR hdecomposition hNodd numerator hnumerator
            z hroot hzPlus hzMinus hprofile hWZero hCapitalW
              hrepresentation representative hanalytic hzero htail

end OnLeConjecture.DThree
