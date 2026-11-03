/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HExceptionalProfileSource
public import OnLeConjecture.DThree.HRegularProfileNoninjectivity

/-!
# Noninjectivity at every regular H profile root

The two zero coordinate cases use the transverse chart.  The remaining case
uses the regular chart where both weighted second coordinates are nonzero.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

/-- A profile root with zero second weighted coordinate excludes injectivity
through every analytic weighted order tail. -/
theorem
    hCapitalWZeroProfileRootWeightedOrderTails_not_hasInjectiveRepresentative
    (a N : ℕ) (ha : 0 < a)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (p : ℂ[X]) (hp : p ≠ 0) (z : ℂ) (hz : p.IsRoot z)
    (hlinear : z + 1 ≠ 0)
    (hden : hConicParamDenominator.eval z ≠ 0)
    (hW : hRegularProfileW z 0 ≠ 0)
    (hCapitalW : hRegularProfileCapitalW z 0 = 0)
    (hrepresentation :
      hConicDifference R =
        algebraMap ℂ[X] (RatFunc ℂ) p /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (N / 2) N))
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (hQuadraticWeightedPolynomialMap a R i) ∈
        Germ.weightedOrderIdeal a
          (hQuadraticWeightedDegrees a N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨data⟩ :=
    exists_hZeroSecondSourceBranchData_of_capitalW_profile_root
      a N ha R hR p hp z hz hlinear hden hW hCapitalW hrepresentation
  exact hZeroSecondWeightedOrderTails_not_hasInjectiveRepresentative
    a N ha R hR data representative hanalytic hzero htail

/-- A profile root with zero first weighted coordinate excludes injectivity
after interchanging the two fibre points. -/
theorem hWZeroProfileRootWeightedOrderTails_not_hasInjectiveRepresentative
    (a N : ℕ) (ha : 0 < a)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (p : ℂ[X]) (hp : p ≠ 0) (z : ℂ) (hz : p.IsRoot z)
    (hlinear : z + 1 ≠ 0)
    (hden : hConicParamDenominator.eval z ≠ 0)
    (hW : hRegularProfileW z 0 = 0)
    (hCapitalW : hRegularProfileCapitalW z 0 ≠ 0)
    (hrepresentation :
      hConicDifference R =
        algebraMap ℂ[X] (RatFunc ℂ) p /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (N / 2) N))
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (hQuadraticWeightedPolynomialMap a R i) ∈
        Germ.weightedOrderIdeal a
          (hQuadraticWeightedDegrees a N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨data⟩ := exists_hZeroSecondSourceBranchData_of_W_profile_root
    a N ha R hR p hp z hz hlinear hden hW hCapitalW hrepresentation
  exact hZeroSecondWeightedOrderTails_not_hasInjectiveRepresentative
    a N ha R hR data representative hanalytic hzero htail

theorem h_conic_one_factor_ne_zero_of_away_from_roots
    (alpha beta z : ℂ)
    (halpha : alpha ^ 2 + 2 * alpha + 4 = 0)
    (hbeta : beta ^ 2 + 2 * beta + 4 = 0)
    (halphaBeta : alpha ≠ beta)
    (hzAlpha : z ≠ alpha) (hzBeta : z ≠ beta) :
    hConicParamOneFactor.eval z ≠ 0 := by
  have hproduct :
      (alpha - beta) * (alpha + beta + 2) = 0 := by
    linear_combination halpha - hbeta
  have hsum : alpha + beta + 2 = 0 :=
    (mul_eq_zero.mp hproduct).resolve_left (sub_ne_zero.mpr halphaBeta)
  have hab : alpha * beta - 4 = 0 := by
    linear_combination alpha * hsum - halpha
  have hfactor :
      (z - alpha) * (z - beta) = z ^ 2 + 2 * z + 4 := by
    linear_combination -z * hsum + hab
  intro hone
  have hz : z ^ 2 + 2 * z + 4 = 0 := by
    simpa [hConicParamOneFactor] using hone
  have hzero : (z - alpha) * (z - beta) = 0 := by
    rw [hfactor, hz]
  rcases mul_eq_zero.mp hzero with hza | hzb
  · exact hzAlpha (sub_eq_zero.mp hza)
  · exact hzBeta (sub_eq_zero.mp hzb)

/-- Every finite profile numerator root away from the two points above
`X = 1` excludes an injective representative, including both zero weighted
coordinate cases. -/
theorem
    hEveryRegularProfileNumeratorRootWeightedOrderTails_not_hasInjectiveRepresentative
    (a N : ℕ) (ha : 0 < a) (hN : 5 ≤ N)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (p : ℂ[X]) (hp : p ≠ 0)
    (alpha beta z : ℂ)
    (halpha : alpha ^ 2 + 2 * alpha + 4 = 0)
    (hbeta : beta ^ 2 + 2 * beta + 4 = 0)
    (halphaBeta : alpha ≠ beta)
    (hzAlpha : z ≠ alpha) (hzBeta : z ≠ beta)
    (hz : p.IsRoot z)
    (hprofile :
      (hPoleProfileDenominator (K := ℂ) (N / 2) N).eval z ≠ 0)
    (hrepresentation :
      hConicDifference R =
        algebraMap ℂ[X] (RatFunc ℂ) p /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (N / 2) N))
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (hQuadraticWeightedPolynomialMap a R i) ∈
        Germ.weightedOrderIdeal a
          (hQuadraticWeightedDegrees a N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨hlinear, hden⟩ := h_pole_profile_factors_ne_zero
    (N / 2) N (by omega) (by omega) z hprofile
  have hfunction := h_regular_function_denominator_ne_zero hlinear hden
  have hone := h_conic_one_factor_ne_zero_of_away_from_roots
    alpha beta z halpha hbeta halphaBeta hzAlpha hzBeta
  have hnotBoth :
      hRegularProfileW z 0 ≠ 0 ∨
        hRegularProfileCapitalW z 0 ≠ 0 := by
    rcases h_conic_param_second_factors_not_both_zero z with hWFactor |
      hCapitalWFactor
    · left
      have hnumerator :
          (-hConicParamOneFactor * hConicParamWFactor).eval z ≠ 0 := by
        rw [Polynomial.eval_mul, Polynomial.eval_neg]
        exact mul_ne_zero (neg_ne_zero.mpr hone) hWFactor
      have hquotient := div_ne_zero hnumerator hfunction
      simpa [hRegularProfileW, hRegularProfileParameter] using hquotient
    · right
      have hnumerator :
          (-hConicParamOneFactor * hConicParamCapitalWFactor).eval z ≠ 0 := by
        rw [Polynomial.eval_mul, Polynomial.eval_neg]
        exact mul_ne_zero (neg_ne_zero.mpr hone) hCapitalWFactor
      have hquotient := div_ne_zero hnumerator hfunction
      simpa [hRegularProfileCapitalW, hRegularProfileParameter] using hquotient
  rcases hnotBoth with hW | hCapitalW
  · by_cases hCapitalWZero : hRegularProfileCapitalW z 0 = 0
    · exact
        hCapitalWZeroProfileRootWeightedOrderTails_not_hasInjectiveRepresentative
          a N ha R hR p hp z hz hlinear hden hW hCapitalWZero
            hrepresentation representative hanalytic hzero htail
    · exact
        hRegularProfileNumeratorRootWeightedOrderTails_not_hasInjectiveRepresentative
          a N ha hN R hR p hp alpha beta z halpha hbeta halphaBeta
            hzAlpha hzBeta hz hprofile hW hCapitalWZero hrepresentation
              representative hanalytic hzero htail
  · by_cases hWZero : hRegularProfileW z 0 = 0
    · exact
        hWZeroProfileRootWeightedOrderTails_not_hasInjectiveRepresentative
          a N ha R hR p hp z hz hlinear hden hWZero hCapitalW
            hrepresentation representative hanalytic hzero htail
    · exact
        hRegularProfileNumeratorRootWeightedOrderTails_not_hasInjectiveRepresentative
          a N ha hN R hR p hp alpha beta z halpha hbeta halphaBeta
            hzAlpha hzBeta hz hprofile hWZero hCapitalW hrepresentation
              representative hanalytic hzero htail

end OnLeConjecture.DThree
