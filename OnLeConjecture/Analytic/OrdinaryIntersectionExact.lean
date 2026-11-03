/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedParameterTranslation
public import OnLeConjecture.Analytic.WeightedIntersectionExact

/-!
# Exact ordinary intersection from disjoint initial directions

Convergent Weierstrass preparation is constructed from the original
regular first germ. No prepared polynomial is an additional input.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- Homogeneous initial forms with no common finite-chart root give
finite intersection and the product formula. First-axis regularity
ensures that the first initial form has no missing root at infinity. -/
theorem ordinary_intersection_eq_of_regular_no_common_initial_root
    (m n : ℕ) (hm : 0 < m) (f h : Germ 2)
    (hregular : IsRegularInFirstCoordinateOfOrder f m)
    (hf : f ∈ maximalIdeal 2 ^ m)
    (P H : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![1, 1] m) (hPne : P ≠ 0)
    (hH : H.IsWeightedHomogeneous ![1, 1] n)
    (hftail : f - coordinatePolynomialAlgHom 2 P ∈ maximalIdeal 2 ^ (m + 1))
    (hhtail : h - coordinatePolynomialAlgHom 2 H ∈ maximalIdeal 2 ^ (n + 1))
    (hno : ∀ z : ℂ, ¬ (MvPolynomial.eval ![z, 1] P = 0 ∧
      MvPolynomial.eval ![z, 1] H = 0)) :
    ∃ hfinite : PlaneCurve.HasFiniteIntersection f h,
      PlaneCurve.intersectionMultiplicity f h hfinite = m * n := by
  have hfweight : f ∈ weightedOrderIdeal 1 (1 * m) := by
    simpa only [one_mul, weightedOrderIdeal_one_eq_maximalIdeal_pow] using hf
  obtain ⟨Q, U, hQ, hdegree, hU, hfactor, hcoeff⟩ :=
    exists_weierstrass_preparation_with_weighted_coefficients 1 m hm f hregular hfweight
  have hfactor' : f = U * firstCoordinatePolynomialEvaluation Q :=
    hfactor.trans (mul_comm _ _)
  have htail : U * firstCoordinatePolynomialEvaluation Q - coordinatePolynomialAlgHom 2 P ∈
      weightedOrderIdeal 1 (1 * m + 1) := by
    simpa only [← hfactor', one_mul, weightedOrderIdeal_one_eq_maximalIdeal_pow] using hftail
  have htail' : h - coordinatePolynomialAlgHom 2 H ∈ weightedOrderIdeal 1 (n + 1) := by
    simpa only [weightedOrderIdeal_one_eq_maximalIdeal_pow] using hhtail
  have hresult := weighted_intersection_unit_eq_any_order_of_no_common_initial_root
    1 n m (by omega) hm Q hQ hdegree (fun j _ ↦ hcoeff j) U h hU P H
    (by simpa only [one_mul] using hP) hPne hH htail htail' hno
  simpa only [← hfactor'] using hresult

end OnLeConjecture.Analytic.Germ
