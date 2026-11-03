/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RationalInitialCoefficientOrder

/-!
# Strict coefficient orders from vanishing initial coefficients

A zero coefficient of the weighted initial chart means that the
corresponding analytic coefficient has strictly larger weighted order.
The conclusion includes identically zero coefficients.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

theorem RationalPreparedWeightedPair.coefficient_order_gt_of_chart_zero
    {s r m t : ℕ} {hs : 0 < s} {P : Polynomial (Germ 1)} {U u : Germ 2}
    {hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u}
    (data : RationalPreparedWeightedPair s r m t hs P U u hfinite)
    (hr : 0 < r) (hP : P.Monic) (hPm : P.natDegree = m) (hU : IsUnit U)
    (horder : ∀ i, i < m →
      ((r * (m - i) : ℕ) : ℕ∞) ≤ s • vanishingOrder (P.coeff i))
    (j : ℕ)
    (hj : (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.firstInitial).coeff j = 0) :
    ((r * (m - j) : ℕ) : ℕ∞) < s • vanishingOrder (P.coeff j) := by
  let PR := P.map (oneVariablePowerMapGerm s hs).pullbackRingHom
  have hPR : PR.Monic := hP.map _
  have hPRm : PR.natDegree = m := (hP.natDegree_map _).trans hPm
  have hcoeff : ∀ i, PR.coeff i ∈ maximalIdeal 1 ^ (r * (m - i)) := by
    intro i
    by_cases hi : i < m
    · exact coefficient_mem_maximalIdeal_pow_after_ramification s r m hs P horder i hi
    · simp [Nat.sub_eq_zero_of_le (by omega : m ≤ i)]
  obtain ⟨A, _hA, hAm, hscale, hfactor⟩ := exists_monic_weighted_polynomial_scaling
    PR m r hPR hPRm hcoeff
  have hchart := weighted_initial_chart_eq_scaled_residue r m hr PR A hAm hscale
    data.firstInitial data.first_homogeneous (data.bare_first_tail hr hU)
  rw [hchart, coeff_map] at hj
  have hmem : PR.coeff j ∈ maximalIdeal 1 ^ (r * (m - j) + 1) := by
    rw [hfactor j, pow_succ]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 0) _)
      (mem_maximalIdeal_iff.mpr hj)
  have hbound := mem_maximalIdeal_one_pow_iff.mp hmem
  change ((r * (m - j) + 1 : ℕ) : ℕ∞) ≤
    vanishingOrder ((P.map (oneVariablePowerMapGerm s hs).pullbackRingHom).coeff j) at hbound
  rw [coeff_map, vanishingOrder_oneVariablePowerMapGerm_pullback] at hbound
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self (r * (m - j))) hbound

end OnLeConjecture.Analytic.Germ
