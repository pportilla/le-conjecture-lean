/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RationalPreparedWeightedInitialPair

/-!
# Removing the normalized preparation unit from the first initial form

The scalar-normalized preparation unit has value one. Multiplication by
its analytic inverse therefore preserves the first weighted initial form.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- The normalized preparation unit has value one. Its inverse removes
that unit from the initial-form identity without changing the first form. -/
theorem RationalPreparedWeightedPair.bare_first_tail
    {s r m t : ℕ} {hs : 0 < s} {P : Polynomial (Germ 1)} {U u : Germ 2}
    {hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u}
    (data : RationalPreparedWeightedPair s r m t hs P U u hfinite)
    (hr : 0 < r) (hU : IsUnit U) :
    firstCoordinatePolynomialEvaluation (P.map (oneVariablePowerMapGerm s hs).pullbackRingHom) -
      coordinatePolynomialAlgHom 2 data.firstInitial ∈ weightedOrderIdeal r (r * m + 1) := by
  let φ := (secondCoordinatePowerGerm s hs).pullbackRingHom
  let V := constRingHom 2 data.scalar * φ U
  have hV : IsUnit V :=
    (isUnit_of_valueRingHom_ne_zero (by simpa using data.scalar_ne)).mul (hU.map φ)
  have hvalue : valueRingHom 2 V = 1 := by
    dsimp only [V]
    rw [map_mul, valueRingHom_const, PointedMapGerm.valueRingHom_pullback, data.scalar_eq,
      inv_mul_cancel₀ (valueRingHom_ne_zero_of_isUnit hU)]
  obtain ⟨v, hv⟩ := hV.exists_left_inv
  have hvvalue : valueRingHom 2 v = 1 := by
    have h := congrArg (valueRingHom 2) hv
    simpa only [map_mul, map_one, hvalue, mul_one] using h
  have ht : V * firstCoordinatePolynomialEvaluation
      (P.map (oneVariablePowerMapGerm s hs).pullbackRingHom) -
        coordinatePolynomialAlgHom 2 data.firstInitial ∈ weightedOrderIdeal r (r * m + 1) := by
    have h := data.first_tail
    rw [map_mul, secondCoordinatePowerGerm_pullback_polynomial] at h
    simpa only [V, φ, mul_assoc] using h
  have h := mul_weighted_initial_tail r (r * m) hr v _ data.firstInitial data.first_homogeneous ht
  simpa only [← mul_assoc, hv, one_mul, hvvalue, map_one] using h

end OnLeConjecture.Analytic.Germ
