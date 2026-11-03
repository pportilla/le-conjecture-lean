/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedDerivativeIntersection
public import OnLeConjecture.Analytic.RamifiedPreparedPairTransport

/-!
# Exact weighted intersections at rational weights

Finite intersection descends through positive coordinate ramification by
the resultant of an analytic Weierstrass remainder. The exact weighted
intersection and first-derivative formulas therefore apply to the original
pair, with the ramification denominator cleared.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- Finite intersection of a ramified prepared pair implies finite
intersection of the original pair. -/
theorem hasFiniteIntersection_of_ramified_prepared_pair
    (s m : ℕ) (hs : 0 < s) (hm : 0 < m)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = m)
    (hdist : ∀ j, j < m → P.coeff j ∈ maximalIdeal 1)
    (H : Germ 2)
    (hfinite : PlaneCurve.HasFiniteIntersection
      ((secondCoordinatePowerGerm s hs).pullbackRingHom (firstCoordinatePolynomialEvaluation P))
      ((secondCoordinatePowerGerm s hs).pullbackRingHom H)) :
    PlaneCurve.HasFiniteIntersection (firstCoordinatePolynomialEvaluation P) H := by
  let φ := (secondCoordinatePowerGerm s hs).pullbackRingHom
  let ψ := (oneVariablePowerMapGerm s hs).pullbackRingHom
  have hmPred : m - 1 + 1 = m := Nat.sub_add_cancel hm
  obtain ⟨R, hR⟩ := exists_polynomial_mod_distinguished (m - 1) P hP
    (by simpa only [hmPred] using hPm) (by simpa only [hmPred] using hdist) H
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hR
  have hdivision : H = firstCoordinatePolynomialEvaluation P * q +
      firstCoordinatePolynomialEvaluation R := by rw [← hq]; ring
  have hpoly (Q : Polynomial (Germ 1)) : φ (firstCoordinatePolynomialEvaluation Q) =
      firstCoordinatePolynomialEvaluation (Q.map ψ) :=
    secondCoordinatePowerGerm_pullback_polynomial s hs Q
  have hdivisionR : φ H = firstCoordinatePolynomialEvaluation (P.map ψ) * φ q +
      firstCoordinatePolynomialEvaluation (R.map ψ) := by
    rw [hdivision, map_add, map_mul, hpoly, hpoly]
  have hfiniteH : PlaneCurve.HasFiniteIntersection
      (firstCoordinatePolynomialEvaluation (P.map ψ)) (φ H) := by
    rwa [hpoly] at hfinite
  have hidealR := PlaneCurve.pairIdeal_eq_of_remainder
    (firstCoordinatePolynomialEvaluation (P.map ψ)) (φ H)
    (firstCoordinatePolynomialEvaluation (R.map ψ)) (φ q) hdivisionR
  have hfiniteR := hfiniteH.of_pairIdeal_eq hidealR
  have hPmR : (P.map ψ).natDegree = m - 1 + 1 := by
    rw [hP.natDegree_map, hPm, hmPred]
  have hdistR : ∀ j, j < m - 1 + 1 → (P.map ψ).coeff j ∈ maximalIdeal 1 := by
    intro j hj
    rw [Polynomial.coeff_map]
    exact PointedMapGerm.pullback_mem_maximalIdeal _ (hdist j (by omega))
  have hresR := resultant_ne_zero_of_hasFiniteIntersection (m - 1) (P.map ψ) (R.map ψ)
    (hP.map ψ) hPmR hdistR hfiniteR
  have hres : P.resultant R ≠ 0 := by
    intro hzero
    apply hresR
    rw [resultant_map_oneVariablePowerMapGerm, hzero, map_zero]
  have hfiniteBareR := hasFiniteIntersection_of_resultant_ne_zero (m - 1) P R hP
    (by simpa only [hmPred] using hPm) (by simpa only [hmPred] using hdist) hres
  exact hfiniteBareR.of_pairIdeal_eq
    (PlaneCurve.pairIdeal_eq_of_remainder (firstCoordinatePolynomialEvaluation P) H
      (firstCoordinatePolynomialEvaluation R) q hdivision).symm

/-- Descent of finite intersection also retains a preparation unit. -/
theorem hasFiniteIntersection_of_ramified_unit_pair
    (s m : ℕ) (hs : 0 < s) (hm : 0 < m)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = m)
    (hdist : ∀ j, j < m → P.coeff j ∈ maximalIdeal 1)
    (U H : Germ 2) (hU : IsUnit U)
    (hfinite : PlaneCurve.HasFiniteIntersection
      ((secondCoordinatePowerGerm s hs).pullbackRingHom
        (U * firstCoordinatePolynomialEvaluation P))
      ((secondCoordinatePowerGerm s hs).pullbackRingHom H)) :
    PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) H := by
  let φ := (secondCoordinatePowerGerm s hs).pullbackRingHom
  have hUR : IsUnit (φ U) := hU.map φ
  have hbareR : PlaneCurve.HasFiniteIntersection (φ (firstCoordinatePolynomialEvaluation P))
      (φ H) := by
    rw [map_mul] at hfinite
    exact (PlaneCurve.hasFiniteIntersection_unit_mul_left_iff _ _ _ hUR).mp hfinite
  exact (PlaneCurve.hasFiniteIntersection_unit_mul_left_iff _ _ _ hU).mpr
    (hasFiniteIntersection_of_ramified_prepared_pair s m hs hm P hP hPm hdist H hbareR)

/-- The exact ramified intersection identity with both finite proofs
supplied, so it rewrites any already constructed local intersection number. -/
theorem intersectionMultiplicity_ramified_unit_eq
    (s m : ℕ) (hs : 0 < s) (hm : 0 < m)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = m)
    (hdist : ∀ j, j < m → P.coeff j ∈ maximalIdeal 1)
    (U H : Germ 2) (hU : IsUnit U)
    (hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) H)
    (hfiniteR : PlaneCurve.HasFiniteIntersection
      ((secondCoordinatePowerGerm s hs).pullbackRingHom
        (U * firstCoordinatePolynomialEvaluation P))
      ((secondCoordinatePowerGerm s hs).pullbackRingHom H)) :
    PlaneCurve.intersectionMultiplicity
      ((secondCoordinatePowerGerm s hs).pullbackRingHom
        (U * firstCoordinatePolynomialEvaluation P))
      ((secondCoordinatePowerGerm s hs).pullbackRingHom H) hfiniteR =
    s * PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P) H hfinite := by
  obtain ⟨_, hinter⟩ := exists_finite_ramified_unit_intersection_eq
    s m hs hm P hP hPm hdist U H hU hfinite
  exact hinter

/-- Coprime initial charts after ramification give the exact rational
weighted intersection formula for the original analytic pair. -/
theorem rational_weighted_intersection_eq_of_no_common_initial_root
    (s r L m : ℕ) (hs : 0 < s) (hr : 0 < r) (hm : 0 < m)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = m)
    (hdist : ∀ j, j < m → P.coeff j ∈ maximalIdeal 1)
    (horder : ∀ j, j < m →
      ((r * (m - j) : ℕ) : ℕ∞) ≤ s • vanishingOrder (P.coeff j))
    (U H : Germ 2) (hU : IsUnit U) (P₀ H₀ : MvPolynomial (Fin 2) ℂ)
    (hP₀ : P₀.IsWeightedHomogeneous ![r, 1] (r * m)) (hP₀ne : P₀ ≠ 0)
    (hH₀ : H₀.IsWeightedHomogeneous ![r, 1] L)
    (hPtail : (secondCoordinatePowerGerm s hs).pullbackRingHom
      (U * firstCoordinatePolynomialEvaluation P) - coordinatePolynomialAlgHom 2 P₀ ∈
        weightedOrderIdeal r (r * m + 1))
    (hHtail : (secondCoordinatePowerGerm s hs).pullbackRingHom H -
      coordinatePolynomialAlgHom 2 H₀ ∈ weightedOrderIdeal r (L + 1))
    (hno : ∀ z : ℂ, ¬ (MvPolynomial.eval ![z, 1] P₀ = 0 ∧
      MvPolynomial.eval ![z, 1] H₀ = 0)) :
    ∃ hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) H,
      s * PlaneCurve.intersectionMultiplicity
        (U * firstCoordinatePolynomialEvaluation P) H hfinite =
        m * L := by
  let φ := (secondCoordinatePowerGerm s hs).pullbackRingHom
  let ψ := (oneVariablePowerMapGerm s hs).pullbackRingHom
  have hf : φ (U * firstCoordinatePolynomialEvaluation P) =
      φ U * firstCoordinatePolynomialEvaluation (P.map ψ) := by
    rw [map_mul, secondCoordinatePowerGerm_pullback_polynomial]
  obtain ⟨hfiniteR, hinterR⟩ := weighted_intersection_unit_eq_any_order_of_no_common_initial_root
    r L m hr hm (P.map ψ) (hP.map ψ) ((hP.natDegree_map ψ).trans hPm)
    (coefficient_mem_maximalIdeal_pow_after_ramification s r m hs P horder)
    (φ U) (φ H) (hU.map φ) P₀ H₀ hP₀ hP₀ne hH₀ (by rwa [← hf]) hHtail hno
  have hfiniteR' : PlaneCurve.HasFiniteIntersection
      (φ (U * firstCoordinatePolynomialEvaluation P)) (φ H) := by rwa [hf]
  have hfinite := hasFiniteIntersection_of_ramified_unit_pair
    s m hs hm P hP hPm hdist U H hU hfiniteR'
  refine ⟨hfinite, ?_⟩
  have hscale := intersectionMultiplicity_ramified_unit_eq
    s m hs hm P hP hPm hdist U H hU hfinite hfiniteR'
  rw [← hscale]
  convert hinterR using 1
  change Module.finrank ℂ _ = Module.finrank ℂ _
  rw [hf]

/-- Differentiation in the unramified coordinate commutes with the
actual positive ramification of the other coordinate. -/
theorem partialDerivative_zero_secondCoordinatePowerGerm_pullback
    (s : ℕ) (hs : 0 < s) (f : Germ 2) :
    partialDerivative (0 : Fin 2) ((secondCoordinatePowerGerm s hs).pullbackRingHom f) =
      (secondCoordinatePowerGerm s hs).pullbackRingHom (partialDerivative (0 : Fin 2) f) := by
  rw [PointedMapGerm.pullbackRingHom_apply, partialDerivative_compPointed]
  rw [← PointedMapGerm.pullback_coordinate, ← PointedMapGerm.pullback_coordinate,
    secondCoordinatePowerGerm_pullback_zero, secondCoordinatePowerGerm_pullback_one]
  simp only [partialDerivative_coordinate_same, mul_one, partialDerivative_pow,
    partialDerivative_coordinate_ne (by decide : (0 : Fin 2) ≠ 1), smul_zero, mul_zero, add_zero]
  rfl

/-- A squarefree initial chart after ramification determines the original
first-derivative intersection, with no finite-intersection assumption. -/
theorem rational_weighted_intersection_first_derivative_eq_of_squarefree_chart
    (s r m : ℕ) (hs : 0 < s) (hr : 0 < r) (hm : 0 < m)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = m)
    (hdist : ∀ j, j < m → P.coeff j ∈ maximalIdeal 1)
    (horder : ∀ j, j < m →
      ((r * (m - j) : ℕ) : ℕ∞) ≤ s • vanishingOrder (P.coeff j))
    (U : Germ 2) (hU : IsUnit U) (P₀ : MvPolynomial (Fin 2) ℂ)
    (hP₀ : P₀.IsWeightedHomogeneous ![r, 1] (r * m)) (hP₀ne : P₀ ≠ 0)
    (hPtail : (secondCoordinatePowerGerm s hs).pullbackRingHom
      (U * firstCoordinatePolynomialEvaluation P) - coordinatePolynomialAlgHom 2 P₀ ∈
        weightedOrderIdeal r (r * m + 1))
    (hsquarefree : Squarefree (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P₀)) :
    ∃ hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P)
        (partialDerivative (0 : Fin 2) (U * firstCoordinatePolynomialEvaluation P)),
      s * PlaneCurve.intersectionMultiplicity (U * firstCoordinatePolynomialEvaluation P)
        (partialDerivative (0 : Fin 2) (U * firstCoordinatePolynomialEvaluation P)) hfinite =
          m * (r * (m - 1)) := by
  let φ := (secondCoordinatePowerGerm s hs).pullbackRingHom
  let ψ := (oneVariablePowerMapGerm s hs).pullbackRingHom
  let f := U * firstCoordinatePolynomialEvaluation P
  have hf : φ f = φ U * firstCoordinatePolynomialEvaluation (P.map ψ) := by
    rw [map_mul, secondCoordinatePowerGerm_pullback_polynomial]
  obtain ⟨hfiniteR, hinterR⟩ := weighted_intersection_first_derivative_eq_of_squarefree_chart
    r m hr hm (P.map ψ) (hP.map ψ) ((hP.natDegree_map ψ).trans hPm)
    (coefficient_mem_maximalIdeal_pow_after_ramification s r m hs P horder)
    (φ U) (hU.map φ) P₀ hP₀ hP₀ne (by rwa [← hf]) hsquarefree
  have hderiv : φ (partialDerivative (0 : Fin 2) f) =
      partialDerivative (0 : Fin 2) (φ U * firstCoordinatePolynomialEvaluation (P.map ψ)) := by
    rw [← partialDerivative_zero_secondCoordinatePowerGerm_pullback, hf]
  have hfiniteR' : PlaneCurve.HasFiniteIntersection (φ f) (φ (partialDerivative 0 f)) := by
    rwa [hf, hderiv]
  have hfinite := hasFiniteIntersection_of_ramified_unit_pair
    s m hs hm P hP hPm hdist U (partialDerivative 0 f) hU hfiniteR'
  refine ⟨hfinite, ?_⟩
  have hscale := intersectionMultiplicity_ramified_unit_eq
    s m hs hm P hP hPm hdist U (partialDerivative 0 f) hU hfinite hfiniteR'
  rw [← hscale]
  convert hinterR using 1
  change Module.finrank ℂ _ = Module.finrank ℂ _
  rw [hf, hderiv]

end OnLeConjecture.Analytic.Germ
