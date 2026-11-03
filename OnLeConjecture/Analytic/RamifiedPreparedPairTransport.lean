/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PreparedWeightedInitialPair
public import OnLeConjecture.Analytic.RamifiedIntersection
public import OnLeConjecture.Analytic.DepressedCubicCoefficientOrder

/-!
# Transport of prepared analytic pairs through ramification

The intersection scaling formula retains the preparation unit. Polynomial
target corrections commute with analytic pullback, and constant target
normalization is absorbed by composition of the correction polynomial.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- Polynomial evaluation in a scalar germ commutes with pointed analytic
pullback. -/
theorem pointed_pullback_polynomial_aeval
    {n m : ℕ} (φ : PointedMapGerm n m) (f : Germ m) (p : ℂ[X]) :
    φ.pullbackRingHom (Polynomial.aeval f p) =
      Polynomial.aeval (φ.pullbackRingHom f) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial k c =>
    simp only [Polynomial.aeval_def, Polynomial.eval₂_monomial, map_mul, map_pow]
    change φ.pullbackRingHom (constRingHom m c) * φ.pullbackRingHom f ^ k = _
    rw [PointedMapGerm.pullback_constRingHom]
    rfl

/-- Composing a correction polynomial with a constant dilation gives the
same correction in the original first germ. -/
theorem polynomial_correction_constant_rescaling
    (p : ℂ[X]) (c : ℂ) (f : Germ 2) :
    Polynomial.aeval f (p.comp (C c * X)) = Polynomial.aeval (constRingHom 2 c * f) p := by
  rw [Polynomial.aeval_comp, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
  rfl

/-- Constant dilation preserves the zero constant term of a correction
polynomial. -/
theorem polynomial_correction_constant_rescaling_zero
    (p : ℂ[X]) (c : ℂ) (hp : p.coeff 0 = 0) :
    (p.comp (C c * X)).coeff 0 = 0 := by
  simp only [coeff_zero_eq_eval_zero, eval_comp, eval_mul, eval_C, eval_X, mul_zero]
  simpa only [← coeff_zero_eq_eval_zero] using hp

/-- Ramification multiplies the intersection number of a prepared pair,
including an arbitrary analytic preparation unit and second germ. -/
theorem exists_finite_ramified_unit_intersection_eq
    (s m : ℕ) (hs : 0 < s) (hm : 0 < m)
    (P : Polynomial (Germ 1)) (hP : P.Monic) (hPm : P.natDegree = m)
    (hdist : ∀ i, i < m → P.coeff i ∈ maximalIdeal 1)
    (U u : Germ 2) (hU : IsUnit U)
    (hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u) :
    ∃ hfinite' : PlaneCurve.HasFiniteIntersection
        ((secondCoordinatePowerGerm s hs).pullbackRingHom
          (U * firstCoordinatePolynomialEvaluation P))
        ((secondCoordinatePowerGerm s hs).pullbackRingHom u),
      PlaneCurve.intersectionMultiplicity
        ((secondCoordinatePowerGerm s hs).pullbackRingHom
          (U * firstCoordinatePolynomialEvaluation P))
        ((secondCoordinatePowerGerm s hs).pullbackRingHom u) hfinite' =
      s * PlaneCurve.intersectionMultiplicity (U * firstCoordinatePolynomialEvaluation P) u
        hfinite := by
  let φ := (secondCoordinatePowerGerm s hs).pullbackRingHom
  have hbare := (PlaneCurve.hasFiniteIntersection_unit_mul_left_iff
    U (firstCoordinatePolynomialEvaluation P) u hU).mp hfinite
  obtain ⟨hbareR, hinterBareR⟩ := exists_finite_ramified_intersection_eq
    s (m - 1) hs P hP (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ m)] using hPm)
      (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ m)] using hdist) u hbare
  have hUR : IsUnit (φ U) := hU.map φ
  have hfiniteR : PlaneCurve.HasFiniteIntersection
      (φ (U * firstCoordinatePolynomialEvaluation P)) (φ u) := by
    rw [map_mul]
    exact (PlaneCurve.hasFiniteIntersection_unit_mul_left_iff _ _ _ hUR).mpr hbareR
  refine ⟨hfiniteR, ?_⟩
  have hinterR : PlaneCurve.intersectionMultiplicity
      (φ (U * firstCoordinatePolynomialEvaluation P)) (φ u) hfiniteR =
      PlaneCurve.intersectionMultiplicity (φ (firstCoordinatePolynomialEvaluation P)) (φ u)
        hbareR := by
    change Module.finrank ℂ _ = Module.finrank ℂ _
    rw [map_mul, PlaneCurve.pairIdeal_unit_mul_left _ _ _ hUR]
  rw [hinterR, hinterBareR, PlaneCurve.intersectionMultiplicity_unit_mul_left
    U (firstCoordinatePolynomialEvaluation P) u hU hfinite hbare]

end OnLeConjecture.Analytic.Germ
