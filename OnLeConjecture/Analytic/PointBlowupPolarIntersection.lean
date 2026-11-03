/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PointBlowupPolynomial

/-!
# The first blowup recurrence for a transverse polar

For a monic prepared polynomial with ordinary coefficient orders, root
scaling constructs its chart polynomial. Scaling of the polar resultant
and the sum over all finite residue roots prove the intersection
recurrence. The preparation unit remains in both the original curve and
its chart transforms. No sum over later resolution centers is asserted.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial
open scoped BigOperators

/-- The polar pair ideal is unchanged by multiplication of the curve
equation by a unit. The derivative of the unit is removed by a change of
the second ideal generator. -/
theorem pairIdeal_unit_mul_polar (U f : Germ 2) (hU : IsUnit U) :
    PlaneCurve.pairIdeal (U * f) (partialDerivative (0 : Fin 2) (U * f)) =
      PlaneCurve.pairIdeal f (partialDerivative (0 : Fin 2) f) := by
  rw [PlaneCurve.pairIdeal_unit_mul_left U f _ hU]
  have hsubtract := PlaneCurve.pairIdeal_sub_mul_right f
    (partialDerivative (0 : Fin 2) (U * f)) (partialDerivative (0 : Fin 2) U)
  have heq : partialDerivative (0 : Fin 2) (U * f) -
      f * partialDerivative (0 : Fin 2) U = U * partialDerivative (0 : Fin 2) f := by
    rw [partialDerivative_mul]
    ring
  rw [← hsubtract, heq, PlaneCurve.pairIdeal_comm,
    PlaneCurve.pairIdeal_unit_mul_left U _ _ hU, PlaneCurve.pairIdeal_comm]

/-- The first blowup polar recurrence, including an arbitrary
preparation unit. The coefficient orders and monic degree ensure that
the tangent polynomial has full degree, so there is no omitted tangent
at infinity. -/
theorem exists_pointBlowup_polar_intersection_recurrence
    (m : ℕ) (hm : 0 < m) (P : Polynomial (Germ 1)) (hP : P.Monic)
    (hdegree : P.natDegree = m)
    (hcoeff : ∀ j, P.coeff j ∈ maximalIdeal 1 ^ (m - j))
    (U : Germ 2) (hU : IsUnit U)
    (hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P)
      (partialDerivative (0 : Fin 2) (U * firstCoordinatePolynomialEvaluation P))) :
    ∃ A : Polynomial (Germ 1), A.Monic ∧ A.natDegree = m ∧
      P = A.scaleRoots (coordinate (0 : Fin 1)) ∧
      (∀ c : ℂ, (pointBlowupChartGerm c).pullbackRingHom
          (U * firstCoordinatePolynomialEvaluation P) =
        coordinate (1 : Fin 2) ^ m *
          ((pointBlowupChartGerm c).pullbackRingHom U *
            firstCoordinatePolynomialEvaluation (rootTranslation A c))) ∧
      (∀ c : ℂ, (pointBlowupChartGerm c).pullbackRingHom
          (partialDerivative (0 : Fin 2) (U * firstCoordinatePolynomialEvaluation P)) =
        coordinate (1 : Fin 2) ^ (m - 1) * partialDerivative (0 : Fin 2)
          ((pointBlowupChartGerm c).pullbackRingHom U *
            firstCoordinatePolynomialEvaluation (rootTranslation A c))) ∧
      ∃ hf : ∀ c : (A.map (valueRingHom 1)).roots.toFinset,
        PlaneCurve.HasFiniteIntersection
          ((pointBlowupChartGerm c).pullbackRingHom U *
            firstCoordinatePolynomialEvaluation (rootTranslation A c))
          (partialDerivative (0 : Fin 2)
            ((pointBlowupChartGerm c).pullbackRingHom U *
              firstCoordinatePolynomialEvaluation (rootTranslation A c))),
        PlaneCurve.intersectionMultiplicity (U * firstCoordinatePolynomialEvaluation P)
          (partialDerivative (0 : Fin 2) (U * firstCoordinatePolynomialEvaluation P)) hfinite =
          m * (m - 1) + ∑ c : (A.map (valueRingHom 1)).roots.toFinset,
            PlaneCurve.intersectionMultiplicity
              ((pointBlowupChartGerm c).pullbackRingHom U *
                firstCoordinatePolynomialEvaluation (rootTranslation A c))
              (partialDerivative (0 : Fin 2)
                ((pointBlowupChartGerm c).pullbackRingHom U *
                  firstCoordinatePolynomialEvaluation (rootTranslation A c))) (hf c) := by
  obtain ⟨A, hA, hAm, hscale, _⟩ := exists_monic_weighted_polynomial_scaling P m 1
    hP hdegree (by simpa only [one_mul] using hcoeff)
  simp only [pow_one] at hscale
  have hdist : ∀ j, j < (m - 1) + 1 → P.coeff j ∈ maximalIdeal 1 := by
    simpa only [Nat.sub_add_cancel hm] using
      coeff_mem_maximalIdeal_of_weighted_bounds 1 m (by decide) P
        (fun j _ ↦ by simpa only [one_mul] using hcoeff j)
  have hdegree' : P.natDegree = (m - 1) + 1 := by
    rw [hdegree, Nat.sub_add_cancel hm]
  have hideal : PlaneCurve.pairIdeal (U * firstCoordinatePolynomialEvaluation P)
        (partialDerivative (0 : Fin 2) (U * firstCoordinatePolynomialEvaluation P)) =
      PlaneCurve.pairIdeal (firstCoordinatePolynomialEvaluation P)
        (firstCoordinatePolynomialEvaluation P.derivative) := by
    rw [pairIdeal_unit_mul_polar U _ hU, partialDerivative_firstCoordinatePolynomialEvaluation]
  have hfP : PlaneCurve.HasFiniteIntersection (firstCoordinatePolynomialEvaluation P)
      (firstCoordinatePolynomialEvaluation P.derivative) := by
    unfold PlaneCurve.HasFiniteIntersection
    rw [← hideal]
    exact hfinite
  have hPresultant := resultant_ne_zero_of_hasFiniteIntersection (m - 1) P P.derivative
    hP hdegree' hdist hfP
  have hresultant : P.resultant P.derivative =
      coordinate (0 : Fin 1) ^ (m * (m - 1)) * A.resultant A.derivative := by
    rw [hscale, derivative_scaleRoots_germ, resultant_scaleRoots,
      natDegree_derivative_germ, hAm]
  have hAresultant : A.resultant A.derivative ≠ 0 :=
    (mul_ne_zero_iff.mp (hresultant ▸ hPresultant)).2
  have hinter : PlaneCurve.intersectionMultiplicity
      (U * firstCoordinatePolynomialEvaluation P)
      (partialDerivative (0 : Fin 2) (U * firstCoordinatePolynomialEvaluation P)) hfinite =
        m * (m - 1) + (vanishingOrder (A.resultant A.derivative)).toNat := by
    have hpair : PlaneCurve.intersectionMultiplicity
        (U * firstCoordinatePolynomialEvaluation P)
        (partialDerivative (0 : Fin 2) (U * firstCoordinatePolynomialEvaluation P)) hfinite =
      PlaneCurve.intersectionMultiplicity (firstCoordinatePolynomialEvaluation P)
        (firstCoordinatePolynomialEvaluation P.derivative) hfP := by
      change Module.finrank ℂ _ = Module.finrank ℂ _
      rw [hideal]
    rw [hpair, intersectionMultiplicity_eq_resultant_order (m - 1) P P.derivative
      hP hdegree' hdist hfP, hresultant, vanishingOrder_mul, vanishingOrder_coordinate_pow,
      ENat.toNat_add (ENat.natCast_ne_top _) (vanishingOrder_eq_top_iff.not.mpr hAresultant),
      ENat.toNat_natCast]
  have htransform (c : ℂ) : (pointBlowupChartGerm c).pullbackRingHom
      (U * firstCoordinatePolynomialEvaluation P) = coordinate (1 : Fin 2) ^ m *
        ((pointBlowupChartGerm c).pullbackRingHom U *
          firstCoordinatePolynomialEvaluation (rootTranslation A c)) := by
    rw [map_mul, hscale, pointBlowupChart_pullback_scaled_polynomial, hAm]
    ring
  obtain ⟨hfA, hiA⟩ := exists_resultant_order_eq_sum_translated_intersections
    A A.derivative hA hAresultant
  have hlocalIdeal (c : ℂ) : PlaneCurve.pairIdeal
      ((pointBlowupChartGerm c).pullbackRingHom U *
        firstCoordinatePolynomialEvaluation (rootTranslation A c))
      (partialDerivative (0 : Fin 2)
        ((pointBlowupChartGerm c).pullbackRingHom U *
          firstCoordinatePolynomialEvaluation (rootTranslation A c))) =
    PlaneCurve.pairIdeal (firstCoordinatePolynomialEvaluation (rootTranslation A c))
      (firstCoordinatePolynomialEvaluation (rootTranslation A.derivative c)) := by
    rw [pairIdeal_unit_mul_polar _ _ (hU.map _),
      partialDerivative_firstCoordinatePolynomialEvaluation]
    simp only [rootTranslation, taylor_apply, derivative_comp, derivative_add,
      derivative_X, derivative_C, add_zero, one_mul]
  have hf (c : (A.map (valueRingHom 1)).roots.toFinset) :
      PlaneCurve.HasFiniteIntersection
        ((pointBlowupChartGerm c).pullbackRingHom U *
          firstCoordinatePolynomialEvaluation (rootTranslation A c))
        (partialDerivative (0 : Fin 2)
          ((pointBlowupChartGerm c).pullbackRingHom U *
            firstCoordinatePolynomialEvaluation (rootTranslation A c))) := by
    unfold PlaneCurve.HasFiniteIntersection
    rw [hlocalIdeal]
    exact hfA c
  refine ⟨A, hA, hAm, hscale, htransform, ?_, hf, ?_⟩
  · intro c
    exact pointBlowupTransform_partialDerivative_zero c m hm _ _ (htransform c)
  · rw [hinter, hiA]
    congr 1
    apply Finset.sum_congr rfl
    intro c _
    change Module.finrank ℂ _ = Module.finrank ℂ _
    rw [hlocalIdeal]

end OnLeConjecture.Analytic.Germ
