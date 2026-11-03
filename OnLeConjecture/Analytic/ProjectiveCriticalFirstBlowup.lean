/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SmoothCriticalFirstBlowup
public import OnLeConjecture.Analytic.TwoChartBlowupLift

/-!
# The first transform at either projective critical tangent

The finite or complementary chart is determined by the differential of
the fixed critical equation. Smoothness of that equation suffices. There
is no nonzero-coordinate-derivative hypothesis on the original chart.
-/

public section

namespace OnLeConjecture.Analytic.Germ

@[expose] noncomputable def criticalProjectiveTangent (h : Germ 2) : Option ℂ :=
  if valueRingHom 2 (partialDerivative (0 : Fin 2) h) = 0 then none
  else some (finiteCriticalTangent h)

theorem partialDerivative_zero_coordinateSwap_pullback (f : Germ 2) :
    partialDerivative (0 : Fin 2)
      ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom f) =
        (coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom
          (partialDerivative (1 : Fin 2) f) := by
  have hx : (coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom
      (coordinate (0 : Fin 2)) = coordinate (1 : Fin 2) := by
    rw [PointedMapGerm.pullback_coordinate]
    exact coordinateSwapPointedEquiv_component_zero 1
  rw [PointedMapGerm.pullbackRingHom_apply, partialDerivative_compPointed]
  rw [← PointedMapGerm.pullback_coordinate, ← PointedMapGerm.pullback_coordinate,
    hx, coordinateSwapPointedEquiv_pullback_second]
  simp only [
    partialDerivative_coordinate_same, partialDerivative_coordinate_ne (by decide :
      (0 : Fin 2) ≠ 1), mul_zero, zero_add, mul_one]
  rfl

theorem partialDerivative_one_coordinateSwap_pullback (f : Germ 2) :
    partialDerivative (1 : Fin 2)
      ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom f) =
        (coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom
          (partialDerivative (0 : Fin 2) f) := by
  have hx : (coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom
      (coordinate (0 : Fin 2)) = coordinate (1 : Fin 2) := by
    rw [PointedMapGerm.pullback_coordinate]
    exact coordinateSwapPointedEquiv_component_zero 1
  rw [PointedMapGerm.pullbackRingHom_apply, partialDerivative_compPointed]
  rw [← PointedMapGerm.pullback_coordinate, ← PointedMapGerm.pullback_coordinate,
    hx, coordinateSwapPointedEquiv_pullback_second]
  simp only [
    partialDerivative_coordinate_same, partialDerivative_coordinate_ne (by decide :
      (1 : Fin 2) ≠ 0), mul_zero, add_zero, mul_one]
  rfl

theorem exists_smooth_first_transform_of_critical_intersection_succ
    (m : ℕ) (v h : Germ 2) (hv : v ∈ maximalIdeal 2 ^ m)
    (hh : h ∈ maximalIdeal 2) (hsmooth : differential h ≠ 0)
    (hfinite : PlaneCurve.HasFiniteIntersection h v)
    (hinter : PlaneCurve.intersectionMultiplicity h v hfinite = m + 1) :
    ∃ V : Germ 2,
      (pointBlowupChartGerm (projectiveChartCenter (criticalProjectiveTangent h))).pullbackRingHom
          ((projectiveChartSource (criticalProjectiveTangent h)).forward.pullbackRingHom v) =
        coordinate (1 : Fin 2) ^ m * V ∧
      V ∈ maximalIdeal 2 ∧ V ∉ maximalIdeal 2 ^ 2 := by
  classical
  by_cases hdx : valueRingHom 2 (partialDerivative (0 : Fin 2) h) = 0
  · have hdy : valueRingHom 2 (partialDerivative (1 : Fin 2) h) ≠ 0 := by
      intro hz
      apply hsmooth
      rw [differential_eq_zero_iff_partialDerivatives_vanish]
      intro i
      fin_cases i
      · exact hdx
      · exact hz
    let e := coordinateSwapPointedEquiv (1 : Fin 2)
    have hex : valueRingHom 2 (partialDerivative (0 : Fin 2)
        (e.forward.pullbackRingHom h)) ≠ 0 := by
      rw [partialDerivative_zero_coordinateSwap_pullback,
        PointedMapGerm.valueRingHom_pullback]
      exact hdy
    have hcenter : finiteCriticalTangent (e.forward.pullbackRingHom h) = 0 := by
      rw [finiteCriticalTangent, partialDerivative_one_coordinateSwap_pullback,
        PointedMapGerm.valueRingHom_pullback, hdx, neg_zero, zero_div]
    have hpullfinite := hfinite.pullback e
    have hpullinter := PlaneCurve.intersectionMultiplicity_pullback e hfinite
    obtain ⟨V, hV, hVmem, hVnext⟩ :=
      exists_smooth_first_transform_of_finite_critical_intersection_succ m
        (e.forward.pullbackRingHom v) (e.forward.pullbackRingHom h)
        (e.forward.pullback_mem_maximalIdeal_pow hv)
        (e.forward.pullback_mem_maximalIdeal hh) hex hpullfinite
        (hpullinter.symm.trans hinter)
    refine ⟨V, ?_, hVmem, hVnext⟩
    simpa only [criticalProjectiveTangent, if_pos hdx,
      projectiveChartSource, projectiveChartCenter, hcenter] using hV
  · simpa only [criticalProjectiveTangent, if_neg hdx,
      projectiveChartSource, projectiveChartCenter,
      PointedEquivGerm.identity_forward, PointedMapGerm.pullbackRingHom_identity,
      RingHom.id_apply] using
      exists_smooth_first_transform_of_finite_critical_intersection_succ
        m v h hv hh hdx hfinite hinter

end OnLeConjecture.Analytic.Germ
