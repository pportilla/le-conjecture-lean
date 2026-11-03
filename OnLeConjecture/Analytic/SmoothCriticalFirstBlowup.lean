/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SourceEquivalenceBlowupLift
public import OnLeConjecture.Analytic.PointBlowupSmoothIntersection
public import OnLeConjecture.Analytic.AnalyticPointBasis

/-!
# The first transform along a smooth critical tangent

The first derivative in the first coordinate is explicitly required to be
nonzero, so the critical tangent belongs to the given finite blowup chart.
Straightening the critical equation while keeping the second coordinate,
then lifting that equivalence, proves smoothness of the member's transform
in the original coordinates. No change of a recorded point basis is used.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- The finite tangent direction of a smooth equation whose first
coordinate derivative is nonzero. -/
@[expose] noncomputable def finiteCriticalTangent (h : Germ 2) : ℂ :=
  -valueRingHom 2 (partialDerivative (1 : Fin 2) h) /
    valueRingHom 2 (partialDerivative (0 : Fin 2) h)

/-- Intersection equal to the member's order plus one constructs a
smooth first transform at the critical tangent in the original chart. -/
theorem exists_smooth_first_transform_of_finite_critical_intersection_succ
    (m : ℕ) (v h : Germ 2) (hv : v ∈ maximalIdeal 2 ^ m)
    (hh : h ∈ maximalIdeal 2)
    (hdx : valueRingHom 2 (partialDerivative (0 : Fin 2) h) ≠ 0)
    (hfinite : PlaneCurve.HasFiniteIntersection h v)
    (hinter : PlaneCurve.intersectionMultiplicity h v hfinite = m + 1) :
    ∃ V : Germ 2,
      (pointBlowupChartGerm (finiteCriticalTangent h)).pullbackRingHom v =
        coordinate (1 : Fin 2) ^ m * V ∧
      V ∈ maximalIdeal 2 ∧ V ∉ maximalIdeal 2 ^ 2 := by
  have hregular : differential h (firstCoordinateVector 1) ≠ 0 := by
    change differential h (coordinateVector (0 : Fin 2)) ≠ 0
    rw [← valueRingHom_partialDerivative]
    exact hdx
  obtain ⟨e, he, hfix⟩ :=
    exists_equiv_pullback_coordinate_eq_preserving_hyperplaneExtension h hh hregular
  have he' : e.forward.pullbackRingHom (coordinate (0 : Fin 2)) = h := he
  have hy := parameterTranslation_preserves_y e hfix
  have hcenter : finiteChartCenter e (finiteCriticalTangent h) = 0 := by
    simp only [finiteChartCenter, he', finiteCriticalTangent]
    field_simp
    ring
  obtain ⟨E, hEy, _, hchart, _⟩ :=
    exists_preserves_y_pointBlowup_lift e hy (finiteCriticalTangent h)
  rw [hcenter] at hchart
  let w := e.pullbackAlgEquiv.symm v
  have hewSymm : e.symm.pullbackAlgEquiv v = w := by
    change e.pullbackAlgEquiv.symm v = w
    rfl
  have heh : e.symm.pullbackAlgEquiv h = coordinate (0 : Fin 2) := by
    change e.pullbackAlgEquiv.symm h = _
    rw [← he, AlgEquiv.symm_apply_apply]
  have hw : w ∈ maximalIdeal 2 ^ m := e.inverse.pullback_mem_maximalIdeal_pow hv
  have hfinitew : PlaneCurve.HasFiniteIntersection (coordinate (0 : Fin 2)) w := by
    have hpull := hfinite.pullback e.symm
    simpa only [heh, hewSymm] using hpull
  have hinterw : PlaneCurve.intersectionMultiplicity (coordinate (0 : Fin 2)) w
      hfinitew = m + 1 := by
    have hpull := PlaneCurve.intersectionMultiplicity_pullback e.symm hfinite
    simpa only [heh, hewSymm, hinter] using hpull.symm
  obtain ⟨W, hW⟩ := exists_pointBlowupChart_factor 0 m w hw
  obtain ⟨hWmem, hWnext, _, _⟩ :=
    pointBlowupTransform_smooth_of_coordinate_intersection_succ m w W hW hfinitew hinterw
  refine ⟨E.forward.pullbackRingHom W, ?_,
    E.forward.pullback_mem_maximalIdeal hWmem,
    (E.pullback_mem_maximalIdeal_pow_iff W).not.mpr hWnext⟩
  have hpull := congrArg (fun f : PointedMapGerm 2 2 => f.pullbackRingHom w) hchart
  simp only [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply] at hpull
  have hew : e.forward.pullbackRingHom w = v := e.pullbackAlgEquiv.apply_symm_apply v
  rw [hew, hW, map_mul, map_pow, hEy] at hpull
  exact hpull

end OnLeConjecture.Analytic.Germ
