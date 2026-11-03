/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GenericDivisorSpecialization
public import OnLeConjecture.Analytic.TransverseSourceCoordinates
public import OnLeConjecture.Analytic.CriticalCurveTangent

/-!
# Transverse target coordinates along a parametrized curve

The derivative of a curve equation annihilates the parametrization tangent.
For a finite plane map, some target component has nonzero derivative on
that tangent. Together with smoothness of an irreducible curve away from
the parameter origin, this proves the unit Jacobian required for the
simultaneous analytic source coordinates.
-/

@[expose] public section

open Filter
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- Differentiating the representative curve equation gives zero on the
parametrization tangent throughout a sufficiently small neighborhood. -/
theorem eventually_curve_equation_tangent_zero
    (P : Source 2 → ℂ) (hP : AnalyticAt ℂ P 0)
    (C : Source 1 → Source 2) (hC : AnalyticAt ℂ C 0) (hC0 : C 0 = 0)
    (hvanish : (PointedMapGerm.ofFunction C hC hC0).pullbackRingHom
      (Germ.ofFunction P hP) = 0) :
    ∀ᶠ t in 𝓝 (0 : Source 1),
      fderiv ℂ P (C t) (fderiv ℂ C t (coordinateVector 0)) = 0 := by
  have hPC : (fun t => P (C t)) =ᶠ[𝓝 (0 : Source 1)] fun _ => 0 :=
    Filter.Germ.coe_eq.mp (congrArg (fun a : Germ 1 => a.1) hvanish)
  have hCt : Tendsto C (𝓝 0) (𝓝 (0 : Source 2)) := by
    simpa only [hC0] using hC.continuousAt.tendsto
  filter_upwards [hPC.fderiv (𝕜 := ℂ), hC.eventually_analyticAt,
    hCt.eventually hP.eventually_analyticAt] with t ht htC htP
  have hcomp := fderiv_comp t htP.differentiableAt htC.differentiableAt
  have hzero : fderiv ℂ (P ∘ C) t = 0 := by
    simpa only [Function.comp_def, fderiv_const_apply] using ht
  rw [hzero] at hcomp
  exact congrArg (fun L : Source 1 →L[ℂ] ℂ => L (coordinateVector 0)) hcomp.symm

namespace PointedMapGerm

/-- Every sufficiently small nonzero point on an irreducible parametrized
curve has a target component which, together with the curve equation,
forms analytic source coordinates. The target component may depend on
the point. Its Jacobian is a proved unit in the rebased analytic ring. -/
theorem eventually_exists_rebased_component_curve_jacobian_unit
    {m : ℕ} (g : PointedMapGerm 2 m) (hf : g.IsFiniteAtOrigin)
    (G : Source 2 → Source m) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hg : g = ofFunction G hG hG0)
    (P : Source 2 → ℂ) (hP : AnalyticAt ℂ P 0)
    (hp : Irreducible (Germ.ofFunction P hP))
    (C : Source 1 → Source 2) (hC : AnalyticAt ℂ C 0) (hC0 : C 0 = 0)
    (hn : ∃ i, (ofFunction C hC hC0).pullbackRingHom (coordinate i) ≠ 0)
    (hker : ∀ h : Germ 2,
      (ofFunction C hC hC0).pullbackRingHom h = 0 ↔ Germ.ofFunction P hP ∣ h) :
    ∀ᶠ t in 𝓝 (0 : Source 1), t ≠ 0 →
      ∃ (hGt : AnalyticAt ℂ G (C t)) (hPt : AnalyticAt ℂ P (C t)),
        P (C t) = 0 ∧
        ∃ i : Fin m, IsUnit (jacobian ((recenterOfFunction G (C t) hGt).1.component i)
          (Germ.ofFunctionAt P (C t) hPt)) := by
  have hv := (hker (Germ.ofFunction P hP)).mpr dvd_rfl
  have hPC : ∀ᶠ t in 𝓝 (0 : Source 1), P (C t) = 0 :=
    Filter.Germ.coe_eq.mp (congrArg (fun a : Germ 1 => a.1) hv)
  have hCt : Tendsto C (𝓝 0) (𝓝 (0 : Source 2)) := by
    simpa only [hC0] using hC.continuousAt.tendsto
  have htangent := g.eventually_tangent_image_ne_zero_of_finite hf
    (ofFunction C hC hC0) hn G hG hG0 hg C hC hC0 rfl
  filter_upwards [hCt.eventually hG.eventually_analyticAt,
    hCt.eventually hP.eventually_analyticAt, hPC, htangent,
    eventually_fderiv_ne_zero_along_irreducible_curve P hP hp C hC hC0 hker,
    eventually_curve_equation_tangent_zero P hP C hC hC0 hv]
    with t htG htP htP0 htimage htPder htPtangent htn
  have hne := htimage htn
  obtain ⟨i, hi⟩ : ∃ i : Fin m,
      fderiv ℂ G (C t) (fderiv ℂ C t (coordinateVector 0)) i ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  refine ⟨htG, htP, htP0, i, ?_⟩
  apply jacobian_isUnit_of_transverse_tangent _ _ (fderiv ℂ C t (coordinateVector 0))
  · simpa only [Germ.differential_ofFunctionAt] using htPder htn
  · simpa only [Germ.differential_ofFunctionAt] using htPtangent
  · rw [MapGerm.germDifferential_component, MapGerm.componentDifferential_apply]
    change (recenterOfFunction G (C t) htG).differential _ i ≠ 0
    rwa [differential_recenterOfFunction]

end PointedMapGerm

end OnLeConjecture.Analytic
