/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GenericTransverseCoordinates

/-!
# One fixed target coordinate along a critical component

If a target component does not vanish identically on the parametrized
irreducible curve, its derivative along that curve is nonzero away from
the origin in a sufficiently small neighborhood. The same chosen target
coordinate then gives transverse sections at all these points.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

namespace PointedMapGerm

/-- The fixed coordinate works throughout the punctured parameter germ.
The condition is precisely that its restriction to the curve is nonzero. -/
theorem eventually_rebased_fixed_component_curve_jacobian_unit
    {m : ℕ} (G : Source 2 → Source m) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (P : Source 2 → ℂ) (hP : AnalyticAt ℂ P 0)
    (hp : Irreducible (Germ.ofFunction P hP))
    (C : Source 1 → Source 2) (hC : AnalyticAt ℂ C 0) (hC0 : C 0 = 0)
    (hker : ∀ h : Germ 2,
      (ofFunction C hC hC0).pullbackRingHom h = 0 ↔ Germ.ofFunction P hP ∣ h)
    (i : Fin m)
    (hnot : ¬ Germ.ofFunction P hP ∣ (ofFunction G hG hG0).1.component i) :
    ∀ᶠ t in 𝓝 (0 : Source 1), t ≠ 0 →
      ∃ (hGt : AnalyticAt ℂ G (C t)) (hPt : AnalyticAt ℂ P (C t)),
        P (C t) = 0 ∧
        IsUnit (jacobian ((recenterOfFunction G (C t) hGt).1.component i)
          (Germ.ofFunctionAt P (C t) hPt)) := by
  have hv := (hker (Germ.ofFunction P hP)).mpr dvd_rfl
  have hPC : ∀ᶠ t in 𝓝 (0 : Source 1), P (C t) = 0 :=
    Filter.Germ.coe_eq.mp (congrArg (fun a : Germ 1 => a.1) hv)
  have hCt : Tendsto C (𝓝 0) (𝓝 (0 : Source 2)) := by
    simpa only [hC0] using hC.continuousAt.tendsto
  have hGat : AnalyticAt ℂ G (C 0) := by simpa only [hC0] using hG
  have hcoord : AnalyticAt ℂ (fun t => G (C t) i) 0 :=
    (analyticAt_pi_iff.mp (hGat.comp hC)) i
  have hcoord0 : G (C 0) i = 0 := by simp only [hC0, hG0, Pi.zero_apply]
  have hne : Germ.ofFunction (fun t => G (C t) i) hcoord ≠ 0 :=
    (hker _).not.mpr hnot
  have hder := eventually_derivative_ne_zero_of_nonzero_pointed_germ
    _ hcoord hcoord0 hne
  filter_upwards [hCt.eventually hG.eventually_analyticAt,
    hCt.eventually hP.eventually_analyticAt, hC.eventually_analyticAt, hPC, hder,
    eventually_fderiv_ne_zero_along_irreducible_curve P hP hp C hC hC0 hker,
    eventually_curve_equation_tangent_zero P hP C hC hC0 hv]
    with t htG htP htC htP0 htder htPder htPtangent htn
  refine ⟨htG, htP, htP0, ?_⟩
  apply jacobian_isUnit_of_transverse_tangent _ _ (fderiv ℂ C t (coordinateVector 0))
  · simpa only [Germ.differential_ofFunctionAt] using htPder htn
  · simpa only [Germ.differential_ofFunctionAt] using htPtangent
  · rw [MapGerm.germDifferential_component, MapGerm.componentDifferential_apply]
    change (recenterOfFunction G (C t) htG).differential _ i ≠ 0
    rw [differential_recenterOfFunction]
    have hcomp := fderiv_comp t htG.differentiableAt htC.differentiableAt
    have hcoordDeriv := fderiv_apply (htG.differentiableAt.comp t htC.differentiableAt) i
    rw [hcomp] at hcoordDeriv
    change fderiv ℂ (fun t => G (C t) i) t = _ at hcoordDeriv
    have h := htder htn
    change fderiv ℂ (fun t => G (C t) i) t (coordinateVector 0) ≠ 0 at h
    rwa [hcoordDeriv] at h

end PointedMapGerm

end OnLeConjecture.Analytic
