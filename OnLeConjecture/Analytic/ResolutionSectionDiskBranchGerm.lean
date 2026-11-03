/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionBranchReparametrization

/-! # The germ of the retained disk parametrization

The source chart is centered at its listed critical point, and its image
germ is the literal centered diskBranch. The regular source coordinate
proves that its differential is injective before applying the singular
target map.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

namespace ResolutionSectionLevel

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative} {A : ResolutionSectionAssembly g hd hi}

def diskSourceParam (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points) (t : Source 1) : Source 2 :=
  (EuclideanSpace.equiv (Fin 2) ℂ) ((D j).ψ (curveParameterEquiv t)) - (j : Source 2)

theorem diskSourceParam_analytic (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points) :
    AnalyticAt ℂ (L.diskSourceParam D j) 0 := by
  have h0W := (D j).closedBall_subset (mem_closedBall_self (D j).radius_pos.le)
  have hψ := (D j).analytic 0 h0W
  exact (((EuclideanSpace.equiv (Fin 2) ℂ).analyticAt _).comp
    (hψ.comp_of_eq (curveParameterEquiv.analyticAt 0) (map_zero _))).sub analyticAt_const

@[simp] theorem diskSourceParam_zero (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points) :
    L.diskSourceParam D j 0 = 0 := by
  simp only [diskSourceParam, map_zero, (D j).ψ_zero,
    ContinuousLinearEquiv.apply_symm_apply, sub_self]

/-- The regular source parametrization, before the singular section map. -/
def diskSourceGerm (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points) : PointedMapGerm 1 2 :=
  PointedMapGerm.ofFunction _ (L.diskSourceParam_analytic D j) (L.diskSourceParam_zero D j)

theorem diskSourceGerm_differential_injective (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points) :
    Injective (L.diskSourceGerm D j).differential := by
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  have h0W := (D j).closedBall_subset (mem_closedBall_self (D j).radius_pos.le)
  have hψ := (D j).analytic 0 h0W
  have hdp : HasFDerivAt (fun t => (D j).ψ (curveParameterEquiv t))
      ((fderiv ℂ (D j).ψ 0).comp curveParameterEquiv.toContinuousLinearMap) 0 := by
    have hψ' : HasFDerivAt (D j).ψ (fderiv ℂ (D j).ψ 0)
        (curveParameterEquiv (0 : Source 1)) := by
      simpa only [map_zero] using hψ.differentiableAt.hasFDerivAt
    exact hψ'.comp (0 : Source 1) curveParameterEquiv.hasFDerivAt
  have hdg : (L.diskSourceGerm D j).differential = e.toContinuousLinearMap.comp
      ((fderiv ℂ (D j).ψ 0).comp curveParameterEquiv.toContinuousLinearMap) :=
    (e.hasFDerivAt.comp 0 hdp |>.sub_const (j : Source 2)).fderiv
  intro v w hvw
  rw [hdg] at hvw
  change e (fderiv ℂ (D j).ψ 0 (curveParameterEquiv v)) =
    e (fderiv ℂ (D j).ψ 0 (curveParameterEquiv w)) at hvw
  have hvw' := e.injective hvw
  apply curveParameterEquiv.injective
  have hc := congrArg (D j).coordinate hvw'
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    (D j).coordinate_fderiv h0W] using hc

/-- The actual source chart lies in the centered first-component level. -/
theorem diskSourceGerm_first_pullback_zero (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points)
    (hA : AnalyticAt ℂ A.H (j : Source 2)) :
    (L.diskSourceGerm D j).pullbackRingHom
      ((PointedMapGerm.recenterOfFunction A.H j hA).1.component 0) = 0 := by
  rw [← PointedMapGerm.component_comp_eq_pullback, PointedMapGerm.recenterOfFunction,
    diskSourceGerm, PointedMapGerm.comp_ofFunction]
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  have h0W := (D j).closedBall_subset (mem_closedBall_self (D j).radius_pos.le)
  have hnear : ∀ᶠ t in 𝓝 (0 : Source 1), curveParameterEquiv t ∈ (D j).W := by
    apply curveParameterEquiv.continuous.continuousAt.eventually
    change (D j).W ∈ 𝓝 (curveParameterEquiv (0 : Source 1))
    rw [map_zero]
    exact (D j).isOpen_W.mem_nhds h0W
  filter_upwards [hnear] with t ht
  change (A.H ((j : Source 2) + L.diskSourceParam D j t) - A.H j) 0 = 0
  have hp := ((L.points_iff j).mp j.property).2.1
  have hc : (j : Source 2) + L.diskSourceParam D j t =
      (EuclideanSpace.equiv (Fin 2) ℂ) ((D j).ψ (curveParameterEquiv t)) := by
    dsimp only [diskSourceParam]
    abel
  rw [hc, Pi.sub_apply, hp]
  exact sub_eq_zero.mpr ((D j).level_eq _ ht)

/-- The image germ of the retained regular source chart. -/
def diskBranchGerm (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points)
    (hA : AnalyticAt ℂ A.H (j : Source 2)) : PointedMapGerm 1 2 :=
  (PointedMapGerm.recenterOfFunction A.H j hA).sectionBranch (L.diskSourceGerm D j)

/-- The literal diskBranch is analytic at its center, from the analytic
map at the same listed point. -/
theorem diskBranch_at_center (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points)
    (hA : AnalyticAt ℂ A.H (j : Source 2)) :
    AnalyticAt ℂ (fun t : Source 1 =>
      (EuclideanSpace.equiv (Fin 2) ℂ) (L.diskBranch D j (curveParameterEquiv t))) 0 := by
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  have h0W := (D j).closedBall_subset (mem_closedBall_self (D j).radius_pos.le)
  have hψ := (D j).analytic 0 h0W
  have hP := (e.analyticAt _).comp
    (hψ.comp_of_eq (curveParameterEquiv.analyticAt 0) (map_zero _))
  have he0 : e ((D j).ψ (curveParameterEquiv (0 : Source 1))) = (j : Source 2) := by
    simp only [map_zero, (D j).ψ_zero, e, ContinuousLinearEquiv.apply_symm_apply]
  have h := ((hyperplaneTail 2).analyticAt _).comp (hA.comp_of_eq hP he0)
  simpa only [diskBranch, euclideanSectionMap, map_sub, e, Function.comp_def, Pi.sub_def,
    ContinuousLinearEquiv.apply_symm_apply] using
      h.sub (analyticAt_const (v := hyperplaneTail 2 (A.H j)))

/-- The image germ is exactly the Euclidean centered diskBranch in source
coordinates, not merely a germ with the same image set. -/
theorem diskBranchGerm_eq_ofFunction (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points)
    (hA : AnalyticAt ℂ A.H (j : Source 2)) :
    L.diskBranchGerm D j hA = PointedMapGerm.ofFunction
      (fun t => (EuclideanSpace.equiv (Fin 2) ℂ) (L.diskBranch D j (curveParameterEquiv t)))
      (L.diskBranch_at_center D j hA) (by simp) := by
  rw [diskBranchGerm, PointedMapGerm.sectionBranch, PointedMapGerm.recenterOfFunction,
    diskSourceGerm, hyperplaneTailGerm, PointedMapGerm.comp_ofFunction,
    PointedMapGerm.comp_ofFunction]
  apply Subtype.ext
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  filter_upwards with t
  simp only [Function.comp_apply, diskSourceParam, diskBranch, euclideanSectionMap,
    map_sub, ContinuousLinearEquiv.apply_symm_apply]
  rw [show (j : Source 2) + ((EuclideanSpace.equiv (Fin 2) ℂ)
      ((D j).ψ (curveParameterEquiv t)) - j) =
      (EuclideanSpace.equiv (Fin 2) ℂ) ((D j).ψ (curveParameterEquiv t)) by abel]

end ResolutionSectionLevel
end OnLeConjecture.Analytic
