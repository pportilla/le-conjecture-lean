/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionDiskBranchImage

/-! # Immersion on the punctured retained parameter disk

Completeness of the critical-point list and disjointness of the retained
coordinate disks imply that their centered section parametrizations are
immersions away from their centers, including at their existing boundaries.
-/

@[expose] public noncomputable section

open Set Metric Function
open scoped Topology ContDiff

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

namespace ResolutionSectionLevel

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative} {A : ResolutionSectionAssembly g hd hi}

theorem diskSource_not_mem_points (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j)
    (hdisj : Pairwise (fun j k => Disjoint (D j).closedDisk (D k).closedDisk))
    (j : L.points) {u : ℂ} (hu : u ∈ closedBall 0 (D j).radius) (hu0 : u ≠ 0) :
    (EuclideanSpace.equiv (Fin 2) ℂ) ((D j).ψ u) ∉ L.points := by
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  intro hmem
  let k : L.points := ⟨e ((D j).ψ u), hmem⟩
  have hzj : (D j).ψ u ∈ (D j).closedDisk := ⟨u, hu, rfl⟩
  have hzk : (D j).ψ u ∈ (D k).closedDisk := by
    have h := (D k).openDisk_subset_closedDisk (D k).center_mem_openDisk
    simpa only [k, e, ContinuousLinearEquiv.symm_apply_apply] using h
  have hkj : k = j := by
    by_contra h
    exact Set.disjoint_left.mp (hdisj h) hzk hzj
  have he : e ((D j).ψ u) = (j : Source 2) := congrArg Subtype.val hkj
  have hψ : (D j).ψ u = (D j).ψ 0 := by
    rw [(D j).ψ_zero]
    exact e.injective (by simpa only [e, ContinuousLinearEquiv.apply_symm_apply] using he)
  exact hu0 ((D j).injOn ((D j).closedBall_subset hu)
    ((D j).closedBall_subset (mem_closedBall_self (D j).radius_pos.le)) hψ)

/-- The same centered branch has injective complex differential at every
nonzero point of the whole retained parameter disk. -/
theorem diskBranch_fderiv_injective (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j)
    (ha : AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) L.radius))
    (hdisj : Pairwise (fun j k => Disjoint (D j).closedDisk (D k).closedDisk))
    (hD : ∀ j, ∀ w ∈ (D j).closedDisk,
      (EuclideanSpace.equiv (Fin 2) ℂ) w ∈ ball 0 L.radius)
    (j : L.points) {u : ℂ} (hu : u ∈ closedBall 0 (D j).radius) (hu0 : u ≠ 0) :
    Injective (fderiv ℂ (L.diskBranch D j) u) := by
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  let z := (D j).ψ u
  have huW := (D j).closedBall_subset hu
  have hzs := hD j z ⟨u, hu, rfl⟩
  have hlevel := (D j).level_eq u huW
  have hH := ha (e z) (ball_subset_closedBall hzs)
  have hS : AnalyticAt ℂ (euclideanSectionMap A.H) z :=
    (e.symm.analyticAt _).comp (((hyperplaneTail 2).analyticAt _).comp
      (hH.comp (e.analyticAt z)))
  have hψ := (D j).analytic u huW
  have hB : fderiv ℂ (L.diskBranch D j) u =
      (fderiv ℂ (euclideanSectionMap A.H) z).comp (fderiv ℂ (D j).ψ u) := by
    exact ((hS.differentiableAt.hasFDerivAt.comp u hψ.differentiableAt.hasFDerivAt).sub_const
      (euclideanSectionMap A.H (e.symm (j : Source 2)))).fderiv
  have hznot := L.diskSource_not_mem_points D hdisj j hu hu0
  have hdf : fderiv ℂ (euclideanEquation (fun x => A.H x 0)) z =
      (fderiv ℂ (fun x => A.H x 0) (e z)).comp e.toContinuousLinearMap :=
    (((analyticAt_pi_iff.mp hH) 0).differentiableAt.hasFDerivAt.comp z e.hasFDerivAt).fderiv
  have hdS : fderiv ℂ (euclideanSectionMap A.H) z =
      e.symm.toContinuousLinearMap.comp
        ((fderiv ℂ A.sectionMap (e z)).comp e.toContinuousLinearMap) :=
    (e.symm.hasFDerivAt.comp z
      ((A.sectionMap_analyticAt hH).differentiableAt.hasFDerivAt.comp z e.hasFDerivAt)).fderiv
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have hvker : e (fderiv ℂ (D j).ψ u v) ∈ L.sectionTangent (e z) := by
    have h := (D j).level_fderiv huW ((analyticAt_pi_iff.mp hH) 0 |>.comp
      (e.analyticAt z)).differentiableAt v
    rw [hdf] at h
    exact h
  have hv0 : L.sectionTangentMap (e z) ⟨e (fderiv ℂ (D j).ψ u v), hvker⟩ = 0 := by
    have he := congrArg e hv
    change fderiv ℂ A.sectionMap (e z) (e (fderiv ℂ (D j).ψ u v)) = 0
    simpa only [hB, hdS, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, map_zero] using he
  have hzv := L.sectionTangentMap_injective ⟨hzs, hlevel⟩ hznot hH
    (hv0.trans (map_zero _).symm)
  have hzv' : e (fderiv ℂ (D j).ψ u v) = 0 := congrArg Subtype.val hzv
  have hv' : fderiv ℂ (D j).ψ u v = 0 := e.injective (by simpa using hzv')
  have h := (D j).coordinate_fderiv huW v
  rw [hv', map_zero] at h
  exact h.symm

end ResolutionSectionLevel
end OnLeConjecture.Analytic
