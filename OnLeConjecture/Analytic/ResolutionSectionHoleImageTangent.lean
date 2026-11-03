/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionDiskBranch

/-! # Oriented tangents under the actual section embedding

The clockwise source-circle tangent maps to a nonzero tangent of the
centered analytic parametrization. The positive-ray agreement of the
hole chart is preserved by the literal section differential.
-/

@[expose] public noncomputable section

open Set Metric Function
open scoped Topology ContDiff

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

namespace ResolutionSectionLevel

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative} {A : ResolutionSectionAssembly g hd hi}

/-- The image boundary tangent is a positive multiple of the nonzero
clockwise tangent of the same centered section parametrization. -/
theorem holeChart_image_tangent (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) {ε : ℝ} (hε : 0 < ε)
    (ha : AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) L.radius))
    (hdisj : Pairwise (fun j k => Disjoint (D j).closedDisk (D k).closedDisk))
    (hD : ∀ j, ∀ w ∈ (D j).closedDisk,
      (EuclideanSpace.equiv (Fin 2) ℂ) w ∈ ball 0 L.radius ∧
      ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm
        (A.H ((EuclideanSpace.equiv (Fin 2) ℂ) w))‖ < ε / 2)
    (j : L.points) {u : ℂ} (hu : u ∈ sphere 0 (D j).radius)
    {O : Set CollarPlane}
    (C : SectionRadiusBoundaryChart (euclideanEquation (fun x => A.H x 0))
      (D j).holeRadius O ((D j).ψ u)) :
    (fderiv ℂ (L.diskBranch D j) u (-Complex.I * u) ≠ 0) ∧
      ∃ a : ℝ, 0 < a ∧
        fderiv ℂ (euclideanSectionMap A.H) ((D j).ψ u) (fderiv ℝ C.φ 0 1) =
          a • fderiv ℂ (L.diskBranch D j) u (-Complex.I * u) := by
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  let z := (D j).ψ u
  have huW := (D j).closedBall_subset (sphere_subset_closedBall hu)
  have hzD : z ∈ (D j).closedDisk := ⟨u, sphere_subset_closedBall hu, rfl⟩
  have hzs := (hD j z hzD).1
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
  have hDc : ∀ k, (D k).closedDisk ⊆ targetSectionCut A.H L.radius ε L.parameter := by
    intro k w hw
    exact (mem_targetSectionCut_iff hε.le).mpr
      ⟨⟨ball_subset_closedBall (hD k w hw).1, (D k).closedDisk_subset_level hw⟩,
        ((hD k w hw).2.trans (half_lt_self hε)).le⟩
  have hzE : z ∈ L.diskExterior D ε := by
    have hzC : z ∈ (D j).boundaryCircle := ⟨u, hu, rfl⟩
    rw [← L.diskExterior_inter_closedDisk D hdisj hDc j] at hzC
    exact hzC.1
  have hznot := L.not_mem_points_of_mem_diskExterior D hzE
  have hdf : fderiv ℂ (euclideanEquation (fun x => A.H x 0)) z =
      (fderiv ℂ (fun x => A.H x 0) (e z)).comp e.toContinuousLinearMap :=
    (((analyticAt_pi_iff.mp hH) 0).differentiableAt.hasFDerivAt.comp z e.hasFDerivAt).fderiv
  have hdS : fderiv ℂ (euclideanSectionMap A.H) z =
      e.symm.toContinuousLinearMap.comp
        ((fderiv ℂ A.sectionMap (e z)).comp e.toContinuousLinearMap) :=
    (e.symm.hasFDerivAt.comp z
      ((A.sectionMap_analyticAt hH).differentiableAt.hasFDerivAt.comp z e.hasFDerivAt)).fderiv
  have hu0 : u ≠ 0 := by
    intro hn
    have he := mem_sphere_zero_iff_norm.mp hu
    rw [hn, norm_zero] at he
    exact (ne_of_gt (D j).radius_pos) he.symm
  have hvker : e (fderiv ℂ (D j).ψ u (-Complex.I * u)) ∈ L.sectionTangent (e z) := by
    have h := (D j).level_fderiv huW ((analyticAt_pi_iff.mp hH) 0 |>.comp
      (e.analyticAt z)).differentiableAt (-Complex.I * u)
    rw [hdf] at h
    exact h
  have hnonzero : fderiv ℂ (L.diskBranch D j) u (-Complex.I * u) ≠ 0 := by
    intro hn
    have hv0 : L.sectionTangentMap (e z)
        ⟨e (fderiv ℂ (D j).ψ u (-Complex.I * u)), hvker⟩ = 0 := by
      have he := congrArg e hn
      change fderiv ℂ A.sectionMap (e z) (e (fderiv ℂ (D j).ψ u (-Complex.I * u))) = 0
      simpa only [hB, hdS, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply, map_zero] using he
    have hzv := L.sectionTangentMap_injective ⟨hzs, hlevel⟩ hznot hH (hv0.trans (map_zero _).symm)
    have hzv' : e (fderiv ℂ (D j).ψ u (-Complex.I * u)) = 0 := congrArg Subtype.val hzv
    have hv : fderiv ℂ (D j).ψ u (-Complex.I * u) = 0 := e.injective (by simpa using hzv')
    have h := (D j).coordinate_fderiv huW (-Complex.I * u)
    rw [hv, map_zero] at h
    exact (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hu0) h.symm
  obtain ⟨hf, hfn⟩ := L.euclidean_level_analytic_regular ha hzs hlevel
  obtain ⟨a, ha, he⟩ := (D j).holeChart_tangent_eq_pos_clockwise huW hu0 hf hfn C
  refine ⟨hnonzero, a, ha, ?_⟩
  rw [he, hB, ContinuousLinearMap.comp_apply]
  exact (fderiv ℂ (euclideanSectionMap A.H) z).map_smul_of_tower a _

end ResolutionSectionLevel
end OnLeConjecture.Analytic
