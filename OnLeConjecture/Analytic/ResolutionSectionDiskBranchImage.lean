/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionDiskBranchKernel

/-! # Equation coverage by the same diskBranch

A smaller parameter disk in the retained holomorphic chart covers the
entire local section equation near its singular image point. This is an
explicit restriction of the same map, not a replacement of the removed
disk or a claim that its existing boundary is a target norm sphere.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

namespace ResolutionSectionLevel

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative} {A : ResolutionSectionAssembly g hd hi}

/-- The actual local equation is covered by a strictly smaller parameter
disk of the same centered section parametrization. -/
theorem exists_diskBranch_equation_coverage (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j)
    (ha : AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) L.radius))
    (hD : ∀ j, ∀ w ∈ (D j).closedDisk,
      (EuclideanSpace.equiv (Fin 2) ℂ) w ∈ ball 0 L.radius)
    (j : L.points) (W : Source 2 → ℂ) (hW : AnalyticAt ℂ W 0)
    (hWgerm : localSectionEquation A.H j = ofFunction W hW) :
    ∃ r : ℝ, 0 < r ∧ r < (D j).radius ∧
      AnalyticOnNhd ℂ (L.diskBranch D j) (closedBall 0 r) ∧
      InjOn (L.diskBranch D j) (closedBall 0 r) ∧
      (∀ z ∈ closedBall (0 : ℂ) r,
        W ((EuclideanSpace.equiv (Fin 2) ℂ) (L.diskBranch D j z)) = 0) ∧
      ∀ᶠ y in 𝓝 (0 : CollarPlane),
        W ((EuclideanSpace.equiv (Fin 2) ℂ) y) = 0 ↔
          y ∈ L.diskBranch D j '' closedBall 0 r := by
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  let G : Source 1 → Source 2 := fun t => e (L.diskBranch D j (curveParameterEquiv t))
  have hpoint := (L.points_iff j).mp j.property
  have hA := ha j (ball_subset_closedBall hpoint.1)
  have hG : AnalyticAt ℂ G 0 := L.diskBranch_at_center D j hA
  have hG0 : G 0 = 0 := by simp only [G, map_zero, L.diskBranch_zero D j]
  have hg : L.diskBranchGerm D j hA = PointedMapGerm.ofFunction G hG hG0 :=
    L.diskBranchGerm_eq_ofFunction D j hA
  have hiG : (PointedMapGerm.ofFunction G hG hG0).HasInjectiveRepresentative :=
    hg ▸ L.diskBranchGerm_hasInjectiveRepresentative D j hA
  have hn := PointedMapGerm.exists_nonzero_coordinate_pullback_of_injective_curve
    (PointedMapGerm.ofFunction G hG hG0) hiG
  have hker : ∀ q, (PointedMapGerm.ofFunction G hG hG0).pullbackRingHom q = 0 ↔
      ofFunction W hW ∣ q := by
    intro q
    rw [← RingHom.mem_ker, ← hg, L.diskBranchGerm_kernel D j hA, hWgerm]
    exact Ideal.mem_span_singleton
  let S : Set (Source 1) := curveParameterEquiv ⁻¹' ball 0 (D j).radius
  have hS : S ∈ 𝓝 (0 : Source 1) := by
    apply curveParameterEquiv.continuous.continuousAt.preimage_mem_nhds
    simpa only [map_zero] using ball_mem_nhds (0 : ℂ) (D j).radius_pos
  have hinj : InjOn G S := by
    intro u hu v hv huv
    apply curveParameterEquiv.injective
    exact L.diskBranch_injOn D hD j (ball_subset_closedBall hu) (ball_subset_closedBall hv)
      (e.injective huv)
  obtain ⟨r, hr, hrS, _, _, hvanish, himage⟩ :=
    exists_curve_closedBall_image_eq_zero_set G hG hG0 hn W hW hker S hS hinj
  have hball (z : ℂ) : curveParameterEquiv.symm z ∈ closedBall (0 : Source 1) r ↔
      z ∈ closedBall 0 r := by
    simp only [mem_closedBall, dist_zero_right, curveParameterEquiv_symm_apply, pi_norm_const]
  have hrD : r < (D j).radius := by
    have hmem : (r : ℂ) ∈ closedBall (0 : ℂ) r := by
      simpa only [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr] using (le_rfl : r ≤ r)
    have h := hrS ((hball (r : ℂ)).mpr hmem)
    change curveParameterEquiv (curveParameterEquiv.symm (r : ℂ)) ∈ ball 0 (D j).radius at h
    simpa only [ContinuousLinearEquiv.apply_symm_apply, mem_ball_zero_iff,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using h
  refine ⟨r, hr, hrD,
    (L.diskBranch_analytic D ha hD j).mono (closedBall_subset_closedBall hrD.le),
    (L.diskBranch_injOn D hD j).mono (closedBall_subset_closedBall hrD.le), ?_, ?_⟩
  · intro z hz
    simpa only [G, ContinuousLinearEquiv.apply_symm_apply] using
      hvanish (curveParameterEquiv.symm z) ((hball z).mpr hz)
  · have he : Tendsto e (𝓝 (0 : CollarPlane)) (𝓝 0) := by
      simpa only [map_zero] using e.continuous.continuousAt.tendsto (x := 0)
    filter_upwards [he.eventually himage] with y hy
    constructor
    · intro hwy
      obtain ⟨t, ht, hty⟩ := hy.mp hwy
      refine ⟨curveParameterEquiv t, ?_, e.injective hty⟩
      exact (hball _).mp (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using ht)
    · rintro ⟨z, hz, hzy⟩
      apply hy.mpr
      refine ⟨curveParameterEquiv.symm z, (hball z).mpr hz, ?_⟩
      simpa only [G, ContinuousLinearEquiv.apply_symm_apply] using congrArg e hzy

end ResolutionSectionLevel
end OnLeConjecture.Analytic
