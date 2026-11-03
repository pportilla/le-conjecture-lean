/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionHoleRadius

/-! # Literal exterior membership near a removed circle

Near a circle of one chosen disk, the other disks and the outer target
cutoff impose no additional condition. The exterior is exactly the level
and the sublevel of the negative squared coordinate radius.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology ContDiff

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

namespace PlaneLevelCoordinateDisk

variable {f : CollarPlane → ℂ} {s : ℂ} {z : CollarPlane}

theorem holeRadius_le_iff (D : PlaneLevelCoordinateDisk f s z) {u : ℂ}
    (hu : u ∈ sphere 0 D.radius) (w : CollarPlane) :
    D.holeRadius w ≤ D.holeRadius (D.ψ u) ↔ D.radius ≤ ‖D.coordinate (w - z)‖ := by
  rw [holeRadius, holeRadius, D.left_inverse _ (D.closedBall_subset (sphere_subset_closedBall hu)),
    mem_sphere_zero_iff_norm.mp hu, neg_le_neg_iff]
  exact sq_le_sq₀ D.radius_pos.le (norm_nonneg _)

theorem holeRadius_eq_iff (D : PlaneLevelCoordinateDisk f s z) {u : ℂ}
    (hu : u ∈ sphere 0 D.radius) (w : CollarPlane) :
    D.holeRadius w = D.holeRadius (D.ψ u) ↔ ‖D.coordinate (w - z)‖ = D.radius := by
  rw [holeRadius, holeRadius, D.left_inverse _ (D.closedBall_subset (sphere_subset_closedBall hu)),
    mem_sphere_zero_iff_norm.mp hu, neg_inj]
  exact pow_left_inj₀ (norm_nonneg _) D.radius_pos.le two_ne_zero

theorem eventually_mem_boundaryCircle_iff (D : PlaneLevelCoordinateDisk f s z) {u : ℂ}
    (hu : u ∈ D.W) (hf : AnalyticAt ℂ f (D.ψ u))
    (hfn : fderiv ℂ f (D.ψ u) ≠ 0) :
    ∀ᶠ w in 𝓝 (D.ψ u), w ∈ D.boundaryCircle ↔
      f w = s ∧ ‖D.coordinate (w - z)‖ = D.radius := by
  filter_upwards [D.eventually_local_inverse hu hf hfn] with w hw
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hvW := D.closedBall_subset (sphere_subset_closedBall hv)
    exact ⟨D.level_eq v hvW, by rw [D.left_inverse v hvW]; exact mem_sphere_zero_iff_norm.mp hv⟩
  · rintro ⟨hfw, hnorm⟩
    exact ⟨D.coordinate (w - z), mem_sphere_zero_iff_norm.mpr hnorm, (hw hfw).2⟩

end PlaneLevelCoordinateDisk

namespace ResolutionSectionLevel

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative} {A : ResolutionSectionAssembly g hd hi}

theorem euclidean_level_analytic_regular (L : ResolutionSectionLevel A)
    (ha : AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) L.radius))
    {z : CollarPlane} (hz : (EuclideanSpace.equiv (Fin 2) ℂ) z ∈ ball 0 L.radius)
    (hlevel : A.H ((EuclideanSpace.equiv (Fin 2) ℂ) z) 0 = L.parameter) :
    AnalyticAt ℂ (euclideanEquation (fun x => A.H x 0)) z ∧
      fderiv ℂ (euclideanEquation (fun x => A.H x 0)) z ≠ 0 := by
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  have hH := ha (e z) (ball_subset_closedBall hz)
  have hf := (analyticAt_pi_iff.mp hH) 0
  refine ⟨hf.comp (e.analyticAt z), ?_⟩
  have hd : fderiv ℂ (euclideanEquation (fun x => A.H x 0)) z =
      (fderiv ℂ (fun x => A.H x 0) (e z)).comp e.toContinuousLinearMap :=
    (hf.differentiableAt.hasFDerivAt.comp z e.hasFDerivAt).fderiv
  intro hn
  apply (L.regular _ hz hlevel).1
  ext v
  have he := DFunLike.congr_fun hn (e.symm v)
  simpa only [hd, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, zero_apply] using he

/-- The same exterior has the exact negative-radius sublevel description
near each of its retained hole circles. -/
theorem eventually_diskExterior_hole_iff (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) {ε : ℝ}
    (hε : 0 < ε) (ha : AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) L.radius))
    (hdisj : Pairwise (fun j k => Disjoint (D j).closedDisk (D k).closedDisk))
    (hD : ∀ j, ∀ w ∈ (D j).closedDisk,
      (EuclideanSpace.equiv (Fin 2) ℂ) w ∈ ball 0 L.radius ∧
      ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm
        (A.H ((EuclideanSpace.equiv (Fin 2) ℂ) w))‖ < ε / 2)
    (j : L.points) {z : CollarPlane} (hz : z ∈ (D j).boundaryCircle) :
    ∀ᶠ w in 𝓝 z,
      (w ∈ L.diskExterior D ε ↔
        euclideanEquation (fun x => A.H x 0) w = L.parameter ∧
          (D j).holeRadius w ≤ (D j).holeRadius z) ∧
      (w ∈ (D j).boundaryCircle ↔
        euclideanEquation (fun x => A.H x 0) w = L.parameter ∧
          (D j).holeRadius w = (D j).holeRadius z) := by
  classical
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  let Q : CollarPlane → EuclideanSpace ℂ (Fin 3) :=
    fun w => (EuclideanSpace.equiv (Fin 3) ℂ).symm (A.H (e w))
  obtain ⟨u, hu, rfl⟩ := hz
  have huW := (D j).closedBall_subset (sphere_subset_closedBall hu)
  have hzD : (D j).ψ u ∈ (D j).closedDisk := ⟨u, sphere_subset_closedBall hu, rfl⟩
  have hsource := (hD j _ hzD).1
  have hlevel := (D j).level_eq u huW
  obtain ⟨hf, hfn⟩ := L.euclidean_level_analytic_regular ha hsource hlevel
  have hnear : ∀ᶠ w in 𝓝 ((D j).ψ u), e w ∈ ball 0 L.radius ∧ ‖Q w‖ < ε := by
    have hQ : ContinuousAt Q ((D j).ψ u) :=
      ((EuclideanSpace.equiv (Fin 3) ℂ).symm.continuous.continuousAt).comp
        ((ha _ (ball_subset_closedBall hsource)).continuousAt.comp e.continuous.continuousAt)
    have hn : ‖Q ((D j).ψ u)‖ < ε := (hD j _ hzD).2.trans (half_lt_self hε)
    exact (e.continuous.continuousAt.eventually (isOpen_ball.mem_nhds hsource)).and
      (hQ.norm.eventually (gt_mem_nhds hn))
  have hother : ∀ᶠ w in 𝓝 ((D j).ψ u), ∀ k, k ≠ j → w ∉ (D k).closedDisk := by
    apply Filter.eventually_all.mpr
    intro k
    by_cases hkj : k = j
    · exact Filter.Eventually.of_forall (fun _ hn => (hn hkj).elim)
    · have hnot : (D j).ψ u ∉ (D k).closedDisk :=
        fun hk => Set.disjoint_left.mp (hdisj (Ne.symm hkj)) hzD hk
      filter_upwards [(D k).isCompact_closedDisk.isClosed.isOpen_compl.mem_nhds hnot]
        with w hw using fun _ => hw
  filter_upwards [hnear, hother, (D j).eventually_mem_openDisk_iff huW hf hfn,
    (D j).eventually_mem_boundaryCircle_iff huW hf hfn] with w hnear hother hopen hcircle
  refine ⟨?_, ?_⟩
  · rw [(D j).holeRadius_le_iff hu]
    constructor
    · intro hw
      have hs : euclideanEquation (fun x => A.H x 0) w = L.parameter := hw.1.1.2
      refine ⟨hs, le_of_not_gt ?_⟩
      intro hlt
      exact hw.2 (mem_iUnion.mpr ⟨j, (hopen hs).mpr hlt⟩)
    · rintro ⟨hs, hnorm⟩
      refine ⟨(mem_targetSectionCut_iff hε.le).mpr
        ⟨⟨ball_subset_closedBall hnear.1, hs⟩, hnear.2.le⟩, ?_⟩
      intro hU
      obtain ⟨k, hk⟩ := mem_iUnion.mp hU
      by_cases hkj : k = j
      · subst k
        exact (not_lt_of_ge hnorm) ((hopen hs).mp hk)
      · exact hother k hkj ((D k).openDisk_subset_closedDisk hk)
  · rw [(D j).holeRadius_eq_iff hu]
    exact hcircle

end ResolutionSectionLevel
end OnLeConjecture.Analytic
