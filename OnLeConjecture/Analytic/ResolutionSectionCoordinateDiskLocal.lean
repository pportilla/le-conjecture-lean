/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionCriticalExterior

/-! # Local inverses around the entire source coordinate disk

At regular points of the level, the retained coordinate is a local inverse
also near the boundary circle. No replacement of the previously chosen
disk is required.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology ContDiff

namespace OnLeConjecture.Analytic
namespace PlaneLevelCoordinateDisk

variable {f : CollarPlane → ℂ} {s : ℂ} {z : CollarPlane}

/-- Differentiating the explicit coordinate identity. -/
theorem coordinate_fderiv (D : PlaneLevelCoordinateDisk f s z) {u : ℂ} (hu : u ∈ D.W)
    (v : ℂ) : D.coordinate (fderiv ℂ D.ψ u v) = v := by
  have hleft : (fun t => D.coordinate (D.ψ t - z)) =ᶠ[𝓝 u] id := by
    filter_upwards [D.isOpen_W.mem_nhds hu] with t ht using D.left_inverse t ht
  have hd := D.coordinate.hasFDerivAt.comp u
    ((D.analytic u hu).differentiableAt.hasFDerivAt.sub_const z)
  have he := hd.unique ((hasFDerivAt_id u).congr_of_eventuallyEq hleft)
  exact DFunLike.congr_fun he v

/-- Differentiating the constant level identity. -/
theorem level_fderiv (D : PlaneLevelCoordinateDisk f s z) {u : ℂ} (hu : u ∈ D.W)
    (hf : DifferentiableAt ℂ f (D.ψ u)) (v : ℂ) :
    fderiv ℂ f (D.ψ u) (fderiv ℂ D.ψ u v) = 0 := by
  have hlevel : (fun t => f (D.ψ t)) =ᶠ[𝓝 u] fun _ => s := by
    filter_upwards [D.isOpen_W.mem_nhds hu] with t ht using D.level_eq t ht
  have hd := hf.hasFDerivAt.comp u (D.analytic u hu).differentiableAt.hasFDerivAt
  have he := hd.unique ((hasFDerivAt_const s u).congr_of_eventuallyEq hlevel)
  exact DFunLike.congr_fun he v

/-- The retained coordinate and level equation give nonsingular complex
coordinates at every regular point of the disk chart. -/
theorem coordinate_prod_fderiv_injective (D : PlaneLevelCoordinateDisk f s z)
    {u : ℂ} (hu : u ∈ D.W) (hf : DifferentiableAt ℂ f (D.ψ u))
    (hfn : fderiv ℂ f (D.ψ u) ≠ 0) :
    Injective (D.coordinate.prod (fderiv ℂ f (D.ψ u))) := by
  have hk := D.level_fderiv hu hf 1
  obtain ⟨a, ha⟩ := exists_smul_euclideanKernelVector hfn hk
  have hK : D.coordinate (euclideanKernelVector f (D.ψ u)) ≠ 0 := by
    intro hn
    have h1 := D.coordinate_fderiv hu 1
    rw [ha, map_smul, hn, smul_zero] at h1
    exact zero_ne_one h1
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have hcv : D.coordinate v = 0 := congrArg Prod.fst hv
  have hfv : fderiv ℂ f (D.ψ u) v = 0 := congrArg Prod.snd hv
  obtain ⟨b, hb⟩ := exists_smul_euclideanKernelVector hfn hfv
  have hb0 : b = 0 := by
    rw [hb, map_smul, smul_eq_mul] at hcv
    exact (mul_eq_zero.mp hcv).resolve_right hK
  rw [hb, hb0, zero_smul]

/-- The chosen coordinate is a local inverse along the same level near
every regular point of the retained parameter neighborhood. -/
theorem eventually_local_inverse (D : PlaneLevelCoordinateDisk f s z) {u : ℂ}
    (hu : u ∈ D.W) (hf : AnalyticAt ℂ f (D.ψ u))
    (hfn : fderiv ℂ f (D.ψ u) ≠ 0) :
    ∀ᶠ w in 𝓝 (D.ψ u), f w = s →
      D.coordinate (w - z) ∈ D.W ∧ D.ψ (D.coordinate (w - z)) = w := by
  let q : CollarPlane → ℂ := fun w => D.coordinate (w - z)
  let F : CollarPlane → ℂ × ℂ := fun w => (q w, f w)
  have hq : HasFDerivAt q D.coordinate (D.ψ u) := by
    simpa [q] using D.coordinate.hasFDerivAt (x := D.ψ u)
  obtain ⟨e, he⟩ := exists_continuousLinearEquiv_of_injective_euclidean _
    (D.coordinate_prod_fderiv_injective hu hf.differentiableAt hfn)
  have hFd : HasFDerivAt F (e : CollarPlane →L[ℂ] ℂ × ℂ) (D.ψ u) := by
    rw [he]
    exact hq.prodMk hf.differentiableAt.hasFDerivAt
  have hFa : ∀ᶠ w in 𝓝 (D.ψ u), ContDiffAt ℂ ω F w := by
    filter_upwards [hf.eventually_analyticAt] with w hw
    exact (((D.coordinate.analyticAt _).comp
      (analyticAt_id.sub analyticAt_const)).prod hw).contDiffAt
  obtain ⟨Φ, hΦ, huΦ, _⟩ := exists_openPartialHomeomorph_contDiffAt_symm hFa hFd
  have hqu : q (D.ψ u) = u := D.left_inverse u hu
  have hqc : ContinuousAt q (D.ψ u) := hq.continuousAt
  have hqw : ∀ᶠ w in 𝓝 (D.ψ u), q w ∈ D.W := by
    apply hqc.eventually
    rw [hqu]
    exact D.isOpen_W.mem_nhds hu
  have hpc : ContinuousAt (D.ψ ∘ q) (D.ψ u) :=
    ((hqu.symm ▸ (D.analytic u hu).continuousAt)).comp hqc
  have hp : ∀ᶠ w in 𝓝 (D.ψ u), D.ψ (q w) ∈ Φ.source := by
    apply hpc.eventually
    change Φ.source ∈ 𝓝 (D.ψ (q (D.ψ u)))
    rw [hqu]
    exact Φ.open_source.mem_nhds huΦ
  filter_upwards [Φ.open_source.mem_nhds huΦ, hqw, hp] with w hw hqw hp hfw
  refine ⟨hqw, Φ.injOn hp hw ?_⟩
  rw [hΦ]
  change (q (D.ψ (q w)), f (D.ψ (q w))) = (q w, f w)
  change (D.coordinate (D.ψ (q w) - z), f (D.ψ (q w))) = (q w, f w)
  rw [D.left_inverse _ hqw, D.level_eq _ hqw, hfw]

/-- Near a circle point, the open disk is exactly the strict coordinate
norm inequality on the level. -/
theorem eventually_mem_openDisk_iff (D : PlaneLevelCoordinateDisk f s z) {u : ℂ}
    (hu : u ∈ D.W) (hf : AnalyticAt ℂ f (D.ψ u))
    (hfn : fderiv ℂ f (D.ψ u) ≠ 0) :
    ∀ᶠ w in 𝓝 (D.ψ u), f w = s →
      (w ∈ D.openDisk ↔ ‖D.coordinate (w - z)‖ < D.radius) := by
  filter_upwards [D.eventually_local_inverse hu hf hfn] with w hw hfw
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [D.left_inverse v (D.closedBall_subset (ball_subset_closedBall hv))]
    exact mem_ball_zero_iff.mp hv
  · intro hnorm
    exact ⟨D.coordinate (w - z), mem_ball_zero_iff.mpr hnorm, (hw hfw).2⟩

end PlaneLevelCoordinateDisk
end OnLeConjecture.Analytic
