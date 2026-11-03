/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CurveRadialLevelSmooth
public import OnLeConjecture.Analytic.CurveRadialImmersion
public import OnLeConjecture.Analytic.CurveLevelEmbedding

/-!
# Smooth parametrizations of the norm levels of an analytic curve

The inverse radial parametrization is smooth with injective differential.
Composing it with the analytic curve gives a smooth circle map whose
differential is injective. Local injectivity of the analytic curve makes
the same map a closed embedding on the ambient norm sphere.
-/

public noncomputable section

open Filter
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

namespace OnLeConjecture.Analytic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {F : ℂ → E} {R c : ℝ}
    (hc : ContinuousOn (fun z => ‖F z‖ ^ 2) (Metric.closedBall 0 R))
    (hzero : ‖F 0‖ ^ 2 ≠ c)
    (hboundary : ∀ z : ℂ, ‖z‖ = R → ‖F z‖ ^ 2 ≠ c)
    (hray : ∀ u : ℂ, ‖u‖ = 1 →
      ∃! t : ℝ, t ∈ Set.Ioo 0 R ∧ ‖F (t • u)‖ ^ 2 = c)

/-- The curve composed with its inverse radial parametrization is smooth. -/
theorem curveNormLevelCircle_coe_contMDiff
    (hF : AnalyticOnNhd ℂ F (Metric.ball 0 R))
    (hpos : ∀ z ∈ Metric.ball 0 R, z ≠ 0 →
      0 < fderiv ℝ (fun w => ‖F w‖ ^ 2) z z) :
    ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞
      (fun u => (curveNormLevelCircle F R c
        (radialLevelHomeomorph hc hzero hboundary hray) u : E)) := by
  have hsmooth : ∀ z ∈ Metric.ball 0 R,
      ContDiffAt ℝ ∞ (fun w => ‖F w‖ ^ 2) z := by
    intro z hz
    exact (hF z hz).restrictScalars.contDiffAt.norm_sq (𝕜 := ℂ)
  have hh := radialLevelHomeomorph_symm_coe_contMDiff hc hzero hboundary hray
    hsmooth hpos
  intro u
  have hr := radialLevelRadius_mem_Ioo hc hzero hboundary hray u
  have hball : ((radialLevelHomeomorph hc hzero hboundary hray).symm u : ℂ) ∈
      Metric.ball 0 R := by
    simpa only [Metric.mem_ball, dist_zero_right, radialLevelRadius] using hr.2
  change ContMDiffAt (𝓡 1) 𝓘(ℝ, E) ∞
    (F ∘ fun v => ((radialLevelHomeomorph hc hzero hboundary hray).symm v : ℂ)) u
  exact ((hF _ hball).restrictScalars.contDiffAt.contMDiffAt).comp u hh.contMDiffAt

/-- The circle parametrization in the ambient vector space has injective
manifold differential at every direction. -/
theorem curveNormLevelCircle_coe_mfderiv_injective
    (hF : AnalyticOnNhd ℂ F (Metric.ball 0 R))
    (hpos : ∀ z ∈ Metric.ball 0 R, z ≠ 0 →
      0 < fderiv ℝ (fun w => ‖F w‖ ^ 2) z z)
    (u : Metric.sphere (0 : ℂ) 1) :
    Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, E)
      (fun v => (curveNormLevelCircle F R c
        (radialLevelHomeomorph hc hzero hboundary hray) v : E)) u) := by
  let h : Metric.sphere (0 : ℂ) 1 → ℂ :=
    fun v => ((radialLevelHomeomorph hc hzero hboundary hray).symm v : ℂ)
  have hr := radialLevelRadius_mem_Ioo hc hzero hboundary hray u
  have hball : h u ∈ Metric.ball 0 R := by
    simpa only [Metric.mem_ball, dist_zero_right, radialLevelRadius, h] using hr.2
  have hnz : h u ≠ 0 := radialLevelSet_ne_zero hzero _
  have hsmooth : ∀ z ∈ Metric.ball 0 R,
      ContDiffAt ℝ ∞ (fun w => ‖F w‖ ^ 2) z := by
    intro z hz
    exact (hF z hz).restrictScalars.contDiffAt.norm_sq (𝕜 := ℂ)
  have hh := radialLevelHomeomorph_symm_coe_contMDiff hc hzero hboundary hray
    hsmooth hpos
  have hhi := radialLevelHomeomorph_symm_coe_mfderiv_injective hc hzero hboundary hray
    hsmooth hpos u
  have hFi := real_curve_fderiv_injective_of_norm_radial_pos
    (hF _ hball).differentiableAt (hpos _ hball hnz)
  change Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) (F ∘ h) u)
  rw [mfderiv_comp u
    ((hF _ hball).differentiableAt.restrictScalars ℝ).mdifferentiableAt
    (hh.contMDiffAt.mdifferentiableAt (by simp)), mfderiv_eq_fderiv]
  exact hFi.comp hhi

omit hc hzero hboundary hray in
/-- A centered, nonconstant analytic curve that is injective on a
neighborhood has smooth embedded circular norm levels in one closed
parameter disc inside that neighborhood. The parametrizations have
injective differential in the ambient vector space. -/
theorem exists_smooth_injective_curve_norm_level_circles_subset
    (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), F z = 0)
    {S : Set ℂ} (hS : S ∈ 𝓝 0) (hi : Set.InjOn F S) :
    ∃ R δ : ℝ, 0 < R ∧ 0 < δ ∧ Metric.closedBall 0 R ⊆ S ∧
      AnalyticOnNhd ℂ F (Metric.closedBall 0 R) ∧
      Set.InjOn F (Metric.closedBall 0 R) ∧
      ∀ c : ℝ, 0 < c → c < δ →
        ∃ e : radialLevelSet (fun z => ‖F z‖ ^ 2) R c ≃ₜ Metric.sphere (0 : ℂ) 1,
          Topology.IsClosedEmbedding (curveNormLevelCircle F R c e) ∧
          ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ (fun u => (curveNormLevelCircle F R c e u : E)) ∧
          (∀ u, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, E)
            (fun v => (curveNormLevelCircle F R c e v : E)) u)) ∧
          Set.range (fun u => (curveNormLevelCircle F R c e u : E)) =
            Metric.sphere (0 : E) (Real.sqrt c) ∩ F '' Metric.closedBall 0 R := by
  obtain ⟨R, hR, hRS, ha, hc, hd, hp⟩ :=
    exists_analytic_curve_radial_ball_subset hF hF0 hne hS
  have hφ0 : ‖F 0‖ ^ 2 = 0 := by simp [hF0]
  obtain ⟨δ, hδ, hlevels⟩ :=
    exists_uniform_ray_levels_of_radial_derivative_pos hR hφ0 hc hd hp
  refine ⟨R, δ, hR, hδ, hRS, ha, hi.mono hRS, ?_⟩
  intro c hcpos hcsmall
  have hray := fun u hu => hlevels u hu c hcpos hcsmall
  have hboundary : ∀ z : ℂ, ‖z‖ = R → ‖F z‖ ^ 2 ≠ c := by
    intro z hz
    exact ne_of_gt (ray_level_lt_boundary_of_radial_derivative_pos hR hc hd hp
      (fun u hu => (hray u hu).exists) z hz)
  have hzero : ‖F 0‖ ^ 2 ≠ c := by rw [hφ0]; exact hcpos.ne
  let e := radialLevelHomeomorph hc hzero hboundary hray
  refine ⟨e, curveNormLevelCircle_isClosedEmbedding e ha.continuousOn (hi.mono hRS),
    curveNormLevelCircle_coe_contMDiff hc hzero hboundary hray
      (ha.mono Metric.ball_subset_closedBall) hp,
    curveNormLevelCircle_coe_mfderiv_injective hc hzero hboundary hray
      (ha.mono Metric.ball_subset_closedBall) hp,
    curveNormLevelCircle_range_eq_sphere_inter_image hcpos.le e⟩

end OnLeConjecture.Analytic
