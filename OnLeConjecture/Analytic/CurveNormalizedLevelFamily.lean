/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CurveJointRadialRadius

/-!
# A smooth family of curve circles on the ambient unit sphere

Dividing a curve point on squared-norm level `c` by `sqrt c` puts every
level on the same unit sphere. The radius is the unique ray solution,
and the constructed map is jointly smooth in direction and positive level.
-/

public noncomputable section

open Filter
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

namespace OnLeConjecture.Analytic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {F : ℂ → E} {R δ : ℝ}
    (hlevels : ∀ c ∈ Set.Ioo 0 δ, ∀ u : Metric.sphere (0 : ℂ) 1,
      ∃! t : ℝ, t ∈ Set.Ioo 0 R ∧ ‖F (t • (u : ℂ))‖ ^ 2 = c)

/-- The curve circle at squared-norm level `c`, scaled onto the ambient
unit sphere. The formula is defined for all real levels. -/
@[expose] def normalizedCurveLevelFamily (p : Metric.sphere (0 : ℂ) 1 × ℝ) : E :=
  (Real.sqrt p.2)⁻¹ • F (jointRadialRadius (φ := fun z => ‖F z‖ ^ 2) hlevels p • (p.1 : ℂ))

omit [CompleteSpace E] in
/-- On the prescribed level interval the normalized family lies on
the ambient unit sphere. -/
theorem normalizedCurveLevelFamily_norm (p : Metric.sphere (0 : ℂ) 1 × ℝ)
    (hp : p.2 ∈ Set.Ioo 0 δ) : ‖normalizedCurveLevelFamily hlevels p‖ = 1 := by
  have hlevel := (jointRadialRadius_spec (φ := fun z => ‖F z‖ ^ 2) hlevels p hp).2
  have hn : ‖F (jointRadialRadius (φ := fun z => ‖F z‖ ^ 2) hlevels p • (p.1 : ℂ))‖ =
      Real.sqrt p.2 :=
    (Real.sqrt_sq (norm_nonneg _)).symm.trans (congrArg Real.sqrt hlevel)
  rw [normalizedCurveLevelFamily, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos (Real.sqrt_pos.mpr hp.1), hn,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr hp.1).ne']

/-- Joint smoothness of the normalized curve circles follows from the
joint implicit radius and analyticity of the given curve. -/
theorem normalizedCurveLevelFamily_contMDiffAt
    (hF : AnalyticOnNhd ℂ F (Metric.ball 0 R))
    (hpos : ∀ z ∈ Metric.ball 0 R, z ≠ 0 →
      0 < fderiv ℝ (fun w => ‖F w‖ ^ 2) z z)
    (p : Metric.sphere (0 : ℂ) 1 × ℝ) (hp : p.2 ∈ Set.Ioo 0 δ) :
    ContMDiffAt ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞
      (normalizedCurveLevelFamily hlevels) p := by
  have hr := (jointRadialRadius_spec (φ := fun z => ‖F z‖ ^ 2) hlevels p hp).1
  have hu : ‖(p.1 : ℂ)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.1.property
  have hball : jointRadialRadius (φ := fun z => ‖F z‖ ^ 2) hlevels p • (p.1 : ℂ) ∈
      Metric.ball 0 R := by
    simpa only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr.1, hu, mul_one] using hr.2
  have hsmooth : ∀ z ∈ Metric.ball 0 R,
      ContDiffAt ℝ ∞ (fun w => ‖F w‖ ^ 2) z := by
    intro z hz
    exact (hF z hz).restrictScalars.contDiffAt.norm_sq (𝕜 := ℂ)
  have hparam := jointRadialParameter_contMDiffAt (φ := fun z => ‖F z‖ ^ 2)
    hlevels hsmooth hpos p hp
  have hcurve := ((hF _ hball).restrictScalars.contDiffAt.contMDiffAt).comp p hparam
  have hsqrt : ContMDiffAt ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun q : Metric.sphere (0 : ℂ) 1 × ℝ => Real.sqrt q.2) p :=
    (Real.contDiffAt_sqrt hp.1.ne').contMDiffAt.comp p contMDiffAt_snd
  exact (hsqrt.inv₀ (Real.sqrt_pos.mpr hp.1).ne').smul hcurve

/-- Each positive-level circle is smooth as a map to the ambient space. -/
theorem normalizedCurveLevelFamily_slice_contMDiff
    (hF : AnalyticOnNhd ℂ F (Metric.ball 0 R))
    (hpos : ∀ z ∈ Metric.ball 0 R, z ≠ 0 →
      0 < fderiv ℝ (fun w => ‖F w‖ ^ 2) z z)
    {c : ℝ} (hc : c ∈ Set.Ioo 0 δ) :
    ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞
      (fun u => normalizedCurveLevelFamily hlevels (u, c)) := by
  intro u
  exact (normalizedCurveLevelFamily_contMDiffAt hlevels hF hpos (u, c) hc).comp u
    (contMDiffAt_id.prodMk contMDiffAt_const)

omit [CompleteSpace E] in
/-- At a fixed level, the jointly defined family equals the previously
constructed circle parametrization followed by constant radial scaling. -/
theorem normalizedCurveLevelFamily_eq_scaled_circle
    {c : ℝ} (hc : c ∈ Set.Ioo 0 δ)
    (hcont : ContinuousOn (fun z => ‖F z‖ ^ 2) (Metric.closedBall 0 R))
    (hzero : ‖F 0‖ ^ 2 ≠ c)
    (hboundary : ∀ z : ℂ, ‖z‖ = R → ‖F z‖ ^ 2 ≠ c)
    (hray : ∀ u : ℂ, ‖u‖ = 1 →
      ∃! t : ℝ, t ∈ Set.Ioo 0 R ∧ ‖F (t • u)‖ ^ 2 = c)
    (u : Metric.sphere (0 : ℂ) 1) :
    normalizedCurveLevelFamily hlevels (u, c) =
      (Real.sqrt c)⁻¹ • (curveNormLevelCircle F R c
        (radialLevelHomeomorph hcont hzero hboundary hray) u : E) := by
  have hr := jointRadialRadius_eq_of_spec (φ := fun z => ‖F z‖ ^ 2) hlevels (u, c) hc
    (radialLevelRadius_mem_Ioo hcont hzero hboundary hray u)
    (radialLevelRadius_level hcont hzero hboundary hray u)
  simp only [normalizedCurveLevelFamily, hr,
    radialLevelRadius_smul, curveNormLevelCircle, curveNormLevelMap, Function.comp_apply]

/-- Every slice is a closed embedding when the analytic curve is
injective on the parameter disc. -/
theorem normalizedCurveLevelFamily_slice_isClosedEmbedding
    {c : ℝ} (hc : c ∈ Set.Ioo 0 δ)
    (hcont : ContinuousOn (fun z => ‖F z‖ ^ 2) (Metric.closedBall 0 R))
    (hzero : ‖F 0‖ ^ 2 ≠ c)
    (hboundary : ∀ z : ℂ, ‖z‖ = R → ‖F z‖ ^ 2 ≠ c)
    (hray : ∀ u : ℂ, ‖u‖ = 1 →
      ∃! t : ℝ, t ∈ Set.Ioo 0 R ∧ ‖F (t • u)‖ ^ 2 = c)
    (hF : AnalyticOnNhd ℂ F (Metric.ball 0 R))
    (hpos : ∀ z ∈ Metric.ball 0 R, z ≠ 0 →
      0 < fderiv ℝ (fun w => ‖F w‖ ^ 2) z z)
    (hi : Set.InjOn F (Metric.closedBall 0 R)) :
    Topology.IsClosedEmbedding (fun u => normalizedCurveLevelFamily hlevels (u, c)) := by
  apply (normalizedCurveLevelFamily_slice_contMDiff hlevels hF hpos hc).continuous.isClosedEmbedding
  intro u v huv
  change normalizedCurveLevelFamily hlevels (u, c) =
    normalizedCurveLevelFamily hlevels (v, c) at huv
  have hEq := normalizedCurveLevelFamily_eq_scaled_circle hlevels hc hcont hzero hboundary hray
  rw [hEq u, hEq v] at huv
  have hval := smul_right_injective E (inv_ne_zero (Real.sqrt_pos.mpr hc.1).ne') huv
  exact ((curveNormLevelMap_injective hi).comp
    (radialLevelHomeomorph hcont hzero hboundary hray).symm.injective) (Subtype.ext hval)

/-- The differential of each normalized circle is injective. -/
theorem normalizedCurveLevelFamily_slice_mfderiv_injective
    {c : ℝ} (hc : c ∈ Set.Ioo 0 δ)
    (hcont : ContinuousOn (fun z => ‖F z‖ ^ 2) (Metric.closedBall 0 R))
    (hzero : ‖F 0‖ ^ 2 ≠ c)
    (hboundary : ∀ z : ℂ, ‖z‖ = R → ‖F z‖ ^ 2 ≠ c)
    (hray : ∀ u : ℂ, ‖u‖ = 1 →
      ∃! t : ℝ, t ∈ Set.Ioo 0 R ∧ ‖F (t • u)‖ ^ 2 = c)
    (hF : AnalyticOnNhd ℂ F (Metric.ball 0 R))
    (hpos : ∀ z ∈ Metric.ball 0 R, z ≠ 0 →
      0 < fderiv ℝ (fun w => ‖F w‖ ^ 2) z z)
    (u : Metric.sphere (0 : ℂ) 1) :
    Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, E)
      (fun v => normalizedCurveLevelFamily hlevels (v, c)) u) := by
  let C : Metric.sphere (0 : ℂ) 1 → E := fun v =>
    (curveNormLevelCircle F R c (radialLevelHomeomorph hcont hzero hboundary hray) v : E)
  let a := (Real.sqrt c)⁻¹
  have hEq : (fun v => normalizedCurveLevelFamily hlevels (v, c)) = (fun x : E => a • x) ∘ C :=
    funext (normalizedCurveLevelFamily_eq_scaled_circle hlevels hc hcont hzero hboundary hray)
  rw [hEq]
  change Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) ((a • id) ∘ C) u)
  have hscale := (hasFDerivAt_id (𝕜 := ℝ) (C u)).const_smul a
  have hCs := curveNormLevelCircle_coe_contMDiff hcont hzero hboundary hray hF hpos
  rw [mfderiv_comp u hscale.differentiableAt.mdifferentiableAt
    (hCs.contMDiffAt.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, hscale.fderiv]
  exact (smul_right_injective E (inv_ne_zero (Real.sqrt_pos.mpr hc.1).ne')).comp
    (curveNormLevelCircle_coe_mfderiv_injective hcont hzero hboundary hray hF hpos u)

omit [CompleteSpace E] in
/-- The normalized slice has exactly the scaled image of the original
curve on the corresponding ambient sphere. -/
theorem normalizedCurveLevelFamily_slice_range
    {c : ℝ} (hc : c ∈ Set.Ioo 0 δ)
    (hcont : ContinuousOn (fun z => ‖F z‖ ^ 2) (Metric.closedBall 0 R))
    (hzero : ‖F 0‖ ^ 2 ≠ c)
    (hboundary : ∀ z : ℂ, ‖z‖ = R → ‖F z‖ ^ 2 ≠ c)
    (hray : ∀ u : ℂ, ‖u‖ = 1 →
      ∃! t : ℝ, t ∈ Set.Ioo 0 R ∧ ‖F (t • u)‖ ^ 2 = c) :
    Set.range (fun u => normalizedCurveLevelFamily hlevels (u, c)) =
      (fun y : E => (Real.sqrt c)⁻¹ • y) ''
        (Metric.sphere (0 : E) (Real.sqrt c) ∩ F '' Metric.closedBall 0 R) := by
  have hEq : (fun u => normalizedCurveLevelFamily hlevels (u, c)) =
      (fun y : E => (Real.sqrt c)⁻¹ • y) ∘ (fun u => (curveNormLevelCircle F R c
        (radialLevelHomeomorph hcont hzero hboundary hray) u : E)) :=
    funext (normalizedCurveLevelFamily_eq_scaled_circle hlevels hc hcont hzero hboundary hray)
  rw [hEq, Set.range_comp, curveNormLevelCircle_range_eq_sphere_inter_image hc.1.le]

omit hlevels in
/-- A locally injective centered analytic curve supplies a jointly smooth
family of embedded circles on the fixed ambient unit sphere. The parameter
disc lies inside any prescribed neighborhood of injectivity. -/
theorem exists_normalized_analytic_curve_level_family_subset
    (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), F z = 0)
    {S : Set ℂ} (hS : S ∈ 𝓝 0) (hi : Set.InjOn F S) :
    ∃ R δ : ℝ, 0 < R ∧ 0 < δ ∧ Metric.closedBall 0 R ⊆ S ∧
      AnalyticOnNhd ℂ F (Metric.closedBall 0 R) ∧
      ∃ K : Metric.sphere (0 : ℂ) 1 × ℝ → E,
        ∀ c ∈ Set.Ioo 0 δ,
          (∀ u, ‖K (u, c)‖ = 1) ∧
          (∀ u, ContMDiffAt ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ K (u, c)) ∧
          Topology.IsClosedEmbedding (fun u => K (u, c)) ∧
          (∀ u, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) (fun v => K (v, c)) u)) ∧
          Set.range (fun u => K (u, c)) =
            (fun y : E => (Real.sqrt c)⁻¹ • y) ''
              (Metric.sphere (0 : E) (Real.sqrt c) ∩ F '' Metric.closedBall 0 R) := by
  obtain ⟨R, hR, hRS, ha, hcont, hd, hp⟩ :=
    exists_analytic_curve_radial_ball_subset hF hF0 hne hS
  have hφ0 : ‖F 0‖ ^ 2 = 0 := by simp [hF0]
  obtain ⟨δ, hδ, hlev⟩ :=
    exists_uniform_ray_levels_of_radial_derivative_pos hR hφ0 hcont hd hp
  have hlevels : ∀ c ∈ Set.Ioo 0 δ, ∀ u : Metric.sphere (0 : ℂ) 1,
      ∃! t : ℝ, t ∈ Set.Ioo 0 R ∧ ‖F (t • (u : ℂ))‖ ^ 2 = c := by
    intro c hc u
    apply hlev u _ c hc.1 hc.2
    simpa only [Metric.mem_sphere, dist_zero_right] using u.property
  refine ⟨R, δ, hR, hδ, hRS, ha, normalizedCurveLevelFamily hlevels, ?_⟩
  intro c hc
  have hray := fun u hu => hlev u hu c hc.1 hc.2
  have hboundary : ∀ z : ℂ, ‖z‖ = R → ‖F z‖ ^ 2 ≠ c := by
    intro z hz
    exact ne_of_gt (ray_level_lt_boundary_of_radial_derivative_pos hR hcont hd hp
      (fun u hu => (hray u hu).exists) z hz)
  have hzero : ‖F 0‖ ^ 2 ≠ c := by rw [hφ0]; exact hc.1.ne
  exact ⟨fun u => normalizedCurveLevelFamily_norm hlevels (u, c) hc,
    fun u => normalizedCurveLevelFamily_contMDiffAt hlevels
      (ha.mono Metric.ball_subset_closedBall) hp (u, c) hc,
    normalizedCurveLevelFamily_slice_isClosedEmbedding hlevels hc hcont hzero hboundary hray
      (ha.mono Metric.ball_subset_closedBall) hp (hi.mono hRS),
    normalizedCurveLevelFamily_slice_mfderiv_injective hlevels hc hcont hzero hboundary hray
      (ha.mono Metric.ball_subset_closedBall) hp,
    normalizedCurveLevelFamily_slice_range hlevels hc hcont hzero hboundary hray⟩

end OnLeConjecture.Analytic
