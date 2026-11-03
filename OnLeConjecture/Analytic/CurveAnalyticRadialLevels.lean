/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CurveInitialFactor
public import OnLeConjecture.Analytic.CurveRadialLevels
public import OnLeConjecture.Analytic.CurveRadialLevelHomeomorph

/-!
# Uniform radial levels of an analytic curve

Analyticity and nonconstancy supply a closed parameter ball on which the
squared Euclidean norm is continuous, differentiable, and has positive
radial derivative away from the origin. The ray-level theorem then gives
a common positive interval of levels and a unique intersection with each
unit direction. All hypotheses concern the given analytic representative.
-/

public noncomputable section

open Filter
open scoped Topology

namespace OnLeConjecture.Analytic

/-- A nonconstant analytic curve admits a closed parameter ball carrying
all differential and continuity hypotheses of the radial-level theorem. -/
theorem exists_analytic_curve_radial_ball
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {F : ℂ → E} (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), F z = 0) :
    ∃ R : ℝ, 0 < R ∧ AnalyticOnNhd ℂ F (Metric.closedBall 0 R) ∧
      ContinuousOn (fun z => ‖F z‖ ^ 2) (Metric.closedBall 0 R) ∧
      (∀ z ∈ Metric.ball 0 R, z ≠ 0 →
        DifferentiableAt ℝ (fun w => ‖F w‖ ^ 2) z) ∧
      ∀ z ∈ Metric.ball 0 R, z ≠ 0 →
        0 < fderiv ℝ (fun w => ‖F w‖ ^ 2) z z := by
  have hpos := eventually_nonconstant_curve_norm_radial_derivative_pos hF hF0 hne
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    (hF.eventually_analyticAt.and hpos)
  have hsmall (z : ℂ) (hz : z ∈ Metric.closedBall 0 (r / 2)) :
      dist z 0 < r :=
    lt_of_le_of_lt hz (half_lt_self hr)
  refine ⟨r / 2, half_pos hr, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (hball (hsmall z hz)).1
  · intro z hz
    exact ((hball (hsmall z hz)).1.continuousAt.norm.pow 2).continuousWithinAt
  · intro z hz _
    have ha := (hball (hsmall z (Metric.ball_subset_closedBall hz))).1
    have hs : ContDiffAt ℝ 1 F z := ha.restrictScalars.contDiffAt
    exact (hs.norm_sq (𝕜 := ℂ)).differentiableAt (by norm_num)
  · intro z hz hzne
    exact (hball (hsmall z (Metric.ball_subset_closedBall hz))).2 hzne

/-- Every sufficiently small positive squared-norm level of a centered
nonconstant analytic curve meets each parameter ray exactly once. -/
theorem exists_uniform_analytic_curve_norm_levels
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {F : ℂ → E} (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), F z = 0) :
    ∃ R δ : ℝ, 0 < R ∧ 0 < δ ∧
      AnalyticOnNhd ℂ F (Metric.closedBall 0 R) ∧
      ∀ u : ℂ, ‖u‖ = 1 → ∀ c : ℝ, 0 < c → c < δ →
        ∃! t : ℝ, t ∈ Set.Ioo 0 R ∧ ‖F (t • u)‖ ^ 2 = c := by
  obtain ⟨R, hR, ha, hc, hd, hp⟩ := exists_analytic_curve_radial_ball hF hF0 hne
  obtain ⟨δ, hδ, hlevels⟩ := exists_uniform_ray_levels_of_radial_derivative_pos
    hR (by simp only [hF0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow]) hc hd hp
  exact ⟨R, δ, hR, hδ, ha, hlevels⟩

/-- A level that meets every open parameter ray lies strictly below the
boundary values when the radial differential is positive. -/
theorem ray_level_lt_boundary_of_radial_derivative_pos
    {φ : ℂ → ℝ} {R c : ℝ} (hR : 0 < R)
    (hc : ContinuousOn φ (Metric.closedBall 0 R))
    (hd : ∀ z ∈ Metric.ball 0 R, z ≠ 0 → DifferentiableAt ℝ φ z)
    (hpos : ∀ z ∈ Metric.ball 0 R, z ≠ 0 → 0 < fderiv ℝ φ z z)
    (hlevel : ∀ u : ℂ, ‖u‖ = 1 →
      ∃ t : ℝ, t ∈ Set.Ioo 0 R ∧ φ (t • u) = c)
    (z : ℂ) (hz : ‖z‖ = R) : c < φ z := by
  let u : ℂ := (R⁻¹ : ℝ) • z
  have hu : ‖u‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, hz, inv_mul_cancel₀ hR.ne']
  have hRu : R • u = z := by
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  have hnorm (t : ℝ) (ht : 0 ≤ t) : ‖t • u‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hu, mul_one]
  have hcont : ContinuousOn (fun t : ℝ => φ (t • u)) (Set.Icc 0 R) :=
    hc.comp (continuous_id.smul continuous_const).continuousOn (by
      intro t ht
      simpa only [Metric.mem_closedBall, dist_zero_right, hnorm t ht.1] using ht.2)
  have hball (t : ℝ) (ht : t ∈ Set.Ioo 0 R) :
      t • u ∈ Metric.ball 0 R ∧ t • u ≠ 0 := by
    constructor
    · simpa only [Metric.mem_ball, dist_zero_right, hnorm t ht.1.le] using ht.2
    · exact norm_pos_iff.mp (by rw [hnorm t ht.1.le]; exact ht.1)
  have hm := strictMonoOn_ray_of_radial_derivative_pos hcont
    (fun t ht => hd _ (hball t ht).1 (hball t ht).2)
    (fun t ht => hpos _ (hball t ht).1 (hball t ht).2)
  obtain ⟨t, ht, heq⟩ := hlevel u hu
  have hlt := hm ⟨ht.1.le, ht.2.le⟩ ⟨hR.le, le_rfl⟩ ht.2
  simpa only [heq, hRu] using hlt

/-- Small levels have unique ray intersections and avoid the boundary of
one closed parameter ball. These are actual squared-norm levels. -/
theorem exists_uniform_analytic_curve_norm_levels_below_boundary
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {F : ℂ → E} (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), F z = 0) :
    ∃ R δ : ℝ, 0 < R ∧ 0 < δ ∧
      AnalyticOnNhd ℂ F (Metric.closedBall 0 R) ∧
      ContinuousOn (fun z => ‖F z‖ ^ 2) (Metric.closedBall 0 R) ∧
      ∀ c : ℝ, 0 < c → c < δ →
        (∀ u : ℂ, ‖u‖ = 1 →
          ∃! t : ℝ, t ∈ Set.Ioo 0 R ∧ ‖F (t • u)‖ ^ 2 = c) ∧
        ∀ z : ℂ, ‖z‖ = R → c < ‖F z‖ ^ 2 := by
  obtain ⟨R, hR, ha, hc, hd, hp⟩ := exists_analytic_curve_radial_ball hF hF0 hne
  obtain ⟨δ, hδ, hlevels⟩ := exists_uniform_ray_levels_of_radial_derivative_pos
    hR (by simp only [hF0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow]) hc hd hp
  refine ⟨R, δ, hR, hδ, ha, hc, ?_⟩
  intro c hcpos hcsmall
  refine ⟨fun u hu => hlevels u hu c hcpos hcsmall, ?_⟩
  exact ray_level_lt_boundary_of_radial_derivative_pos hR hc hd hp
    (fun u hu => (hlevels u hu c hcpos hcsmall).exists)

/-- The radial parameter ball can be chosen inside any prescribed
neighborhood of zero. -/
theorem exists_analytic_curve_radial_ball_subset
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {F : ℂ → E} (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), F z = 0)
    {S : Set ℂ} (hS : S ∈ 𝓝 0) :
    ∃ R : ℝ, 0 < R ∧ Metric.closedBall 0 R ⊆ S ∧
      AnalyticOnNhd ℂ F (Metric.closedBall 0 R) ∧
      ContinuousOn (fun z => ‖F z‖ ^ 2) (Metric.closedBall 0 R) ∧
      (∀ z ∈ Metric.ball 0 R, z ≠ 0 →
        DifferentiableAt ℝ (fun w => ‖F w‖ ^ 2) z) ∧
      ∀ z ∈ Metric.ball 0 R, z ≠ 0 →
        0 < fderiv ℝ (fun w => ‖F w‖ ^ 2) z z := by
  have hpos := eventually_nonconstant_curve_norm_radial_derivative_pos hF hF0 hne
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    (Filter.Eventually.and hS (hF.eventually_analyticAt.and hpos))
  have hsmall (z : ℂ) (hz : z ∈ Metric.closedBall 0 (r / 2)) :
      dist z 0 < r := lt_of_le_of_lt hz (half_lt_self hr)
  refine ⟨r / 2, half_pos hr, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (hball (hsmall z hz)).1
  · intro z hz
    exact (hball (hsmall z hz)).2.1
  · intro z hz
    exact ((hball (hsmall z hz)).2.1.continuousAt.norm.pow 2).continuousWithinAt
  · intro z hz _
    have ha := (hball (hsmall z (Metric.ball_subset_closedBall hz))).2.1
    have hs : ContDiffAt ℝ 1 F z := ha.restrictScalars.contDiffAt
    exact (hs.norm_sq (𝕜 := ℂ)).differentiableAt (by norm_num)
  · intro z hz hzne
    exact (hball (hsmall z (Metric.ball_subset_closedBall hz))).2.2 hzne

/-- Small squared-norm levels of a nonconstant analytic curve are
homeomorphic to the unit circle, with the parameter ball inside any
prescribed neighborhood. -/
theorem exists_analytic_curve_norm_level_homeomorphs_subset
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {F : ℂ → E} (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), F z = 0)
    {S : Set ℂ} (hS : S ∈ 𝓝 0) :
    ∃ R δ : ℝ, 0 < R ∧ 0 < δ ∧ Metric.closedBall 0 R ⊆ S ∧
      AnalyticOnNhd ℂ F (Metric.closedBall 0 R) ∧
      ∀ c : ℝ, 0 < c → c < δ →
        Nonempty (radialLevelSet (fun z => ‖F z‖ ^ 2) R c ≃ₜ
          Metric.sphere (0 : ℂ) 1) := by
  obtain ⟨R, hR, hRS, ha, hc, hd, hp⟩ :=
    exists_analytic_curve_radial_ball_subset hF hF0 hne hS
  obtain ⟨δ, hδ, hlevels⟩ := exists_uniform_ray_levels_of_radial_derivative_pos
    hR (by simp only [hF0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow]) hc hd hp
  refine ⟨R, δ, hR, hδ, hRS, ha, ?_⟩
  intro c hcpos hcsmall
  have hray := fun u hu => hlevels u hu c hcpos hcsmall
  have hboundary : ∀ z : ℂ, ‖z‖ = R → ‖F z‖ ^ 2 ≠ c := by
    intro z hz
    exact ne_of_gt (ray_level_lt_boundary_of_radial_derivative_pos hR hc hd hp
      (fun u hu => (hray u hu).exists) z hz)
  have hzero : ‖F 0‖ ^ 2 ≠ c := by
    simpa only [hF0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      using hcpos.ne
  exact ⟨radialLevelHomeomorph hc hzero hboundary hray⟩

/-- If the analytic representative is locally injective, the ball for its
circular norm levels can be chosen so that it remains injective on the
whole closed ball. -/
theorem exists_injective_analytic_curve_norm_level_homeomorphs
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {F : ℂ → E} (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), F z = 0)
    (hi : ∃ S ∈ 𝓝 (0 : ℂ), Set.InjOn F S) :
    ∃ R δ : ℝ, 0 < R ∧ 0 < δ ∧
      AnalyticOnNhd ℂ F (Metric.closedBall 0 R) ∧
      Set.InjOn F (Metric.closedBall 0 R) ∧
      ∀ c : ℝ, 0 < c → c < δ →
        Nonempty (radialLevelSet (fun z => ‖F z‖ ^ 2) R c ≃ₜ
          Metric.sphere (0 : ℂ) 1) := by
  obtain ⟨S, hS, hinj⟩ := hi
  obtain ⟨R, δ, hR, hδ, hRS, ha, hlevels⟩ :=
    exists_analytic_curve_norm_level_homeomorphs_subset hF hF0 hne hS
  exact ⟨R, δ, hR, hδ, ha, hinj.mono hRS, hlevels⟩

namespace PointedMapGerm

/-- Every injective analytic curve germ has an injective Euclidean
representative on a closed parameter ball whose small squared-norm levels
are homeomorphic to the unit circle. -/
theorem exists_injective_euclidean_norm_level_homeomorphs
    {n : ℕ} (g : PointedMapGerm 1 n) (hi : g.HasInjectiveRepresentative) :
    ∃ G : Source 1 → Source n, ∃ hG : AnalyticAt ℂ G 0, ∃ hG0 : G 0 = 0,
      g = PointedMapGerm.ofFunction G hG hG0 ∧
      ∃ R δ : ℝ, 0 < R ∧ 0 < δ ∧
        let F : ℂ → EuclideanSpace ℂ (Fin n) := fun z =>
          (EuclideanSpace.equiv (Fin n) ℂ).symm (G (curveParameterEquiv.symm z))
        AnalyticOnNhd ℂ F (Metric.closedBall 0 R) ∧
        Set.InjOn F (Metric.closedBall 0 R) ∧
        ∀ c : ℝ, 0 < c → c < δ →
          Nonempty (radialLevelSet (fun z => ‖F z‖ ^ 2) R c ≃ₜ
            Metric.sphere (0 : ℂ) 1) := by
  obtain ⟨G, hG, hG0, hg, d, hd, U, r, hr, hFball, hinj, hUball, hUnz, hfactor⟩ :=
    g.exists_injective_euclidean_curve_initial_factor_on_ball hi
  let F : ℂ → EuclideanSpace ℂ (Fin n) := fun z =>
    (EuclideanSpace.equiv (Fin n) ℂ).symm (G (curveParameterEquiv.symm z))
  have hmem : (0 : ℂ) ∈ Metric.ball 0 r := Metric.mem_ball_self hr
  have hF : AnalyticAt ℂ F 0 := hFball 0 hmem
  have hF0 : F 0 = 0 := by
    change (EuclideanSpace.equiv (Fin n) ℂ).symm
      (G (curveParameterEquiv.symm 0)) = 0
    rw [map_zero, hG0, map_zero]
  have hfact : F =ᶠ[𝓝 0] fun z => (z - 0) ^ d • U z := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with z hz
    simpa only [sub_zero] using hfactor z hz
  have hnF : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), F z = 0 :=
    hF.exists_eventuallyEq_pow_smul_nonzero_iff.mp
      ⟨d, U, hUball 0 hmem, hUnz 0 hmem, hfact⟩
  refine ⟨G, hG, hG0, hg, ?_⟩
  exact exists_injective_analytic_curve_norm_level_homeomorphs hF hF0 hnF
    ⟨Metric.ball 0 r, Metric.ball_mem_nhds _ hr, hinj⟩

end PointedMapGerm

end OnLeConjecture.Analytic
