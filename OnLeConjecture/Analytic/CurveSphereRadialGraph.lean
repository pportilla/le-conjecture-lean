/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CurveJointRadialRadius
public import OnLeConjecture.Analytic.CurveLocalImageShrink

/-! # Exact small sphere links as positive radial graphs of the same curve -/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

namespace OnLeConjecture.Analytic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option backward.isDefEq.respectTransparency false in
/-- A fixed injective representative covering an equation near zero has
small sphere links given by smooth positive radial graphs in that same
parameter disk. The sphere radius and equation are literal. -/
theorem exists_small_sphere_radialGraph {F : ℂ → E} (hF : AnalyticAt ℂ F 0)
    (hF0 : F 0 = 0) (hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), F z = 0)
    {R : ℝ} (hR : 0 < R) (hcont : ContinuousOn F (closedBall 0 R))
    (hi : InjOn F (closedBall 0 R)) (H : E → ℂ)
    (himage : ∀ᶠ y in 𝓝 (0 : E), H y = 0 ↔ y ∈ F '' closedBall 0 R) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ ρ : Circle → ℝ,
        (∀ u, 0 < ρ u ∧ ρ u < R) ∧
        ContMDiff (𝓡 1) 𝓘(ℝ) ∞ ρ ∧
        (∀ u, 0 < fderiv ℝ (fun z => ‖F z‖ ^ 2)
          (ρ u • (u : ℂ)) (ρ u • (u : ℂ))) ∧
        (∀ u, ‖F (ρ u • (u : ℂ))‖ = ε) ∧
        range (fun u => F (ρ u • (u : ℂ))) = sphere 0 ε ∩ {y | H y = 0} := by
  obtain ⟨r, hr, hrR, ha, hc, hd, hp⟩ :=
    exists_analytic_curve_radial_ball_subset hF hF0 hne (ball_mem_nhds (0 : ℂ) hR)
  have hrlt : r < R := by
    have hm : (r : ℂ) ∈ closedBall (0 : ℂ) r := by
      simpa only [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr] using (le_rfl : r ≤ r)
    have h := hrR hm
    simpa only [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using h
  have hzero (z : ℂ) (hz : z ∈ closedBall 0 R) (hz0 : F z = 0) : z = 0 :=
    hi hz (mem_closedBall_self hR.le) (hz0.trans hF0.symm)
  have heq := eventually_equation_zero_iff_mem_smaller_curve_image
    hr hrlt.le hcont hzero himage
  obtain ⟨η, hη, hηeq⟩ := Metric.eventually_nhds_iff.mp heq
  have hφ0 : ‖F 0‖ ^ 2 = 0 := by simp only [hF0, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow]
  obtain ⟨δ, hδ, hlevels⟩ := exists_uniform_ray_levels_of_radial_derivative_pos hr hφ0 hc hd hp
  have hlev : ∀ c ∈ Ioo 0 δ, ∀ u : Circle,
      ∃! t : ℝ, t ∈ Ioo 0 r ∧ ‖F (t • (u : ℂ))‖ ^ 2 = c :=
    fun c hc u => hlevels u (Circle.norm_coe u) c hc.1 hc.2
  have hsmooth : ∀ z ∈ ball 0 r, ContDiffAt ℝ ∞ (fun w => ‖F w‖ ^ 2) z :=
    fun z hz => (ha z (ball_subset_closedBall hz)).restrictScalars.contDiffAt.norm_sq (𝕜 := ℂ)
  refine ⟨min (Real.sqrt δ) η, lt_min (Real.sqrt_pos.mpr hδ) hη, ?_⟩
  intro ε hε hεsmall
  have hεδ : ε < Real.sqrt δ := hεsmall.trans_le (min_le_left _ _)
  have hεη : ε < η := hεsmall.trans_le (min_le_right _ _)
  have hεsq : ε ^ 2 ∈ Ioo 0 δ := by
    refine ⟨sq_pos_of_pos hε, ?_⟩
    have h := (sq_lt_sq₀ hε.le (Real.sqrt_nonneg δ)).mpr hεδ
    rwa [Real.sq_sqrt hδ.le] at h
  let ρ : Circle → ℝ := fun u => jointRadialRadius (φ := fun z => ‖F z‖ ^ 2) hlev (u, ε ^ 2)
  have hρ (u : Circle) := jointRadialRadius_spec (φ := fun z => ‖F z‖ ^ 2) hlev (u, ε ^ 2) hεsq
  have hn (u : Circle) : ‖F (ρ u • (u : ℂ))‖ = ε := by
    have h := (hρ u).2
    change ‖F (ρ u • (u : ℂ))‖ ^ 2 = ε ^ 2 at h
    nlinarith [norm_nonneg (F (ρ u • (u : ℂ)))]
  refine ⟨ρ, fun u => ⟨(hρ u).1.1, (hρ u).1.2.trans hrlt⟩, ?_, ?_, hn, ?_⟩
  · intro u
    exact (jointRadialRadius_contMDiffAt (φ := fun z => ‖F z‖ ^ 2)
      hlev hsmooth hp (u, ε ^ 2) hεsq).comp u
      (contMDiffAt_id.prodMk contMDiffAt_const)
  · intro u
    have hnorm : ‖ρ u • (u : ℂ)‖ = ρ u := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hρ u).1.1, Circle.norm_coe, mul_one]
    apply hp _ (mem_ball_zero_iff.mpr (by rw [hnorm]; exact (hρ u).1.2))
    exact norm_pos_iff.mp (by rw [hnorm]; exact (hρ u).1.1)
  · ext y
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨mem_sphere_zero_iff_norm.mpr (hn u), ?_⟩
      apply (hηeq (by simpa only [dist_zero_right, hn] using hεη)).mpr
      refine ⟨ρ u • (u : ℂ), ?_, rfl⟩
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
        abs_of_pos (hρ u).1.1, Circle.norm_coe, mul_one]
      exact (hρ u).1.2.le
    · rintro ⟨hys, hyH⟩
      have hyn : ‖y‖ = ε := mem_sphere_zero_iff_norm.mp hys
      obtain ⟨z, hz, hzy⟩ := (hηeq (by simpa only [dist_zero_right, hyn] using hεη)).mp hyH
      have hz0 : z ≠ 0 := by
        intro hz0
        rw [hz0, hF0] at hzy
        rw [← hzy, norm_zero] at hyn
        exact hε.ne' hyn.symm
      have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      let u : Circle := ⟨‖z‖⁻¹ • z, by
        apply mem_sphere_zero_iff_norm.mpr
        rw [norm_smul, Real.norm_eq_abs, abs_inv,
          abs_of_pos hzn, inv_mul_cancel₀ hzn.ne']⟩
      have huzu : ‖z‖ • (u : ℂ) = z := by
        change ‖z‖ • (‖z‖⁻¹ • z) = z
        rw [smul_smul, mul_inv_cancel₀ hzn.ne', one_smul]
      have hzr : ‖z‖ < r := by
        have hbound := ray_level_lt_boundary_of_radial_derivative_pos hr hc hd hp
          (fun v hv => (hlevels v hv (ε ^ 2) hεsq.1 hεsq.2).exists)
        by_contra hnot
        have hzeq : ‖z‖ = r := le_antisymm (mem_closedBall_zero_iff.mp hz) (not_lt.mp hnot)
        have h := hbound z hzeq
        rw [hzy, hyn] at h
        exact lt_irrefl _ h
      have hrad : ρ u = ‖z‖ := jointRadialRadius_eq_of_spec
        (φ := fun z => ‖F z‖ ^ 2) hlev (u, ε ^ 2) hεsq
        ⟨hzn, hzr⟩ (by rw [huzu, hzy, hyn])
      exact ⟨u, by change F (ρ u • (u : ℂ)) = y; rw [hrad, huzu, hzy]⟩

end OnLeConjecture.Analytic
