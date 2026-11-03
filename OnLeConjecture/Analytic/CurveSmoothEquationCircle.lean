/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CurveLocalImageShrink
public import OnLeConjecture.Analytic.CurveSmoothLevelCircle

/-!
# Smooth sphere intersections of a parametrized local zero set

Local image coverage and shrinking of the parameter disc identify each
small sphere intersection with the constructed smooth norm-level circle.
The same parametrization is a closed embedding and has injective
differential in the ambient vector space.
-/

public noncomputable section

open Filter Set
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

namespace OnLeConjecture.Analytic

/-- A locally injective analytic parametrization covering the zero set
gives smooth embedded circles on every sufficiently small ambient sphere. -/
theorem exists_smooth_sphere_zero_set_circle_of_parametrization
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {F : ℂ → E} {H : E → ℂ} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), F z = 0)
    (hc : ContinuousOn F (Metric.closedBall 0 R₀))
    (hi : InjOn F (Metric.closedBall 0 R₀))
    (himage : ∀ᶠ y in 𝓝 (0 : E), H y = 0 ↔ y ∈ F '' Metric.closedBall 0 R₀) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ L : Metric.sphere (0 : ℂ) 1 → Metric.sphere (0 : E) ε,
        Topology.IsClosedEmbedding L ∧
        ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ (fun u => (L u : E)) ∧
        (∀ u, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) (fun v => (L v : E)) u)) ∧
        Set.range (fun u => (L u : E)) = Metric.sphere 0 ε ∩ {y | H y = 0} := by
  obtain ⟨R, δ, hR, hδ, hsub, _, _, hlevels⟩ :=
    exists_smooth_injective_curve_norm_level_circles_subset hF hF0 hne
      (Metric.closedBall_mem_nhds (0 : ℂ) hR₀) hi
  have hRR₀ : R ≤ R₀ := by
    have hz : (R : ℂ) ∈ Metric.closedBall 0 R := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hR] using le_rfl (a := R)
    simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR] using hsub hz
  have hzero : ∀ z ∈ Metric.closedBall 0 R₀, F z = 0 → z = 0 := by
    intro z hz hFz
    exact hi hz (Metric.mem_closedBall_self hR₀.le) (hFz.trans hF0.symm)
  have himageR := eventually_equation_zero_iff_mem_smaller_curve_image hR hRR₀ hc hzero himage
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp himageR
  refine ⟨min (Real.sqrt δ) r, lt_min (Real.sqrt_pos.mpr hδ) hr, ?_⟩
  intro ε hε hεsmall
  have hεδ : ε ^ 2 < δ := (Real.lt_sqrt hε.le).mp ((lt_min_iff.mp hεsmall).1)
  have hεr : ε < r := (lt_min_iff.mp hεsmall).2
  obtain ⟨e, he, hs, hd, hrange⟩ := hlevels (ε ^ 2) (sq_pos_of_pos hε) hεδ
  have hex : ∃ L : Metric.sphere (0 : ℂ) 1 → Metric.sphere (0 : E) ε,
      Topology.IsClosedEmbedding L ∧
      ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ (fun u => (L u : E)) ∧
      (∀ u, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) (fun v => (L v : E)) u)) ∧
      Set.range (fun u => (L u : E)) =
        Metric.sphere 0 ε ∩ F '' Metric.closedBall 0 R := by
    have hraw : ∃ L : Metric.sphere (0 : ℂ) 1 → Metric.sphere (0 : E) (Real.sqrt (ε ^ 2)),
        Topology.IsClosedEmbedding L ∧
        ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ (fun u => (L u : E)) ∧
        (∀ u, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) (fun v => (L v : E)) u)) ∧
        Set.range (fun u => (L u : E)) =
          Metric.sphere 0 (Real.sqrt (ε ^ 2)) ∩ F '' Metric.closedBall 0 R :=
      ⟨curveNormLevelCircle F R (ε ^ 2) e, he, hs, hd, hrange⟩
    rw [Real.sqrt_sq hε.le] at hraw
    exact hraw
  obtain ⟨L, hL, hs, hd, hrange⟩ := hex
  refine ⟨L, hL, hs, hd, hrange.trans ?_⟩
  ext y
  simp only [mem_inter_iff, mem_ofPred_eq]
  apply and_congr_right
  intro hy
  have hdist : dist y 0 < r := by
    have hnorm : ‖y‖ = ε := by simpa only [Metric.mem_sphere, dist_zero_right] using hy
    simpa only [dist_zero_right, hnorm] using hεr
  exact (hball hdist).symm

end OnLeConjecture.Analytic
