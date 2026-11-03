/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CurveNormalizedLevelFamily
public import OnLeConjecture.Analytic.CurveLocalImageShrink

/-!
# Normalized smooth families of local curve zero sets

The whole small-sphere zero set is parametrized on a fixed unit sphere.
The family varies smoothly with the squared ambient radius and each slice
is a closed embedding with injective differential.
-/

public noncomputable section

open Filter Set
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

namespace OnLeConjecture.Analytic

/-- Local image coverage identifies the normalized family with the
entire equation zero set on every sufficiently small sphere. -/
theorem exists_normalized_zero_set_family_of_parametrization
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {F : ℂ → E} {H : E → ℂ} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), F z = 0)
    (hc : ContinuousOn F (Metric.closedBall 0 R₀))
    (hi : InjOn F (Metric.closedBall 0 R₀))
    (himage : ∀ᶠ y in 𝓝 (0 : E), H y = 0 ↔ y ∈ F '' Metric.closedBall 0 R₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K : Metric.sphere (0 : ℂ) 1 × ℝ → E,
      ∀ c ∈ Set.Ioo 0 δ,
        (∀ u, ‖K (u, c)‖ = 1) ∧
        (∀ u, ContMDiffAt ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ K (u, c)) ∧
        Topology.IsClosedEmbedding (fun u => K (u, c)) ∧
        (∀ u, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) (fun v => K (v, c)) u)) ∧
        Set.range (fun u => K (u, c)) =
          (fun y : E => (Real.sqrt c)⁻¹ • y) ''
            (Metric.sphere (0 : E) (Real.sqrt c) ∩ {y | H y = 0}) := by
  obtain ⟨R, δ, hR, hδ, hsub, _, K, hK⟩ :=
    exists_normalized_analytic_curve_level_family_subset hF hF0 hne
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
  refine ⟨min δ (r ^ 2), lt_min hδ (sq_pos_of_pos hr), K, ?_⟩
  intro c hc
  have hcd : c ∈ Set.Ioo 0 δ := ⟨hc.1, lt_of_lt_of_le hc.2 (min_le_left _ _)⟩
  have hcr : Real.sqrt c < r :=
    (Real.sqrt_lt' hr).mpr (lt_of_lt_of_le hc.2 (min_le_right _ _))
  obtain ⟨hn, hs, he, hd, hrange⟩ := hK c hcd
  refine ⟨hn, hs, he, hd, hrange.trans ?_⟩
  congr 1
  ext y
  simp only [mem_inter_iff, mem_ofPred_eq]
  apply and_congr_right
  intro hy
  have hdist : dist y 0 < r := by
    have hnorm : ‖y‖ = Real.sqrt c := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hy
    simpa only [dist_zero_right, hnorm] using hcr
  exact (hball hdist).symm

end OnLeConjecture.Analytic
