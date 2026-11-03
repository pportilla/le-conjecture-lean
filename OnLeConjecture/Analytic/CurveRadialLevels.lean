/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CurveRadialTransversality
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Uniqueness of radial level intersections

A differentiable real function whose differential is positive on the
radial vector is strictly increasing along every ray. Continuity and the
intermediate value theorem then give a unique intersection with each
intermediate level. The hypotheses refer to the actual function and its
Fréchet differential.
-/

public section

open Set

namespace OnLeConjecture.Analytic

/-- Positive radial derivative gives strict monotonicity along a closed
ray segment, with continuity required at its endpoints. -/
theorem strictMonoOn_ray_of_radial_derivative_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} {u : E} {R : ℝ}
    (hc : ContinuousOn (fun t : ℝ => φ (t • u)) (Icc 0 R))
    (hd : ∀ t ∈ Ioo 0 R, DifferentiableAt ℝ φ (t • u))
    (hpos : ∀ t ∈ Ioo 0 R, 0 < fderiv ℝ φ (t • u) (t • u)) :
    StrictMonoOn (fun t : ℝ => φ (t • u)) (Icc 0 R) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 R) hc
  intro t ht
  rw [interior_Icc] at ht
  have hderiv : HasDerivAt (fun t : ℝ => φ (t • u))
      (fderiv ℝ φ (t • u) u) t := by
    convert! (hd t ht).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const u) using 1
    simp
  rw [hderiv.deriv]
  have hp := hpos t ht
  rw [map_smul, smul_eq_mul] at hp
  exact (mul_pos_iff_of_pos_left ht.1).mp hp

/-- Every intermediate level meets such a ray in exactly one parameter
strictly between its endpoints. -/
theorem existsUnique_ray_level_of_radial_derivative_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} {u : E} {R c : ℝ} (hR : 0 < R)
    (hc : ContinuousOn (fun t : ℝ => φ (t • u)) (Icc 0 R))
    (hd : ∀ t ∈ Ioo 0 R, DifferentiableAt ℝ φ (t • u))
    (hpos : ∀ t ∈ Ioo 0 R, 0 < fderiv ℝ φ (t • u) (t • u))
    (hlo : φ 0 < c) (hhi : c < φ (R • u)) :
    ∃! t : ℝ, t ∈ Ioo 0 R ∧ φ (t • u) = c := by
  have hm := strictMonoOn_ray_of_radial_derivative_pos hc hd hpos
  have hlevel : c ∈ Icc (φ ((0 : ℝ) • u)) (φ (R • u)) := by
    simpa only [mem_Icc, zero_smul] using And.intro hlo.le hhi.le
  obtain ⟨t, ht, htc⟩ := intermediate_value_Icc hR.le hc hlevel
  have ht0 : 0 < t := by
    apply lt_of_le_of_ne ht.1
    intro he
    subst t
    exact (ne_of_lt hlo) (by simpa only [zero_smul] using htc)
  have htR : t < R := by
    apply lt_of_le_of_ne ht.2
    intro he
    subst t
    exact (ne_of_lt hhi) htc.symm
  refine ⟨t, ⟨⟨ht0, htR⟩, htc⟩, ?_⟩
  intro s hs
  exact hm.injOn ⟨hs.1.1.le, hs.1.2.le⟩ ht (hs.2.trans htc.symm)

/-- The unit directions have a common positive interval of levels, each
of which meets every radial segment exactly once. -/
theorem exists_uniform_ray_levels_of_radial_derivative_pos
    {φ : ℂ → ℝ} {R : ℝ} (hR : 0 < R) (hzero : φ 0 = 0)
    (hc : ContinuousOn φ (Metric.closedBall 0 R))
    (hd : ∀ z ∈ Metric.ball 0 R, z ≠ 0 → DifferentiableAt ℝ φ z)
    (hpos : ∀ z ∈ Metric.ball 0 R, z ≠ 0 → 0 < fderiv ℝ φ z z) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ = 1 → ∀ c : ℝ, 0 < c → c < δ →
      ∃! t : ℝ, t ∈ Ioo 0 R ∧ φ (t • u) = c := by
  have hraynorm (u : ℂ) (hu : ‖u‖ = 1) (t : ℝ) (ht : 0 ≤ t) :
      ‖t • u‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hu, mul_one]
  have hcont (u : ℂ) (hu : ‖u‖ = 1) :
      ContinuousOn (fun t : ℝ => φ (t • u)) (Icc 0 R) :=
    hc.comp (continuous_id.smul continuous_const).continuousOn (by
      intro t ht
      simpa only [Metric.mem_closedBall, dist_zero_right, hraynorm u hu t ht.1]
        using ht.2)
  have hball (u : ℂ) (hu : ‖u‖ = 1) (t : ℝ) (ht : t ∈ Ioo 0 R) :
      t • u ∈ Metric.ball 0 R ∧ t • u ≠ 0 := by
    constructor
    · simpa only [Metric.mem_ball, dist_zero_right, hraynorm u hu t ht.1.le] using ht.2
    · exact norm_pos_iff.mp (by rw [hraynorm u hu t ht.1.le]; exact ht.1)
  have hdiff (u : ℂ) (hu : ‖u‖ = 1) (t : ℝ) (ht : t ∈ Ioo 0 R) :=
    hd (t • u) (hball u hu t ht).1 (hball u hu t ht).2
  have hrad (u : ℂ) (hu : ‖u‖ = 1) (t : ℝ) (ht : t ∈ Ioo 0 R) :=
    hpos (t • u) (hball u hu t ht).1 (hball u hu t ht).2
  have hend (u : ℂ) (hu : ‖u‖ = 1) : 0 < φ (R • u) := by
    have hm := strictMonoOn_ray_of_radial_derivative_pos (hcont u hu)
      (hdiff u hu) (hrad u hu)
    simpa only [zero_smul, hzero] using
      hm ⟨le_rfl, hR.le⟩ ⟨hR.le, le_rfl⟩ hR
  have hsphere : (Metric.sphere (0 : ℂ) 1).Nonempty :=
    ⟨1, by simp⟩
  have hboundary : ContinuousOn (fun u : ℂ => φ (R • u)) (Metric.sphere 0 1) :=
    hc.comp (continuous_id.const_smul R).continuousOn (by
      intro u hu
      have hunorm : ‖u‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hu
      simp only [Metric.mem_closedBall, dist_zero_right, hraynorm u hunorm R hR.le,
        le_refl])
  obtain ⟨u₀, hu₀, hmin⟩ := (isCompact_sphere (0 : ℂ) 1).exists_isMinOn
    hsphere hboundary
  have hu₀norm : ‖u₀‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hu₀
  refine ⟨φ (R • u₀), hend u₀ hu₀norm, ?_⟩
  intro u hu c hcpos hcsmall
  apply existsUnique_ray_level_of_radial_derivative_pos hR (hcont u hu)
    (hdiff u hu) (hrad u hu)
  · simpa only [hzero] using hcpos
  · exact hcsmall.trans_le (hmin (by simpa only [Metric.mem_sphere, dist_zero_right] using hu))

end OnLeConjecture.Analytic
