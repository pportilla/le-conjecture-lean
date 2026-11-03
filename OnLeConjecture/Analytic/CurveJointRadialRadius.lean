/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CurveSmoothLevelCircle

/-!
# Smooth dependence of the radial radius on the level

Unique ray intersections define a radius for every unit direction and
every level in an open interval. The local joint implicit function has
values in the same parameter interval near each such point. Uniqueness
therefore identifies it with the chosen radius and proves joint smoothness.
-/

public noncomputable section

open Filter
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

namespace OnLeConjecture.Analytic

variable {φ : ℂ → ℝ} {R δ : ℝ}
    (hlevels : ∀ c ∈ Set.Ioo 0 δ, ∀ u : Metric.sphere (0 : ℂ) 1,
      ∃! t : ℝ, t ∈ Set.Ioo 0 R ∧ φ (t • (u : ℂ)) = c)

/-- The unique ray radius at a level in `(0,δ)`, extended by zero outside
that interval so that smoothness can be stated on an open subset. -/
@[expose] def jointRadialRadius (p : Metric.sphere (0 : ℂ) 1 × ℝ) : ℝ :=
  if hp : p.2 ∈ Set.Ioo 0 δ then Classical.choose (hlevels p.2 hp p.1) else 0

theorem jointRadialRadius_spec (p : Metric.sphere (0 : ℂ) 1 × ℝ)
    (hp : p.2 ∈ Set.Ioo 0 δ) :
    jointRadialRadius hlevels p ∈ Set.Ioo 0 R ∧
      φ (jointRadialRadius hlevels p • (p.1 : ℂ)) = p.2 := by
  simp only [jointRadialRadius, dif_pos hp]
  exact (Classical.choose_spec (hlevels p.2 hp p.1)).1

/-- Any radius in the parameter interval satisfying the level equation
is the chosen radius. -/
theorem jointRadialRadius_eq_of_spec (p : Metric.sphere (0 : ℂ) 1 × ℝ)
    (hp : p.2 ∈ Set.Ioo 0 δ) {t : ℝ} (ht : t ∈ Set.Ioo 0 R)
    (heq : φ (t • (p.1 : ℂ)) = p.2) : jointRadialRadius hlevels p = t :=
  (hlevels p.2 hp p.1).unique (jointRadialRadius_spec hlevels p hp) ⟨ht, heq⟩

/-- The radius is jointly smooth in unit direction and level wherever
the level lies in the prescribed open interval. -/
theorem jointRadialRadius_contMDiffAt
    (hsmooth : ∀ z ∈ Metric.ball 0 R, ContDiffAt ℝ ∞ φ z)
    (hpos : ∀ z ∈ Metric.ball 0 R, z ≠ 0 → 0 < fderiv ℝ φ z z)
    (p : Metric.sphere (0 : ℂ) 1 × ℝ) (hp : p.2 ∈ Set.Ioo 0 δ) :
    ContMDiffAt ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ (jointRadialRadius hlevels) p := by
  let r := jointRadialRadius hlevels
  have hr := jointRadialRadius_spec hlevels p hp
  have hu : ‖(p.1 : ℂ)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.1.property
  have hnorm : ‖r p • (p.1 : ℂ)‖ = r p := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1.1, hu, mul_one]
  have hball : r p • (p.1 : ℂ) ∈ Metric.ball 0 R := by
    simpa only [Metric.mem_ball, dist_zero_right, hnorm] using hr.1.2
  have hnz : r p • (p.1 : ℂ) ≠ 0 := norm_pos_iff.mp (by rw [hnorm]; exact hr.1.1)
  obtain ⟨ρ, hρ, hρ0, hsolve, _⟩ :=
    exists_smooth_joint_radial_radius hr.1.1 (hsmooth _ hball) (hpos _ hball hnz)
  have hlevel : φ (r p • (p.1 : ℂ)) = p.2 := (jointRadialRadius_spec hlevels p hp).2
  rw [hlevel] at hρ hρ0 hsolve
  let J : Metric.sphere (0 : ℂ) 1 × ℝ → ℂ × ℝ := fun q => ((q.1 : ℂ), q.2)
  have hJ : Continuous J := (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hJt : Tendsto J (𝓝 p) (𝓝 ((p.1 : ℂ), p.2)) := hJ.continuousAt.tendsto
  have hrho : ∀ᶠ q in 𝓝 p, ρ (J q) ∈ Set.Ioo 0 R := by
    apply (hρ.continuousAt.tendsto.comp hJt).eventually
    exact isOpen_Ioo.mem_nhds (by rw [hρ0]; exact (jointRadialRadius_spec hlevels p hp).1)
  have hlevelmem : ∀ᶠ q : Metric.sphere (0 : ℂ) 1 × ℝ in 𝓝 p,
      q.2 ∈ Set.Ioo 0 δ :=
    continuous_snd.continuousAt.eventually (isOpen_Ioo.mem_nhds hp)
  have hagree : r =ᶠ[𝓝 p] fun q => ρ (J q) := by
    filter_upwards [hlevelmem, hrho, hJt.eventually hsolve] with q hq ht hsol
    exact (hlevels q.2 hq q.1).unique
      (jointRadialRadius_spec hlevels q hq) ⟨ht, hsol⟩
  have hJsmooth : ContMDiffAt ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ × ℝ) ∞ J p :=
    ((contMDiff_coe_sphere (m := ∞)).contMDiffAt.comp p contMDiffAt_fst).prodMk_space
      contMDiffAt_snd
  exact (hρ.contMDiffAt.comp p hJsmooth).congr_of_eventuallyEq hagree

/-- The parameter point on the level varies smoothly with both its
direction and its level. -/
theorem jointRadialParameter_contMDiffAt
    (hsmooth : ∀ z ∈ Metric.ball 0 R, ContDiffAt ℝ ∞ φ z)
    (hpos : ∀ z ∈ Metric.ball 0 R, z ≠ 0 → 0 < fderiv ℝ φ z z)
    (p : Metric.sphere (0 : ℂ) 1 × ℝ) (hp : p.2 ∈ Set.Ioo 0 δ) :
    ContMDiffAt ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ) ∞
      (fun q => jointRadialRadius hlevels q • (q.1 : ℂ)) p :=
  (jointRadialRadius_contMDiffAt hlevels hsmooth hpos p hp).smul
    ((contMDiff_coe_sphere (m := ∞)).contMDiffAt.comp p contMDiffAt_fst)

end OnLeConjecture.Analytic
