/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CurveAnalyticRadialLevels
public import OnLeConjecture.External.TauCeti.Analysis.Calculus.JointImplicitFunctionSmooth

/-!
# Smooth dependence of the radial radius

A positive radial derivative makes the derivative with respect to the real
radius invertible. The joint implicit function theorem therefore solves
`φ(t • u) = c` by a radius depending smoothly on both the direction `u`
and the level `c`. This supplies actual local functions and their inverse
identities, with no assumed smoothness of a topological level parametrization.
-/

public noncomputable section

open Filter
open scoped Topology ContDiff

namespace OnLeConjecture.Analytic

/-- Positive radial derivative gives a smooth local radius function of
both the direction and the level. -/
theorem exists_smooth_joint_radial_radius
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {φ : E → ℝ} {u : E} {t : ℝ} (ht : 0 < t)
    (hφ : ContDiffAt ℝ ∞ φ (t • u))
    (hpos : 0 < fderiv ℝ φ (t • u) (t • u)) :
    ∃ ρ : E × ℝ → ℝ, ContDiffAt ℝ ∞ ρ (u, φ (t • u)) ∧
      ρ (u, φ (t • u)) = t ∧
      (∀ᶠ p in 𝓝 (u, φ (t • u)), φ (ρ p • p.1) = p.2) ∧
      ∀ᶠ p in 𝓝 (u, t), ρ (p.1, φ (p.2 • p.1)) = p.2 := by
  let H : E × ℝ → ℝ := fun p => φ (p.2 • p.1)
  have hH : ContDiffAt ℝ ∞ H (u, t) :=
    hφ.comp (u, t) (contDiffAt_snd.smul contDiffAt_fst)
  let a : ℝ := fderiv ℝ φ (t • u) u
  have ha : 0 < a := by
    rw [map_smul, smul_eq_mul] at hpos
    exact (mul_pos_iff_of_pos_left ht).mp hpos
  have hd : HasDerivAt (fun r : ℝ => H (u, r)) a t :=
    (hφ.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
      (by simpa only [id_eq, one_smul] using (hasDerivAt_id t).smul_const u)
  have hpartial : fderiv ℝ H (u, t) ∘L .inr ℝ E ℝ =
      ContinuousLinearEquiv.unitsEquivAut ℝ (.mk0 a ha.ne') := by
    have hd' : HasFDerivAt (fun r : ℝ => H (u, r))
        (fderiv ℝ H (u, t) ∘L .inr ℝ E ℝ) t :=
      (hH.differentiableAt (by simp)).hasFDerivAt.comp t (hasFDerivAt_prodMk_right u t)
    ext
    simpa using hd'.hasDerivAt.unique hd
  have hi : (fderiv ℝ H (u, t) ∘L .inr ℝ E ℝ).IsInvertible :=
    ⟨_, hpartial.symm⟩
  have hdH := hH.hasStrictFDerivAt (by simp)
  refine ⟨hdH.jointImplicitFunctionOfProdDomain hi,
    hdH.contDiffAt_jointImplicitFunctionOfProdDomain hi hH,
    hdH.jointImplicitFunctionOfProdDomain_apply_self hi, ?_, ?_⟩
  · exact hdH.eventually_apply_jointImplicitFunctionOfProdDomain hi
  · exact hdH.eventually_jointImplicitFunctionOfProdDomain_apply hi

/-- At a regular radial point of an analytic curve, its squared-norm
radius depends smoothly on direction and on the squared-norm level. -/
theorem exists_smooth_joint_radius_of_analytic_curve
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {F : ℂ → E} {u : ℂ} {t : ℝ} (ht : 0 < t)
    (hF : AnalyticAt ℂ F (t • u))
    (hpos : 0 < fderiv ℝ (fun z => ‖F z‖ ^ 2) (t • u) (t • u)) :
    ∃ ρ : ℂ × ℝ → ℝ, ContDiffAt ℝ ∞ ρ (u, ‖F (t • u)‖ ^ 2) ∧
      ρ (u, ‖F (t • u)‖ ^ 2) = t ∧
      (∀ᶠ p in 𝓝 (u, ‖F (t • u)‖ ^ 2), ‖F (ρ p • p.1)‖ ^ 2 = p.2) ∧
      ∀ᶠ p in 𝓝 (u, t), ρ (p.1, ‖F (p.2 • p.1)‖ ^ 2) = p.2 := by
  have hs : ContDiffAt ℝ ∞ F (t • u) := hF.restrictScalars.contDiffAt
  exact exists_smooth_joint_radial_radius ht (hs.norm_sq (𝕜 := ℂ)) hpos

/-- Every sufficiently small positive squared-norm level of a nonconstant
analytic curve has a smooth local radius function at every unit direction.
The analytic hypothesis supplies all radial regularity assumptions. -/
theorem exists_uniform_smooth_joint_curve_radii
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {F : ℂ → E} (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), F z = 0) :
    ∃ R δ : ℝ, 0 < R ∧ 0 < δ ∧
      ∀ u : ℂ, ‖u‖ = 1 → ∀ c : ℝ, 0 < c → c < δ →
        ∃ t : ℝ, t ∈ Set.Ioo 0 R ∧ ‖F (t • u)‖ ^ 2 = c ∧
          ∃ ρ : ℂ × ℝ → ℝ, ContDiffAt ℝ ∞ ρ (u, c) ∧ ρ (u, c) = t ∧
            (∀ᶠ p in 𝓝 (u, c), ‖F (ρ p • p.1)‖ ^ 2 = p.2) ∧
            ∀ᶠ p in 𝓝 (u, t), ρ (p.1, ‖F (p.2 • p.1)‖ ^ 2) = p.2 := by
  obtain ⟨R, hR, ha, hc, hd, hp⟩ := exists_analytic_curve_radial_ball hF hF0 hne
  obtain ⟨δ, hδ, hlevels⟩ := exists_uniform_ray_levels_of_radial_derivative_pos
    hR (by simp only [hF0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow]) hc hd hp
  refine ⟨R, δ, hR, hδ, ?_⟩
  intro u hu c hcpos hcsmall
  obtain ⟨t, ⟨ht, heq⟩, _⟩ := hlevels u hu c hcpos hcsmall
  have hnorm : ‖t • u‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1, hu, mul_one]
  have hball : t • u ∈ Metric.ball 0 R := by
    simpa only [Metric.mem_ball, dist_zero_right, hnorm] using ht.2
  have hneparam : t • u ≠ 0 := norm_pos_iff.mp (by rw [hnorm]; exact ht.1)
  have hradius := exists_smooth_joint_radius_of_analytic_curve ht.1
    (ha _ (Metric.ball_subset_closedBall hball)) (hp _ hball hneparam)
  rw [heq] at hradius
  exact ⟨t, ht, heq, hradius⟩

end OnLeConjecture.Analytic
