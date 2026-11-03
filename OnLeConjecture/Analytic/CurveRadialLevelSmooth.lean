/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CurveSmoothRadialRadius
public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Smoothness of the inverse radial projection

The inverse radial homeomorphism has radius equal to the norm of its
parameter point. This radius is continuous. The local joint implicit
radius agrees with it by the proved inverse identity, so the radius and
the inverse parameter map are smooth on the standard unit circle.
-/

public noncomputable section

open Filter
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

namespace OnLeConjecture.Analytic

variable {φ : ℂ → ℝ} {R c : ℝ}
    (hc : ContinuousOn φ (Metric.closedBall 0 R)) (hzero : φ 0 ≠ c)
    (hboundary : ∀ z : ℂ, ‖z‖ = R → φ z ≠ c)
    (hray : ∀ u : ℂ, ‖u‖ = 1 →
      ∃! t : ℝ, t ∈ Set.Ioo 0 R ∧ φ (t • u) = c)

/-- The radius of the unique point of a level in each unit direction. -/
@[expose] def radialLevelRadius (u : Metric.sphere (0 : ℂ) 1) : ℝ :=
  ‖((radialLevelHomeomorph hc hzero hboundary hray).symm u : ℂ)‖

/-- The radius is continuous because the inverse radial map is a
homeomorphism. -/
theorem radialLevelRadius_continuous :
    Continuous (radialLevelRadius hc hzero hboundary hray) :=
  (continuous_subtype_val.comp
    (radialLevelHomeomorph hc hzero hboundary hray).symm.continuous).norm

/-- The radius is strictly between zero and the parameter-disc radius. -/
theorem radialLevelRadius_mem_Ioo (u : Metric.sphere (0 : ℂ) 1) :
    radialLevelRadius hc hzero hboundary hray u ∈ Set.Ioo 0 R := by
  let z := (radialLevelHomeomorph hc hzero hboundary hray).symm u
  refine ⟨norm_pos_iff.mpr (radialLevelSet_ne_zero hzero z), ?_⟩
  exact lt_of_le_of_ne z.property.1 (fun he => hboundary z he z.property.2)

/-- The inverse radial projection is recovered by multiplying direction
by its radius. -/
theorem radialLevelRadius_smul (u : Metric.sphere (0 : ℂ) 1) :
    radialLevelRadius hc hzero hboundary hray u • (u : ℂ) =
      ((radialLevelHomeomorph hc hzero hboundary hray).symm u : ℂ) := by
  let e := radialLevelHomeomorph hc hzero hboundary hray
  have h := congrArg (fun v : Metric.sphere (0 : ℂ) 1 => (v : ℂ)) (e.apply_symm_apply u)
  have hdir : ‖(e.symm u : ℂ)‖⁻¹ • (e.symm u : ℂ) = (u : ℂ) := h
  change ‖(e.symm u : ℂ)‖ • (u : ℂ) = (e.symm u : ℂ)
  rw [← hdir]
  exact smul_inv_smul₀ (norm_ne_zero_iff.mpr (radialLevelSet_ne_zero hzero (e.symm u))) _

/-- The chosen radius solves the defining level equation. -/
theorem radialLevelRadius_level (u : Metric.sphere (0 : ℂ) 1) :
    φ (radialLevelRadius hc hzero hboundary hray u • (u : ℂ)) = c := by
  rw [radialLevelRadius_smul]
  exact ((radialLevelHomeomorph hc hzero hboundary hray).symm u).property.2

/-- The inverse radial radius is smooth on the standard circle when the
level function is smooth and its radial differential is positive. -/
theorem radialLevelRadius_contMDiff
    (hsmooth : ∀ z ∈ Metric.ball 0 R, ContDiffAt ℝ ∞ φ z)
    (hpos : ∀ z ∈ Metric.ball 0 R, z ≠ 0 → 0 < fderiv ℝ φ z z) :
    ContMDiff (𝓡 1) 𝓘(ℝ) ∞ (radialLevelRadius hc hzero hboundary hray) := by
  intro u
  let r := radialLevelRadius hc hzero hboundary hray
  have hr := radialLevelRadius_mem_Ioo hc hzero hboundary hray u
  have hu : ‖(u : ℂ)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using u.property
  have hnorm : ‖r u • (u : ℂ)‖ = r u := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hu, mul_one]
  have hball : r u • (u : ℂ) ∈ Metric.ball 0 R := by
    simpa only [Metric.mem_ball, dist_zero_right, hnorm] using hr.2
  have hnz : r u • (u : ℂ) ≠ 0 := norm_pos_iff.mp (by rw [hnorm]; exact hr.1)
  obtain ⟨ρ, hρ, hρ0, _, hinverse⟩ :=
    exists_smooth_joint_radial_radius hr.1 (hsmooth _ hball) (hpos _ hball hnz)
  have hlevel := radialLevelRadius_level hc hzero hboundary hray u
  change φ (r u • (u : ℂ)) = c at hlevel
  rw [hlevel] at hρ hρ0
  have hpairs : Tendsto (fun v : Metric.sphere (0 : ℂ) 1 => ((v : ℂ), r v))
      (𝓝 u) (𝓝 ((u : ℂ), r u)) :=
    (continuous_subtype_val.prodMk
      (radialLevelRadius_continuous hc hzero hboundary hray)).continuousAt.tendsto
  have hagree : r =ᶠ[𝓝 u] fun v => ρ ((v : ℂ), c) := by
    filter_upwards [hpairs.eventually hinverse] with v hv
    rw [radialLevelRadius_level hc hzero hboundary hray v] at hv
    exact hv.symm
  have hs : ContMDiffAt (𝓡 1) 𝓘(ℝ) ∞
      (fun v : Metric.sphere (0 : ℂ) 1 => ρ ((v : ℂ), c)) u := by
    exact hρ.contMDiffAt.comp u
      ((contMDiff_coe_sphere (m := ∞)).contMDiffAt.prodMk_space contMDiffAt_const)
  exact hs.congr_of_eventuallyEq hagree

/-- The inverse radial homeomorphism, viewed as a complex parameter map,
is smooth on the standard circle. -/
theorem radialLevelHomeomorph_symm_coe_contMDiff
    (hsmooth : ∀ z ∈ Metric.ball 0 R, ContDiffAt ℝ ∞ φ z)
    (hpos : ∀ z ∈ Metric.ball 0 R, z ≠ 0 → 0 < fderiv ℝ φ z z) :
    ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞
      (fun u => ((radialLevelHomeomorph hc hzero hboundary hray).symm u : ℂ)) := by
  have hs := (radialLevelRadius_contMDiff hc hzero hboundary hray hsmooth hpos).smul
    (contMDiff_coe_sphere (m := ∞))
  exact hs.congr (fun u => (radialLevelRadius_smul hc hzero hboundary hray u).symm)

/-- The inverse radial map has injective differential. Radial normalization
is a smooth left inverse to the inclusion of the circle. -/
theorem radialLevelHomeomorph_symm_coe_mfderiv_injective
    (hsmooth : ∀ z ∈ Metric.ball 0 R, ContDiffAt ℝ ∞ φ z)
    (hpos : ∀ z ∈ Metric.ball 0 R, z ≠ 0 → 0 < fderiv ℝ φ z z)
    (u : Metric.sphere (0 : ℂ) 1) :
    Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, ℂ)
      (fun v => ((radialLevelHomeomorph hc hzero hboundary hray).symm v : ℂ)) u) := by
  let h : Metric.sphere (0 : ℂ) 1 → ℂ :=
    fun v => ((radialLevelHomeomorph hc hzero hboundary hray).symm v : ℂ)
  let N : ℂ → ℂ := fun z => ‖z‖⁻¹ • z
  have hnz : h u ≠ 0 := radialLevelSet_ne_zero hzero _
  have hN : ContDiffAt ℝ ∞ N (h u) :=
    ((contDiffAt_norm ℝ hnz).inv (norm_ne_zero_iff.mpr hnz)).smul contDiffAt_id
  have hh : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ h :=
    radialLevelHomeomorph_symm_coe_contMDiff hc hzero hboundary hray hsmooth hpos
  have hleft : N ∘ h = (Subtype.val : Metric.sphere (0 : ℂ) 1 → ℂ) := by
    funext v
    exact congrArg (fun w : Metric.sphere (0 : ℂ) 1 => (w : ℂ))
      ((radialLevelHomeomorph hc hzero hboundary hray).apply_symm_apply v)
  have hd : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) N (h u)).comp
      (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) h u) =
      mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (Subtype.val : Metric.sphere (0 : ℂ) 1 → ℂ) u := by
    rw [← mfderiv_comp u (hN.contMDiffAt.mdifferentiableAt (by simp))
      (hh.contMDiffAt.mdifferentiableAt (by simp)), hleft]
  intro a b hab
  have hinj : Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, ℂ)
      (Subtype.val : Metric.sphere (0 : ℂ) 1 → ℂ) u) := by
    convert! injective_mvfderiv_subtypeVal_sphere u
  apply hinj
  rw [← hd]
  exact congrArg (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) N (h u)) hab

end OnLeConjecture.Analytic
