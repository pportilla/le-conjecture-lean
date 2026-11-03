/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Radial transversality of a parametrized curve

A positive smooth factor times a positive power of the squared norm has
strictly positive radial derivative near the origin, away from the origin.
For a complex curve with a nonvanishing factor after division by its initial
parameter power, this applies to its squared ambient norm. The conclusion
concerns the differential of that actual norm function.
-/

public section

open Filter
open scoped Topology RealInnerProductSpace

namespace OnLeConjecture.Analytic

/-- The radial derivative of a positive power of the squared norm times
a differentiable factor. -/
theorem fderiv_norm_sq_pow_mul_apply_self
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {h : E → ℝ} {z : E} (hh : DifferentiableAt ℝ h z) {m : ℕ} (hm : 0 < m) :
    fderiv ℝ (fun w => (‖w‖ ^ 2) ^ m * h w) z z =
      (‖z‖ ^ 2) ^ m * (2 * (m : ℝ) * h z + fderiv ℝ h z z) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have hd := (((hasStrictFDerivAt_norm_sq z).hasFDerivAt.pow (k + 1)).mul hh.hasFDerivAt)
  change HasFDerivAt (fun w => (‖w‖ ^ 2) ^ k.succ * h w) _ z at hd
  rw [hd.fderiv]
  simp only [add_apply, smul_apply,
    smul_eq_mul, Nat.add_sub_cancel, innerSL_apply_apply, real_inner_self_eq_norm_sq,
    Nat.cast_succ, pow_succ]
  ring

/-- A positive continuously differentiable factor gives a positive radial
derivative on a sufficiently small punctured neighborhood. -/
theorem eventually_radial_derivative_pos_of_positive_factor
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {h : E → ℝ} (hh : ContDiffAt ℝ 1 h 0) (hpos : 0 < h 0)
    {m : ℕ} (hm : 0 < m) :
    ∀ᶠ z in 𝓝 (0 : E), z ≠ 0 →
      0 < fderiv ℝ (fun w => (‖w‖ ^ 2) ^ m * h w) z z := by
  have hc : ContinuousAt (fun z => 2 * (m : ℝ) * h z + fderiv ℝ h z z) 0 :=
    (continuousAt_const.mul hh.continuousAt).add
      ((hh.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_id)
  have hcpos : 0 < 2 * (m : ℝ) * h 0 + fderiv ℝ h 0 0 := by
    simp only [map_zero, add_zero]
    positivity
  have he := hc.eventually (lt_mem_nhds hcpos)
  filter_upwards [he, hh.eventually (by norm_num)] with z hz hhz hzne
  rw [fderiv_norm_sq_pow_mul_apply_self (hhz.differentiableAt (by norm_num)) hm]
  exact mul_pos (pow_pos (sq_pos_of_pos (norm_pos_iff.mpr hzne)) _) hz

/-- A complex parametrization with a nonvanishing smooth factor meets
small squared-norm levels transversely in the radial parameter direction. -/
theorem eventually_curve_norm_radial_derivative_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {F U : ℂ → E} (hU : ContDiffAt ℝ 1 U 0) (hU0 : U 0 ≠ 0)
    {m : ℕ} (hm : 0 < m)
    (hfactor : F =ᶠ[𝓝 0] fun z => z ^ m • U z) :
    ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 →
      0 < fderiv ℝ (fun w => ‖F w‖ ^ 2) z z := by
  have heq : (fun w => ‖F w‖ ^ 2) =ᶠ[𝓝 0]
      (fun w => (‖w‖ ^ 2) ^ m * ‖U w‖ ^ 2) := by
    filter_upwards [hfactor] with z hz
    rw [hz, norm_smul, norm_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm m 2]
  have hsq : ContDiffAt ℝ 1 (fun z => ‖U z‖ ^ 2) 0 := hU.norm_sq (𝕜 := ℂ)
  have hpos := eventually_radial_derivative_pos_of_positive_factor hsq
    (sq_pos_of_pos (norm_pos_iff.mpr hU0)) hm
  filter_upwards [heq.fderiv (𝕜 := ℝ), hpos] with z he hz hzne
  rw [he]
  exact hz hzne

/-- The squared norm of the parametrized curve has surjective real
differential at every sufficiently small nonzero parameter. -/
theorem eventually_curve_norm_sq_fderiv_surjective
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {F U : ℂ → E} (hU : ContDiffAt ℝ 1 U 0) (hU0 : U 0 ≠ 0)
    {m : ℕ} (hm : 0 < m)
    (hfactor : F =ᶠ[𝓝 0] fun z => z ^ m • U z) :
    ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 →
      Function.Surjective (fderiv ℝ (fun w => ‖F w‖ ^ 2) z) := by
  filter_upwards [eventually_curve_norm_radial_derivative_pos hU hU0 hm hfactor]
    with z hz hzne
  intro a
  refine ⟨(a / fderiv ℝ (fun w => ‖F w‖ ^ 2) z z) • z, ?_⟩
  simp only [map_smul, smul_eq_mul]
  exact div_mul_cancel₀ _ (ne_of_gt (hz hzne))

end OnLeConjecture.Analytic
