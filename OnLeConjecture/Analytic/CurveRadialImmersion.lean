/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CurveInitialFactor

/-!
# Immersion of a nonconstant complex curve away from its center

Positive radial derivative of the squared norm forces the complex
differential to be nonzero. A nonzero complex linear map from the complex
line is injective, as is its underlying real linear map.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.Analytic

/-- Positive radial change of the squared norm forces the differential
of a complex curve to be injective. -/
theorem complex_curve_fderiv_injective_of_norm_radial_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {F : ℂ → E} {z : ℂ} (hF : DifferentiableAt ℂ F z)
    (hpos : 0 < fderiv ℝ (fun w => ‖F w‖ ^ 2) z z) :
    Function.Injective (fderiv ℂ F z) := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  have hlinear (w : ℂ) : fderiv ℂ F z w = w • fderiv ℂ F z 1 := by
    simpa only [smul_eq_mul, mul_one] using (fderiv ℂ F z).map_smul w 1
  have hone : fderiv ℂ F z 1 ≠ 0 := by
    intro hzero
    have hreal : fderiv ℝ F z z = 0 := by
      rw [hF.fderiv_restrictScalars ℝ]
      change fderiv ℂ F z z = 0
      rw [hlinear, hzero, smul_zero]
    have hd := ((hF.restrictScalars ℝ).hasFDerivAt).norm_sq
    rw [hd.fderiv] at hpos
    simp only [smul_apply, ContinuousLinearMap.comp_apply, hreal, map_zero,
      smul_zero, lt_self_iff_false] at hpos
  intro a b hab
  apply smul_left_injective ℂ hone
  change a • fderiv ℂ F z 1 = b • fderiv ℂ F z 1
  rwa [← hlinear a, ← hlinear b]

/-- The same differential is injective when viewed over the reals. -/
theorem real_curve_fderiv_injective_of_norm_radial_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {F : ℂ → E} {z : ℂ} (hF : DifferentiableAt ℂ F z)
    (hpos : 0 < fderiv ℝ (fun w => ‖F w‖ ^ 2) z z) :
    Function.Injective (fderiv ℝ F z) := by
  rw [hF.fderiv_restrictScalars ℝ]
  exact complex_curve_fderiv_injective_of_norm_radial_pos hF hpos

/-- Every centered nonconstant analytic curve is immersed, over both
the complex and real scalar fields, at sufficiently small nonzero parameters. -/
theorem eventually_nonconstant_analytic_curve_fderiv_injective
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {F : ℂ → E} (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), F z = 0) :
    ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 →
      Function.Injective (fderiv ℂ F z) ∧ Function.Injective (fderiv ℝ F z) := by
  filter_upwards [hF.eventually_analyticAt,
    eventually_nonconstant_curve_norm_radial_derivative_pos hF hF0 hne]
    with z hz hp hzne
  exact ⟨complex_curve_fderiv_injective_of_norm_radial_pos hz.differentiableAt (hp hzne),
    real_curve_fderiv_injective_of_norm_radial_pos hz.differentiableAt (hp hzne)⟩

end OnLeConjecture.Analytic
