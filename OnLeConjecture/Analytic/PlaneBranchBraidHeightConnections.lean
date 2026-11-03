/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchBraidCircleFibres
public import OnLeConjecture.Analytic.PlaneBranchBraidProjectionAssembly

/-! # The actual analytic branch height on labelled power fibres

The complementary coordinate of the solid-torus circle is divided by `r^a`.
Its labelled values agree with the scaled branch sheets used in the finite
projection theorem. Thus continuity, cyclic matching and projected event
conditions all concern the same geometric circle.
-/

@[expose] public noncomputable section

open Set Metric Manifold
open scoped Topology ContDiff Manifold

namespace OnLeConjecture.Analytic

theorem mul_braidCircleSheet_coe (a : ℕ) (r : ℝ) (k : Fin a) (θ : ℝ) :
    (r : ℂ) * (braidCircleSheet a k θ : ℂ) = planeBranchBraidParameter a r k θ := by
  simp [braidCircleSheet_coe, planeBranchBraidParameter, planeBranchAngularParameter]

/-- Exact identification with the height of the actual scaled solid-torus circle. -/
theorem curvePowerSolidTorusCircle_snd_braidCircleSheet
    (F : ℂ → Source 2) (i : Fin 2) (a : ℕ) (r : ℝ) (k : Fin a) (θ : ℝ) :
    (curvePowerSolidTorusCircle F i a r (braidCircleSheet a k θ)).2 =
      ((r : ℂ) ^ a)⁻¹ * planeBranchBraidSheet F i a r k θ := by
  simp only [curvePowerSolidTorusCircle, mul_braidCircleSheet_coe, planeBranchBraidSheet,
    div_eq_mul_inv, mul_comm]

theorem scaled_planeBranchBraidSheet_continuous
    {F : ℂ → Source 2} (i : Fin 2) (a : ℕ) {R r : ℝ}
    (hr : 0 < r) (hrR : r < R) (hF : AnalyticOnNhd ℂ F (ball 0 R)) (k : Fin a) :
    Continuous (fun θ => ((r : ℂ) ^ a)⁻¹ * planeBranchBraidSheet F i a r k θ) := by
  have hw := (contMDiff_snd.comp
    (curvePowerSolidTorusCircle_contMDiff i a hr hrR hF)).continuous
  have hs : Continuous (braidCircleSheet a k) :=
    Circle.exp.continuous.comp ((continuous_id.add continuous_const).div_const _)
  simpa only [Function.comp_def, curvePowerSolidTorusCircle_snd_braidCircleSheet] using
    hw.comp hs

theorem scaled_planeBranchBraidSheet_cyclic
    (F : ℂ → Source 2) (i : Fin 2) {a : ℕ} (ha : 0 < a)
    (r θ : ℝ) (k : Fin a) :
    ((r : ℂ) ^ a)⁻¹ * planeBranchBraidSheet F i a r k (θ + 2 * Real.pi) =
      ((r : ℂ) ^ a)⁻¹ * planeBranchBraidSheet F i a r (finRotate a k) θ := by
  rw [planeBranchBraidSheet_add_two_pi F i ha]

theorem scaled_planeBranchBraidSheet_sub
    (F : ℂ → Source 2) (i : Fin 2) (a : ℕ) (r : ℝ) (k l : Fin a) (θ : ℝ) :
    ((r : ℂ) ^ a)⁻¹ * planeBranchBraidSheet F i a r k θ -
        ((r : ℂ) ^ a)⁻¹ * planeBranchBraidSheet F i a r l θ =
      ((r : ℂ) ^ a)⁻¹ * planeBranchBraidPairDifference F i a r k l θ := by
  simp only [planeBranchBraidPairDifference, mul_sub]

end OnLeConjecture.Analytic
