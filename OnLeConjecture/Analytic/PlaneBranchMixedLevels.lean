/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchSmoothEmbedding

/-!
# Normalizing the mixed cylinder and sphere levels

The quadratic function `(1-t)|yᵢ|²+t‖y‖²` interpolates between the
coordinate-cylinder and Euclidean-sphere equations. On each nonzero level,
radial normalization is injective. Thus an embedded circle on any one of
these levels stays embedded when normalized onto the ambient unit sphere.
Construction of a joint family of such circles is a separate step.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.Analytic

open Set Metric

/-- The quadratic equation interpolating a coordinate cylinder and a sphere. -/
def planeMixedRadiusSq (i : Fin 2) (t : ℝ) (y : EuclideanSpace ℂ (Fin 2)) : ℝ :=
  (1 - t) * ‖y i‖ ^ 2 + t * ‖y‖ ^ 2

@[simp]
theorem planeMixedRadiusSq_zero (i : Fin 2) (t : ℝ) : planeMixedRadiusSq i t 0 = 0 := by
  simp [planeMixedRadiusSq]

/-- Every interpolated equation is homogeneous of degree two under real scaling. -/
theorem planeMixedRadiusSq_smul (i : Fin 2) (t r : ℝ)
    (y : EuclideanSpace ℂ (Fin 2)) :
    planeMixedRadiusSq i t (r • y) = r ^ 2 * planeMixedRadiusSq i t y := by
  change (1 - t) * ‖r • y i‖ ^ 2 + t * ‖r • y‖ ^ 2 = _
  rw [norm_smul, norm_smul]
  simp only [mul_pow, Real.norm_eq_abs, sq_abs]
  unfold planeMixedRadiusSq
  ring

/-- Ambient radial normalization into the unit sphere. -/
def planeRadialNormalization (y : EuclideanSpace ℂ (Fin 2)) : EuclideanSpace ℂ (Fin 2) :=
  (‖y‖⁻¹ : ℝ) • y

theorem norm_planeRadialNormalization {y : EuclideanSpace ℂ (Fin 2)} (hy : y ≠ 0) :
    ‖planeRadialNormalization y‖ = 1 := by
  simp only [planeRadialNormalization, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg y))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)

/-- Two normalized points on the same nonzero mixed level must have been equal. -/
theorem planeRadialNormalization_injOn_mixedLevel (i : Fin 2) (t c : ℝ) (hc : c ≠ 0) :
    InjOn planeRadialNormalization {y | planeMixedRadiusSq i t y = c} := by
  intro y hy z hz heq
  have hy0 : y ≠ 0 := by
    intro h
    exact hc (hy.symm.trans (by rw [h, planeMixedRadiusSq_zero]))
  have hz0 : z ≠ 0 := by
    intro h
    exact hc (hz.symm.trans (by rw [h, planeMixedRadiusSq_zero]))
  have hyn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy0
  have hzn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  set r : ℝ := ‖y‖ / ‖z‖ with hrdef
  have hr : 0 < r := div_pos (norm_pos_iff.mpr hy0) (norm_pos_iff.mpr hz0)
  have hscale : y = r • z := by
    have h := congrArg (fun w : EuclideanSpace ℂ (Fin 2) => (‖y‖ : ℝ) • w) heq
    simpa only [planeRadialNormalization, smul_smul, mul_inv_cancel₀ hyn, one_smul,
      div_eq_mul_inv, hrdef] using h
  have hq := planeMixedRadiusSq_smul i t r z
  rw [← hscale, hy, hz] at hq
  have hmul : (r ^ 2 - 1) * c = 0 := by linear_combination -hq
  have hr2 : r ^ 2 = 1 := sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hc)
  have hr1 : r = 1 := by nlinarith
  simpa only [hr1, one_smul] using hscale

/-- The normalized circle on a fixed nonzero mixed level is a closed embedding. -/
theorem isClosedEmbedding_normalized_mixedLevel_circle
    (i : Fin 2) (t c : ℝ) (hc : c ≠ 0)
    (F : Metric.sphere (0 : ℂ) 1 → EuclideanSpace ℂ (Fin 2))
    (hF : Continuous F) (hinj : Function.Injective F)
    (hlevel : ∀ u, planeMixedRadiusSq i t (F u) = c) :
    Topology.IsClosedEmbedding (fun u => planeRadialNormalization (F u)) := by
  have hne (u : Metric.sphere (0 : ℂ) 1) : F u ≠ 0 := by
    intro h
    exact hc ((hlevel u).symm.trans (by rw [h, planeMixedRadiusSq_zero]))
  apply Continuous.isClosedEmbedding
  · exact (hF.norm.inv₀ (fun u => norm_ne_zero_iff.mpr (hne u))).smul hF
  · intro u v h
    exact hinj (planeRadialNormalization_injOn_mixedLevel i t c hc (hlevel u) (hlevel v) h)

end OnLeConjecture.Analytic
