/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CurveRadialLevelHomeomorph
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The embedded circle on an ambient norm sphere

An injective continuous curve on a parameter disc sends a circular norm
level to an embedded circle on the ambient sphere. The range is exactly
the intersection of that sphere with the image of the closed parameter
disc. This does not assert smooth knot isotopy invariance.
-/

public noncomputable section

open Set

namespace OnLeConjecture.Analytic

/-- Restrict the actual curve to its squared-norm level, with codomain
the corresponding ambient sphere. -/
@[expose] def curveNormLevelMap {E : Type*} [NormedAddCommGroup E]
    (F : ℂ → E) (R c : ℝ) :
    radialLevelSet (fun z => ‖F z‖ ^ 2) R c → Metric.sphere (0 : E) (Real.sqrt c) :=
  fun z => ⟨F z, by
    simp only [Metric.mem_sphere, dist_zero_right]
    exact (Real.sqrt_sq (norm_nonneg (F z))).symm.trans
      (congrArg Real.sqrt z.property.2)⟩

theorem curveNormLevelMap_continuous {E : Type*} [NormedAddCommGroup E]
    {F : ℂ → E} {R c : ℝ} (hc : ContinuousOn F (Metric.closedBall 0 R)) :
    Continuous (curveNormLevelMap F R c) := by
  apply Continuous.subtype_mk
  apply continuousOn_iff_continuous_domRestrict.mp (hc.mono ?_)
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1

theorem curveNormLevelMap_injective {E : Type*} [NormedAddCommGroup E]
    {F : ℂ → E} {R c : ℝ} (hi : Set.InjOn F (Metric.closedBall 0 R)) :
    Function.Injective (curveNormLevelMap F R c) := by
  intro z w hzw
  apply Subtype.ext
  apply hi
  · simpa only [Metric.mem_closedBall, dist_zero_right] using z.property.1
  · simpa only [Metric.mem_closedBall, dist_zero_right] using w.property.1
  · exact congrArg Subtype.val hzw

/-- A homeomorphism of the parameter level with the circle induces the
actual circle parametrization on the ambient sphere. -/
@[expose] def curveNormLevelCircle {E : Type*} [NormedAddCommGroup E]
    (F : ℂ → E) (R c : ℝ)
    (e : radialLevelSet (fun z => ‖F z‖ ^ 2) R c ≃ₜ Metric.sphere (0 : ℂ) 1) :
    Metric.sphere (0 : ℂ) 1 → Metric.sphere (0 : E) (Real.sqrt c) :=
  curveNormLevelMap F R c ∘ e.symm

/-- The circle parametrization is a closed embedding for an injective
continuous curve on the closed parameter disc. -/
theorem curveNormLevelCircle_isClosedEmbedding {E : Type*} [NormedAddCommGroup E]
    {F : ℂ → E} {R c : ℝ}
    (e : radialLevelSet (fun z => ‖F z‖ ^ 2) R c ≃ₜ Metric.sphere (0 : ℂ) 1)
    (hc : ContinuousOn F (Metric.closedBall 0 R))
    (hi : Set.InjOn F (Metric.closedBall 0 R)) :
    Topology.IsClosedEmbedding (curveNormLevelCircle F R c e) := by
  exact ((curveNormLevelMap_continuous hc).comp e.symm.continuous).isClosedEmbedding
    ((curveNormLevelMap_injective hi).comp e.symm.injective)

/-- Its range is the image of the actual parameter level. -/
theorem curveNormLevelCircle_range {E : Type*} [NormedAddCommGroup E]
    {F : ℂ → E} {R c : ℝ}
    (e : radialLevelSet (fun z => ‖F z‖ ^ 2) R c ≃ₜ Metric.sphere (0 : ℂ) 1) :
    Set.range (fun u => (curveNormLevelCircle F R c e u : E)) =
      F '' radialLevelSet (fun z => ‖F z‖ ^ 2) R c := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨e.symm u, (e.symm u).property, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨e ⟨z, hz⟩, ?_⟩
    simp only [curveNormLevelCircle, Function.comp_apply, Homeomorph.symm_apply_apply]
    rfl

/-- The ambient image is precisely the sphere intersection with the
image of the closed parameter disc. -/
theorem curveNormLevelCircle_range_eq_sphere_inter_image
    {E : Type*} [NormedAddCommGroup E] {F : ℂ → E} {R c : ℝ}
    (hc : 0 ≤ c)
    (e : radialLevelSet (fun z => ‖F z‖ ^ 2) R c ≃ₜ Metric.sphere (0 : ℂ) 1) :
    Set.range (fun u => (curveNormLevelCircle F R c e u : E)) =
      Metric.sphere (0 : E) (Real.sqrt c) ∩ F '' Metric.closedBall 0 R := by
  rw [curveNormLevelCircle_range]
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨?_, z, ?_, rfl⟩
    · simp only [Metric.mem_sphere, dist_zero_right]
      rw [← hz.2, Real.sqrt_sq (norm_nonneg _)]
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1
  · rintro ⟨hv, z, hz, rfl⟩
    refine ⟨z, ⟨?_, ?_⟩, rfl⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    · have he : ‖F z‖ = Real.sqrt c := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hv
      change ‖F z‖ ^ 2 = c
      rw [he, Real.sq_sqrt hc]

end OnLeConjecture.Analytic
