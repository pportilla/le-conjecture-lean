/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ReducedCurveLinkFamily
public import OnLeConjecture.Analytic.ReducedPlaneRegularLocus
public import OnLeConjecture.DifferentialTopology.RadialSubmersion
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Joint radial submersions along a reduced plane curve

Varying the squared radius in the constructed normalized link family
gives a smooth curve in the analytic zero set whose squared norm is the
parameter. Its velocity supplies a tangent vector on which the radial
differential is one. Together with regularity of the equation away from
the origin, this proves surjectivity of the joint real differential.
-/

public noncomputable section

open Filter Set Function Manifold
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

local instance reducedCurveRadialRealInner : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _

namespace OnLeConjecture.Analytic

namespace NormalizedPlaneCurveLinkFamily

variable {H : Source 2 → ℂ} {ι : Type*} (F : NormalizedPlaneCurveLinkFamily H ι)

/-- Recover the curve point at its original radius from the normalized link. -/
@[expose] def radiusMotion (i : ι) (u : Metric.sphere (0 : ℂ) 1) (c : ℝ) :
    EuclideanSpace ℂ (Fin 2) := Real.sqrt c • F.component i (u, c)

theorem radiusMotion_norm_sq (i : ι) (u : Metric.sphere (0 : ℂ) 1)
    {c : ℝ} (hc : c ∈ Ioo 0 F.radiusSq) : ‖F.radiusMotion i u c‖ ^ 2 = c := by
  simp only [radiusMotion, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg c), F.norm_eq_one c hc i u, mul_one,
    Real.sq_sqrt hc.1.le]

theorem radiusMotion_equation (i : ι) (u : Metric.sphere (0 : ℂ) 1)
    {c : ℝ} (hc : c ∈ Ioo 0 F.radiusSq) :
    H ((EuclideanSpace.equiv (Fin 2) ℂ) (F.radiusMotion i u c)) = 0 := by
  have hm : F.component i (u, c) ∈ ⋃ j, range (fun v => F.component j (v, c)) :=
    mem_iUnion.mpr ⟨i, ⟨u, rfl⟩⟩
  rw [F.range_eq c hc] at hm
  obtain ⟨y, hy, hys⟩ := hm
  have heq : F.radiusMotion i u c = y := by
    rw [radiusMotion, ← hys, smul_smul,
      mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hc.1)), one_smul]
  rw [heq]
  exact hy.2

theorem radiusMotion_contDiffAt (i : ι) (u : Metric.sphere (0 : ℂ) 1)
    {c : ℝ} (hc : c ∈ Ioo 0 F.radiusSq) : ContDiffAt ℝ ∞ (F.radiusMotion i u) c := by
  have hk : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞
      (fun t => F.component i (u, t)) c :=
    (F.smooth c hc i u).comp c (contMDiffAt_const.prodMk contMDiffAt_id)
  exact (Real.contDiffAt_sqrt hc.1.ne').smul hk.contDiffAt

/-- Every point on a covered zero fibre has a smooth motion changing its
squared radius at unit speed. -/
theorem exists_radiusMotion_through {x : EuclideanSpace ℂ (Fin 2)}
    (hx : H ((EuclideanSpace.equiv (Fin 2) ℂ) x) = 0)
    (hc : ‖x‖ ^ 2 ∈ Ioo 0 F.radiusSq) :
    ∃ i u, F.radiusMotion i u (‖x‖ ^ 2) = x := by
  have hxs : x ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) (Real.sqrt (‖x‖ ^ 2)) := by
    simp [Real.sqrt_sq (norm_nonneg x)]
  have hm : (Real.sqrt (‖x‖ ^ 2))⁻¹ • x ∈
      ⋃ i, range (fun u => F.component i (u, ‖x‖ ^ 2)) := by
    rw [F.range_eq _ hc]
    exact ⟨x, ⟨hxs, hx⟩, rfl⟩
  obtain ⟨i, u, hu⟩ := mem_iUnion.mp hm
  dsimp only at hu
  refine ⟨i, u, ?_⟩
  rw [radiusMotion, hu, smul_smul,
    mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hc.1)), one_smul]

/-- The equation and squared norm have jointly surjective real derivative
at every covered point where the equation is a submersion. -/
theorem joint_fderiv_surjective {x : EuclideanSpace ℂ (Fin 2)}
    (hx : H ((EuclideanSpace.equiv (Fin 2) ℂ) x) = 0)
    (hc : ‖x‖ ^ 2 ∈ Ioo 0 F.radiusSq)
    (hH : DifferentiableAt ℝ (H ∘ (EuclideanSpace.equiv (Fin 2) ℂ)) x)
    (hsub : Surjective (fderiv ℝ (H ∘ (EuclideanSpace.equiv (Fin 2) ℂ)) x)) :
    Surjective (fderiv ℝ
      (fun y : EuclideanSpace ℂ (Fin 2) =>
        (H ((EuclideanSpace.equiv (Fin 2) ℂ) y), ‖y‖ ^ 2)) x) := by
  obtain ⟨i, u, hq⟩ := F.exists_radiusMotion_through hx hc
  apply DifferentialTopology.surjective_fderiv_pair_of_level_curve hH
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.differentiableAt) hsub
    ((F.radiusMotion_contDiffAt i u hc).differentiableAt (by simp)) hq
  · filter_upwards [isOpen_Ioo.mem_nhds hc] with t ht
    exact (F.radiusMotion_equation i u ht).trans hx.symm
  · filter_upwards [isOpen_Ioo.mem_nhds hc] with t ht
    exact F.radiusMotion_norm_sq i u ht

end NormalizedPlaneCurveLinkFamily

namespace Germ

/-- The real map consisting of a reduced pointed plane equation and the
squared Euclidean norm is a submersion at every sufficiently small
nonzero point of the equation's zero set. -/
theorem eventually_joint_radial_fderiv_surjective_of_squarefree
    (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0) (hH0 : H 0 = 0)
    (hsq : Squarefree (ofFunction H hH)) :
    ∀ᶠ x in 𝓝 (0 : EuclideanSpace ℂ (Fin 2)), x ≠ 0 →
      H ((EuclideanSpace.equiv (Fin 2) ℂ) x) = 0 →
        Surjective (fderiv ℝ
          (fun y : EuclideanSpace ℂ (Fin 2) =>
            (H ((EuclideanSpace.equiv (Fin 2) ℂ) y), ‖y‖ ^ 2)) x) := by
  obtain ⟨s, ⟨F⟩⟩ := exists_normalized_link_family_of_squarefree H hH hsq
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  have he : Tendsto e (𝓝 (0 : EuclideanSpace ℂ (Fin 2))) (𝓝 0) := by
    simpa only [map_zero] using e.continuous.continuousAt.tendsto (x := 0)
  have hsmall : ∀ᶠ x in 𝓝 (0 : EuclideanSpace ℂ (Fin 2)), ‖x‖ ^ 2 < F.radiusSq := by
    have hn : ContinuousAt (fun x : EuclideanSpace ℂ (Fin 2) => ‖x‖ ^ 2) 0 :=
      continuousAt_id.norm.pow 2
    exact hn.eventually (gt_mem_nhds (by simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0)]
      using F.radiusSq_pos))
  filter_upwards [he.eventually (eventually_real_fderiv_surjective_of_squarefree H hH hH0 hsq),
    he.eventually hH.eventually_analyticAt, hsmall] with x hx ha hxs hxn hxH
  have hxe : e x ≠ 0 := fun hz => hxn (e.injective (hz.trans (map_zero e).symm))
  have hHa : DifferentiableAt ℝ H (e x) := ha.differentiableAt.restrictScalars ℝ
  have hcomp : fderiv ℝ (H ∘ e) x =
      (fderiv ℝ H (e x)).comp (e.toContinuousLinearMap.restrictScalars ℝ) :=
    (hHa.hasFDerivAt.comp x (e.hasFDerivAt.restrictScalars ℝ)).fderiv
  apply F.joint_fderiv_surjective hxH ⟨sq_pos_of_pos (norm_pos_iff.mpr hxn), hxs⟩
    (hHa.comp x (e.differentiableAt.restrictScalars ℝ))
  rw [hcomp]
  exact (hx hxe).comp e.surjective

end Germ

end OnLeConjecture.Analytic
