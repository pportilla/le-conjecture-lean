/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchBraidLinkIsotopy
public import OnLeConjecture.Analytic.PlaneBranchSheetRotation

/-! # Sheet rotation for the parametrization used in the branch-link isotopy

The source equivalence and analytic representative are chosen once. The compact
disc that covers the equation germ is then shrunk inside the common disc of
positive sheet rotation. The cylinder endpoint of the ambient isotopy uses a
radius strictly smaller than that same disc. No braid word or grid presentation
is asserted here.
-/

@[expose] public noncomputable section

open Filter Set Manifold
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

local instance planePositiveBraidLinkRealInner :
    InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _

local instance planePositiveBraidLinkRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

namespace OnLeConjecture.Analytic

/-- The sphere link is ambient diffeotopic to a circle obtained from one
power-normalized representative. All its nontrivial sheet differences have
strictly positive angular logarithmic derivative on the same parameter disc,
and the endpoint radius lies strictly inside that disc. -/
theorem PointedMapGerm.exists_braid_link_diffeotopy_with_sheetRotation
    (β : PointedMapGerm 1 2) (hi : β.HasInjectiveRepresentative)
    (i : Fin 2) {a : ℕ} (ha : 0 < a)
    (ho : Germ.vanishingOrder (β.1.component i) = a)
    (W : Source 2 → ℂ) (hW : AnalyticAt ℂ W 0)
    (hker : RingHom.ker β.pullbackRingHom = Ideal.span {Germ.ofFunction W hW}) :
    ∃ (e : PointedEquivGerm 1) (G : Source 1 → Source 2)
      (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0),
      β.comp e.inverse = PointedMapGerm.ofFunction G hG hG0 ∧
      ∃ R : ℝ, 0 < R ∧
        let Fraw : ℂ → Source 2 := fun z => G (curveParameterEquiv.symm z)
        let F : ℂ → EuclideanSpace ℂ (Fin 2) := fun z =>
          (EuclideanSpace.equiv (Fin 2) ℂ).symm (Fraw z)
        AnalyticAt ℂ Fraw 0 ∧ Fraw 0 = 0 ∧
        AnalyticOnNhd ℂ F (Metric.closedBall 0 R) ∧
        InjOn F (Metric.closedBall 0 R) ∧
        (∀ z ∈ Metric.closedBall 0 R, F z i = z ^ a) ∧
        (∀ᶠ y in 𝓝 (0 : EuclideanSpace ℂ (Fin 2)),
          W ((EuclideanSpace.equiv (Fin 2) ℂ) y) = 0 ↔
            y ∈ F '' Metric.closedBall 0 R) ∧
        (∀ ζ : ℂ, ζ ^ a = 1 → ζ ≠ 1 →
          ∀ z ∈ Metric.ball 0 R, z ≠ 0 →
            planeBranchSheetDifference Fraw i ζ z ≠ 0 ∧
            0 < (z * deriv (planeBranchSheetDifference Fraw i ζ) z /
              planeBranchSheetDifference Fraw i ζ z).re) ∧
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          ∃ r : ℝ, 0 < r ∧ r < R ∧
          ∃ (L₀ L₁ : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
              (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)),
            (∀ u, (L₀ u : EuclideanSpace ℂ (Fin 2)) =
              planeRadialNormalization (F (r • (u : ℂ)))) ∧
            (∀ u, ‖(L₀ u : EuclideanSpace ℂ (Fin 2)) i‖⁻¹ •
              (L₀ u : EuclideanSpace ℂ (Fin 2)) i = (u : ℂ) ^ a) ∧
            Set.range (fun u => (L₁ u : EuclideanSpace ℂ (Fin 2))) =
              (fun y : EuclideanSpace ℂ (Fin 2) => ε⁻¹ • y) ''
                (Metric.sphere 0 ε ∩
                  {y | W ((EuclideanSpace.equiv (Fin 2) ℂ) y) = 0}) ∧
            ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞
                (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
              ∀ u, Φ.final (L₀ u) = L₁ u := by
  obtain ⟨e, G, hG, hG0, hg, R₀, hR₀, hF, hF0, hFa, hFi, hp, himage⟩ :=
    β.exists_injective_power_equation_coverage hi i ha ho W hW hker
  let Fraw : ℂ → Source 2 := fun z => G (curveParameterEquiv.symm z)
  let F : ℂ → EuclideanSpace ℂ (Fin 2) := fun z =>
    (EuclideanSpace.equiv (Fin 2) ℂ).symm (Fraw z)
  have hraw : AnalyticAt ℂ Fraw 0 :=
    hG.comp_of_eq (curveParameterEquiv.symm.analyticAt 0) (map_zero _)
  have hraw0 : Fraw 0 = 0 := by simpa only [Fraw, map_zero] using hG0
  have hrawi : InjOn Fraw (Metric.ball 0 R₀) := by
    intro z hz w hw heq
    exact hFi (Metric.ball_subset_closedBall hz) (Metric.ball_subset_closedBall hw)
      (congrArg (EuclideanSpace.equiv (Fin 2) ℂ).symm heq)
  have hrawp : ∀ z ∈ Metric.ball 0 R₀, Fraw z i = z ^ a := by
    intro z hz
    exact hp z (Metric.ball_subset_closedBall hz)
  obtain ⟨ρ, hρ, hρR, hrot⟩ :=
    exists_radius_planeBranchSheetDifference_re_pos hraw ha hR₀ hrawi hrawp
  let R : ℝ := ρ / 2
  have hR : 0 < R := half_pos hρ
  have hRρ : R < ρ := half_lt_self hρ
  have hRR₀ : R ≤ R₀ := hRρ.le.trans hρR
  have hsub : Metric.closedBall (0 : ℂ) R ⊆ Metric.closedBall 0 R₀ :=
    Metric.closedBall_subset_closedBall hRR₀
  have hzero : ∀ z ∈ Metric.closedBall 0 R₀, F z = 0 → z = 0 := by
    intro z hz hzero
    exact hFi hz (Metric.mem_closedBall_self hR₀.le) (hzero.trans hF0.symm)
  have himageR := eventually_equation_zero_iff_mem_smaller_curve_image
    hR hRR₀ hFa.continuousOn hzero himage
  have hpower : ∀ᶠ z in 𝓝 (0 : ℂ), F z i = z ^ a := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) hR₀] with z hz
    exact hp z hz
  refine ⟨e, G, hG, hG0, hg, R, hR, hraw, hraw0, hFa.mono hsub,
    hFi.mono hsub, (fun z hz => hp z (hsub hz)), himageR, ?_, ?_⟩
  · intro ζ hζ hζ1 z hz hz0
    exact hrot ζ hζ hζ1 z (Metric.ball_subset_ball hRρ.le hz) hz0
  · exact exists_plane_branch_braid_link_diffeotopy_with_radius_bound
      hF hF0 i a ha hpower R hR (hFa.mono hsub).continuousOn (hFi.mono hsub)
      (fun y => W ((EuclideanSpace.equiv (Fin 2) ℂ) y)) himageR

end OnLeConjecture.Analytic
