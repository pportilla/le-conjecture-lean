/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchBraidRotationConnections
public import OnLeConjecture.Analytic.PlaneBranchSolidTorus

/-!
# Finite positive projections of the actual equation link

One normalized representative supplies the solid-torus circle, the
ambient isotopy to the equation link, a finite projected event set, its
positive transverse crossings, and regular endpoint sorting. The radius
used for these statements is the actual radius of that circle.
-/

@[expose] public noncomputable section

open Filter Set Metric Manifold
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

local instance planeProjectionAssemblyRealInner :
    InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _

local instance planeProjectionAssemblyRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

namespace OnLeConjecture.Analytic

/-- An injective branch and its exact equation ideal construct the
geometric sphere link and a finite positive braid projection of the
same circle. A finite braid word and its geometric realization are not
assumed or asserted. -/
theorem PointedMapGerm.exists_equation_link_finite_braid_projection
    (β : PointedMapGerm 1 2) (hi : β.HasInjectiveRepresentative)
    (i : Fin 2) {a : ℕ} (ha : 0 < a)
    (ho : Germ.vanishingOrder (β.1.component i) = a)
    (W : Source 2 → ℂ) (hW : AnalyticAt ℂ W 0)
    (hker : RingHom.ker β.pullbackRingHom = Ideal.span {Germ.ofFunction W hW}) :
    ∃ (e : PointedEquivGerm 1) (G : Source 1 → Source 2)
      (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0),
      β.comp e.inverse = PointedMapGerm.ofFunction G hG hG0 ∧
      ∃ R : ℝ, 0 < R ∧
        let F : ℂ → Source 2 := fun z => G (curveParameterEquiv.symm z)
        AnalyticOnNhd ℂ F (ball 0 R) ∧ InjOn F (ball 0 R) ∧
        (∀ z ∈ ball 0 R, F z i = z ^ a) ∧
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          ∃ r : ℝ, 0 < r ∧ r < R ∧
          IsSmoothEmbedding (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞
            (curvePowerSolidTorusCircle F i a r) ∧
          ∃ (L₀ L₁ : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
              (sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)),
            (∀ u, (L₀ u : EuclideanSpace ℂ (Fin 2)) =
              planeSolidTorusMap i (curvePowerSolidTorusCircle F i a r u)) ∧
            Set.range (fun u => (L₁ u : EuclideanSpace ℂ (Fin 2))) =
              (fun y : EuclideanSpace ℂ (Fin 2) => ε⁻¹ • y) ''
                (sphere 0 ε ∩ {y | W ((EuclideanSpace.equiv (Fin 2) ℂ) y) = 0}) ∧
            (∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞
                (sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
              ∀ u, Φ.final (L₀ u) = L₁ u) ∧
            let c : ℂ := ((r : ℂ) ^ a)⁻¹
            (∃ θ ∈ Ioo (0 : ℝ) (2 * Real.pi), ∃ E : Finset ℝ,
              (∀ t, t ∈ E ↔ t ∈ planeBranchProjectedCrossingTimes F i a r c
                θ (θ + 2 * Real.pi)) ∧
              θ ∉ E ∧ θ + 2 * Real.pi ∉ E ∧
              ∃ σ₀ σ₁ : Equiv.Perm (Fin a),
                StrictMono (fun j => planeBranchBraidProjection F i a r c θ (σ₀ j)) ∧
                StrictMono (fun j =>
                  planeBranchBraidProjection F i a r c (θ + 2 * Real.pi) (σ₁ j)) ∧
                σ₁.trans (finRotate a) = σ₀) ∧
            ∀ k l : Fin a, k ≠ l → ∀ θ : ℝ,
              (c * planeBranchBraidPairDifference F i a r k l θ).re = 0 →
              0 < -deriv (fun t => (c * planeBranchBraidPairDifference F i a r k l t).re) θ *
                (c * planeBranchBraidPairDifference F i a r k l θ).im ∧
              deriv (fun t => (c * planeBranchBraidPairDifference F i a r k l t).re) θ ≠ 0 := by
  obtain ⟨e, G, hG, hG0, hg, R, hR, _hraw, _hraw0, hFa, hFi, hp,
    _hcoverage, hrot, ε₀, hε₀, hlinks⟩ :=
    β.exists_braid_link_diffeotopy_with_sheetRotation hi i ha ho W hW hker
  let F : ℂ → Source 2 := fun z => G (curveParameterEquiv.symm z)
  let C : ℂ → EuclideanSpace ℂ (Fin 2) := fun z =>
    (EuclideanSpace.equiv (Fin 2) ℂ).symm (F z)
  have hFaRaw : AnalyticOnNhd ℂ F (ball 0 R) := by
    intro z hz
    have h := ((EuclideanSpace.equiv (Fin 2) ℂ).analyticAt (C z)).comp
      (hFa z (ball_subset_closedBall hz))
    simpa only [C, Function.comp_def, ContinuousLinearEquiv.apply_symm_apply] using h
  have hFiRaw : InjOn F (ball 0 R) := by
    intro z hz w hw heq
    exact hFi (ball_subset_closedBall hz) (ball_subset_closedBall hw)
      (congrArg (EuclideanSpace.equiv (Fin 2) ℂ).symm heq)
  have hpRaw (z : ℂ) (hz : z ∈ ball 0 R) : F z i = z ^ a := hp z (ball_subset_closedBall hz)
  refine ⟨e, G, hG, hG0, hg, R, hR, hFaRaw, hFiRaw, hpRaw, ε₀, hε₀, ?_⟩
  intro ε hε hεsmall
  obtain ⟨r, hr, hrR, L₀, L₁, hL₀, _hphase, hrange, Φ, hΦ⟩ := hlinks ε hε hεsmall
  let c : ℂ := ((r : ℂ) ^ a)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (pow_ne_zero _ (by exact_mod_cast hr.ne'))
  refine ⟨r, hr, hrR, curvePowerSolidTorusCircle_isSmoothEmbedding ha hr hrR
    hFaRaw hFiRaw hpRaw, L₀, L₁, ?_, hrange, ⟨Φ, hΦ⟩, ?_, ?_⟩
  · intro u
    exact (hL₀ u).trans (curvePowerSolidTorusCircle_map hr hrR hpRaw u).symm
  · exact exists_planeBranch_regular_sorted_period_of_sheetRotation ha hFaRaw hrot hr hrR hc
  · exact (planeBranchProjectedCrossingTimes_finite_of_sheetRotation
      ha hFaRaw hrot hr hrR hc 0 0).2

end OnLeConjecture.Analytic
