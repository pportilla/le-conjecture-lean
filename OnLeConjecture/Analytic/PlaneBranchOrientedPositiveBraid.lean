/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchBoundaryOrientation
public import OnLeConjecture.Analytic.PlaneBranchPositiveBraidIsotopy
public import OnLeConjecture.Analytic.PlaneBranchSheetRotation

/-! # Oriented equation links and their positive braid models

One power-normalized analytic representative supplies the sheet rotation,
the positively parametrized equation-sphere link, and the positive event-word
model. The ambient diffeotopies retain that chosen parametrization.
-/

@[expose] public noncomputable section

open Filter Set Metric Manifold
open scoped Topology ContDiff Manifold BigOperators

attribute [local instance] finrank_real_complex_fact'

local instance planeOrientedBraidLinkRealInner :
    InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _

local instance planeOrientedBraidLinkRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

namespace OnLeConjecture.Analytic

open KnotTheory

/-- The sphere link is ambient diffeotopic to a circle obtained from one
power-normalized representative. All its nontrivial sheet differences have
strictly positive angular logarithmic derivative on the same parameter disc,
and the endpoint radius lies strictly inside that disc. -/
theorem PointedMapGerm.exists_oriented_braid_link_diffeotopy_with_sheetRotation
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
            (∀ θ : ℝ,
              0 < (inner ℂ (L₁ (Circle.exp θ) : EuclideanSpace ℂ (Fin 2))
                (deriv (fun t : ℝ => (L₁ (Circle.exp t) : EuclideanSpace ℂ (Fin 2))) θ)).im) ∧
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
  · exact exists_plane_branch_braid_link_diffeotopy_with_orientation
      hF hF0 i a ha hpower R hR (hFa.mono hsub).continuousOn (hFi.mono hsub)
      (fun y => W ((EuclideanSpace.equiv (Fin 2) ℂ) y)) himageR

/-- The normalized equation-sphere link is ambient isotopic to the explicit
positive event/gap model of the same power-normalized branch representative. -/
theorem PointedMapGerm.exists_oriented_equation_link_positive_model_diffeotopy
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
          ∃ b ∈ Ioo (0 : ℝ) (2 * Real.pi), ∃ E : Finset ℝ,
            (∀ t, t ∈ E ↔ t ∈ planeBranchProjectedCrossingTimes F i a r
              (((r : ℂ) ^ a)⁻¹) b (b + 2 * Real.pi)) ∧
            b ∉ E ∧ b + 2 * Real.pi ∉ E ∧
            let K : Fin a → ℝ → ℂ := fun k θ =>
              (((r : ℂ) ^ a)⁻¹) * planeBranchBraidSheet F i a r k θ
            ∃ (N : ℕ) (event left right : Fin N → ℝ)
              (σ : Fin (N + 1) → Equiv.Perm (Fin a)) (w : Fin N → PositiveAdjacentWord a),
              N = E.card ∧ List.ofFn event = E.sort (· ≤ ·) ∧ StrictMono event ∧
              (∀ j : Fin N,
                b < left j ∧ left j < event j ∧ event j < right j ∧
                right j < b + 2 * Real.pi ∧
                StrictMono (fun k => (K (σ j.castSucc k) (left j)).re) ∧
                StrictMono (fun k => (K (σ j.succ k) (right j)).re) ∧
                (∀ t ∈ Icc (left j) (right j), t ∈ E ↔ t = event j) ∧
                IsPositiveBraidEventWord K (event j) (σ j.castSucc) (σ j.succ) (w j)) ∧
              (∀ j q, j < q → right j < left q) ∧
              (σ (Fin.last N)).trans (finRotate a) = σ 0 ∧
              σ 0 * (PositiveAdjacentWord.toSigned ((List.ofFn w).flatten)).permutation =
                σ (Fin.last N) ∧
              (List.ofFn w).flatten.length = ∑ j : Fin N,
                (Finset.univ.filter fun p : Fin a × Fin a =>
                  p.1 < p.2 ∧ (K (σ j.succ p.1) (event j)).re =
                    (K (σ j.succ p.2) (event j)).re).card ∧
              ∃ w₁ : Circle → ℂ, ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ w₁ ∧
                (∀ k θ, θ ∈ Icc b (b + 2 * Real.pi) →
                  w₁ (braidCircleSheet a k θ) =
                    planeBranchBraidGlobalModel K b (b + 2 * Real.pi)
                      event left right σ w k θ) ∧
                ∃ (L Lmodel : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
                    (sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)),
                  Set.range (fun u => (L u : EuclideanSpace ℂ (Fin 2))) =
                    (fun y : EuclideanSpace ℂ (Fin 2) => ε⁻¹ • y) ''
                      (sphere 0 ε ∩ {y | W ((EuclideanSpace.equiv (Fin 2) ℂ) y) = 0}) ∧
                  (∀ θ : ℝ,
                    0 < (inner ℂ (L (Circle.exp θ) : EuclideanSpace ℂ (Fin 2))
                      (deriv (fun t : ℝ => (L (Circle.exp t) :
                        EuclideanSpace ℂ (Fin 2))) θ)).im) ∧
                  (∀ u, (Lmodel u : EuclideanSpace ℂ (Fin 2)) =
                    planeSolidTorusMap i (u ^ a, w₁ u)) ∧
                  ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞
                    (sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
                    ∀ u, Φ.final (L u) = Lmodel u := by
  obtain ⟨e, G, hG, hG0, hg, R, hR, _hraw, _hraw0, hFaE, hFiE, hpE,
      _hcoverage, hrot, ε₀, hε₀, hlinks⟩ :=
    β.exists_oriented_braid_link_diffeotopy_with_sheetRotation hi i ha ho W hW hker
  let F : ℂ → Source 2 := fun z => G (curveParameterEquiv.symm z)
  let C : ℂ → EuclideanSpace ℂ (Fin 2) := fun z =>
    (EuclideanSpace.equiv (Fin 2) ℂ).symm (F z)
  have hFa : AnalyticOnNhd ℂ F (ball 0 R) := by
    intro z hz
    have h := ((EuclideanSpace.equiv (Fin 2) ℂ).analyticAt (C z)).comp
      (hFaE z (ball_subset_closedBall hz))
    simpa only [C, Function.comp_def, ContinuousLinearEquiv.apply_symm_apply] using h
  have hFi : InjOn F (ball 0 R) := by
    intro z hz w hw heq
    exact hFiE (ball_subset_closedBall hz) (ball_subset_closedBall hw)
      (congrArg (EuclideanSpace.equiv (Fin 2) ℂ).symm heq)
  have hp (z : ℂ) (hz : z ∈ ball 0 R) : F z i = z ^ a := hpE z (ball_subset_closedBall hz)
  refine ⟨e, G, hG, hG0, hg, R, hR, hFa, hFi, hp, ε₀, hε₀, ?_⟩
  intro ε hε hεsmall
  obtain ⟨r, hr, hrR, A, L, hA, _hphase, hrange, horient, Φ, hΦ⟩ := hlinks ε hε hεsmall
  let c : ℂ := ((r : ℂ) ^ a)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (pow_ne_zero _ (by exact_mod_cast hr.ne'))
  obtain ⟨b, hb, E, hE, hbE, hdE, _σ₀, _σ₁, _hs₀, _hs₁, _hcyc⟩ :=
    exists_planeBranch_regular_sorted_period_of_sheetRotation ha hFa hrot hr hrR hc
  have hpositive := (planeBranchProjectedCrossingTimes_finite_of_sheetRotation
    ha hFa hrot hr hrR hc 0 0).2
  obtain ⟨N, event, left, right, σ, w, hN, henum, hmono, hblocks, hsep, hcycle,
      hperm, hlength, w₁, hw₁, hsheet, B, Lmodel, _hB, hBnorm, hmodel, Ψ, hΨ⟩ :=
    exists_planeBranch_positive_model_diffeotopy i ha hr hrR hFa hp b E hE hbE hdE
      (fun k l hkl θ hθ => (hpositive k l hkl θ hθ).1)
  refine ⟨r, hr, hrR, b, hb, E, hE, hbE, hdE, N, event, left, right, σ, w,
    hN, henum, hmono, hblocks, hsep, hcycle, hperm, hlength, w₁, hw₁, hsheet,
    L, Lmodel, hrange, horient, hmodel, Φ.symm.trans Ψ, ?_⟩
  intro u
  have hAB : A u = B u := Subtype.ext ((hA u).trans (hBnorm u).symm)
  rw [TauCeti.Diffeotopy.final_trans, TauCeti.Diffeotopy.final_symm]
  change Ψ.final (Φ.final.symm (L u)) = Lmodel u
  rw [← hΦ u, Φ.final.symm_apply_apply, hAB, hΨ u]


end OnLeConjecture.Analytic
