/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchBraidGlobalModel
public import OnLeConjecture.Analytic.PlaneBranchBraidHeightConnections
public import OnLeConjecture.Analytic.PlaneBranchBraidProjectionAssembly

/-! # Ambient isotopy to the explicit positive event-word model

The same analytic branch circle supplies the finite crossing data, the global
smooth event/gap model, and the ambient isotopy of native three-sphere circles.
No geometric braid-word presentation or grid/Floer identification is assumed.
-/

@[expose] public noncomputable section

open Set Filter Metric Manifold
open scoped Topology ContDiff Manifold BigOperators

attribute [local instance] finrank_real_complex_fact'

local instance positiveBraidIsotopyRealInner :
    InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _

local instance positiveBraidIsotopyRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

namespace OnLeConjecture.Analytic

open KnotTheory

/-- The actual power-normalized branch circle is ambient isotopic to the
explicit positive event-word model constructed from its projected crossings. -/
theorem exists_planeBranch_positive_model_diffeotopy
    {F : ℂ → Source 2} (i : Fin 2) {a : ℕ} (ha : 0 < a) {R r : ℝ}
    (hr : 0 < r) (hrR : r < R) (hF : AnalyticOnNhd ℂ F (ball 0 R))
    (hp : ∀ z ∈ ball 0 R, F z i = z ^ a) (b : ℝ) (E : Finset ℝ)
    (hE : ∀ t, t ∈ E ↔ t ∈ planeBranchProjectedCrossingTimes F i a r
      (((r : ℂ) ^ a)⁻¹) b (b + 2 * Real.pi))
    (hb : b ∉ E) (hd : b + 2 * Real.pi ∉ E)
    (hpos : ∀ k l : Fin a, k ≠ l → ∀ θ : ℝ,
      ((((r : ℂ) ^ a)⁻¹) * planeBranchBraidPairDifference F i a r k l θ).re = 0 →
      0 < -deriv (fun t => ((((r : ℂ) ^ a)⁻¹) *
        planeBranchBraidPairDifference F i a r k l t).re) θ *
        ((((r : ℂ) ^ a)⁻¹) * planeBranchBraidPairDifference F i a r k l θ).im) :
    let K : Fin a → ℝ → ℂ := fun k θ =>
      (((r : ℂ) ^ a)⁻¹) * planeBranchBraidSheet F i a r k θ
    ∃ (N : ℕ) (event left right : Fin N → ℝ)
      (σ : Fin (N + 1) → Equiv.Perm (Fin a)) (w : Fin N → PositiveAdjacentWord a),
      N = E.card ∧ List.ofFn event = E.sort (· ≤ ·) ∧ StrictMono event ∧
      (∀ j : Fin N,
        b < left j ∧ left j < event j ∧ event j < right j ∧ right j < b + 2 * Real.pi ∧
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
            planeBranchBraidGlobalModel K b (b + 2 * Real.pi) event left right σ w k θ) ∧
        ∃ (L₀ L₁ : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
          (sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)),
          (∀ u, (L₀ u : EuclideanSpace ℂ (Fin 2)) =
            planeSolidTorusMap i (curvePowerSolidTorusCircle F i a r u)) ∧
          (∀ u, (L₀ u : EuclideanSpace ℂ (Fin 2)) =
            planeRadialNormalization
              ((EuclideanSpace.equiv (Fin 2) ℂ).symm (F (r • (u : ℂ))))) ∧
          (∀ u, (L₁ u : EuclideanSpace ℂ (Fin 2)) = planeSolidTorusMap i (u ^ a, w₁ u)) ∧
          ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞
            (sphere (0 : EuclideanSpace ℂ (Fin 2)) 1), ∀ u, Φ.final (L₀ u) = L₁ u := by
  let K : Fin a → ℝ → ℂ := fun k θ =>
    (((r : ℂ) ^ a)⁻¹) * planeBranchBraidSheet F i a r k θ
  have hcont (k : Fin a) : Continuous (K k) :=
    scaled_planeBranchBraidSheet_continuous i a hr hrR hF k
  have hE' : ∀ t, t ∈ E ↔ t ∈ Icc b (b + 2 * Real.pi) ∧
      ∃ k l : Fin a, k ≠ l ∧ (K k t).re = (K l t).re := by
    intro t
    rw [hE, mem_planeBranchProjectedCrossingTimes_iff]
  have hpos' : ∀ θ ∈ E, ∀ k l, k ≠ l → (K k θ).re = (K l θ).re →
      0 < -deriv (fun t => (K k t - K l t).re) θ * (K k θ - K l θ).im := by
    intro θ _ k l hkl he
    have hz : (K k θ - K l θ).re = 0 := by simp only [Complex.sub_re, he, sub_self]
    have hdif : ∀ t, K k t - K l t =
        (((r : ℂ) ^ a)⁻¹) * planeBranchBraidPairDifference F i a r k l t :=
      scaled_planeBranchBraidSheet_sub F i a r k l
    simpa only [hdif] using hpos k l hkl θ (by simpa only [hdif] using hz)
  obtain ⟨N, event, left, right, σ, w, hN, henum, hmono, hσb, hσd, hblocks, hsep,
      hperm, hlength, hM, hleft, hright, hMb, hMd, _hinjM, hseparation⟩ :=
    exists_planeBranchBraidGlobalModel hcont E b (b + 2 * Real.pi)
      (by linarith [Real.pi_pos]) hE' hb hd hpos'
  let M := planeBranchBraidGlobalModel K b (b + 2 * Real.pi) event left right σ w
  have hinjb : Function.Injective (planeBranchBraidProjection F i a r
      (((r : ℂ) ^ a)⁻¹) b) := by
    intro k l he
    by_contra hkl
    exact hb ((hE' b).mpr ⟨⟨le_rfl, by linarith [Real.pi_pos]⟩, k, l, hkl, he⟩)
  have hcycle := planeBranchBraid_endpoint_sortingPerm F i ha r
    (((r : ℂ) ^ a)⁻¹) b hinjb hσb hσd
  have hKcycle (k : Fin a) : K k (b + 2 * Real.pi) = K (finRotate a k) b :=
    scaled_planeBranchBraidSheet_cyclic F i ha r b k
  have hMcycle (k : Fin a) : M k (b + 2 * Real.pi) = M (finRotate a k) b := by
    dsimp only [M]
    rw [hMd, hMb]
    exact braid_rank_endpoint_configs_cyclic K b (b + 2 * Real.pi) (σ 0)
      (σ (Fin.last N)) (finRotate a) hKcycle hcycle k
  have hw₀ : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞
      (fun u => (curvePowerSolidTorusCircle F i a r u).2) :=
    contMDiff_snd.comp (curvePowerSolidTorusCircle_contMDiff i a hr hrR hF)
  obtain ⟨w₁, hw₁, hwSheet, L₀, L₁, hL₀, hL₁, Φ, hΦ⟩ :=
    exists_circle_braid_diffeotopy_of_labelled_period i ha b hw₀ M hM
      (fun k => by dsimp only [M]; simpa only [hMb] using hleft k)
      (fun k => by dsimp only [M]; simpa only [hMd] using hright k) hMcycle
      (by
        intro θ hθ k l hkl
        simpa only [curvePowerSolidTorusCircle_snd_braidCircleSheet] using
          hseparation θ hθ k l hkl)
  refine ⟨N, event, left, right, σ, w, hN, henum, hmono, hblocks, hsep, hcycle,
    hperm, hlength, w₁, hw₁, hwSheet, L₀, L₁, ?_, ?_, hL₁, Φ, hΦ⟩
  · intro u
    exact hL₀ u
  · intro u
    exact (hL₀ u).trans (curvePowerSolidTorusCircle_map hr hrR hp u)

/-- The normalized equation-sphere link is ambient isotopic to the explicit
positive event/gap model of the same power-normalized branch representative. -/
theorem PointedMapGerm.exists_equation_link_positive_model_diffeotopy
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
                  (∀ u, (Lmodel u : EuclideanSpace ℂ (Fin 2)) =
                    planeSolidTorusMap i (u ^ a, w₁ u)) ∧
                  ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞
                    (sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
                    ∀ u, Φ.final (L u) = Lmodel u := by
  obtain ⟨e, G, hG, hG0, hg, R, hR, hFa, hFi, hp, ε₀, hε₀, hlinks⟩ :=
    β.exists_equation_link_finite_braid_projection hi i ha ho W hW hker
  let F : ℂ → Source 2 := fun z => G (curveParameterEquiv.symm z)
  refine ⟨e, G, hG, hG0, hg, R, hR, hFa, hFi, hp, ε₀, hε₀, ?_⟩
  intro ε hε hεsmall
  obtain ⟨r, hr, hrR, _hsmooth, A, L, hA, hrange, ⟨Φ, hΦ⟩, hperiod, hpositive⟩ :=
    hlinks ε hε hεsmall
  obtain ⟨b, hb, E, hE, hbE, hdE, _σ₀, _σ₁, _hs₀, _hs₁, _hcyc⟩ := hperiod
  obtain ⟨N, event, left, right, σ, w, hN, henum, hmono, hblocks, hsep, hcycle,
      hperm, hlength, w₁, hw₁, hsheet, B, Lmodel, hB, _hBnorm, hmodel, Ψ, hΨ⟩ :=
    exists_planeBranch_positive_model_diffeotopy i ha hr hrR hFa hp b E hE hbE hdE
      (fun k l hkl θ hθ => (hpositive k l hkl θ hθ).1)
  refine ⟨r, hr, hrR, b, hb, E, hE, hbE, hdE, N, event, left, right, σ, w,
    hN, henum, hmono, hblocks, hsep, hcycle, hperm, hlength, w₁, hw₁, hsheet,
    L, Lmodel, hrange, hmodel, Φ.symm.trans Ψ, ?_⟩
  intro u
  have hAB : A u = B u := Subtype.ext ((hA u).trans (hB u).symm)
  rw [TauCeti.Diffeotopy.final_trans, TauCeti.Diffeotopy.final_symm]
  change Ψ.final (Φ.final.symm (L u)) = Lmodel u
  rw [← hΦ u, Φ.final.symm_apply_apply, hAB, hΨ u]

end OnLeConjecture.Analytic
