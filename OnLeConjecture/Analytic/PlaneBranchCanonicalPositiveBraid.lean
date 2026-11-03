/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridWordModel
public import OnLeConjecture.Analytic.PlaneBranchOrientedPositiveBraid

/-! # The equation-sphere link and the canonical positive word model

The canonical generators replace the event words with their original sheet
labels and time intervals. Derived coordinate separation gives an ambient
isotopy of the native three-sphere. The branch theorem preserves the normalized
representative, its radius, all event words, and their exact permutation and
crossing counts, together with the positive angular tangent of the same equation
link parametrization. No rectangular diagram or grid realization is assumed.
-/

@[expose] public noncomputable section

open Set Filter Metric Manifold
open scoped Topology ContDiff Manifold BigOperators

attribute [local instance] finrank_real_complex_fact'

local instance canonicalPositiveBraidRealInner :
    InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _

local instance canonicalPositiveBraidRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

namespace OnLeConjecture.Analytic

open KnotTheory

/-- The explicit event/gap model is ambient isotopic to the canonical generator
model. All separation and seam conditions are derived from the event data. -/
theorem exists_canonical_positive_word_diffeotopy
    (i : Fin 2) {a N : ℕ} (ha : 0 < a) (b : ℝ)
    (K : Fin a → ℝ → ℂ) (event left right : Fin N → ℝ)
    (σ : Fin (N + 1) → Equiv.Perm (Fin a)) (w : Fin N → PositiveAdjacentWord a)
    (hlt : ∀ j, left j < right j) (hsep : ∀ j q, j < q → right j < left q)
    (hb : ∀ j, b < left j) (hd : ∀ j, right j < b + 2 * Real.pi)
    (hevent : ∀ j, IsPositiveBraidEventWord K (event j) (σ j.castSucc) (σ j.succ) (w j))
    (hcycle : (σ (Fin.last N)).trans (finRotate a) = σ 0)
    {w₀ : Circle → ℂ} (hw₀ : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ w₀)
    (hsheet : ∀ k θ, θ ∈ Icc b (b + 2 * Real.pi) →
      w₀ (braidCircleSheet a k θ) =
        planeBranchBraidGlobalModel K b (b + 2 * Real.pi) event left right σ w k θ) :
    ∃ (w₁ : Circle → ℂ), ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ w₁ ∧
      (∀ k θ, θ ∈ Icc b (b + 2 * Real.pi) →
        w₁ (braidCircleSheet a k θ) = positiveGridGlobalWordModel left right σ w k θ) ∧
      ∃ (L₀ L₁ : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
        (sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)),
        (∀ u, (L₀ u : EuclideanSpace ℂ (Fin 2)) = planeSolidTorusMap i (u ^ a, w₀ u)) ∧
        (∀ u, (L₁ u : EuclideanSpace ℂ (Fin 2)) = planeSolidTorusMap i (u ^ a, w₁ u)) ∧
        ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
          ∀ u, Φ.final (L₀ u) = L₁ u := by
  have hp : ∀ j, σ j.castSucc * (w j).permutation = σ j.succ := fun j => (hevent j).1
  have hgap := braidModel_gap_pos b (b + 2 * Real.pi) (by linarith [Real.pi_pos])
    left right hb hd hsep
  apply exists_circle_braid_diffeotopy_of_labelled_period i ha b hw₀
    (positiveGridGlobalWordModel left right σ w)
    (positiveGridGlobalWordModel_contDiff left right σ w)
  · intro k
    change ∀ᶠ t in 𝓝 b, positiveGridGlobalWordModel left right σ w k t =
      positiveGridGlobalWordModel left right σ w k b
    have hc := positiveGridGlobalWordModel_left_collar b left right σ w hlt hb k
    simpa only [positiveGridGlobalWordModel_of_le left right σ w hlt k
      (fun j => (hb j).le)] using hc
  · intro k
    change ∀ᶠ t in 𝓝 (b + 2 * Real.pi),
      positiveGridGlobalWordModel left right σ w k t =
        positiveGridGlobalWordModel left right σ w k (b + 2 * Real.pi)
    have hc := positiveGridGlobalWordModel_right_collar (b + 2 * Real.pi)
      left right σ w hlt hp hd k
    simpa only [positiveGridGlobalWordModel_of_ge left right σ w hlt hp k
      (fun j => (hd j).le)] using hc
  · exact positiveGridGlobalWordModel_cyclic b (b + 2 * Real.pi)
      left right σ w hlt hp hb hd hcycle
  · intro θ hθ k l hkl
    rw [hsheet k θ hθ, hsheet l θ hθ]
    exact positiveGridGlobalWordModel_separation K b (b + 2 * Real.pi)
      event left right σ w hlt hsep hgap hevent hkl hθ

/-- The normalized equation-sphere link is ambient isotopic to the specified
canonical positive-generator model, with unchanged branch and crossing data. -/
theorem PointedMapGerm.exists_equation_link_canonical_positive_braid
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
                    positiveGridGlobalWordModel left right σ w k θ) ∧
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
  obtain ⟨e, G, hG, hG0, hg, R, hR, hFa, hFi, hp, ε₀, hε₀, hlinks⟩ :=
    β.exists_oriented_equation_link_positive_model_diffeotopy hi i ha ho W hW hker
  refine ⟨e, G, hG, hG0, hg, R, hR, hFa, hFi, hp, ε₀, hε₀, ?_⟩
  intro ε hε hεsmall
  obtain ⟨r, hr, hrR, b, hb, E, hE, hbE, hdE, N, event, left, right, σ, w,
      hN, henum, hmono, hblocks, hsep, hcycle, hperm, hlength, w₀, hw₀, hsheet,
      L, Lmodel, hrange, horientation, hmodel, Φ, hΦ⟩ := hlinks ε hε hεsmall
  let F : ℂ → Source 2 := fun z => G (curveParameterEquiv.symm z)
  let K : Fin a → ℝ → ℂ := fun k θ =>
    (((r : ℂ) ^ a)⁻¹) * planeBranchBraidSheet F i a r k θ
  have hlt : ∀ j, left j < right j := by
    intro j
    rcases hblocks j with ⟨_, hl, hr, _⟩
    exact hl.trans hr
  have hbl : ∀ j, b < left j := fun j => (hblocks j).1
  have hrd : ∀ j, right j < b + 2 * Real.pi := fun j => (hblocks j).2.2.2.1
  have hevent : ∀ j, IsPositiveBraidEventWord K (event j)
      (σ j.castSucc) (σ j.succ) (w j) := fun j => (hblocks j).2.2.2.2.2.2.2
  obtain ⟨w₁, hw₁, hsheet₁, B, Lcanonical, hB, hcanonical, Ψ, hΨ⟩ :=
    exists_canonical_positive_word_diffeotopy i ha b K event left right σ w
      hlt hsep hbl hrd hevent hcycle hw₀ hsheet
  refine ⟨r, hr, hrR, b, hb, E, hE, hbE, hdE, N, event, left, right, σ, w,
    hN, henum, hmono, hblocks, hsep, hcycle, hperm, hlength,
    w₁, hw₁, hsheet₁, L, Lcanonical, hrange, horientation, hcanonical, Φ.trans Ψ, ?_⟩
  intro u
  have heq : Lmodel u = B u := Subtype.ext ((hmodel u).trans (hB u).symm)
  rw [TauCeti.Diffeotopy.final_trans]
  change Ψ.final (Φ.final (L u)) = Lcanonical u
  rw [hΦ u, heq, hΨ u]

end OnLeConjecture.Analytic
