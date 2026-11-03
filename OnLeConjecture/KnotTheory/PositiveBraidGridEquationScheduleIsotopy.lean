/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridEventRoundedIsotopy
public import OnLeConjecture.Analytic.PlaneBranchCanonicalPositiveBraid

/-! # The equation-sphere link and the literal rounded positive word

The branch representative, radius, event words, crossing count and oriented
sphere-link parametrization are retained from the canonical-word theorem.
Schedule transport and the explicit period-origin rotation compose with its
native ambient diffeotopy. The target is the literal rounded flattened carrier.
Geometric separation of its horizontal rows is a separate obligation.
-/

@[expose] public noncomputable section
open Set Filter Metric Manifold
open scoped Topology ContDiff Manifold BigOperators
open OnLeConjecture.KnotTheory
attribute [local instance] finrank_real_complex_fact'

local instance equationScheduleRealInner : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _
local instance equationScheduleRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

namespace OnLeConjecture.Analytic

/-- The same positively oriented equation-sphere link is ambiently diffeotopic
to the literal rounded positive-word carrier, with its source rotation explicit. -/
theorem PointedMapGerm.exists_equation_link_rounded_positive_word
    (β : PointedMapGerm 1 2) (hi : β.HasInjectiveRepresentative)
    (i : Fin 2) {a : ℕ} (ha : 0 < a)
    (ho : Germ.vanishingOrder (β.1.component i) = a)
    (W : Source 2 → ℂ) (hW : AnalyticAt ℂ W 0)
    (hker : RingHom.ker β.pullbackRingHom = Ideal.span {Germ.ofFunction W hW})
    {δ εround : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 48)
    (hεround : 0 < εround) (hεround' : εround ≤ 1 / 8) :
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
              ∃ l u : ℝ → ℝ, ContDiff ℝ ∞ l ∧ ContDiff ℝ ∞ u ∧
                (∀ q, dist (l q) (positiveGridRectilinearLowerRise q) < εround) ∧
                (∀ q, dist (u q) (positiveGridRectilinearUpperDrop q) < εround) ∧
                EqOn l positiveGridRectilinearLowerRise
                  (positiveGridRoundingCornerNeighborhood δ)ᶜ ∧
                EqOn u positiveGridRectilinearUpperDrop
                  (positiveGridRoundingCornerNeighborhood δ)ᶜ ∧
                ∃ (L Lrounded : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
                    (sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)),
                  Set.range (fun v => (L v : EuclideanSpace ℂ (Fin 2))) =
                    (fun y : EuclideanSpace ℂ (Fin 2) => ε⁻¹ • y) ''
                      (sphere 0 ε ∩ {y | W ((EuclideanSpace.equiv (Fin 2) ℂ) y) = 0}) ∧
                  (∀ θ : ℝ,
                    0 < (inner ℂ (L (Circle.exp θ) : EuclideanSpace ℂ (Fin 2))
                      (deriv (fun t : ℝ => (L (Circle.exp t) :
                        EuclideanSpace ℂ (Fin 2))) θ)).im) ∧
                  (∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
                    (Lrounded (braidCircleSheet a k θ) : EuclideanSpace ℂ (Fin 2)) =
                      planeSolidTorusMap i (positiveRectilinearCylinderPoint (List.ofFn w).flatten
                        (positiveRoundedWord (List.ofFn w).flatten (fun _ => l) (fun _ => u)
                          ((σ 0).symm k) 1
                          (positiveRoundedWordPeriodTime (List.ofFn w).flatten θ)))) ∧
                  ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞
                    (sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
                    (∀ v, Φ.final (L v) = Lrounded (positiveScheduleSourceRotation a b v)) ∧
                    Set.range (fun v => Φ.final (L v)) = Set.range Lrounded := by
  obtain ⟨e, G, hG, hG0, hg, R, hR, hFa, hFi, hpower, ε₀, hε₀, hlinks⟩ :=
    β.exists_equation_link_canonical_positive_braid hi i ha ho W hW hker
  refine ⟨e, G, hG, hG0, hg, R, hR, hFa, hFi, hpower, ε₀, hε₀, ?_⟩
  intro ε hε hεsmall
  obtain ⟨r, hr, hrR, b, hb, E, hE, hbE, hdE, N, event, left, right, σ, w,
      hN, henum, hmono, hblocks, hsep, hcycle, hperm, hlength, w₁, hw₁, hsheet,
      L, Lmodel, hrange, horientation, hmodel, Φ, hΦ⟩ := hlinks ε hε hεsmall
  have hlt : ∀ j, left j < right j := by
    intro j
    rcases hblocks j with ⟨_, hl, hr, _⟩
    exact hl.trans hr
  have hbl : ∀ j, b < left j := fun j => (hblocks j).1
  have hrd : ∀ j, right j < b + 2 * Real.pi := fun j => (hblocks j).2.2.2.1
  have hp : ∀ j, σ j.castSucc * (w j).permutation = σ j.succ :=
    fun j => (hblocks j).2.2.2.2.2.2.2.1
  have hmodelSheet (k : Fin a) (θ : ℝ) (hθ : θ ∈ Icc b (b + 2 * Real.pi)) :
      (Lmodel (braidCircleSheet a k θ) : EuclideanSpace ℂ (Fin 2)) =
        planeSolidTorusMap i (Circle.exp θ, positiveGridGlobalWordModel left right σ w k θ) := by
    rw [hmodel, braidCircleSheet_pow ha, hsheet k θ hθ]
  obtain ⟨l, u, hls, hus, hla, hua, hl, hu, Lrounded, hrounded, Ψ, hΨ⟩ :=
    exists_positiveGridGlobalWordModel_rounded_diffeotopy_of_embedding ha left right σ w
      hlt hsep hp hcycle i b hbl hrd Lmodel hmodelSheet hδ hδ' hεround hεround'
  have hfinal (v : Circle) : (Φ.trans Ψ).final (L v) =
      Lrounded (positiveScheduleSourceRotation a b v) := by
    rw [TauCeti.Diffeotopy.final_trans]
    change Ψ.final (Φ.final (L v)) = _
    rw [hΦ, hΨ]
  refine ⟨r, hr, hrR, b, hb, E, hE, hbE, hdE, N, event, left, right, σ, w,
    hN, henum, hmono, hblocks, hsep, hcycle, hperm, hlength,
    l, u, hls, hus, hla, hua, hl, hu, L, Lrounded, hrange, horientation, hrounded,
    Φ.trans Ψ, hfinal, ?_⟩
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨positiveScheduleSourceRotation a b v, (hfinal v).symm⟩
  · rintro ⟨v, rfl⟩
    refine ⟨v * (Circle.exp (-b / (a : ℝ)))⁻¹, ?_⟩
    change (Φ.trans Ψ).final (L (v * (Circle.exp (-b / (a : ℝ)))⁻¹)) = Lrounded v
    rw [hfinal]
    simp only [positiveScheduleSourceRotation, inv_mul_cancel_right]

end OnLeConjecture.Analytic
