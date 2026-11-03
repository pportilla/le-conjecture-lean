/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridScheduleRotation

/-! # The retained event model and the rounded closed word

The schedule transport and the explicit ambient rotation connect the literal
retained event model to the previously constructed rounded word. The final source
rotation is stated explicitly. No geometric row perturbation is asserted here.
-/

@[expose] public noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff Manifold
open OnLeConjecture.Analytic OnLeConjecture.DifferentialTopology
attribute [local instance] finrank_real_complex_fact'

local instance eventRoundedRealInner : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _
local instance eventRoundedRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

namespace OnLeConjecture.KnotTheory

set_option backward.isDefEq.respectTransparency false in
/-- The rounded-word family may be placed in either complex coordinate. -/
theorem exists_positiveRoundedWord_selected_endpoint_diffeotopy {m : ℕ} (hm : 0 < m)
    (w : PositiveAdjacentWord m) (σ : Equiv.Perm (Fin m)) (i : Fin 2)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla : ∀ j q, dist (l j q) (positiveGridRectilinearLowerRise q) < 1 / 8)
    (hua : ∀ j q, dist (u j q) (positiveGridRectilinearUpperDrop q) < 1 / 8)
    (hls : ∀ j, ContDiff ℝ ∞ (l j)) (hus : ∀ j, ContDiff ℝ ∞ (u j))
    {F : Circle × ℝ → Circle × ℂ}
    (hF : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞ F)
    (he : ∀ k θ s, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
      F (braidCircleSheet m k θ, s) = positiveRectilinearCylinderPoint w
        (positiveRoundedWordDeformation w l u (σ k) s (positiveRoundedWordPeriodTime w θ))) :
    ∃ (A B : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
        (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)),
      (∀ v, (A v : EuclideanSpace ℂ (Fin 2)) = planeSolidTorusMap i (F (v, 0))) ∧
      (∀ v, (B v : EuclideanSpace ℂ (Fin 2)) = planeSolidTorusMap i (F (v, 1))) ∧
      ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
        ∀ v, Φ.final (A v) = B v := by
  have hU' : U ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    have hh := hU ht
    constructor <;> linarith [hh.1, hh.2]
  have hs := (planeSolidTorusMap_isSmoothEmbedding i).contMDiff.comp hF
  apply exists_plane_sphere_family_endpoint_diffeotopy
    (fun p => planeSolidTorusMap i (F p)) (fun _ _ => planeSolidTorusMap_norm i _) hs
  · intro s v
    let e := planeSolidTorusCoordinateEquiv i
    let C := fun v => complexSolidTorusMap (F (v, s))
    have hFs : ContMDiff (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞ (fun v => F (v, s)) :=
      hF.comp (contMDiff_id.prodMk contMDiff_const)
    have hC : ContMDiff (𝓡 1) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞ C :=
      complexSolidTorusMap_contMDiff.comp hFs
    have heC : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin 2))
        𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞ e := e.contDiff.contMDiff
    rw [show (fun u => planeSolidTorusMap i (F (u, s))) = e ∘ C by
      funext u; exact congrFun (planeSolidTorusMap_eq_coordinateEquiv i) (F (u, s)),
      mfderiv_comp v (heC.mdifferentiableAt (by simp)) (hC.mdifferentiableAt (by simp)),
      mfderiv_eq_fderiv, e.fderiv]
    apply e.injective.comp
    change Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2))
      (complexSolidTorusMap ∘ (fun u => F (u, s))) v)
    rw [mfderiv_comp v (complexSolidTorusMap_contMDiff.mdifferentiableAt (by simp))
      (hFs.mdifferentiableAt (by simp))]
    exact (complexSolidTorusMap_mfderiv_injective _).comp
      (positiveRoundedWord_circle_family_mfderiv_injective hm w σ hl hu hU' hls hus hF he s v)
  · intro s
    exact (planeSolidTorusMap_isSmoothEmbedding i).isEmbedding.comp
      ((hF.continuous.comp (continuous_id.prodMk continuous_const)).isClosedEmbedding
        (positiveRoundedWord_circle_family_injective hm w σ hU hl hu hla hua he s)).isEmbedding

/-- Exact fixed-word cylinder phase after rescaling one period. -/
theorem positiveRectilinearCylinderPoint_lift_zero_fst {m : ℕ}
    (w : PositiveAdjacentWord m) (k : Fin m) (θ : ℝ) :
    (positiveRectilinearCylinderPoint w
      (positiveRoundedWordLift w k 0 (positiveRoundedWordPeriodTime w θ))).1 = Circle.exp θ := by
  unfold positiveRectilinearCylinderPoint positiveRoundedWordLift positiveRoundedWordPeriodTime
  dsimp only
  congr 1
  have hT : (2 * (w.length : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- The retained event model is ambiently diffeotopic to the rounded closed word,
with the exact source rotation accounting for its original period origin. -/
theorem exists_positiveGridGlobalWordModel_rounded_diffeotopy {m N : ℕ}
    (hm : 0 < m) (left right : Fin N → ℝ)
    (σ : Fin (N + 1) → Equiv.Perm (Fin m)) (w : Fin N → PositiveAdjacentWord m)
    (hlt : ∀ j, left j < right j)
    (hsep : ∀ j q, j < q → right j < left q)
    (hp : ∀ j, σ j.castSucc * (w j).permutation = σ j.succ)
    (hc : (σ (Fin.last N)).trans (finRotate m) = σ 0)
    (i : Fin 2) (b : ℝ) (hb : ∀ j, b < left j)
    (hd : ∀ j, right j < b + 2 * Real.pi)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 48) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) :
    ∃ l u : ℝ → ℝ, ContDiff ℝ ∞ l ∧ ContDiff ℝ ∞ u ∧
      (∀ q, dist (l q) (positiveGridRectilinearLowerRise q) < ε) ∧
      (∀ q, dist (u q) (positiveGridRectilinearUpperDrop q) < ε) ∧
      EqOn l positiveGridRectilinearLowerRise (positiveGridRoundingCornerNeighborhood δ)ᶜ ∧
      EqOn u positiveGridRectilinearUpperDrop (positiveGridRoundingCornerNeighborhood δ)ᶜ ∧
      ∃ (A B : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
          (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)),
        (∀ k θ, θ ∈ Icc b (b + 2 * Real.pi) →
          (A (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
            planeSolidTorusMap i (Circle.exp θ, positiveGridGlobalWordModel left right σ w k θ)) ∧
        (∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
          (B (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
            planeSolidTorusMap i (positiveRectilinearCylinderPoint (List.ofFn w).flatten
              (positiveRoundedWord (List.ofFn w).flatten (fun _ => l) (fun _ => u)
                ((σ 0).symm k) 1 (positiveRoundedWordPeriodTime (List.ofFn w).flatten θ)))) ∧
        ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
          ∀ v, Φ.final (A v) = B (positiveScheduleSourceRotation m b v) := by
  let flat := (List.ofFn w).flatten
  have hw : σ 0 * PositiveAdjacentWord.permutation flat = σ (Fin.last N) :=
    positiveWordSequence_permutation σ w hp
  obtain ⟨W, hW, hs₀, hs₁, A, B₀, hA, hB₀, Φ₀, hΦ₀⟩ :=
    exists_positiveGridGlobalWordModel_fixed_schedule_diffeotopy hm left right σ w hlt hsep hp hc
      i b hb hd
  obtain ⟨l, u, hls, hus, hla, hua, hl, hu, F, hF, he, _, _, _, _, _, _, _, _, _⟩ :=
    exists_positiveWord_rounded_sphere_diffeotopy hm flat (σ 0) (σ (Fin.last N)) hw hc
      hδ hδ' hε hε'
  have hU := positiveGridRoundingCornerNeighborhood_subset hδ'
  have hU' : positiveGridRoundingCornerNeighborhood δ ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    have hh := hU ht
    constructor <;> linarith [hh.1, hh.2]
  obtain ⟨C, B, hC, hB, Ψ, hΨ⟩ := exists_positiveRoundedWord_selected_endpoint_diffeotopy
    hm flat (σ 0).symm i hU (fun _ => hl) (fun _ => hu)
      (fun _ q => (hla q).trans_le hε') (fun _ q => (hua q).trans_le hε')
      (fun _ => hls) (fun _ => hus) hF he
  have hrotate (v : Circle) : (positiveScheduleRotationDiffeotopy i b).final (B₀ v) =
      C (positiveScheduleSourceRotation m b v) := by
    obtain ⟨θ, hθ, hbase⟩ := exists_circle_angle_in_period b (v ^ m)
    obtain ⟨k, rfl⟩ := exists_braidCircleSheet_eq hm θ hbase.symm
    have hθ' : θ - b ∈ Icc (0 : ℝ) (2 * Real.pi) := by
      constructor <;> linarith [hθ.1, hθ.2]
    apply Subtype.ext
    rw [positiveScheduleRotationDiffeotopy_final, hB₀,
      positiveScheduleCoordinateRotation_solidTorus, positiveScheduleSourceRotation_sheet,
      hC, he k (θ - b) 0 hθ', positiveRoundedWordDeformation_zero flat
        (fun _ => hl) (fun _ => hu) hU' ((σ 0).symm k)
        (positiveRoundedWordPeriodTime_mem flat hθ')]
    congr 1
    apply Prod.ext
    · rw [braidCircleSheet_pow hm,
        positiveRectilinearCylinderPoint_lift_zero_fst, ← Circle.exp_add]
      exact congrArg Circle.exp (by ring : -b + θ = θ - b)
    · exact hs₁ k θ hθ
  refine ⟨l, u, hls, hus, hla, hua, hl, hu, A, B, ?_, ?_,
    (Φ₀.trans (positiveScheduleRotationDiffeotopy i b)).trans Ψ, ?_⟩
  · intro k θ hθ
    rw [hA, braidCircleSheet_pow hm, hs₀ k θ hθ]
  · intro k θ hθ
    rw [hB, he k θ 1 hθ, positiveRoundedWordDeformation_one]
  · intro v
    rw [TauCeti.Diffeotopy.final_trans, TauCeti.Diffeotopy.final_trans]
    change Ψ.final ((positiveScheduleRotationDiffeotopy i b).final (Φ₀.final (A v))) = _
    rw [hΦ₀, hrotate, hΨ]

/-- A previously constructed embedding with the retained event-model formula can
be used as the literal initial endpoint. No new geometric identification is assumed. -/
theorem exists_positiveGridGlobalWordModel_rounded_diffeotopy_of_embedding {m N : ℕ}
    (hm : 0 < m) (left right : Fin N → ℝ)
    (σ : Fin (N + 1) → Equiv.Perm (Fin m)) (w : Fin N → PositiveAdjacentWord m)
    (hlt : ∀ j, left j < right j)
    (hsep : ∀ j q, j < q → right j < left q)
    (hp : ∀ j, σ j.castSucc * (w j).permutation = σ j.succ)
    (hc : (σ (Fin.last N)).trans (finRotate m) = σ 0)
    (i : Fin 2) (b : ℝ) (hb : ∀ j, b < left j)
    (hd : ∀ j, right j < b + 2 * Real.pi)
    (A : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
      (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1))
    (hA : ∀ k θ, θ ∈ Icc b (b + 2 * Real.pi) →
      (A (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
        planeSolidTorusMap i (Circle.exp θ, positiveGridGlobalWordModel left right σ w k θ))
    {δ ε : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 48) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) :
    ∃ l u : ℝ → ℝ, ContDiff ℝ ∞ l ∧ ContDiff ℝ ∞ u ∧
      (∀ q, dist (l q) (positiveGridRectilinearLowerRise q) < ε) ∧
      (∀ q, dist (u q) (positiveGridRectilinearUpperDrop q) < ε) ∧
      EqOn l positiveGridRectilinearLowerRise (positiveGridRoundingCornerNeighborhood δ)ᶜ ∧
      EqOn u positiveGridRectilinearUpperDrop (positiveGridRoundingCornerNeighborhood δ)ᶜ ∧
      ∃ B : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
          (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
        (∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
          (B (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
            planeSolidTorusMap i (positiveRectilinearCylinderPoint (List.ofFn w).flatten
              (positiveRoundedWord (List.ofFn w).flatten (fun _ => l) (fun _ => u)
                ((σ 0).symm k) 1 (positiveRoundedWordPeriodTime (List.ofFn w).flatten θ)))) ∧
        ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
          ∀ v, Φ.final (A v) = B (positiveScheduleSourceRotation m b v) := by
  obtain ⟨l, u, hls, hus, hla, hua, hl, hu, A', B, hA', hB, Φ, hΦ⟩ :=
    exists_positiveGridGlobalWordModel_rounded_diffeotopy hm left right σ w hlt hsep hp hc
      i b hb hd hδ hδ' hε hε'
  refine ⟨l, u, hls, hus, hla, hua, hl, hu, B, hB, Φ, ?_⟩
  intro v
  have heq : A v = A' v := by
    obtain ⟨θ, hθ, hbase⟩ := exists_circle_angle_in_period b (v ^ m)
    obtain ⟨k, rfl⟩ := exists_braidCircleSheet_eq hm θ hbase.symm
    exact Subtype.ext ((hA k θ hθ).trans (hA' k θ hθ).symm)
  rw [heq, hΦ]

end OnLeConjecture.KnotTheory
