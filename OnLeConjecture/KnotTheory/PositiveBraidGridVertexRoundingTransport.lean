/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridVertexRoundingProfiles

/-! # Transport of the retained curve to rounding at its own vertices

The original and replacement rounded profiles are connected through their
literally identical canonical endpoint. Composing the already proved native
ambient deformations retains the word, source labels, and terminal row shear.
-/

@[expose] public noncomputable section
open Set Manifold
open scoped Topology ContDiff Manifold
open OnLeConjecture.Analytic OnLeConjecture.DifferentialTopology
attribute [local instance] finrank_real_complex_fact'

local instance vertexRoundingRealInner : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _
local instance vertexRoundingRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

namespace OnLeConjecture.KnotTheory

/-- A retained profile and row shear have an exact canonical initial endpoint. -/
theorem exists_positiveRoundedWord_sheared_from_canonical {m : ℕ} (hm : 0 < m)
    (w : PositiveAdjacentWord m) (before after : Equiv.Perm (Fin m))
    (hw : before * w.permutation = after) (hc : after.trans (finRotate m) = before)
    (i : Fin 2) {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla : ∀ j t, dist (l j t) (positiveGridRectilinearLowerRise t) < 1 / 8)
    (hua : ∀ j t, dist (u j t) (positiveGridRectilinearUpperDrop t) < 1 / 8)
    (hls : ∀ j, ContDiff ℝ ∞ (l j)) (hus : ∀ j, ContDiff ℝ ∞ (u j))
    {q : ℂ × ℝ → ℝ} (hqs : ContDiff ℝ ∞ q) (hq : LipschitzWith (1 / 2) q) :
    ∃ (C B : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
        (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)),
      (∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
        (C (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
          planeSolidTorusMap i (positiveRectilinearCylinderPoint w
            (positiveRoundedWordLift w (before.symm k) 0 (positiveRoundedWordPeriodTime w θ)))) ∧
      (∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
        (B (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
          planeSolidTorusMap i (positiveGridRowShearCylinder q 1
            (positiveRectilinearCylinderPoint w
              (positiveRoundedWord w l u (before.symm k) 1 (positiveRoundedWordPeriodTime w θ))))) ∧
      ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
        ∀ v, Φ.final (C v) = B v := by
  have hU' : U ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    have hh := hU ht
    constructor <;> linarith [hh.1, hh.2]
  obtain ⟨F, hF, he, hEmb⟩ := exists_positiveRoundedWord_circle_embeddings hm w before.symm
    (positiveWord_inverse_sorting_rotation w before after hw hc) hU hl hu hla hua hls hus
  obtain ⟨C, A, hC, hA, Φ, hΦ⟩ := exists_positiveRoundedWord_selected_endpoint_diffeotopy
    hm w before.symm i hU hl hu hla hua hls hus hF he
  obtain ⟨A', B, hA', hB, Ψ, hΨ⟩ := exists_positiveGridRowShear_sphere_diffeotopy i
    (hF.comp (contMDiff_id.prodMk contMDiff_const)) (hEmb 1).injective
    (positiveRoundedWord_circle_family_mfderiv_injective hm w before.symm
      hl hu hU' hls hus hF he 1) hqs hq
  refine ⟨C, B, ?_, ?_, Φ.trans Ψ, ?_⟩
  · intro k θ hθ
    rw [hC, he k θ 0 hθ, positiveRoundedWordDeformation_zero w hl hu hU'
      (before.symm k) (positiveRoundedWordPeriodTime_mem w hθ)]
  · intro k θ hθ
    rw [hB]
    simp only [Function.comp_apply, id_eq]
    rw [he k θ 1 hθ, positiveRoundedWordDeformation_one]
  · intro v
    have hAA : A v = A' v := Subtype.ext ((hA v).trans (hA' v).symm)
    rw [TauCeti.Diffeotopy.final_trans]
    change Ψ.final (Φ.final (C v)) = B v
    rw [hΦ, hAA, hΨ]

/-- Replace the retained profiles by profiles supported only near each strand's
own vertices. The initial curve is the SAME supplied sheared rounded embedding,
and the final curve has the SAME word, source labels, and row-offset function. -/
theorem exists_positiveRoundedWord_own_vertex_diffeotopy {m : ℕ} (hm : 0 < m)
    (w : PositiveAdjacentWord m) (before after : Equiv.Perm (Fin m))
    (hw : before * w.permutation = after) (hc : after.trans (finRotate m) = before)
    (i : Fin 2) {l₀ u₀ : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl₀ : ∀ j, EqOn (l₀ j) positiveGridRectilinearLowerRise Uᶜ)
    (hu₀ : ∀ j, EqOn (u₀ j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla₀ : ∀ j t, dist (l₀ j t) (positiveGridRectilinearLowerRise t) < 1 / 8)
    (hua₀ : ∀ j t, dist (u₀ j t) (positiveGridRectilinearUpperDrop t) < 1 / 8)
    (hls₀ : ∀ j, ContDiff ℝ ∞ (l₀ j)) (hus₀ : ∀ j, ContDiff ℝ ∞ (u₀ j))
    {q : ℂ × ℝ → ℝ} (hqs : ContDiff ℝ ∞ q) (hq : LipschitzWith (1 / 2) q)
    (A : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
      (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1))
    (hA : ∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
      (A (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
        planeSolidTorusMap i (positiveGridRowShearCylinder q 1
          (positiveRectilinearCylinderPoint w (positiveRoundedWord w l₀ u₀ (before.symm k) 1
            (positiveRoundedWordPeriodTime w θ)))))
    {δ ε : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 48) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) :
    ∃ l u : ℝ → ℝ, ContDiff ℝ ∞ l ∧ ContDiff ℝ ∞ u ∧
      (∀ t, dist (l t) (positiveGridRectilinearLowerRise t) < ε) ∧
      (∀ t, dist (u t) (positiveGridRectilinearUpperDrop t) < ε) ∧
      EqOn l positiveGridRectilinearLowerRise (positiveGridLowerVertexNeighborhood δ)ᶜ ∧
      EqOn u positiveGridRectilinearUpperDrop (positiveGridUpperVertexNeighborhood δ)ᶜ ∧
      ∃ B : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
          (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
        (∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
          (B (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
            planeSolidTorusMap i (positiveGridRowShearCylinder q 1
              (positiveRectilinearCylinderPoint w
                (positiveRoundedWord w (fun _ => l) (fun _ => u) (before.symm k) 1
                  (positiveRoundedWordPeriodTime w θ))))) ∧
        ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
          ∀ v, Φ.final (A v) = B v := by
  obtain ⟨l, u, hls, hus, hla, hua, hl, hu, hlc, huc⟩ :=
    exists_positiveGrid_own_vertex_profiles hδ hε
  obtain ⟨C₀, B₀, hC₀, hB₀, Φ₀, hΦ₀⟩ :=
    exists_positiveRoundedWord_sheared_from_canonical hm w before after hw hc i hU
      hl₀ hu₀ hla₀ hua₀ hls₀ hus₀ hqs hq
  obtain ⟨C₁, B, hC₁, hB, Φ₁, hΦ₁⟩ :=
    exists_positiveRoundedWord_sheared_from_canonical hm w before after hw hc i
      (positiveGridRoundingCornerNeighborhood_subset hδ') (fun _ => hlc) (fun _ => huc)
      (fun _ t => (hla t).trans_le hε') (fun _ t => (hua t).trans_le hε')
      (fun _ => hls) (fun _ => hus) hqs hq
  refine ⟨l, u, hls, hus, hla, hua, hl, hu, B, hB, Φ₀.symm.trans Φ₁, ?_⟩
  intro v
  obtain ⟨θ, hθ, hbase⟩ := exists_circle_angle_in_period 0 (v ^ m)
  obtain ⟨k, rfl⟩ := exists_braidCircleSheet_eq hm θ hbase.symm
  have hθ' : θ ∈ Icc (0 : ℝ) (2 * Real.pi) := by simpa using hθ
  have hAB : A (braidCircleSheet m k θ) = B₀ (braidCircleSheet m k θ) :=
    Subtype.ext ((hA k θ hθ').trans (hB₀ k θ hθ').symm)
  have hCC : C₀ (braidCircleSheet m k θ) = C₁ (braidCircleSheet m k θ) :=
    Subtype.ext ((hC₀ k θ hθ').trans (hC₁ k θ hθ').symm)
  rw [TauCeti.Diffeotopy.final_trans, TauCeti.Diffeotopy.final_symm]
  change Φ₁.final (Φ₀.final.symm (A (braidCircleSheet m k θ))) = B (braidCircleSheet m k θ)
  rw [hAB, ← hΦ₀, Φ₀.final.symm_apply_apply, hCC, hΦ₁]

end OnLeConjecture.KnotTheory
