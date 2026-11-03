/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRoundedWordImmersion
public import OnLeConjecture.Analytic.PlaneBranchBraidWordCycle

/-! # Ambient deformation from the canonical word to its rounded carrier

The endpoint rotation determines the source labels. Smooth rise profiles are
chosen by the proved relative approximation theorem. The resulting circle family
has the exact rounded-word formula and extends to an ambient sphere diffeotopy.
The subsequent geometric separation of horizontal rows for the constructed grid
is not asserted here.
-/

@[expose] public noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff Manifold
open OnLeConjecture.Analytic OnLeConjecture.DifferentialTopology
attribute [local instance] finrank_real_complex_fact'

local instance roundedWordRealInner : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _
local instance roundedWordRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

namespace OnLeConjecture.KnotTheory

/-- The already proved endpoint rotation supplies the required source labelling. -/
theorem positiveWord_inverse_sorting_rotation {m : ℕ} (w : PositiveAdjacentWord m)
    (before after : Equiv.Perm (Fin m)) (hw : before * w.permutation = after)
    (hc : after.trans (finRotate m) = before) (k : Fin m) :
    before.symm (finRotate m k) = w.permutation.symm (before.symm k) := by
  have hp : w.permutation⁻¹ = before⁻¹ * finRotate m * before := by
    rw [braid_permutation_eq_conjugate_inverse_rotation before after w.permutation hw hc]
    group
  change before⁻¹ (finRotate m k) = w.permutation⁻¹ (before⁻¹ k)
  rw [hp]
  simp only [Equiv.Perm.mul_apply]
  rw [show before (before⁻¹ k) = k from before.apply_symm_apply k]

/-- Any exact native rounded-word family has ambiently diffeotopic sphere endpoints.
All immersion and embedding conditions are proved from its retained word formula. -/
theorem exists_positiveRoundedWord_endpoint_diffeotopy {m : ℕ} (hm : 0 < m)
    (w : PositiveAdjacentWord m) (σ : Equiv.Perm (Fin m))
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
    ∃ (L₀ L₁ : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
        (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)),
      (∀ v, (L₀ v : EuclideanSpace ℂ (Fin 2)) = complexSolidTorusMap (F (v, 0))) ∧
      (∀ v, (L₁ v : EuclideanSpace ℂ (Fin 2)) = complexSolidTorusMap (F (v, 1))) ∧
      ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
        ∀ v, Φ.final (L₀ v) = L₁ v := by
  have hU' : U ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    have hh := hU ht
    constructor <;> linarith [hh.1, hh.2]
  apply exists_plane_sphere_family_endpoint_diffeotopy
    (fun p => complexSolidTorusMap (F p))
    (fun _ _ => complexSolidTorusMap_norm _) (complexSolidTorusMap_contMDiff.comp hF)
  · intro s v
    have hFs : ContMDiff (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞ (fun v => F (v, s)) :=
      hF.comp (contMDiff_id.prodMk (contMDiff_const (c := s)))
    rw [show (fun u => complexSolidTorusMap (F (u, s))) =
      complexSolidTorusMap ∘ (fun u => F (u, s)) from rfl,
      mfderiv_comp v (complexSolidTorusMap_contMDiff.mdifferentiableAt (by simp))
        (hFs.mdifferentiableAt (by simp))]
    exact (complexSolidTorusMap_mfderiv_injective _).comp
      (positiveRoundedWord_circle_family_mfderiv_injective hm w σ hl hu hU' hls hus hF he s v)
  · intro s
    exact complexSolidTorusMap_isEmbedding.comp
      ((hF.continuous.comp (continuous_id.prodMk continuous_const)).isClosedEmbedding
        (positiveRoundedWord_circle_family_injective hm w σ hU hl hu hla hua he s)).isEmbedding

/-- Endpoint rotation alone supplies the labels and the smooth rounding choices.
The resulting native sphere diffeotopy starts at the canonical generator word
and ends at its specified rounded carrier, with one common source circle.
The empty word at one strand is included. -/
theorem exists_positiveWord_rounded_sphere_diffeotopy {m : ℕ} (hm : 0 < m)
    (w : PositiveAdjacentWord m) (before after : Equiv.Perm (Fin m))
    (hw : before * w.permutation = after) (hc : after.trans (finRotate m) = before)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 48) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) :
    ∃ l u : ℝ → ℝ, ContDiff ℝ ∞ l ∧ ContDiff ℝ ∞ u ∧
      (∀ q, dist (l q) (positiveGridRectilinearLowerRise q) < ε) ∧
      (∀ q, dist (u q) (positiveGridRectilinearUpperDrop q) < ε) ∧
      EqOn l positiveGridRectilinearLowerRise (positiveGridRoundingCornerNeighborhood δ)ᶜ ∧
      EqOn u positiveGridRectilinearUpperDrop (positiveGridRoundingCornerNeighborhood δ)ᶜ ∧
      ∃ F : Circle × ℝ → Circle × ℂ,
        ContMDiff ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞ F ∧
        (∀ k θ s, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
          F (braidCircleSheet m k θ, s) = positiveRectilinearCylinderPoint w
            (positiveRoundedWordDeformation w (fun _ => l) (fun _ => u) (before.symm k) s
              (positiveRoundedWordPeriodTime w θ))) ∧
        (∀ s, IsSmoothEmbedding (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞ (fun v => F (v, s))) ∧
        ∃ (L₀ L₁ : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
            (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)),
          (∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
            (L₀ (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
              complexSolidTorusMap (positiveRectilinearCylinderPoint w
                (positiveRoundedWordLift w (before.symm k) 0
                  (positiveRoundedWordPeriodTime w θ)))) ∧
          (∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
            (L₁ (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
              complexSolidTorusMap (positiveRectilinearCylinderPoint w
                (positiveRoundedWord w (fun _ => l) (fun _ => u) (before.symm k) 1
                  (positiveRoundedWordPeriodTime w θ)))) ∧
          (∀ v, (L₀ v : EuclideanSpace ℂ (Fin 2)) = complexSolidTorusMap (F (v, 0))) ∧
          (∀ v, (L₁ v : EuclideanSpace ℂ (Fin 2)) = complexSolidTorusMap (F (v, 1))) ∧
          ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
            ∀ v, Φ.final (L₀ v) = L₁ v := by
  obtain ⟨l, u, hls, hus, hla, hua, hl, hu⟩ :=
    exists_positiveGridRectilinear_smooth_rises hε
      (positiveGridRoundingCornerNeighborhood_isOpen δ)
      (positiveGridRoundingCornerNeighborhood_contains hδ)
  have hU := positiveGridRoundingCornerNeighborhood_subset hδ'
  have hU' : positiveGridRoundingCornerNeighborhood δ ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    have hh := hU ht
    constructor <;> linarith [hh.1, hh.2]
  have hla' : ∀ q, dist (l q) (positiveGridRectilinearLowerRise q) < 1 / 8 :=
    fun q => (hla q).trans_le hε'
  have hua' : ∀ q, dist (u q) (positiveGridRectilinearUpperDrop q) < 1 / 8 :=
    fun q => (hua q).trans_le hε'
  obtain ⟨F, hF, he, hEmb⟩ := exists_positiveRoundedWord_circle_embeddings hm w before.symm
    (positiveWord_inverse_sorting_rotation w before after hw hc) hU
    (fun _ => hl) (fun _ => hu) (fun _ => hla') (fun _ => hua')
    (fun _ => hls) (fun _ => hus)
  refine ⟨l, u, hls, hus, hla, hua, hl, hu, F, hF, he, ?_, ?_⟩
  · intro s
    exact (hF.comp (contMDiff_id.prodMk contMDiff_const)).isSmoothEmbedding_of_injective_mfderiv
      (by simp)
      (positiveRoundedWord_circle_family_mfderiv_injective hm w before.symm
        (fun _ => hl) (fun _ => hu) hU' (fun _ => hls) (fun _ => hus) hF he s)
      (hEmb s).isEmbedding
  · obtain ⟨L₀, L₁, hL₀, hL₁, Φ, hΦ⟩ := exists_positiveRoundedWord_endpoint_diffeotopy hm w
      before.symm hU (fun _ => hl) (fun _ => hu) (fun _ => hla') (fun _ => hua')
      (fun _ => hls) (fun _ => hus) hF he
    refine ⟨L₀, L₁, ?_, ?_, hL₀, hL₁, Φ, hΦ⟩
    · intro k θ hθ
      rw [hL₀, he k θ 0 hθ, positiveRoundedWordDeformation_zero w
        (fun _ => hl) (fun _ => hu) hU' (before.symm k) (positiveRoundedWordPeriodTime_mem w hθ)]
    · intro k θ hθ
      rw [hL₁, he k θ 1 hθ, positiveRoundedWordDeformation_one]

end OnLeConjecture.KnotTheory
