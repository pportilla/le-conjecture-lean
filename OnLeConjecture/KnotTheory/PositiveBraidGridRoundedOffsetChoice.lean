/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRowOffsetAmbientIsotopy

/-! # Row-offset independence for the retained rounded word

The native ambient interpolation keeps the word, profiles, progress, labels, and
marking permutations fixed. Original horizontal-arc curve points are fixed at
every time, and the literal native marking coordinates do not vary.
-/

@[expose] public noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff Manifold
open OnLeConjecture.Analytic
attribute [local instance] finrank_real_complex_fact'

local instance offsetChoiceRealInner : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _
local instance offsetChoiceRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

namespace OnLeConjecture.KnotTheory

/-- The actual ambient interpolation between two offsets realizing the same
native rows, with all original horizontal-arc curve points fixed throughout. -/
theorem exists_positiveRoundedWord_offset_choice_diffeotopy {m : ℕ} (hm : 0 < m)
    (w : PositiveAdjacentWord m) (σ : Equiv.Perm (Fin m))
    (hσ : ∀ k, σ (finRotate m k) = w.permutation.symm (σ k))
    (i : Fin 2) {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla : ∀ j t, dist (l j t) (positiveGridRectilinearLowerRise t) < 1 / 8)
    (hua : ∀ j t, dist (u j t) (positiveGridRectilinearUpperDrop t) < 1 / 8)
    (hls : ∀ j, ContDiff ℝ ∞ (l j)) (hus : ∀ j, ContDiff ℝ ∞ (u j))
    (g : Fin w.length × Fin 3 → ℝ) {q₀ q₁ : ℂ × ℝ → ℝ}
    (hqs₀ : ContDiff ℝ ∞ q₀) (hqs₁ : ContDiff ℝ ∞ q₁)
    (hq₀ : LipschitzWith (1 / 2) q₀) (hq₁ : LipschitzWith (1 / 2) q₁)
    (harc₀ : ∀ a p, p ∈ positiveRectilinearHorizontalArcSet w a →
      q₀ p = g ((positiveRectilinearOutgoingArc w).symm a) -
        positiveRectilinearHorizontalArcRow w a)
    (harc₁ : ∀ a p, p ∈ positiveRectilinearHorizontalArcSet w a →
      q₁ p = g ((positiveRectilinearOutgoingArc w).symm a) -
        positiveRectilinearHorizontalArcRow w a)
    (G : TauCeti.GridDiagram (w.length * 3)) (row : Fin (w.length * 3) → ℝ)
    (hO : ∀ p, row (G.O (finProdFinEquiv p)) = g p)
    (hX : ∀ p, row (G.X (finProdFinEquiv p)) =
      g ((positiveRectilinearWordMatching w).symm p))
    (A B : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
      (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1))
    (hA : ∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
      (A (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
        planeSolidTorusMap i (positiveGridRowShearCylinder q₀ 1
          (positiveRectilinearCylinderPoint w (positiveRoundedWord w l u (σ k) 1
            (positiveRoundedWordPeriodTime w θ)))))
    (hB : ∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
      (B (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
        planeSolidTorusMap i (positiveGridRowShearCylinder q₁ 1
          (positiveRectilinearCylinderPoint w (positiveRoundedWord w l u (σ k) 1
            (positiveRoundedWordPeriodTime w θ))))) :
    (∀ s : ℝ, LipschitzWith (1 / 2) (positiveGridRowOffsetInterpolation q₀ q₁ s)) ∧
    (∀ s j c o, positiveGridRowShearCylinder (positiveGridRowOffsetInterpolation q₀ q₁ s) 1
      (positiveRectilinearCylinderPoint w (positiveRectilinearWordMarkedCorner w j c o)) =
        positiveWordNativeMarkedCorner w G row j c o) ∧
    ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
      (∀ t : unitInterval, ∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
        (Φ (t, A (braidCircleSheet m k θ)) : EuclideanSpace ℂ (Fin 2)) =
          planeSolidTorusMap i (positiveGridRowShearCylinder
            (positiveGridRowOffsetInterpolation q₀ q₁ t) 1
            (positiveRectilinearCylinderPoint w (positiveRoundedWord w l u (σ k) 1
              (positiveRoundedWordPeriodTime w θ))))) ∧
      (∀ v, Φ.final (A v) = B v) ∧
      ∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
        (∃ a : PositiveRectilinearHorizontalArc w,
          let p := positiveRectilinearCylinderPoint w (positiveRoundedWord w l u (σ k) 1
            (positiveRoundedWordPeriodTime w θ))
          ((p.1 : ℂ), p.2.re) ∈ positiveRectilinearHorizontalArcSet w a) →
        ∀ t : unitInterval, Φ (t, A (braidCircleSheet m k θ)) = A (braidCircleSheet m k θ) := by
  refine ⟨positiveGridRowOffsetInterpolation_lipschitz hq₀ hq₁,
    positiveGridRowOffsetInterpolation_markedCorner w g harc₀ harc₁ G row hO hX, ?_⟩
  obtain ⟨F, hF, he, hEmb⟩ := exists_positiveRoundedWord_circle_embeddings hm w σ hσ hU
    hl hu hla hua hls hus
  have hU' : U ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    have hh := hU ht
    constructor <;> linarith [hh.1, hh.2]
  have he₁ (k : Fin m) (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) (2 * Real.pi)) :
      F (braidCircleSheet m k θ, 1) = positiveRectilinearCylinderPoint w
        (positiveRoundedWord w l u (σ k) 1 (positiveRoundedWordPeriodTime w θ)) := by
    rw [he k θ 1 hθ, positiveRoundedWordDeformation_one]
  have hA' (v : Circle) : (A v : EuclideanSpace ℂ (Fin 2)) =
      planeSolidTorusMap i (positiveGridRowShearCylinder q₀ 1 (F (v, 1))) := by
    obtain ⟨θ, hθ, k, rfl⟩ := exists_braidCircleSheet_half_open hm v
    rw [he₁ k θ ⟨hθ.1, hθ.2.le⟩, hA k θ ⟨hθ.1, hθ.2.le⟩]
  have hB' (v : Circle) : (B v : EuclideanSpace ℂ (Fin 2)) =
      planeSolidTorusMap i (positiveGridRowShearCylinder q₁ 1 (F (v, 1))) := by
    obtain ⟨θ, hθ, k, rfl⟩ := exists_braidCircleSheet_half_open hm v
    rw [he₁ k θ ⟨hθ.1, hθ.2.le⟩, hB k θ ⟨hθ.1, hθ.2.le⟩]
  have hF₁ : ContMDiff (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞
      (fun v : Circle => F (v, 1)) := hF.comp (contMDiff_id.prodMk contMDiff_const)
  obtain ⟨Φ, hΦ, hfinal, hfixed⟩ := exists_positiveGridRowOffset_choice_diffeotopy i
    (F := fun v : Circle => F (v, 1)) hF₁ (hEmb 1).injective
    (positiveRoundedWord_circle_family_mfderiv_injective hm w σ hl hu hU' hls hus hF he 1)
    hqs₀ hqs₁ hq₀ hq₁ A B hA' hB'
  refine ⟨Φ, ?_, hfinal, ?_⟩
  · intro s k θ hθ
    rw [hΦ s, he₁ k θ hθ]
  · intro k θ hθ ⟨a, ha⟩ s
    apply hfixed
    rw [he₁ k θ hθ]
    exact (harc₀ a _ ha).trans (harc₁ a _ ha).symm

end OnLeConjecture.KnotTheory
