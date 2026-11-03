/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridSeparatedRows
public import OnLeConjecture.KnotTheory.PositiveBraidGridRowShearNative

/-! # Ambient row separation of the same rounded closed word

The literal rounded-word embedding is the initial endpoint. One jointly chosen
smooth offset realizes the separated rows of the native marking permutations,
and its cylinder shear extends to an ambient sphere diffeotopy. The terminal
formula is retained explicitly. Its identification with a rounded grid drawing
still requires the straight-portion and corner descriptions.
-/

@[expose] public noncomputable section
open Set Manifold
open scoped Topology ContDiff Manifold
open OnLeConjecture.Analytic OnLeConjecture.DifferentialTopology
attribute [local instance] finrank_real_complex_fact'

local instance separatedRowsRealInner : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _
local instance separatedRowsRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

namespace OnLeConjecture.KnotTheory

/-- The retained rounded carrier admits a native ambient row deformation with
exactly the separated rows defining the constructed grid. All smoothness,
injectivity, and immersion properties are derived. The empty one-strand word is
allowed, without interpreting its zero-mark diagram as a geometric grid. -/
theorem exists_positiveRoundedWord_separated_rows_diffeotopy {m : ℕ} (hm : 0 < m)
    (w : PositiveAdjacentWord m) (before after : Equiv.Perm (Fin m))
    (hw : before * w.permutation = after) (hc : after.trans (finRotate m) = before)
    (i : Fin 2) {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla : ∀ j q, dist (l j q) (positiveGridRectilinearLowerRise q) < 1 / 8)
    (hua : ∀ j q, dist (u j q) (positiveGridRectilinearUpperDrop q) < 1 / 8)
    (hls : ∀ j, ContDiff ℝ ∞ (l j)) (hus : ∀ j, ContDiff ℝ ∞ (u j))
    (A : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
      (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1))
    (hA : ∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
      (A (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
        planeSolidTorusMap i (positiveRectilinearCylinderPoint w
          (positiveRoundedWord w l u (before.symm k) 1 (positiveRoundedWordPeriodTime w θ))))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : Fin w.length × Fin 3 → ℝ)
      (G : TauCeti.GridDiagram (w.length * 3)) (row : Fin (w.length * 3) → ℝ)
      (q : ℂ × ℝ → ℝ),
      Function.Injective g ∧
      (∀ p, |g p - positiveRectilinearWordArcRow w p| < ε) ∧
      (∀ p p', positiveRectilinearWordArcRow w p < positiveRectilinearWordArcRow w p' →
        g p < g p') ∧ StrictMono row ∧
      (∀ p, row (G.O (finProdFinEquiv p)) = g p) ∧
      (∀ p, row (G.X (finProdFinEquiv p)) =
        g ((positiveRectilinearWordMatching w).symm p)) ∧
      ContDiff ℝ ∞ q ∧ LipschitzWith (1 / 2) q ∧
      (∀ a p, p ∈ positiveRectilinearHorizontalArcSet w a →
        q p = g ((positiveRectilinearOutgoingArc w).symm a) -
          positiveRectilinearHorizontalArcRow w a) ∧
      ∃ B : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
          (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
        (∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
          (B (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
            planeSolidTorusMap i (positiveGridRowShearCylinder q 1
              (positiveRectilinearCylinderPoint w
                (positiveRoundedWord w l u (before.symm k) 1
                  (positiveRoundedWordPeriodTime w θ))))) ∧
        ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
          ∀ v, Φ.final (A v) = B v := by
  obtain ⟨g, G, row, q, hg, hclose, horder, hrow, hO, hX, hqs, hq, hqarc⟩ :=
    exists_positiveRectilinearWordGrid_smooth_row_offset w hε
  obtain ⟨F, hF, he, hEmb⟩ := exists_positiveRoundedWord_circle_embeddings hm w before.symm
    (positiveWord_inverse_sorting_rotation w before after hw hc) hU hl hu hla hua hls hus
  have hU' : U ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    have hh := hU ht
    constructor <;> linarith [hh.1, hh.2]
  have hFone : ContMDiff (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞ (fun v => F (v, 1)) :=
    hF.comp (contMDiff_id.prodMk contMDiff_const)
  obtain ⟨A', B, hA', hB, Φ, hΦ⟩ := exists_positiveGridRowShear_sphere_diffeotopy i hFone
    (hEmb 1).injective
    (positiveRoundedWord_circle_family_mfderiv_injective hm w before.symm
      hl hu hU' hls hus hF he 1) hqs hq
  refine ⟨g, G, row, q, hg, hclose, horder, hrow, hO, hX, hqs, hq, hqarc, B, ?_, Φ, ?_⟩
  · intro k θ hθ
    rw [hB, he k θ 1 hθ, positiveRoundedWordDeformation_one]
  · intro v
    have heq : A v = A' v := by
      obtain ⟨θ, hθ, hbase⟩ := exists_circle_angle_in_period 0 (v ^ m)
      obtain ⟨k, rfl⟩ := exists_braidCircleSheet_eq hm θ hbase.symm
      have hθ' : θ ∈ Icc (0 : ℝ) (2 * Real.pi) := by simpa using hθ
      apply Subtype.ext
      rw [hA k θ hθ', hA', he k θ 1 hθ', positiveRoundedWordDeformation_one]
    rw [heq, hΦ]

end OnLeConjecture.KnotTheory
