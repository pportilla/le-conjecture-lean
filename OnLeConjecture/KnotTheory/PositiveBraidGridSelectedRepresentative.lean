/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRoundedOffsetChoice

/-! # A fixed selected representative of the word's native grid data

Fixed positive tolerances select one admissible row-offset construction and one
own-supported profile pair. The resulting native smooth sphere embedding has an
exact sheet formula. Its data retain the word, labels, and coordinate choices.
No independence from the word or reduction to a grid diagram alone is asserted.
-/

@[expose] public noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff Manifold
open OnLeConjecture.Analytic
attribute [local instance] finrank_real_complex_fact'

local instance selectedRepresentativeRealInner : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _
local instance selectedRepresentativeRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

namespace OnLeConjecture.KnotTheory

/-- Admissible geometric data at the fixed approximation tolerance `1/64` and
own-vertex parameter radius `1/96`. These are properties of constructed data. -/
structure PositiveRoundedWordRepresentativeData {m : ℕ} (w : PositiveAdjacentWord m) where
  g : Fin w.length × Fin 3 → ℝ
  grid : TauCeti.GridDiagram (w.length * 3)
  row : Fin (w.length * 3) → ℝ
  offset : ℂ × ℝ → ℝ
  g_injective : Function.Injective g
  g_close : ∀ p, |g p - positiveRectilinearWordArcRow w p| < 1 / 64
  g_order : ∀ p p', positiveRectilinearWordArcRow w p < positiveRectilinearWordArcRow w p' →
    g p < g p'
  row_strictMono : StrictMono row
  row_O : ∀ p, row (grid.O (finProdFinEquiv p)) = g p
  row_X : ∀ p, row (grid.X (finProdFinEquiv p)) =
    g ((positiveRectilinearWordMatching w).symm p)
  offset_smooth : ContDiff ℝ ∞ offset
  offset_lipschitz : LipschitzWith (1 / 2) offset
  offset_on_arcs : ∀ a p, p ∈ positiveRectilinearHorizontalArcSet w a →
    offset p = g ((positiveRectilinearOutgoingArc w).symm a) -
      positiveRectilinearHorizontalArcRow w a
  lower : ℝ → ℝ
  upper : ℝ → ℝ
  lower_smooth : ContDiff ℝ ∞ lower
  upper_smooth : ContDiff ℝ ∞ upper
  lower_close : ∀ t, dist (lower t) (positiveGridRectilinearLowerRise t) < 1 / 64
  upper_close : ∀ t, dist (upper t) (positiveGridRectilinearUpperDrop t) < 1 / 64
  lower_eq : EqOn lower positiveGridRectilinearLowerRise
    (positiveGridLowerVertexNeighborhood (1 / 96))ᶜ
  upper_eq : EqOn upper positiveGridRectilinearUpperDrop
    (positiveGridUpperVertexNeighborhood (1 / 96))ᶜ

/-- The fixed data exist by the proved row-offset and own-profile constructions. -/
theorem nonempty_positiveRoundedWordRepresentativeData {m : ℕ} (w : PositiveAdjacentWord m) :
    Nonempty (PositiveRoundedWordRepresentativeData w) := by
  obtain ⟨g, G, row, q, hg, hclose, horder, hrow, hO, hX, hqs, hq, harc⟩ :=
    exists_positiveRectilinearWordGrid_smooth_row_offset w (by norm_num : (0 : ℝ) < 1 / 64)
  obtain ⟨l, u, hls, hus, hla, hua, hl, hu, _, _⟩ :=
    exists_positiveGrid_own_vertex_profiles (by norm_num : (0 : ℝ) < 1 / 96)
      (by norm_num : (0 : ℝ) < 1 / 64)
  exact ⟨⟨g, G, row, q, hg, hclose, horder, hrow, hO, hX, hqs, hq, harc,
    l, u, hls, hus, hla, hua, hl, hu⟩⟩

/-- A fixed choice of the constructed data, with no remaining external certificate input. -/
def positiveRoundedWordSelectedData {m : ℕ} (w : PositiveAdjacentWord m) :
    PositiveRoundedWordRepresentativeData w :=
  Classical.choice (nonempty_positiveRoundedWordRepresentativeData w)

/-- The chosen data have a native smooth representative with the exact sheet formula. -/
theorem exists_positiveRoundedWord_selected_representative {m : ℕ} (hm : 0 < m)
    (w : PositiveAdjacentWord m) (before after : Equiv.Perm (Fin m))
    (hw : before * w.permutation = after) (hc : after.trans (finRotate m) = before)
    (i : Fin 2) :
    let d := positiveRoundedWordSelectedData w
    ∃ B : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
        (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
      ∀ k θ, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
        (B (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
          planeSolidTorusMap i (positiveGridRowShearCylinder d.offset 1
            (positiveRectilinearCylinderPoint w (positiveRoundedWord w
              (fun _ => d.lower) (fun _ => d.upper) (before.symm k) 1
                (positiveRoundedWordPeriodTime w θ)))) := by
  let d := positiveRoundedWordSelectedData w
  have hl := d.lower_eq.mono
    (compl_subset_compl.mpr (positiveGridLowerVertexNeighborhood_subset (1 / 96)))
  have hu := d.upper_eq.mono
    (compl_subset_compl.mpr (positiveGridUpperVertexNeighborhood_subset (1 / 96)))
  obtain ⟨_, B, _, hB, _, _⟩ := exists_positiveRoundedWord_sheared_from_canonical hm w before after
    hw hc i (positiveGridRoundingCornerNeighborhood_subset (by norm_num : (1 / 96 : ℝ) ≤ 1 / 48))
    (fun _ => hl) (fun _ => hu)
    (fun _ t => (d.lower_close t).trans_le (by norm_num : (1 / 64 : ℝ) ≤ 1 / 8))
    (fun _ t => (d.upper_close t).trans_le (by norm_num : (1 / 64 : ℝ) ≤ 1 / 8))
    (fun _ => d.lower_smooth) (fun _ => d.upper_smooth) d.offset_smooth d.offset_lipschitz
  exact ⟨B, hB⟩

/-- The fixed selected smooth embedding, depending on the retained word and labels. -/
def positiveRoundedWordSelectedRepresentative {m : ℕ} (hm : 0 < m)
    (w : PositiveAdjacentWord m) (before after : Equiv.Perm (Fin m))
    (hw : before * w.permutation = after) (hc : after.trans (finRotate m) = before)
    (i : Fin 2) : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
      (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :=
  Classical.choose (exists_positiveRoundedWord_selected_representative hm w before after hw hc i)

/-- The selected embedding has its literal fixed-profile and fixed-offset sheet formula. -/
theorem positiveRoundedWordSelectedRepresentative_sheet {m : ℕ} (hm : 0 < m)
    (w : PositiveAdjacentWord m) (before after : Equiv.Perm (Fin m))
    (hw : before * w.permutation = after) (hc : after.trans (finRotate m) = before)
    (i : Fin 2) (k : Fin m) (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) (2 * Real.pi)) :
    let d := positiveRoundedWordSelectedData w
    (positiveRoundedWordSelectedRepresentative hm w before after hw hc i
      (braidCircleSheet m k θ) : EuclideanSpace ℂ (Fin 2)) =
        planeSolidTorusMap i (positiveGridRowShearCylinder d.offset 1
          (positiveRectilinearCylinderPoint w (positiveRoundedWord w
            (fun _ => d.lower) (fun _ => d.upper) (before.symm k) 1
              (positiveRoundedWordPeriodTime w θ)))) :=
  Classical.choose_spec
    (exists_positiveRoundedWord_selected_representative hm w before after hw hc i) k θ hθ

/-- Given the known product column indexing and injective native row coordinates,
the full horizontal successor matching is recovered from the two native marking permutations. -/
theorem positiveRectilinearWordMatching_recovered_from_grid {m : ℕ}
    (w : PositiveAdjacentWord m) (G : TauCeti.GridDiagram (w.length * 3))
    (row : Fin (w.length * 3) → ℝ) (hrow : Function.Injective row)
    (g : Fin w.length × Fin 3 → ℝ)
    (hO : ∀ p, row (G.O (finProdFinEquiv p)) = g p)
    (hX : ∀ p, row (G.X (finProdFinEquiv p)) =
      g ((positiveRectilinearWordMatching w).symm p)) (p : Fin w.length × Fin 3) :
    positiveRectilinearWordMatching w p = finProdFinEquiv.symm
      (G.X.toPerm.symm (G.O (finProdFinEquiv p))) := by
  apply finProdFinEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply G.X.toPerm.injective
  rw [Equiv.apply_symm_apply]
  exact (positiveRectilinearWordGrid_horizontal_matching w G row hrow g hO hX p).symm

end OnLeConjecture.KnotTheory
