/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRoundedNativeCoverage

/-! # Relative interpolation of admissible rounded profiles

Convex interpolation retains the original progress and constant moving-strand
depths. Every slice is one of the already proved global rounded embeddings.
Outside the moving strand's own vertex supports, the entire word is pointwise
fixed. No monotonicity of a scalar coordinate after the row shear is asserted.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
open OnLeConjecture.Analytic

namespace OnLeConjecture.KnotTheory

/-- Convex profile interpolation, stationary before time zero and after time one. -/
def positiveGridProfileInterpolation (f₀ f₁ : ℝ → ℝ) (s t : ℝ) : ℝ :=
  (1 - Real.smoothTransition s) * f₀ t + Real.smoothTransition s * f₁ t

@[simp] theorem positiveGridProfileInterpolation_zero (f₀ f₁ : ℝ → ℝ) :
    positiveGridProfileInterpolation f₀ f₁ 0 = f₀ := by
  funext t
  simp [positiveGridProfileInterpolation]

@[simp] theorem positiveGridProfileInterpolation_one (f₀ f₁ : ℝ → ℝ) :
    positiveGridProfileInterpolation f₀ f₁ 1 = f₁ := by
  funext t
  simp [positiveGridProfileInterpolation]

theorem positiveGridProfileInterpolation_of_nonpos (f₀ f₁ : ℝ → ℝ) {s : ℝ} (hs : s ≤ 0) :
    positiveGridProfileInterpolation f₀ f₁ s = f₀ := by
  funext t
  simp [positiveGridProfileInterpolation, Real.smoothTransition.zero_of_nonpos hs]

theorem positiveGridProfileInterpolation_of_one_le (f₀ f₁ : ℝ → ℝ) {s : ℝ} (hs : 1 ≤ s) :
    positiveGridProfileInterpolation f₀ f₁ s = f₁ := by
  funext t
  simp [positiveGridProfileInterpolation, Real.smoothTransition.one_of_one_le hs]

theorem positiveGridProfileInterpolation_contDiff {f₀ f₁ : ℝ → ℝ}
    (h₀ : ContDiff ℝ ∞ f₀) (h₁ : ContDiff ℝ ∞ f₁) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => positiveGridProfileInterpolation f₀ f₁ p.1 p.2) :=
  ((contDiff_const.sub (Real.smoothTransition.contDiff.comp contDiff_fst)).mul
    (h₀.comp contDiff_snd)).add
    ((Real.smoothTransition.contDiff.comp contDiff_fst).mul (h₁.comp contDiff_snd))

theorem positiveGridProfileInterpolation_eqOn {f₀ f₁ f : ℝ → ℝ} {S : Set ℝ}
    (h₀ : EqOn f₀ f S) (h₁ : EqOn f₁ f S) (s : ℝ) :
    EqOn (positiveGridProfileInterpolation f₀ f₁ s) f S := by
  intro t ht
  rw [positiveGridProfileInterpolation, h₀ ht, h₁ ht]
  ring

/-- Convex interpolation preserves the same strict uniform approximation bound. -/
theorem positiveGridProfileInterpolation_dist_lt {f₀ f₁ f : ℝ → ℝ} {ε : ℝ}
    (h₀ : ∀ t, dist (f₀ t) (f t) < ε) (h₁ : ∀ t, dist (f₁ t) (f t) < ε)
    (s t : ℝ) : dist (positiveGridProfileInterpolation f₀ f₁ s t) (f t) < ε := by
  have hσ := Real.smoothTransition.nonneg s
  have hσ' := Real.smoothTransition.le_one s
  have h₀' := abs_lt.mp (show |f₀ t - f t| < ε by simpa only [Real.dist_eq] using h₀ t)
  have h₁' := abs_lt.mp (show |f₁ t - f t| < ε by simpa only [Real.dist_eq] using h₁ t)
  rw [Real.dist_eq, positiveGridProfileInterpolation, abs_lt]
  rw [show (1 - Real.smoothTransition s) * f₀ t + Real.smoothTransition s * f₁ t - f t =
    (1 - Real.smoothTransition s) * (f₀ t - f t) +
      Real.smoothTransition s * (f₁ t - f t) by ring]
  exact (convex_Ioo (-ε) ε) h₀' h₁' (sub_nonneg.mpr hσ') hσ (by ring)

/-- The interpolated word uses exactly the existing rounded-word formula. -/
def positiveRoundedWordProfileInterpolation {m : ℕ} (w : PositiveAdjacentWord m)
    (l₀ u₀ l₁ u₁ : Fin w.length → ℝ → ℝ) (k : Fin m) (s t : ℝ) : ℝ × ℂ :=
  positiveRoundedWord w (fun j => positiveGridProfileInterpolation (l₀ j) (l₁ j) s)
    (fun j => positiveGridProfileInterpolation (u₀ j) (u₁ j) s) k 1 t

/-- Jointly smooth profiles give a jointly smooth rounded local tangle. -/
theorem positiveGridRounded_profileInterpolation_contDiff {m : ℕ} (i : Fin (m - 1))
    {l₀ u₀ l₁ u₁ : ℝ → ℝ} (hl₀ : ContDiff ℝ ∞ l₀) (hu₀ : ContDiff ℝ ∞ u₀)
    (hl₁ : ContDiff ℝ ∞ l₁) (hu₁ : ContDiff ℝ ∞ u₁) (k : Fin m) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => positiveGridRoundedDeformation i
      (positiveGridProfileInterpolation l₀ l₁ p.1)
      (positiveGridProfileInterpolation u₀ u₁ p.1) k 1 p.2) := by
  have hp : ContDiff ℝ ∞ (fun p : ℝ × ℝ => positiveGridRoundingProgress p.2) :=
    positiveGridRoundingProgress_contDiff.comp contDiff_snd
  have hl := (positiveGridProfileInterpolation_contDiff hl₀ hl₁).comp
    (contDiff_fst.prodMk (hp.div_const 2))
  have hu := (positiveGridProfileInterpolation_contDiff hu₀ hu₁).comp
    (contDiff_fst.prodMk (hp.div_const 2))
  unfold positiveGridRoundedDeformation
  split_ifs
  · simp only [positiveGridRoundingRise, sub_self, zero_mul, one_mul, zero_add]
    exact (hp.sub hl).prodMk
      ((Complex.ofRealCLM.contDiff.comp (contDiff_const.add hl)).sub contDiff_const)
  · simp only [positiveGridRoundingRise, sub_self, zero_mul, one_mul, zero_add]
    exact (hp.sub hu).prodMk
      ((Complex.ofRealCLM.contDiff.comp ((contDiff_const.add contDiff_const).sub hu)).add
        contDiff_const)
  · exact contDiff_snd.prodMk contDiff_const

/-- The global word interpolation is jointly smooth across all letter and connector seams. -/
theorem positiveRoundedWordProfileInterpolation_contDiff {m : ℕ} (w : PositiveAdjacentWord m)
    {l₀ u₀ l₁ u₁ : Fin w.length → ℝ → ℝ}
    (hl₀ : ∀ j, ContDiff ℝ ∞ (l₀ j)) (hu₀ : ∀ j, ContDiff ℝ ∞ (u₀ j))
    (hl₁ : ∀ j, ContDiff ℝ ∞ (l₁ j)) (hu₁ : ∀ j, ContDiff ℝ ∞ (u₁ j)) (k : Fin m) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => positiveRoundedWordProfileInterpolation w
      l₀ u₀ l₁ u₁ k p.1 p.2) := by
  unfold positiveRoundedWordProfileInterpolation positiveRoundedWord finiteSmoothPathConcat
  apply ContDiff.add
  · exact contDiff_snd.prodMk ((Complex.ofRealCLM.contDiff.comp
      ((positiveRoundedWordDepth_contDiff w k).comp contDiff_snd)).mul contDiff_const)
  · apply contDiff_const.add
    apply ContDiff.sum
    intro j _
    apply ContDiff.sub _ contDiff_const
    unfold positiveRoundedWordLetterCorrection
    have ht : ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
        (p.2 - (2 * (j.val : ℝ) + 1)) /
          ((2 * (j.val : ℝ) + 2) - (2 * (j.val : ℝ) + 1))) :=
      (contDiff_snd.sub contDiff_const).div_const _
    exact ((positiveGridRounded_profileInterpolation_contDiff w[j.val] (hl₀ j) (hu₀ j)
      (hl₁ j) (hu₁ j) ((positiveWordPrefix w j.val).symm k)).comp
        (contDiff_fst.prodMk ht)).sub (ht.prodMk contDiff_const)

/-- All interpolation slices satisfy the original global closed-embedding theorem. -/
theorem positiveRoundedWordProfileInterpolation_isClosedEmbedding {m : ℕ}
    (w : PositiveAdjacentWord m) {l₀ u₀ l₁ u₁ : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl₀ : ∀ j, EqOn (l₀ j) positiveGridRectilinearLowerRise Uᶜ)
    (hu₀ : ∀ j, EqOn (u₀ j) positiveGridRectilinearUpperDrop Uᶜ)
    (hl₁ : ∀ j, EqOn (l₁ j) positiveGridRectilinearLowerRise Uᶜ)
    (hu₁ : ∀ j, EqOn (u₁ j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla₀ : ∀ j t, dist (l₀ j t) (positiveGridRectilinearLowerRise t) < 1 / 8)
    (hua₀ : ∀ j t, dist (u₀ j t) (positiveGridRectilinearUpperDrop t) < 1 / 8)
    (hla₁ : ∀ j t, dist (l₁ j t) (positiveGridRectilinearLowerRise t) < 1 / 8)
    (hua₁ : ∀ j t, dist (u₁ j t) (positiveGridRectilinearUpperDrop t) < 1 / 8)
    (hls₀ : ∀ j, ContDiff ℝ ∞ (l₀ j)) (hus₀ : ∀ j, ContDiff ℝ ∞ (u₀ j))
    (hls₁ : ∀ j, ContDiff ℝ ∞ (l₁ j)) (hus₁ : ∀ j, ContDiff ℝ ∞ (u₁ j)) (s : ℝ) :
    Topology.IsClosedEmbedding (fun p : Fin m × Icc (0 : ℝ) (2 * (w.length : ℝ) + 1) =>
      positiveRoundedWordProfileInterpolation w l₀ u₀ l₁ u₁ p.1 s p.2) := by
  apply positiveRoundedWord_isClosedEmbedding w hU
    (fun j => positiveGridProfileInterpolation_eqOn (hl₀ j) (hl₁ j) s)
    (fun j => positiveGridProfileInterpolation_eqOn (hu₀ j) (hu₁ j) s)
    (fun j t => positiveGridProfileInterpolation_dist_lt (hla₀ j) (hla₁ j) s t)
    (fun j t => positiveGridProfileInterpolation_dist_lt (hua₀ j) (hua₁ j) s t)
    (fun j => (positiveGridProfileInterpolation_contDiff (hls₀ j) (hls₁ j)).comp
      (contDiff_const.prodMk contDiff_id))
    (fun j => (positiveGridProfileInterpolation_contDiff (hus₀ j) (hus₁ j)).comp
      (contDiff_const.prodMk contDiff_id)) (by norm_num : (1 : ℝ) ∈ Icc 0 1)

/-- Every interpolation slice agrees pointwise with its initial curve away from
only the original moving strand's own corner parameter supports. -/
theorem positiveRoundedWordProfileInterpolation_fixed_outside_own_corners {m : ℕ}
    (w : PositiveAdjacentWord m) {l₀ u₀ l₁ u₁ : Fin w.length → ℝ → ℝ} {δ : ℝ}
    (hδ : δ ≤ 1 / 48)
    (hl₀ : ∀ j, EqOn (l₀ j) positiveGridRectilinearLowerRise
      (positiveGridLowerVertexNeighborhood δ)ᶜ)
    (hu₀ : ∀ j, EqOn (u₀ j) positiveGridRectilinearUpperDrop
      (positiveGridUpperVertexNeighborhood δ)ᶜ)
    (hl₁ : ∀ j, EqOn (l₁ j) positiveGridRectilinearLowerRise
      (positiveGridLowerVertexNeighborhood δ)ᶜ)
    (hu₁ : ∀ j, EqOn (u₁ j) positiveGridRectilinearUpperDrop
      (positiveGridUpperVertexNeighborhood δ)ᶜ)
    (k : Fin m) (s : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (2 * (w.length : ℝ) + 1))
    (hout : ¬ ∃ j c o, PositiveRoundedWordOwnCornerParameter w δ k t j c o) :
    positiveRoundedWordProfileInterpolation w l₀ u₀ l₁ u₁ k s t =
      positiveRoundedWord w l₀ u₀ k 1 t := by
  have hl (j) := positiveGridProfileInterpolation_eqOn (hl₀ j) (hl₁ j) s
  have hu (j) := positiveGridProfileInterpolation_eqOn (hu₀ j) (hu₁ j) s
  have hlc₀ (j) := (hl₀ j).mono
    (compl_subset_compl.mpr (positiveGridLowerVertexNeighborhood_subset δ))
  have huc₀ (j) := (hu₀ j).mono
    (compl_subset_compl.mpr (positiveGridUpperVertexNeighborhood_subset δ))
  have hlc (j) := (hl j).mono
    (compl_subset_compl.mpr (positiveGridLowerVertexNeighborhood_subset δ))
  have huc (j) := (hu j).mono
    (compl_subset_compl.mpr (positiveGridUpperVertexNeighborhood_subset δ))
  have hU : positiveGridRoundingCornerNeighborhood δ ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    have hh := positiveGridRoundingCornerNeighborhood_subset hδ hx
    constructor <;> linarith [hh.1, hh.2]
  unfold positiveRoundedWordProfileInterpolation
  rcases positiveWordPeriodTime_gap_or_letter w.length ht with ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [positiveRoundedWord_gap w hlc huc hU k 1 j hj,
      positiveRoundedWord_gap w hlc₀ huc₀ hU k 1 j hj]
  · by_cases hk₀ : (positiveWordPrefix w j.val).symm k = adjacentLower w[j.val]
    · have hn : positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2 ∉
          positiveGridLowerVertexNeighborhood δ := by
        intro h
        obtain ⟨c, hc, o, hco⟩ := positiveGridLowerVertexNeighborhood_iff_marking.mp h
        apply hout
        exact ⟨j, c, o, hj, by simpa [positiveGridMarkingStrand, hc] using hk₀, hco⟩
      rw [positiveRoundedWord_letter_eq_polygon_own_vertices w hδ hl hu k j hj
        (Or.inl ⟨hk₀, hn⟩), positiveRoundedWord_letter_eq_polygon_own_vertices w hδ
          hl₀ hu₀ k j hj (Or.inl ⟨hk₀, hn⟩)]
    · by_cases hk₁ : (positiveWordPrefix w j.val).symm k = adjacentUpper w[j.val]
      · have hn : positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2 ∉
            positiveGridUpperVertexNeighborhood δ := by
          intro h
          obtain ⟨o, hco⟩ := positiveGridUpperVertexNeighborhood_iff_marking.mp h
          apply hout
          exact ⟨j, 1, o, hj, by simpa [positiveGridMarkingStrand] using hk₁, hco⟩
        rw [positiveRoundedWord_letter_eq_polygon_own_vertices w hδ hl hu k j hj
          (Or.inr ⟨hk₁, hn⟩), positiveRoundedWord_letter_eq_polygon_own_vertices w hδ
            hl₀ hu₀ k j hj (Or.inr ⟨hk₁, hn⟩)]
      · rw [positiveRoundedWord_letter w hlc huc hU k 1 j hj,
          positiveRoundedWord_letter w hlc₀ huc₀ hU k 1 j hj,
          positiveGridRoundedDeformation_fixed _ _ _ _ hk₀ hk₁,
          positiveGridRoundedDeformation_fixed _ _ _ _ hk₀ hk₁]

/-- Every lower interpolated arc has the same strictly increasing pre-shear
linear progress coordinate and constant depth, independently of its profiles. -/
theorem positiveGridRounded_profileInterpolation_lower_graph {m : ℕ} (i : Fin (m - 1))
    (l₀ u₀ l₁ u₁ : ℝ → ℝ) (s t : ℝ) :
    let p := positiveGridRoundedDeformation i (positiveGridProfileInterpolation l₀ l₁ s)
      (positiveGridProfileInterpolation u₀ u₁ s) (adjacentLower i) 1 t
    p.1 + p.2.re - i.val = positiveGridRoundingProgress t ∧ p.2.im = -1 := by
  exact ⟨positiveGridRoundedDeformation_lower_progress i _ _ 1 t, by simp⟩

/-- Every upper interpolated arc has the same strictly increasing pre-shear
linear progress coordinate with the opposite row sign, and constant depth. -/
theorem positiveGridRounded_profileInterpolation_upper_graph {m : ℕ} (i : Fin (m - 1))
    (l₀ u₀ l₁ u₁ : ℝ → ℝ) (s t : ℝ) :
    let p := positiveGridRoundedDeformation i (positiveGridProfileInterpolation l₀ l₁ s)
      (positiveGridProfileInterpolation u₀ u₁ s) (adjacentUpper i) 1 t
    p.1 - p.2.re + (i.val + 1) = positiveGridRoundingProgress t ∧ p.2.im = 1 := by
  exact ⟨positiveGridRoundedDeformation_upper_progress i _ _ 1 t, by simp⟩

end OnLeConjecture.KnotTheory
