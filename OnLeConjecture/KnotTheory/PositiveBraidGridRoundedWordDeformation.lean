/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRoundedWordLift

/-! # Joining the two smooth word deformations

Smooth transition functions place a constant interval between depth lifting
and rounding. A finite sum makes the family globally smooth without a
piecewise seam. On the whole source interval it equals one of the two proved
embedded stages at every real deformation time.
-/

@[expose] public noncomputable section

open Set
open scoped Topology ContDiff

namespace OnLeConjecture.KnotTheory

/-- One globally smooth family from canonical generator depths to the rounded word. -/
def positiveRoundedWordDeformation {m : ℕ} (w : PositiveAdjacentWord m)
    (l u : Fin w.length → ℝ → ℝ) (k : Fin m) (s t : ℝ) : ℝ × ℂ :=
  positiveRoundedWordLift w k (Real.smoothTransition (3 * s)) t +
    positiveRoundedWord w l u k (Real.smoothTransition (3 * s - 2)) t -
      positiveRoundedWordLift w k 1 t

/-- Joint smoothness includes the interval joining the two stages. -/
theorem positiveRoundedWordDeformation_contDiff {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} (hl : ∀ j, ContDiff ℝ ∞ (l j))
    (hu : ∀ j, ContDiff ℝ ∞ (u j)) (k : Fin m) :
    ContDiff ℝ ∞ (fun st : ℝ × ℝ => positiveRoundedWordDeformation w l u k st.1 st.2) := by
  have hα : ContDiff ℝ ∞ (fun st : ℝ × ℝ => Real.smoothTransition (3 * st.1)) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_fst)
  have hβ : ContDiff ℝ ∞ (fun st : ℝ × ℝ => Real.smoothTransition (3 * st.1 - 2)) :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_fst).sub contDiff_const)
  exact (((positiveRoundedWordLift_contDiff w k).comp (hα.prodMk contDiff_snd)).add
    ((positiveRoundedWord_contDiff w hl hu k).comp (hβ.prodMk contDiff_snd))).sub
    ((positiveRoundedWordLift_contDiff w k).comp (contDiff_const.prodMk contDiff_snd))

/-- During the first part the joined formula is exactly the depth-lifting stage. -/
theorem positiveRoundedWordDeformation_first {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (k : Fin m) {s t : ℝ} (hs : s ≤ 2 / 3)
    (ht : t ∈ Icc 0 (2 * (w.length : ℝ) + 1)) :
    positiveRoundedWordDeformation w l u k s t =
      positiveRoundedWordLift w k (Real.smoothTransition (3 * s)) t := by
  rw [positiveRoundedWordDeformation,
    Real.smoothTransition.zero_of_nonpos (show 3 * s - 2 ≤ 0 by linarith),
    ← positiveRoundedWordLift_one w hl hu hU k ht]
  abel

/-- During the second part it is exactly the rounded-word stage. -/
theorem positiveRoundedWordDeformation_second {m : ℕ} (w : PositiveAdjacentWord m)
    (l u : Fin w.length → ℝ → ℝ) (k : Fin m) {s : ℝ} (hs : 1 / 3 ≤ s) (t : ℝ) :
    positiveRoundedWordDeformation w l u k s t =
      positiveRoundedWord w l u k (Real.smoothTransition (3 * s - 2)) t := by
  rw [positiveRoundedWordDeformation,
    Real.smoothTransition.one_of_one_le (show 1 ≤ 3 * s by linarith)]
  abel

/-- The initial endpoint is the canonical word with the same inserted connectors. -/
theorem positiveRoundedWordDeformation_zero {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (k : Fin m) {t : ℝ} (ht : t ∈ Icc 0 (2 * (w.length : ℝ) + 1)) :
    positiveRoundedWordDeformation w l u k 0 t = positiveRoundedWordLift w k 0 t := by
  simpa using positiveRoundedWordDeformation_first w hl hu hU k (s := 0) (by norm_num) ht

/-- The terminal endpoint is exactly the smooth rounded word. -/
theorem positiveRoundedWordDeformation_one {m : ℕ} (w : PositiveAdjacentWord m)
    (l u : Fin w.length → ℝ → ℝ) (k : Fin m) (t : ℝ) :
    positiveRoundedWordDeformation w l u k 1 t = positiveRoundedWord w l u k 1 t := by
  simpa only [mul_one, show (3 : ℝ) - 2 = 1 by norm_num, Real.smoothTransition.one] using
    positiveRoundedWordDeformation_second w l u k (s := 1) (by norm_num) t

private theorem subset_middle_unit {U : Set ℝ} (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8)) :
    U ⊆ Ioo (0 : ℝ) 1 := by
  intro t ht
  have hh := hU ht
  constructor <;> linarith [hh.1, hh.2]

/-- Every real time of the combined family is an injective tangle. -/
theorem positiveRoundedWordDeformation_injective {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla : ∀ j q, dist (l j q) (positiveGridRectilinearLowerRise q) < 1 / 8)
    (hua : ∀ j q, dist (u j q) (positiveGridRectilinearUpperDrop q) < 1 / 8)
    (s : ℝ) : Function.Injective
      (fun p : Fin m × Icc (0 : ℝ) (2 * (w.length : ℝ) + 1) =>
        positiveRoundedWordDeformation w l u p.1 s p.2) := by
  intro p q hpq
  change positiveRoundedWordDeformation w l u p.1 s p.2 =
    positiveRoundedWordDeformation w l u q.1 s q.2 at hpq
  by_cases hs : s ≤ 2 / 3
  · rw [positiveRoundedWordDeformation_first w hl hu (subset_middle_unit hU) p.1 hs p.2.property,
      positiveRoundedWordDeformation_first w hl hu
        (subset_middle_unit hU) q.1 hs q.2.property] at hpq
    exact positiveRoundedWordLift_injective w
      ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ hpq
  · have hs' : 1 / 3 ≤ s := by linarith
    rw [positiveRoundedWordDeformation_second w l u p.1 hs' p.2,
      positiveRoundedWordDeformation_second w l u q.1 hs' q.2] at hpq
    exact positiveRoundedWord_injective w hU hl hu hla hua
      ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ hpq

private theorem deriv_eq_of_eqOn_word {m : ℕ} (w : PositiveAdjacentWord m)
    {F G : ℝ → ℝ × ℂ} (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (he : EqOn F G (Icc (0 : ℝ) (2 * (w.length : ℝ) + 1))) {t : ℝ}
    (ht : t ∈ Icc 0 (2 * (w.length : ℝ) + 1)) : deriv F t = deriv G t := by
  have hd := (hG t).hasDerivAt.hasDerivWithinAt.congr_of_mem he ht
  have huniq := uniqueDiffOn_Icc (show (0 : ℝ) < 2 * (w.length : ℝ) + 1 by positivity) t ht
  exact ((hF t).hasDerivAt.hasDerivWithinAt.derivWithin huniq).symm.trans (hd.derivWithin huniq)

/-- Every strand has nonzero velocity at every real deformation time. -/
theorem positiveRoundedWordDeformation_deriv_ne_zero {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (hls : ∀ j, ContDiff ℝ ∞ (l j)) (hus : ∀ j, ContDiff ℝ ∞ (u j))
    (k : Fin m) (s : ℝ) {t : ℝ} (ht : t ∈ Icc 0 (2 * (w.length : ℝ) + 1)) :
    deriv (positiveRoundedWordDeformation w l u k s) t ≠ 0 := by
  have hF : Differentiable ℝ (positiveRoundedWordDeformation w l u k s) :=
    ((positiveRoundedWordDeformation_contDiff w hls hus k).comp
      (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  by_cases hs : s ≤ 2 / 3
  · have hG : Differentiable ℝ (positiveRoundedWordLift w k (Real.smoothTransition (3 * s))) :=
      ((positiveRoundedWordLift_contDiff w k).comp
        (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
    rw [deriv_eq_of_eqOn_word w hF hG
      (fun _ hv => positiveRoundedWordDeformation_first w hl hu hU k hs hv) ht]
    exact positiveRoundedWordLift_deriv_ne_zero w k _ t
  · have hs' : 1 / 3 ≤ s := by linarith
    have hG : Differentiable ℝ
        (positiveRoundedWord w l u k (Real.smoothTransition (3 * s - 2))) :=
      ((positiveRoundedWord_contDiff w hls hus k).comp
        (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
    rw [deriv_eq_of_eqOn_word w hF hG
      (fun v _ => positiveRoundedWordDeformation_second w l u k hs' v) ht]
    exact positiveRoundedWord_deriv_ne_zero w hl hu hU hls hus k _ ht

/-- The initial collar remains fixed in the complete family. -/
theorem positiveRoundedWordDeformation_initial_collar {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (k : Fin m) (s : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 3)) :
    positiveRoundedWordDeformation w l u k s t = (t, (k.val : ℂ)) := by
  rw [positiveRoundedWordDeformation, positiveRoundedWordLift_initial_collar w k _ ht,
    positiveRoundedWord_initial_collar w hl hu hU k _ ht,
    positiveRoundedWordLift_initial_collar w k 1 ht]
  abel

/-- The terminal collar retains the same permutation in the complete family. -/
theorem positiveRoundedWordDeformation_final_collar {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (k : Fin m) (s : ℝ) {t : ℝ}
    (ht : t ∈ Icc (2 * (w.length : ℝ) + 2 / 3) (2 * (w.length : ℝ) + 1)) :
    positiveRoundedWordDeformation w l u k s t = (t, ((w.permutation.symm k).val : ℂ)) := by
  rw [positiveRoundedWordDeformation, positiveRoundedWordLift_final_collar w k _ ht,
    positiveRoundedWord_final_collar w hl hu hU k _ ht,
    positiveRoundedWordLift_final_collar w k 1 ht]
  abel

/-- The rounded word reaches the two boundary planes only at the source endpoints. -/
theorem positiveRoundedWord_fst_slab {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla : ∀ j q, dist (l j q) (positiveGridRectilinearLowerRise q) < 1 / 8)
    (hua : ∀ j q, dist (u j q) (positiveGridRectilinearUpperDrop q) < 1 / 8)
    (k : Fin m) {s t : ℝ} (hs : s ∈ Icc 0 1)
    (ht : t ∈ Icc 0 (2 * (w.length : ℝ) + 1)) :
    (positiveRoundedWord w l u k s t).1 ∈ Icc 0 (2 * (w.length : ℝ) + 1) ∧
      ((positiveRoundedWord w l u k s t).1 = 0 ↔ t = 0) ∧
      ((positiveRoundedWord w l u k s t).1 = 2 * (w.length : ℝ) + 1 ↔
        t = 2 * (w.length : ℝ) + 1) := by
  obtain ⟨e, he⟩ := exists_positiveRectilinearWordPiece w ht
  rw [positiveRoundedWord_piece w hl hu (subset_middle_unit hU) k s e he]
  have hparam : t - (positiveRectilinearWordPieceAddress w e : ℝ) ∈ Icc 0 1 :=
    ⟨by linarith [he.1], by linarith [he.2]⟩
  have hb := positiveRoundedWordPiece_slab w hU hl hu hla hua hs e k hparam
  have hlo := Nat.cast_nonneg (α := ℝ) (positiveRectilinearWordPieceAddress w e)
  have hhi : (positiveRectilinearWordPieceAddress w e : ℝ) ≤ 2 * (w.length : ℝ) := by
    exact_mod_cast positiveRectilinearWordPieceAddress_le w e
  constructor
  · constructor <;> linarith [hb.1.1, hb.1.2]
  · constructor
    · constructor
      · intro h
        have hp := hb.2.1.mp (by linarith [hb.1.1])
        linarith [hb.1.1]
      · intro h
        have hp := hb.2.1.mpr (by linarith [he.1])
        linarith [he.1]
    · constructor
      · intro h
        have hp := hb.2.2.mp (by linarith [hb.1.2])
        linarith [hb.1.2]
      · intro h
        have hp := hb.2.2.mpr (by linarith [he.2])
        linarith [he.2]

/-- All times of the joined deformation have exactly the same boundary-plane property. -/
theorem positiveRoundedWordDeformation_fst_slab {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla : ∀ j q, dist (l j q) (positiveGridRectilinearLowerRise q) < 1 / 8)
    (hua : ∀ j q, dist (u j q) (positiveGridRectilinearUpperDrop q) < 1 / 8)
    (k : Fin m) (s : ℝ) {t : ℝ} (ht : t ∈ Icc 0 (2 * (w.length : ℝ) + 1)) :
    (positiveRoundedWordDeformation w l u k s t).1 ∈ Icc 0 (2 * (w.length : ℝ) + 1) ∧
      ((positiveRoundedWordDeformation w l u k s t).1 = 0 ↔ t = 0) ∧
      ((positiveRoundedWordDeformation w l u k s t).1 = 2 * (w.length : ℝ) + 1 ↔
        t = 2 * (w.length : ℝ) + 1) := by
  by_cases hs : s ≤ 2 / 3
  · rw [positiveRoundedWordDeformation_first w hl hu (subset_middle_unit hU) k hs ht]
    exact ⟨ht, Iff.rfl, Iff.rfl⟩
  · rw [positiveRoundedWordDeformation_second w l u k (by linarith : 1 / 3 ≤ s) t]
    exact positiveRoundedWord_fst_slab w hU hl hu hla hua k
      ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ ht

/-- The combined family consists of closed embeddings of the compact tangle. -/
theorem positiveRoundedWordDeformation_isClosedEmbedding {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla : ∀ j q, dist (l j q) (positiveGridRectilinearLowerRise q) < 1 / 8)
    (hua : ∀ j q, dist (u j q) (positiveGridRectilinearUpperDrop q) < 1 / 8)
    (hls : ∀ j, ContDiff ℝ ∞ (l j)) (hus : ∀ j, ContDiff ℝ ∞ (u j)) (s : ℝ) :
    Topology.IsClosedEmbedding
      (fun p : Fin m × Icc (0 : ℝ) (2 * (w.length : ℝ) + 1) =>
        positiveRoundedWordDeformation w l u p.1 s p.2) := by
  have hc : Continuous
      (fun p : Fin m × Icc (0 : ℝ) (2 * (w.length : ℝ) + 1) =>
        positiveRoundedWordDeformation w l u p.1 s p.2) := by
    apply continuous_prod_of_discrete_left.mpr
    intro k
    exact (positiveRoundedWordDeformation_contDiff w hls hus k).continuous.comp
      (continuous_const.prodMk continuous_subtype_val)
  exact hc.isClosedEmbedding (positiveRoundedWordDeformation_injective w hU hl hu hla hua s)

end OnLeConjecture.KnotTheory
