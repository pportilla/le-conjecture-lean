/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRoundedWord

/-! # Smooth lifting of the canonical word to constant crossing depths

The real coordinates follow the positive generators with the same inserted
connector intervals as the rounded word. Generator bump heights interpolate
to the already constructed smooth connector depths. Prefix labels and the
terminal word permutation are unchanged.
-/

@[expose] public noncomputable section

open Set OnLeConjecture.Analytic
open scoped Topology ContDiff BigOperators

namespace OnLeConjecture.KnotTheory

/-- Real height of the canonical word with the specified unit connector intervals. -/
def positiveRoundedWordCanonicalReal {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) : ℝ → ℝ :=
  finiteSmoothPathConcat (fun j : Fin (w.length + 1) =>
      (((positiveWordPrefix w j.val).symm k).val : ℝ))
    (fun j t => positiveAdjacentReal w[j.val] ((positiveWordPrefix w j.val).symm k) t)
    (fun j => 2 * (j.val : ℝ) + 1) (fun j => 2 * (j.val : ℝ) + 2)

/-- The sum of the disjointly supported imaginary generator bumps. -/
def positiveRoundedWordCanonicalImag {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (t : ℝ) : ℝ :=
  ∑ j : Fin w.length, positiveGridGeneratorImaginary w[j.val]
    ((positiveWordPrefix w j.val).symm k) (t - (2 * j.val + 1))

/-- The smooth depth-lifting stage, with the same connectors as the rounded word. -/
def positiveRoundedWordLift {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (s t : ℝ) : ℝ × ℂ :=
  (t, (positiveRoundedWordCanonicalReal w k t : ℂ) +
    (((1 - s) * positiveRoundedWordCanonicalImag w k t +
      s * positiveRoundedWordDepth w k t : ℝ) : ℂ) * Complex.I)

private theorem adjacentReal_start {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (j : Fin w.length) {t : ℝ} (ht : t ≤ 0) :
    positiveAdjacentReal w[j.val] ((positiveWordPrefix w j.val).symm k) t =
      (((positiveWordPrefix w j.castSucc.val).symm k).val : ℝ) := by
  simp [positiveAdjacentReal, Real.smoothTransition.zero_of_nonpos ht]

private theorem adjacentReal_end {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (j : Fin w.length) {t : ℝ} (ht : 1 ≤ t) :
    positiveAdjacentReal w[j.val] ((positiveWordPrefix w j.val).symm k) t =
      (((positiveWordPrefix w j.succ.val).symm k).val : ℝ) := by
  simp [positiveAdjacentReal, Real.smoothTransition.one_of_one_le ht,
    ← positiveWordPrefix_succ_symm w j.val j.isLt k]

private theorem generatorImaginary_outside {m : ℕ} (i : Fin (m - 1))
    (k : Fin m) {t : ℝ} (ht : t ≤ 0 ∨ 1 ≤ t) : positiveGridGeneratorImaginary i k t = 0 := by
  rcases ht with ht | ht
  · simp [positiveGridGeneratorImaginary, positiveGridGeneratorBump_of_nonpos ht]
  · simp [positiveGridGeneratorImaginary, positiveGridGeneratorBump_of_one_le ht]

theorem positiveRoundedWordCanonicalReal_contDiff {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) : ContDiff ℝ ∞ (positiveRoundedWordCanonicalReal w k) := by
  apply finiteSmoothPathConcat_contDiff
  intro j
  exact positiveAdjacentReal_contDiff _ _

theorem positiveRoundedWordCanonicalImag_contDiff {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) : ContDiff ℝ ∞ (positiveRoundedWordCanonicalImag w k) := by
  apply ContDiff.sum
  intro j _
  exact (positiveGridGeneratorImaginary_contDiff _ _).comp (contDiff_id.sub contDiff_const)

/-- Joint smoothness of the complete depth-lifting stage. -/
theorem positiveRoundedWordLift_contDiff {m : ℕ} (w : PositiveAdjacentWord m) (k : Fin m) :
    ContDiff ℝ ∞ (fun st : ℝ × ℝ => positiveRoundedWordLift w k st.1 st.2) := by
  apply ContDiff.prodMk contDiff_snd
  exact (Complex.ofRealCLM.contDiff.comp
    ((positiveRoundedWordCanonicalReal_contDiff w k).comp contDiff_snd)).add
    ((Complex.ofRealCLM.contDiff.comp
      (((contDiff_const.sub contDiff_fst).mul
        ((positiveRoundedWordCanonicalImag_contDiff w k).comp contDiff_snd)).add
        (contDiff_fst.mul ((positiveRoundedWordDepth_contDiff w k).comp contDiff_snd)))).mul
      contDiff_const)

/-- Canonical real heights are constant on each connector. -/
theorem positiveRoundedWordCanonicalReal_gap {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (j : Fin (w.length + 1)) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ)) (2 * (j.val : ℝ) + 1)) :
    positiveRoundedWordCanonicalReal w k t = (((positiveWordPrefix w j.val).symm k).val : ℝ) := by
  apply finiteSmoothPathConcat_cut _ _ _ _ (fun _ => by linarith)
    (fun q _ h => adjacentReal_start w k q h) (fun q _ h => adjacentReal_end w k q h) j
  · intro q hq
    have hh : (q.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hq
    linarith [ht.1]
  · intro q hq
    have hh : (j.val : ℝ) ≤ q.val := by exact_mod_cast hq
    linarith [ht.2]

/-- Canonical real heights are exactly the generator real heights on each letter. -/
theorem positiveRoundedWordCanonicalReal_letter {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (j : Fin w.length) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2)) :
    positiveRoundedWordCanonicalReal w k t = positiveAdjacentReal w[j.val]
      ((positiveWordPrefix w j.val).symm k) (t - (2 * j.val + 1)) := by
  have h := finiteSmoothPathConcat_stage
    (fun j : Fin (w.length + 1) => (((positiveWordPrefix w j.val).symm k).val : ℝ))
    (fun j t => positiveAdjacentReal w[j.val] ((positiveWordPrefix w j.val).symm k) t)
    (fun j => 2 * (j.val : ℝ) + 1) (fun j => 2 * (j.val : ℝ) + 2)
    (fun _ => by linarith) (fun j q hjq => by
      have hh : (j.val : ℝ) + 1 ≤ q.val := by exact_mod_cast hjq
      linarith)
    (fun q _ h => adjacentReal_start w k q h) (fun q _ h => adjacentReal_end w k q h) j ht
  have hd : 2 * (j.val : ℝ) + 2 - (2 * (j.val : ℝ) + 1) = 1 := by ring
  simpa only [positiveRoundedWordCanonicalReal, hd, div_one] using h

/-- Every bump vanishes on a connector interval. -/
theorem positiveRoundedWordCanonicalImag_gap {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (j : Fin (w.length + 1)) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ)) (2 * (j.val : ℝ) + 1)) :
    positiveRoundedWordCanonicalImag w k t = 0 := by
  apply Finset.sum_eq_zero
  intro q _
  apply generatorImaginary_outside
  by_cases hq : q.val < j.val
  · right
    have hh : (q.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hq
    linarith [ht.1]
  · left
    have hh : (j.val : ℝ) ≤ q.val := by exact_mod_cast (show j.val ≤ q.val by omega)
    linarith [ht.2]

/-- Only the active letter contributes its bump. -/
theorem positiveRoundedWordCanonicalImag_letter {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (j : Fin w.length) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2)) :
    positiveRoundedWordCanonicalImag w k t = positiveGridGeneratorImaginary w[j.val]
      ((positiveWordPrefix w j.val).symm k) (t - (2 * j.val + 1)) := by
  apply Finset.sum_eq_single j
  · intro q _ hq
    apply generatorImaginary_outside
    rcases lt_or_gt_of_ne hq with hq | hq
    · right
      have hh : (q.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hq
      linarith [ht.1]
    · left
      have hh : (j.val : ℝ) + 1 ≤ q.val := by exact_mod_cast hq
      linarith [ht.2]
  · simp

/-- Exact connector formula, with its depth scaled by the lifting parameter. -/
theorem positiveRoundedWordLift_gap {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (s : ℝ) (j : Fin (w.length + 1)) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ)) (2 * (j.val : ℝ) + 1)) :
    positiveRoundedWordLift w k s t =
      (t, (((positiveWordPrefix w j.val).symm k).val : ℂ) +
        (s * positiveRoundedWordDepthPath w k j (t - 2 * j.val) : ℂ) * Complex.I) := by
  rw [positiveRoundedWordLift, positiveRoundedWordCanonicalReal_gap w k j ht,
    positiveRoundedWordCanonicalImag_gap w k j ht, positiveRoundedWordDepth_gap w k j ht]
  simp

/-- Exact local generator lifting formula, with unchanged prefix labels. -/
theorem positiveRoundedWordLift_letter {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (s : ℝ) (j : Fin w.length) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2)) :
    positiveRoundedWordLift w k s t =
      let p := positiveGridDepthLift w[j.val] ((positiveWordPrefix w j.val).symm k) s
        (t - (2 * j.val + 1))
      (2 * (j.val : ℝ) + 1 + p.1, p.2) := by
  rw [positiveRoundedWordLift, positiveRoundedWordCanonicalReal_letter w k j ht,
    positiveRoundedWordCanonicalImag_letter w k j ht, positiveRoundedWordDepth_letter w k j ht]
  simp only [positiveGridDepthLift, positiveGridGeneratorDeformation, positiveRectilinearWordDepth]
  apply Prod.ext
  · simp only
    ring
  · push_cast
    ring

/-- At time zero each letter is the exact canonical positive generator. -/
theorem positiveRoundedWordLift_zero_letter {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (j : Fin w.length) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2)) :
    positiveRoundedWordLift w k 0 t =
      (t, positiveGridGenerator w[j.val] ((positiveWordPrefix w j.val).symm k)
        (t - (2 * j.val + 1))) := by
  rw [positiveRoundedWordLift_letter w k 0 j ht, positiveGridDepthLift_zero]
  apply Prod.ext
  · simp only
    ring
  · rfl

/-- The two smooth stages meet exactly, including every join. -/
theorem positiveRoundedWordLift_one {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (k : Fin m) {t : ℝ} (ht : t ∈ Icc 0 (2 * (w.length : ℝ) + 1)) :
    positiveRoundedWordLift w k 1 t = positiveRoundedWord w l u k 0 t := by
  obtain ⟨e, he⟩ := exists_positiveRectilinearWordPiece w ht
  rcases e with j | j
  · have ht' : t ∈ Icc (2 * (j.val : ℝ)) (2 * (j.val : ℝ) + 1) := by
      simpa only [positiveRectilinearWordPieceAddress, Nat.cast_mul, Nat.cast_ofNat] using he
    rw [positiveRoundedWordLift_gap w k 1 j ht', positiveRoundedWord_gap w hl hu hU k 0 j ht']
    simp
  · have ht' : t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2) := by
      simpa only [positiveRectilinearWordPieceAddress, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_one, add_assoc, one_add_one_eq_two] using he
    rw [positiveRoundedWordLift_letter w k 1 j ht',
      positiveRoundedWord_letter w hl hu hU k 0 j ht', positiveGridRoundedDeformation_zero,
      positiveGridDepthLift_one, positiveGridRectilinearDeformation_zero]

/-- Each depth-lifting slice is injective on the whole word tangle. -/
theorem positiveRoundedWordLift_injective {m : ℕ} (w : PositiveAdjacentWord m)
    {s : ℝ} (hs : s ∈ Icc 0 1) :
    Function.Injective (fun p : Fin m × Icc (0 : ℝ) (2 * (w.length : ℝ) + 1) =>
      positiveRoundedWordLift w p.1 s p.2) := by
  rintro ⟨k, ⟨t, ht⟩⟩ ⟨k', ⟨v, hv⟩⟩ he
  have htv : t = v := congrArg Prod.fst he
  subst v
  suffices k = k' by subst k'; rfl
  change positiveRoundedWordLift w k s t = positiveRoundedWordLift w k' s t at he
  obtain ⟨e, he'⟩ := exists_positiveRectilinearWordPiece w ht
  rcases e with j | j
  · have ht' : t ∈ Icc (2 * (j.val : ℝ)) (2 * (j.val : ℝ) + 1) := by
      simpa only [positiveRectilinearWordPieceAddress, Nat.cast_mul, Nat.cast_ofNat] using he'
    rw [positiveRoundedWordLift_gap w k s j ht', positiveRoundedWordLift_gap w k' s j ht'] at he
    have hr := congrArg (fun p : ℝ × ℂ => p.2.re) he
    simp only [Complex.add_re, Complex.natCast_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.I_re, Complex.mul_im,
      zero_mul, add_zero, Complex.I_im, mul_one, sub_self] at hr
    exact (positiveWordPrefix w j.val).symm.injective (Fin.ext (Nat.cast_injective hr))
  · have ht' : t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2) := by
      simpa only [positiveRectilinearWordPieceAddress, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_one, add_assoc, one_add_one_eq_two] using he'
    rw [positiveRoundedWordLift_letter w k s j ht',
      positiveRoundedWordLift_letter w k' s j ht'] at he
    have hy := congrArg (fun p : ℝ × ℂ => p.2) he
    have hh : positiveGridDepthLift w[j.val] ((positiveWordPrefix w j.val).symm k) s
        (t - (2 * j.val + 1)) =
      positiveGridDepthLift w[j.val] ((positiveWordPrefix w j.val).symm k') s
        (t - (2 * j.val + 1)) := by
      apply Prod.ext
      · rfl
      · exact hy
    have hp := positiveGridDepthLift_injective w[j.val] hs
      (a₁ := ((positiveWordPrefix w j.val).symm k, t - (2 * j.val + 1)))
      (a₂ := ((positiveWordPrefix w j.val).symm k', t - (2 * j.val + 1))) hh
    exact (positiveWordPrefix w j.val).symm.injective (congrArg Prod.fst hp)

/-- The horizontal coordinate itself has derivative one, so velocity never vanishes. -/
theorem positiveRoundedWordLift_deriv_ne_zero {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (s t : ℝ) : deriv (positiveRoundedWordLift w k s) t ≠ 0 := by
  have hf : Differentiable ℝ (positiveRoundedWordLift w k s) :=
    ((positiveRoundedWordLift_contDiff w k).comp
      (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hx := (ContinuousLinearMap.fst ℝ ℝ ℂ).hasFDerivAt.comp_hasDerivAt t (hf t).hasDerivAt
  have he := hx.unique (hasDerivAt_id t)
  intro hz
  simp [hz] at he

/-- The depth-lifting stage consists of closed embeddings of the whole compact tangle. -/
theorem positiveRoundedWordLift_isClosedEmbedding {m : ℕ} (w : PositiveAdjacentWord m)
    {s : ℝ} (hs : s ∈ Icc 0 1) :
    Topology.IsClosedEmbedding (fun p : Fin m × Icc (0 : ℝ) (2 * (w.length : ℝ) + 1) =>
      positiveRoundedWordLift w p.1 s p.2) := by
  have hc : Continuous (fun p : Fin m × Icc (0 : ℝ) (2 * (w.length : ℝ) + 1) =>
      positiveRoundedWordLift w p.1 s p.2) := by
    apply continuous_prod_of_discrete_left.mpr
    intro k
    exact (positiveRoundedWordLift_contDiff w k).continuous.comp
      (continuous_const.prodMk continuous_subtype_val)
  exact hc.isClosedEmbedding (positiveRoundedWordLift_injective w hs)

/-- The initial collar is fixed throughout the depth-lifting stage. -/
theorem positiveRoundedWordLift_initial_collar {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (s : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 3)) :
    positiveRoundedWordLift w k s t = (t, (k.val : ℂ)) := by
  have hg := positiveRoundedWordLift_gap w k s 0
    (show t ∈ Icc (2 * ((0 : Fin (w.length + 1)).val : ℝ))
      (2 * ((0 : Fin (w.length + 1)).val : ℝ) + 1) from
        ⟨by simpa using ht.1, by simpa using (show t ≤ 1 by linarith [ht.2])⟩)
  rw [hg]
  simp [positiveRoundedWordDepthPath, positiveRoundedWordDepthNode,
    Real.smoothTransition.zero_of_nonpos (show 3 * t - 1 ≤ 0 by linarith [ht.2])]
  rfl

/-- The terminal collar retains exactly the word permutation throughout the stage. -/
theorem positiveRoundedWordLift_final_collar {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (s : ℝ) {t : ℝ}
    (ht : t ∈ Icc (2 * (w.length : ℝ) + 2 / 3) (2 * (w.length : ℝ) + 1)) :
    positiveRoundedWordLift w k s t = (t, ((w.permutation.symm k).val : ℂ)) := by
  have hg := positiveRoundedWordLift_gap w k s (Fin.last w.length)
    (show t ∈ Icc (2 * (w.length : ℝ)) (2 * (w.length : ℝ) + 1) from
      ⟨by linarith [ht.1], ht.2⟩)
  rw [hg]
  have hn : positiveRoundedWordDepthNode w k (Fin.last (w.length + 1)) = 0 := by
    change positiveRectilinearWordGapFinal w (Fin.last w.length) k = 0
    simp
  simp [positiveRoundedWordDepthPath, hn,
    Real.smoothTransition.one_of_one_le
      (show 1 ≤ 3 * (t - 2 * (w.length : ℝ)) - 1 by linarith [ht.1])]

end OnLeConjecture.KnotTheory
