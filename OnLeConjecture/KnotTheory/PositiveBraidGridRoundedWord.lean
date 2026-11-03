/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRectilinearRoundingSlab
public import OnLeConjecture.Analytic.PlaneBranchBraidPathConcatenation
public import OnLeConjecture.KnotTheory.PositiveBraidGridRectilinearWordEmbedding

/-! # Smooth joining of the rounded word letters

Subtracting the straight horizontal coordinate makes each letter correction
constant before and after its interval. The real ranks and the connector depths
are then joined by two finite telescoping sums. No clipping operation is used
in this smooth construction.
-/

@[expose] public noncomputable section

open Set OnLeConjecture.Analytic
open scoped Topology ContDiff BigOperators

namespace OnLeConjecture.KnotTheory

/-- Depths before and after the connector intervals, with zero at both ends. -/
def positiveRoundedWordDepthNode {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) : Fin (w.length + 2) → ℝ :=
  Fin.cases 0 (fun j => positiveRectilinearWordGapFinal w j k)

@[simp] theorem positiveRoundedWordDepthNode_succ {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (j : Fin (w.length + 1)) :
    positiveRoundedWordDepthNode w k j.succ = positiveRectilinearWordGapFinal w j k := rfl

@[simp] theorem positiveRoundedWordDepthNode_castSucc {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (j : Fin (w.length + 1)) :
    positiveRoundedWordDepthNode w k j.castSucc = positiveRectilinearWordGapInitial w j k := by
  induction j using Fin.cases with
  | zero => rfl
  | succ j =>
    change positiveRectilinearWordGapFinal w j.castSucc k = positiveRectilinearWordDepth w j k
    exact positiveRectilinearWordGapFinal_castSucc w j k

/-- Smooth interpolation between two consecutive connector depths. -/
def positiveRoundedWordDepthPath {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (j : Fin (w.length + 1)) (t : ℝ) : ℝ :=
  (1 - Real.smoothTransition (3 * t - 1)) * positiveRoundedWordDepthNode w k j.castSucc +
    Real.smoothTransition (3 * t - 1) * positiveRoundedWordDepthNode w k j.succ

/-- The connector depth along the entire word. -/
def positiveRoundedWordDepth {m : ℕ} (w : PositiveAdjacentWord m) (k : Fin m) : ℝ → ℝ :=
  finiteSmoothPathConcat (positiveRoundedWordDepthNode w k) (positiveRoundedWordDepthPath w k)
    (fun j => 2 * (j.val : ℝ)) (fun j => 2 * (j.val : ℝ) + 1)

theorem positiveRoundedWordDepthPath_start {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (j : Fin (w.length + 1)) {t : ℝ} (ht : t ≤ 0) :
    positiveRoundedWordDepthPath w k j t = positiveRoundedWordDepthNode w k j.castSucc := by
  simp [positiveRoundedWordDepthPath,
    Real.smoothTransition.zero_of_nonpos (show 3 * t - 1 ≤ 0 by linarith)]

theorem positiveRoundedWordDepthPath_end {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (j : Fin (w.length + 1)) {t : ℝ} (ht : 1 ≤ t) :
    positiveRoundedWordDepthPath w k j t = positiveRoundedWordDepthNode w k j.succ := by
  simp [positiveRoundedWordDepthPath,
    Real.smoothTransition.one_of_one_le (show 1 ≤ 3 * t - 1 by linarith)]

theorem positiveRoundedWordDepth_contDiff {m : ℕ} (w : PositiveAdjacentWord m) (k : Fin m) :
    ContDiff ℝ ∞ (positiveRoundedWordDepth w k) := by
  apply finiteSmoothPathConcat_contDiff
  intro j
  have hs : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition (3 * t - 1)) :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  exact ((contDiff_const.sub hs).mul contDiff_const).add (hs.mul contDiff_const)

/-- The planar rank configurations at the letter cuts. -/
def positiveRoundedWordRankNode {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (j : Fin (w.length + 1)) : ℝ × ℂ :=
  (0, (((positiveWordPrefix w j.val).symm k).val : ℂ))

/-- A letter with its straight horizontal coordinate and constant depth removed. -/
def positiveRoundedWordLetterCorrection {m : ℕ} (w : PositiveAdjacentWord m)
    (l u : Fin w.length → ℝ → ℝ) (k : Fin m) (s : ℝ) (j : Fin w.length) (t : ℝ) : ℝ × ℂ :=
  positiveGridRoundedDeformation w[j.val] (l j) (u j)
    ((positiveWordPrefix w j.val).symm k) s t -
      (t, (positiveRectilinearWordDepth w j k : ℂ) * Complex.I)

/-- The smooth joined word, with smooth connector depths and the original prefix labels. -/
def positiveRoundedWord {m : ℕ} (w : PositiveAdjacentWord m)
    (l u : Fin w.length → ℝ → ℝ) (k : Fin m) (s t : ℝ) : ℝ × ℂ :=
  (t, (positiveRoundedWordDepth w k t : ℂ) * Complex.I) +
    finiteSmoothPathConcat (positiveRoundedWordRankNode w k)
      (positiveRoundedWordLetterCorrection w l u k s)
      (fun j => 2 * (j.val : ℝ) + 1) (fun j => 2 * (j.val : ℝ) + 2) t

/-- Joint smoothness follows directly from the finite-sum formula. -/
theorem positiveRoundedWord_contDiff {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} (hl : ∀ j, ContDiff ℝ ∞ (l j))
    (hu : ∀ j, ContDiff ℝ ∞ (u j)) (k : Fin m) :
    ContDiff ℝ ∞ (fun st : ℝ × ℝ => positiveRoundedWord w l u k st.1 st.2) := by
  unfold positiveRoundedWord finiteSmoothPathConcat
  apply ContDiff.add
  · exact contDiff_snd.prodMk
      ((Complex.ofRealCLM.contDiff.comp
        ((positiveRoundedWordDepth_contDiff w k).comp contDiff_snd)).mul contDiff_const)
  · apply contDiff_const.add
    apply ContDiff.sum
    intro j _
    apply ContDiff.sub _ contDiff_const
    unfold positiveRoundedWordLetterCorrection
    have ht : ContDiff ℝ ∞ (fun st : ℝ × ℝ =>
        (st.2 - (2 * (j.val : ℝ) + 1)) / ((2 * (j.val : ℝ) + 2) -
          (2 * (j.val : ℝ) + 1))) := (contDiff_snd.sub contDiff_const).div_const _
    exact ((positiveGridRoundedDeformation_contDiff w[j.val] (hl j) (hu j)
      ((positiveWordPrefix w j.val).symm k)).comp (contDiff_fst.prodMk ht)).sub
        (ht.prodMk contDiff_const)

/-- The connector formula agrees exactly with its local interpolation. -/
theorem positiveRoundedWordDepth_gap {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (j : Fin (w.length + 1)) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ)) (2 * (j.val : ℝ) + 1)) :
    positiveRoundedWordDepth w k t = positiveRoundedWordDepthPath w k j (t - 2 * j.val) := by
  have h := finiteSmoothPathConcat_stage (positiveRoundedWordDepthNode w k)
    (positiveRoundedWordDepthPath w k) (fun j => 2 * (j.val : ℝ))
    (fun j => 2 * (j.val : ℝ) + 1) (fun _ => by linarith)
    (fun j k hjk => by
      have hh : (j.val : ℝ) + 1 ≤ k.val := by exact_mod_cast hjk
      linarith)
    (fun j _ h => positiveRoundedWordDepthPath_start w k j h)
    (fun j _ h => positiveRoundedWordDepthPath_end w k j h) j ht
  simpa only [add_sub_cancel_left, div_one, positiveRoundedWordDepth] using h

/-- Throughout a letter interval, the depth is the prescribed constant gadget depth. -/
theorem positiveRoundedWordDepth_letter {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (j : Fin w.length) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2)) :
    positiveRoundedWordDepth w k t = positiveRectilinearWordDepth w j k := by
  have h := finiteSmoothPathConcat_cut (positiveRoundedWordDepthNode w k)
    (positiveRoundedWordDepthPath w k) (fun j => 2 * (j.val : ℝ))
    (fun j => 2 * (j.val : ℝ) + 1) (fun _ => by linarith)
    (fun j _ h => positiveRoundedWordDepthPath_start w k j h)
    (fun j _ h => positiveRoundedWordDepthPath_end w k j h) j.castSucc.succ (t := t)
    (fun q hq => by
      have hh : (q.val : ℝ) ≤ j.val := by exact_mod_cast (show q.val ≤ j.val by simpa using hq)
      linarith [ht.1])
    (fun q hq => by
      have hh : (j.val : ℝ) + 1 ≤ q.val := by exact_mod_cast hq
      linarith [ht.2])
  simpa only [positiveRoundedWordDepthNode_succ, positiveRectilinearWordGapFinal_castSucc,
    positiveRoundedWordDepth] using h

/-- Before its interval the correction is precisely the initial rank configuration. -/
theorem positiveRoundedWordLetterCorrection_start {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (k : Fin m) (s : ℝ) (j : Fin w.length) {t : ℝ} (ht : t ≤ 0) :
    positiveRoundedWordLetterCorrection w l u k s j t =
      positiveRoundedWordRankNode w k j.castSucc := by
  rw [positiveRoundedWordLetterCorrection,
    positiveGridRoundedDeformation_outside w[j.val] (hl j) (hu j) hU _ s (Or.inl ht),
    positiveAdjacentHeight_of_nonpos _ _ _ ht]
  simp [positiveAdjacentHeight, positiveAdjacentReal, positiveRectilinearWordDepth,
    positiveRoundedWordRankNode]

/-- After its interval the correction is precisely the next prefix rank configuration. -/
theorem positiveRoundedWordLetterCorrection_end {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (k : Fin m) (s : ℝ) (j : Fin w.length) {t : ℝ} (ht : 1 ≤ t) :
    positiveRoundedWordLetterCorrection w l u k s j t =
      positiveRoundedWordRankNode w k j.succ := by
  rw [positiveRoundedWordLetterCorrection,
    positiveGridRoundedDeformation_outside w[j.val] (hl j) (hu j) hU _ s (Or.inr ht),
    positiveAdjacentHeight_of_one_le _ _ _ ht]
  simp [positiveAdjacentHeight, positiveAdjacentReal, positiveRectilinearWordDepth,
    positiveRoundedWordRankNode, ← positiveWordPrefix_succ_symm w j.val j.isLt k]

/-- On a connector interval, the joined word has fixed rank and precisely its smooth depth. -/
theorem positiveRoundedWord_gap {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (k : Fin m) (s : ℝ) (j : Fin (w.length + 1)) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ)) (2 * (j.val : ℝ) + 1)) :
    positiveRoundedWord w l u k s t =
      (t, (((positiveWordPrefix w j.val).symm k).val : ℂ) +
        (positiveRoundedWordDepthPath w k j (t - 2 * j.val) : ℂ) * Complex.I) := by
  have h := finiteSmoothPathConcat_cut (positiveRoundedWordRankNode w k)
    (positiveRoundedWordLetterCorrection w l u k s)
    (fun j => 2 * (j.val : ℝ) + 1) (fun j => 2 * (j.val : ℝ) + 2)
    (fun _ => by linarith)
    (fun j _ ht => positiveRoundedWordLetterCorrection_start w hl hu hU k s j ht)
    (fun j _ ht => positiveRoundedWordLetterCorrection_end w hl hu hU k s j ht) j (t := t)
    (fun q hq => by
      have hh : (q.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hq
      linarith [ht.1])
    (fun q hq => by
      have hh : (j.val : ℝ) ≤ q.val := by exact_mod_cast hq
      linarith [ht.2])
  rw [positiveRoundedWord, h, positiveRoundedWordDepth_gap w k j ht]
  ext <;> simp [positiveRoundedWordRankNode, add_comm]

/-- On a letter interval the joined word is exactly the translated rounded crossing. -/
theorem positiveRoundedWord_letter {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (k : Fin m) (s : ℝ) (j : Fin w.length) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2)) :
    positiveRoundedWord w l u k s t =
      let p := positiveGridRoundedDeformation w[j.val] (l j) (u j)
        ((positiveWordPrefix w j.val).symm k) s (t - (2 * j.val + 1))
      (2 * (j.val : ℝ) + 1 + p.1, p.2) := by
  have h := finiteSmoothPathConcat_stage (positiveRoundedWordRankNode w k)
    (positiveRoundedWordLetterCorrection w l u k s)
    (fun j => 2 * (j.val : ℝ) + 1) (fun j => 2 * (j.val : ℝ) + 2)
    (fun _ => by linarith)
    (fun j q hjq => by
      have hh : (j.val : ℝ) + 1 ≤ q.val := by exact_mod_cast hjq
      linarith)
    (fun j _ ht => positiveRoundedWordLetterCorrection_start w hl hu hU k s j ht)
    (fun j _ ht => positiveRoundedWordLetterCorrection_end w hl hu hU k s j ht) j ht
  have hden : 2 * (j.val : ℝ) + 2 - (2 * (j.val : ℝ) + 1) = 1 := by ring
  rw [hden, div_one] at h
  rw [positiveRoundedWord, h, positiveRoundedWordDepth_letter w k j ht]
  simp only [positiveRoundedWordLetterCorrection, Prod.add_def, Prod.sub_def]
  apply Prod.ext
  · simp only
    ring
  · simp only
    abel

/-- The local pieces in their alternating connector and letter order. -/
def positiveRoundedWordPiece {m : ℕ} (w : PositiveAdjacentWord m)
    (l u : Fin w.length → ℝ → ℝ) (s : ℝ)
    (e : PositiveRectilinearWordPieceIndex w) (k : Fin m) (t : ℝ) : ℝ × ℂ :=
  match e with
  | Sum.inl j => (2 * j.val + t, (((positiveWordPrefix w j.val).symm k).val : ℂ) +
      (positiveRoundedWordDepthPath w k j t : ℂ) * Complex.I)
  | Sum.inr j =>
      let p := positiveGridRoundedDeformation w[j.val] (l j) (u j)
        ((positiveWordPrefix w j.val).symm k) s t
      (2 * j.val + 1 + p.1, p.2)

/-- Every unit slab of the global formula agrees with its specified local piece. -/
theorem positiveRoundedWord_piece {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (k : Fin m) (s : ℝ) (e : PositiveRectilinearWordPieceIndex w) {t : ℝ}
    (ht : t ∈ Icc (positiveRectilinearWordPieceAddress w e : ℝ)
      ((positiveRectilinearWordPieceAddress w e : ℝ) + 1)) :
    positiveRoundedWord w l u k s t =
      positiveRoundedWordPiece w l u s e k (t - positiveRectilinearWordPieceAddress w e) := by
  rcases e with j | j
  · have ht' : t ∈ Icc (2 * (j.val : ℝ)) (2 * (j.val : ℝ) + 1) := by
      simpa only [positiveRectilinearWordPieceAddress, Nat.cast_mul, Nat.cast_ofNat] using ht
    rw [positiveRoundedWord_gap w hl hu hU k s j ht']
    simp [positiveRoundedWordPiece, positiveRectilinearWordPieceAddress]
  · have ht' : t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2) := by
      simpa only [positiveRectilinearWordPieceAddress, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_one, add_assoc, one_add_one_eq_two] using ht
    simpa [positiveRoundedWordPiece, positiveRectilinearWordPieceAddress] using
      positiveRoundedWord_letter w hl hu hU k s j ht'

/-- Every local smooth piece is injective on all labels and real parameters. -/
theorem positiveRoundedWordPiece_injective {m : ℕ} (w : PositiveAdjacentWord m)
    (l u : Fin w.length → ℝ → ℝ) (s : ℝ) (e : PositiveRectilinearWordPieceIndex w) :
    Function.Injective (fun p : Fin m × ℝ => positiveRoundedWordPiece w l u s e p.1 p.2) := by
  rintro ⟨k, t⟩ ⟨k', t'⟩ he
  rcases e with j | j
  · have hx := congrArg Prod.fst he
    have hr := congrArg (fun p : ℝ × ℂ => p.2.re) he
    simp only [positiveRoundedWordPiece, Complex.add_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.natCast_re] at hr
    have hk : k = k' := (positiveWordPrefix w j.val).symm.injective
      (Fin.ext (Nat.cast_injective hr))
    have ht : t = t' := by change 2 * (j.val : ℝ) + t = 2 * (j.val : ℝ) + t' at hx; linarith
    exact Prod.ext hk ht
  · have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    have hf : positiveGridRoundedDeformation w[j.val] (l j) (u j)
        ((positiveWordPrefix w j.val).symm k) s t =
      positiveGridRoundedDeformation w[j.val] (l j) (u j)
        ((positiveWordPrefix w j.val).symm k') s t' :=
      Prod.ext (add_left_cancel hx) hy
    have hp := positiveGridRoundedDeformation_injective w[j.val] (l j) (u j) s
      (a₁ := ((positiveWordPrefix w j.val).symm k, t))
      (a₂ := ((positiveWordPrefix w j.val).symm k', t')) hf
    have hk : (positiveWordPrefix w j.val).symm k = (positiveWordPrefix w j.val).symm k' :=
      congrArg (fun p : Fin m × ℝ => p.1) hp
    have ht : t = t' := congrArg (fun p : Fin m × ℝ => p.2) hp
    exact Prod.ext ((positiveWordPrefix w j.val).symm.injective hk) ht

/-- Every local piece stays in its own unit slab and meets its boundary only at its endpoints. -/
theorem positiveRoundedWordPiece_slab {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla : ∀ j q, dist (l j q) (positiveGridRectilinearLowerRise q) < 1 / 8)
    (hua : ∀ j q, dist (u j q) (positiveGridRectilinearUpperDrop q) < 1 / 8)
    {s : ℝ} (hs : s ∈ Icc 0 1) (e : PositiveRectilinearWordPieceIndex w)
    (k : Fin m) {t : ℝ} (ht : t ∈ Icc 0 1) :
    (positiveRoundedWordPiece w l u s e k t).1 ∈
      Icc (positiveRectilinearWordPieceAddress w e : ℝ)
        ((positiveRectilinearWordPieceAddress w e : ℝ) + 1) ∧
      ((positiveRoundedWordPiece w l u s e k t).1 =
        (positiveRectilinearWordPieceAddress w e : ℝ) ↔ t = 0) ∧
      ((positiveRoundedWordPiece w l u s e k t).1 =
        (positiveRectilinearWordPieceAddress w e : ℝ) + 1 ↔ t = 1) := by
  rcases e with j | j
  · simp only [positiveRoundedWordPiece, positiveRectilinearWordPieceAddress,
      Nat.cast_mul, Nat.cast_ofNat]
    refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_, ?_⟩
    all_goals constructor <;> intro h <;> linarith
  · have hb := positiveGridRoundedDeformation_slab w[j.val] hU (hl j) (hu j) (hla j) (hua j)
      ((positiveWordPrefix w j.val).symm k) hs ht
    simp only [positiveRoundedWordPiece, positiveRectilinearWordPieceAddress,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    refine ⟨⟨by linarith [hb.1.1], by linarith [hb.1.2]⟩, ?_, ?_⟩
    · constructor
      · intro h
        exact hb.2.1.mp (by linarith)
      · intro h
        rw [hb.2.1.mpr h]
        ring
    · constructor
      · intro h
        exact hb.2.2.mp (by linarith)
      · intro h
        rw [hb.2.2.mpr h]

/-- The entire smooth joined word is injective throughout the rounding deformation. -/
theorem positiveRoundedWord_injective {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla : ∀ j q, dist (l j q) (positiveGridRectilinearLowerRise q) < 1 / 8)
    (hua : ∀ j q, dist (u j q) (positiveGridRectilinearUpperDrop q) < 1 / 8)
    {s : ℝ} (hs : s ∈ Icc 0 1) :
    Function.Injective (fun p : Fin m × Icc (0 : ℝ) (2 * (w.length : ℝ) + 1) =>
      positiveRoundedWord w l u p.1 s p.2) := by
  have hU' : U ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    have hh := hU ht
    constructor <;> linarith [hh.1, hh.2]
  have hI := positiveRoundedWordPiece_injective w l u s
  have hB := positiveRoundedWordPiece_slab w hU hl hu hla hua hs
  rintro ⟨k, ⟨t, ht⟩⟩ ⟨k', ⟨v, hv⟩⟩ he
  change positiveRoundedWord w l u k s t = positiveRoundedWord w l u k' s v at he
  have hglobal := he
  obtain ⟨e, het⟩ := exists_positiveRectilinearWordPiece w ht
  obtain ⟨f, hfu⟩ := exists_positiveRectilinearWordPiece w hv
  have htu : t - (positiveRectilinearWordPieceAddress w e : ℝ) ∈ Icc 0 1 :=
    ⟨by linarith [het.1], by linarith [het.2]⟩
  have huu : v - (positiveRectilinearWordPieceAddress w f : ℝ) ∈ Icc 0 1 :=
    ⟨by linarith [hfu.1], by linarith [hfu.2]⟩
  rw [positiveRoundedWord_piece w hl hu hU' k s e het,
    positiveRoundedWord_piece w hl hu hU' k' s f hfu] at he
  have hbe := hB e k htu
  have hbf := hB f k' huu
  have hx := congrArg Prod.fst he
  have htime : t = v := by
    rcases lt_trichotomy (positiveRectilinearWordPieceAddress w e)
        (positiveRectilinearWordPieceAddress w f) with h | h | h
    · have hgap : (positiveRectilinearWordPieceAddress w e : ℝ) + 1 ≤
          (positiveRectilinearWordPieceAddress w f : ℝ) := by exact_mod_cast h
      have htend := hbe.2.2.mp (by linarith [hbe.1.2, hbf.1.1])
      have hustart := hbf.2.1.mp (by linarith [hbe.1.2, hbf.1.1])
      linarith [hbe.1.2, hbf.1.1]
    · have hef := positiveRectilinearWordPieceAddress_injective w h
      subst f
      have hp := hI e
        (a₁ := (k, t - (positiveRectilinearWordPieceAddress w e : ℝ)))
        (a₂ := (k', v - (positiveRectilinearWordPieceAddress w e : ℝ))) he
      have hp' := congrArg Prod.snd hp
      dsimp only at hp'
      linarith
    · have hgap : (positiveRectilinearWordPieceAddress w f : ℝ) + 1 ≤
          (positiveRectilinearWordPieceAddress w e : ℝ) := by exact_mod_cast h
      have hustart := hbe.2.1.mp (by linarith [hbf.1.2, hbe.1.1])
      have htend := hbf.2.2.mp (by linarith [hbf.1.2, hbe.1.1])
      linarith [hbf.1.2, hbe.1.1]
  subst v
  rw [positiveRoundedWord_piece w hl hu hU' k s e het,
    positiveRoundedWord_piece w hl hu hU' k' s e het] at hglobal
  have hk : k = k' := congrArg Prod.fst (hI e
    (a₁ := (k, t - (positiveRectilinearWordPieceAddress w e : ℝ)))
    (a₂ := (k', t - (positiveRectilinearWordPieceAddress w e : ℝ))) hglobal)
  subst k'
  rfl

/-- Smooth local replacements produce a closed embedding of the whole compact tangle. -/
theorem positiveRoundedWord_isClosedEmbedding {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla : ∀ j q, dist (l j q) (positiveGridRectilinearLowerRise q) < 1 / 8)
    (hua : ∀ j q, dist (u j q) (positiveGridRectilinearUpperDrop q) < 1 / 8)
    (hls : ∀ j, ContDiff ℝ ∞ (l j)) (hus : ∀ j, ContDiff ℝ ∞ (u j))
    {s : ℝ} (hs : s ∈ Icc 0 1) :
    Topology.IsClosedEmbedding (fun p : Fin m × Icc (0 : ℝ) (2 * (w.length : ℝ) + 1) =>
      positiveRoundedWord w l u p.1 s p.2) := by
  have hc : Continuous (fun p : Fin m × Icc (0 : ℝ) (2 * (w.length : ℝ) + 1) =>
      positiveRoundedWord w l u p.1 s p.2) := by
    apply continuous_prod_of_discrete_left.mpr
    intro k
    exact (positiveRoundedWord_contDiff w hls hus k).continuous.comp
      (continuous_const.prodMk continuous_subtype_val)
  exact hc.isClosedEmbedding (positiveRoundedWord_injective w hU hl hu hla hua hs)

/-- Each local piece is smooth in its source parameter. -/
theorem positiveRoundedWordPiece_contDiff {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} (hl : ∀ j, ContDiff ℝ ∞ (l j))
    (hu : ∀ j, ContDiff ℝ ∞ (u j)) (s : ℝ)
    (e : PositiveRectilinearWordPieceIndex w) (k : Fin m) :
    ContDiff ℝ ∞ (positiveRoundedWordPiece w l u s e k) := by
  rcases e with j | j
  · have hs : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition (3 * t - 1)) :=
      Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
    have hd : ContDiff ℝ ∞ (positiveRoundedWordDepthPath w k j) :=
      ((contDiff_const.sub hs).mul contDiff_const).add (hs.mul contDiff_const)
    exact (contDiff_const.add contDiff_id).prodMk
      (contDiff_const.add ((Complex.ofRealCLM.contDiff.comp hd).mul contDiff_const))
  · have h := (positiveGridRoundedDeformation_contDiff w[j.val] (hl j) (hu j)
      ((positiveWordPrefix w j.val).symm k)).comp ((contDiff_const (c := s)).prodMk contDiff_id)
    exact (contDiff_const.add h.fst).prodMk h.snd

/-- Every local piece has nonzero velocity, including at its endpoints. -/
theorem positiveRoundedWordPiece_deriv_ne_zero {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} (hl : ∀ j, ContDiff ℝ ∞ (l j))
    (hu : ∀ j, ContDiff ℝ ∞ (u j)) (s : ℝ)
    (e : PositiveRectilinearWordPieceIndex w) (k : Fin m) (t : ℝ) :
    deriv (positiveRoundedWordPiece w l u s e k) t ≠ 0 := by
  rcases e with j | j
  · have h := ((positiveRoundedWordPiece_contDiff w hl hu s (Sum.inl j) k).differentiable
      (by simp) t).hasDerivAt
    have hx := (ContinuousLinearMap.fst ℝ ℝ ℂ).hasFDerivAt.comp_hasDerivAt t h
    have hx' : HasDerivAt (fun v : ℝ => 2 * (j.val : ℝ) + v) 1 t :=
      (hasDerivAt_id t).const_add _
    intro hz
    have he := hx.unique hx'
    simp [hz] at he
  · let F : ℝ → ℝ × ℂ := positiveGridRoundedDeformation w[j.val] (l j) (u j)
      ((positiveWordPrefix w j.val).symm k) s
    have hF : Differentiable ℝ F :=
      ((positiveGridRoundedDeformation_contDiff w[j.val] (hl j) (hu j)
        ((positiveWordPrefix w j.val).symm k)).comp
          (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
    have hd := (hF t).hasDerivAt.const_add (2 * (j.val : ℝ) + 1, (0 : ℂ))
    have he : deriv (positiveRoundedWordPiece w l u s (Sum.inr j) k) t = deriv F t := by
      convert hd.deriv using 1
      congr 1
      funext v
      simp [positiveRoundedWordPiece, F, Prod.add_def]
    rw [he]
    exact positiveGridRoundedDeformation_deriv_ne_zero w[j.val] (hl j) (hu j)
      ((positiveWordPrefix w j.val).symm k) s t

/-- The globally smooth joined word is regular also at its connector endpoints.
Equality on a nondegenerate closed interval determines the derivative there. -/
theorem positiveRoundedWord_deriv_ne_zero {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (hls : ∀ j, ContDiff ℝ ∞ (l j)) (hus : ∀ j, ContDiff ℝ ∞ (u j))
    (k : Fin m) (s : ℝ) {t : ℝ} (ht : t ∈ Icc 0 (2 * (w.length : ℝ) + 1)) :
    deriv (positiveRoundedWord w l u k s) t ≠ 0 := by
  obtain ⟨e, he⟩ := exists_positiveRectilinearWordPiece w ht
  let a : ℝ := positiveRectilinearWordPieceAddress w e
  let P : ℝ → ℝ × ℂ := positiveRoundedWordPiece w l u s e k
  have hP : Differentiable ℝ P :=
    (positiveRoundedWordPiece_contDiff w hls hus s e k).differentiable (by simp)
  have hF : Differentiable ℝ (positiveRoundedWord w l u k s) :=
    ((positiveRoundedWord_contDiff w hls hus k).comp
      (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hcomp := (hP (t - a)).hasDerivAt.comp_sub_const t a
  have hd : HasDerivWithinAt (positiveRoundedWord w l u k s) (deriv P (t - a))
      (Icc a (a + 1)) t := by
    apply (show HasDerivAt (fun v => P (v - a)) (deriv P (t - a)) t by
      exact hcomp).hasDerivWithinAt.congr_of_mem
    · intro v hv
      exact positiveRoundedWord_piece w hl hu hU k s e hv
    · exact he
  have hunique := uniqueDiffOn_Icc (show a < a + 1 by linarith) t he
  have heq : deriv (positiveRoundedWord w l u k s) t = deriv P (t - a) :=
    ((hF t).hasDerivAt.hasDerivWithinAt.derivWithin hunique).symm.trans (hd.derivWithin hunique)
  rw [heq]
  exact positiveRoundedWordPiece_deriv_ne_zero w hls hus s e k (t - a)

/-- Actual smooth scalar replacements give a regular embedded deformation of the whole word.
The same six corner profiles can be used for every letter, so this covers the empty word too. -/
theorem exists_positiveRoundedWord_regular_embedded {m : ℕ} (w : PositiveAdjacentWord m)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 48) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) :
    ∃ l u : ℝ → ℝ, ContDiff ℝ ∞ l ∧ ContDiff ℝ ∞ u ∧
      (∀ q, dist (l q) (positiveGridRectilinearLowerRise q) < ε) ∧
      (∀ q, dist (u q) (positiveGridRectilinearUpperDrop q) < ε) ∧
      EqOn l positiveGridRectilinearLowerRise (positiveGridRoundingCornerNeighborhood δ)ᶜ ∧
      EqOn u positiveGridRectilinearUpperDrop (positiveGridRoundingCornerNeighborhood δ)ᶜ ∧
      (∀ k, ContDiff ℝ ∞ (fun st : ℝ × ℝ =>
        positiveRoundedWord w (fun _ => l) (fun _ => u) k st.1 st.2)) ∧
      (∀ k s t, t ∈ Icc (0 : ℝ) (2 * (w.length : ℝ) + 1) →
        deriv (positiveRoundedWord w (fun _ => l) (fun _ => u) k s) t ≠ 0) ∧
      (∀ s, s ∈ Icc (0 : ℝ) 1 → Topology.IsClosedEmbedding
        (fun p : Fin m × Icc (0 : ℝ) (2 * (w.length : ℝ) + 1) =>
          positiveRoundedWord w (fun _ => l) (fun _ => u) p.1 s p.2)) := by
  obtain ⟨l, u, hl, hu, hla, hua, hle, hue⟩ :=
    exists_positiveGridRectilinear_smooth_rises hε
      (positiveGridRoundingCornerNeighborhood_isOpen δ)
      (positiveGridRoundingCornerNeighborhood_contains hδ)
  have hU := positiveGridRoundingCornerNeighborhood_subset hδ'
  have hU' : positiveGridRoundingCornerNeighborhood δ ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    have hh := hU ht
    constructor <;> linarith [hh.1, hh.2]
  exact ⟨l, u, hl, hu, hla, hua, hle, hue,
    positiveRoundedWord_contDiff w (fun _ => hl) (fun _ => hu),
    fun k s _ ht => positiveRoundedWord_deriv_ne_zero w (fun _ => hle) (fun _ => hue) hU'
      (fun _ => hl) (fun _ => hu) k s ht,
    fun _ hs => positiveRoundedWord_isClosedEmbedding w hU (fun _ => hle) (fun _ => hue)
      (fun _ q => (hla q).trans_le hε') (fun _ q => (hua q).trans_le hε')
      (fun _ => hl) (fun _ => hu) hs⟩

/-- The initial part of the first connector is the unchanged straight configuration. -/
theorem positiveRoundedWord_initial_collar {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (k : Fin m) (s : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 3)) :
    positiveRoundedWord w l u k s t = (t, (k.val : ℂ)) := by
  have hg := positiveRoundedWord_gap w hl hu hU k s 0
    (show t ∈ Icc (2 * ((0 : Fin (w.length + 1)).val : ℝ))
      (2 * ((0 : Fin (w.length + 1)).val : ℝ) + 1) from
        ⟨by simpa using ht.1, by simpa using (show t ≤ 1 by linarith [ht.2])⟩)
  rw [hg]
  simp [positiveRoundedWordDepthPath, positiveRoundedWordDepthNode,
    Real.smoothTransition.zero_of_nonpos (show 3 * t - 1 ≤ 0 by linarith [ht.2])]
  rfl

/-- The terminal collar has exactly the rank configuration prescribed by the word permutation. -/
theorem positiveRoundedWord_final_collar {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (k : Fin m) (s : ℝ) {t : ℝ}
    (ht : t ∈ Icc (2 * (w.length : ℝ) + 2 / 3) (2 * (w.length : ℝ) + 1)) :
    positiveRoundedWord w l u k s t = (t, ((w.permutation.symm k).val : ℂ)) := by
  have hg := positiveRoundedWord_gap w hl hu hU k s (Fin.last w.length)
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
