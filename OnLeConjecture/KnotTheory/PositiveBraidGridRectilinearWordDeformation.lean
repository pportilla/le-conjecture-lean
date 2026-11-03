/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRectilinearWordMarkings
public import OnLeConjecture.Analytic.PlaneBranchBraidPathConcatenation
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! # Joining the two geometric word deformations

The letters and connectors are assembled by finite sums with clipped local
parameters. The formulas retain every original label and the terminal word
permutation. The target is a literal polygonal carrier. Smooth ambient
isotopy extension cannot be applied to its corners without a separate rounding.
-/

@[expose] public noncomputable section

open Set
open scoped Topology BigOperators

namespace OnLeConjecture.KnotTheory

open Analytic

/-- Constant extension of a local unit-interval path parameter. -/
def positiveWordClip (t : ℝ) : ℝ := max 0 (min 1 t)

theorem positiveWordClip_continuous : Continuous positiveWordClip :=
  continuous_const.max (continuous_const.min continuous_id)

theorem positiveWordClip_of_nonpos {t : ℝ} (ht : t ≤ 0) : positiveWordClip t = 0 := by
  simp [positiveWordClip, min_eq_right (show t ≤ 1 by linarith), max_eq_left ht]

theorem positiveWordClip_of_one_le {t : ℝ} (ht : 1 ≤ t) : positiveWordClip t = 1 := by
  simp [positiveWordClip, min_eq_left ht]

theorem positiveWordClip_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : positiveWordClip t = t := by
  simp [positiveWordClip, min_eq_right ht.2, max_eq_right ht.1]

/-- The connectors at a common depth-lifting parameter. -/
def positiveRectilinearWordGapDepth {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin (w.length + 1)) (k : Fin m) (d t : ℝ) : ℝ × ℂ :=
  (2 * (j.val : ℝ) + t,
    (((positiveWordPrefix w j.val).symm k).val : ℂ) +
      ((d * ((1 - t) * positiveRectilinearWordGapInitial w j k +
        t * positiveRectilinearWordGapFinal w j k) : ℝ) : ℂ) * Complex.I)

theorem positiveRectilinearWordGapDepth_continuous {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin (w.length + 1)) (k : Fin m) :
    Continuous (fun p : ℝ × ℝ => positiveRectilinearWordGapDepth w j k p.1 p.2) := by
  unfold positiveRectilinearWordGapDepth
  fun_prop

@[simp] theorem positiveRectilinearWordGapDepth_one {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin (w.length + 1)) (k : Fin m) (t : ℝ) :
    positiveRectilinearWordGapDepth w j k 1 t = positiveRectilinearWordGap w j k t := by
  simp only [positiveRectilinearWordGapDepth, one_mul, positiveRectilinearWordGap]

/-- The first local deformation, translated to its word slab and original labels. -/
def positiveRectilinearWordLiftLetter {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) (k : Fin m) (s t : ℝ) : ℝ × ℂ :=
  let p := positiveGridDepthLift w[j.val] ((positiveWordPrefix w j.val).symm k) s t
  (2 * (j.val : ℝ) + 1 + p.1, p.2)

/-- The second local deformation, with the same translation and labels. -/
def positiveRectilinearWordStraightenLetter {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) (k : Fin m) (s t : ℝ) : ℝ × ℂ :=
  let p := positiveGridRectilinearDeformation w[j.val]
    ((positiveWordPrefix w j.val).symm k) s t
  (2 * (j.val : ℝ) + 1 + p.1, p.2)

theorem positiveRectilinearWordLiftLetter_continuous {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) (k : Fin m) :
    Continuous (fun p : ℝ × ℝ => positiveRectilinearWordLiftLetter w j k p.1 p.2) := by
  have h := (positiveGridDepthLift_contDiff w[j.val]
    ((positiveWordPrefix w j.val).symm k)).continuous
  exact (continuous_const.add h.fst).prodMk h.snd

theorem positiveRectilinearWordStraightenLetter_continuous {m : ℕ}
    (w : PositiveAdjacentWord m) (j : Fin w.length) (k : Fin m) :
    Continuous (fun p : ℝ × ℝ => positiveRectilinearWordStraightenLetter w j k p.1 p.2) := by
  have h := positiveGridRectilinearDeformation_continuous w[j.val]
    ((positiveWordPrefix w j.val).symm k)
  exact (continuous_const.add h.fst).prodMk h.snd

/-- A connector followed by its letter, with constant extensions outside `[0,1]`. -/
def positiveRectilinearWordDoublePiece {m : ℕ} (w : PositiveAdjacentWord m)
    (L : Fin w.length → Fin m → ℝ → ℝ × ℂ) (d : ℝ)
    (j : Fin w.length) (k : Fin m) (t : ℝ) : ℝ × ℂ :=
  positiveRectilinearWordGapDepth w j.castSucc k d (positiveWordClip (2 * t)) +
    L j k (positiveWordClip (2 * t - 1)) -
    positiveRectilinearWordGapDepth w j.castSucc k d 1

/-- One global parametrized word, including its initial and terminal connectors. -/
def positiveRectilinearWordJoined {m : ℕ} (w : PositiveAdjacentWord m)
    (L : Fin w.length → Fin m → ℝ → ℝ × ℂ) (d : ℝ) (k : Fin m) (t : ℝ) : ℝ × ℂ :=
  finiteSmoothPathConcat (fun j => positiveRectilinearWordGapDepth w j k d 0)
      (fun j => positiveRectilinearWordDoublePiece w L d j k)
      (fun j => 2 * (j.val : ℝ)) (fun j => 2 * (j.val : ℝ) + 2) t +
    (positiveRectilinearWordGapDepth w (Fin.last w.length) k d
      (positiveWordClip (t - 2 * w.length)) -
      positiveRectilinearWordGapDepth w (Fin.last w.length) k d 0)

/-- The global first stage raises depths without changing the canonical crossing labels. -/
def positiveRectilinearWordLift {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (s t : ℝ) : ℝ × ℂ :=
  positiveRectilinearWordJoined w (fun j k t => positiveRectilinearWordLiftLetter w j k s t) s k t

/-- The global second stage straightens all letters to their polygonal carriers. -/
def positiveRectilinearWordStraighten {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (s t : ℝ) : ℝ × ℂ :=
  positiveRectilinearWordJoined w
    (fun j k t => positiveRectilinearWordStraightenLetter w j k s t) 1 k t

private theorem doublePiece_start {m : ℕ} (w : PositiveAdjacentWord m)
    (L : Fin w.length → Fin m → ℝ → ℝ × ℂ) (d : ℝ)
    (hL : ∀ j k, L j k 0 = positiveRectilinearWordGapDepth w j.castSucc k d 1)
    (j : Fin w.length) (k : Fin m) {t : ℝ} (ht : t ≤ 0) :
    positiveRectilinearWordDoublePiece w L d j k t =
      positiveRectilinearWordGapDepth w j.castSucc k d 0 := by
  rw [positiveRectilinearWordDoublePiece, positiveWordClip_of_nonpos (by linarith),
    positiveWordClip_of_nonpos (by linarith), hL]
  abel

private theorem doublePiece_end {m : ℕ} (w : PositiveAdjacentWord m)
    (L : Fin w.length → Fin m → ℝ → ℝ × ℂ) (d : ℝ)
    (hL : ∀ j k, L j k 1 = positiveRectilinearWordGapDepth w j.succ k d 0)
    (j : Fin w.length) (k : Fin m) {t : ℝ} (ht : 1 ≤ t) :
    positiveRectilinearWordDoublePiece w L d j k t =
      positiveRectilinearWordGapDepth w j.succ k d 0 := by
  rw [positiveRectilinearWordDoublePiece, positiveWordClip_of_one_le (by linarith),
    positiveWordClip_of_one_le (by linarith), hL]
  abel

private theorem wordConcat_stage {m : ℕ} (w : PositiveAdjacentWord m)
    (L : Fin w.length → Fin m → ℝ → ℝ × ℂ) (d : ℝ)
    (hL₀ : ∀ j k, L j k 0 = positiveRectilinearWordGapDepth w j.castSucc k d 1)
    (hL₁ : ∀ j k, L j k 1 = positiveRectilinearWordGapDepth w j.succ k d 0)
    (j : Fin w.length) (k : Fin m) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ)) (2 * (j.val : ℝ) + 2)) :
    positiveRectilinearWordJoined w L d k t =
      positiveRectilinearWordDoublePiece w L d j k ((t - 2 * j.val) / 2) := by
  have hlast : t ≤ 2 * w.length := by
    have hj : (j.val : ℝ) + 1 ≤ w.length := by exact_mod_cast j.isLt
    linarith [ht.2]
  unfold positiveRectilinearWordJoined
  rw [positiveWordClip_of_nonpos (by linarith), sub_self, add_zero]
  convert finiteSmoothPathConcat_stage
    (fun q => positiveRectilinearWordGapDepth w q k d 0)
    (fun q => positiveRectilinearWordDoublePiece w L d q k)
    (fun q => 2 * (q.val : ℝ)) (fun q => 2 * (q.val : ℝ) + 2) (fun _ => by linarith)
    (fun p q hpq => by
      have hh : (p.val : ℝ) + 1 ≤ q.val := by exact_mod_cast hpq
      linarith)
    (fun p u hu => doublePiece_start w L d hL₀ p k hu)
    (fun p u hu => doublePiece_end w L d hL₁ p k hu) j ht using 1
  ring_nf

/-- Exact formula on every connector before a letter. -/
theorem positiveRectilinearWordJoined_gap {m : ℕ} (w : PositiveAdjacentWord m)
    (L : Fin w.length → Fin m → ℝ → ℝ × ℂ) (d : ℝ)
    (hL₀ : ∀ j k, L j k 0 = positiveRectilinearWordGapDepth w j.castSucc k d 1)
    (hL₁ : ∀ j k, L j k 1 = positiveRectilinearWordGapDepth w j.succ k d 0)
    (j : Fin w.length) (k : Fin m) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ)) (2 * (j.val : ℝ) + 1)) :
    positiveRectilinearWordJoined w L d k t =
      positiveRectilinearWordGapDepth w j.castSucc k d (t - 2 * j.val) := by
  rw [wordConcat_stage w L d hL₀ hL₁ j k ⟨ht.1, by linarith [ht.2]⟩,
    positiveRectilinearWordDoublePiece]
  have he : 2 * ((t - 2 * (j.val : ℝ)) / 2) = t - 2 * j.val := by ring
  rw [he, positiveWordClip_of_mem ⟨by linarith [ht.1], by linarith [ht.2]⟩,
    positiveWordClip_of_nonpos (by linarith [ht.2]), hL₀]
  abel

/-- Exact formula on every letter interval, retaining its original labels. -/
theorem positiveRectilinearWordJoined_letter {m : ℕ} (w : PositiveAdjacentWord m)
    (L : Fin w.length → Fin m → ℝ → ℝ × ℂ) (d : ℝ)
    (hL₀ : ∀ j k, L j k 0 = positiveRectilinearWordGapDepth w j.castSucc k d 1)
    (hL₁ : ∀ j k, L j k 1 = positiveRectilinearWordGapDepth w j.succ k d 0)
    (j : Fin w.length) (k : Fin m) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2)) :
    positiveRectilinearWordJoined w L d k t = L j k (t - (2 * j.val + 1)) := by
  rw [wordConcat_stage w L d hL₀ hL₁ j k ⟨by linarith [ht.1], ht.2⟩,
    positiveRectilinearWordDoublePiece]
  have he : 2 * ((t - 2 * (j.val : ℝ)) / 2) = t - 2 * j.val := by ring
  rw [he, positiveWordClip_of_one_le (by linarith [ht.1]),
    positiveWordClip_of_mem ⟨by linarith [ht.1], by linarith [ht.2]⟩]
  have ht' : t - 2 * (j.val : ℝ) - 1 = t - (2 * j.val + 1) := by ring
  rw [ht']
  abel

/-- Exact formula on the terminal connector, also valid for the empty word. -/
theorem positiveRectilinearWordJoined_last_gap {m : ℕ} (w : PositiveAdjacentWord m)
    (L : Fin w.length → Fin m → ℝ → ℝ × ℂ) (d : ℝ)
    (hL₁ : ∀ j k, L j k 1 = positiveRectilinearWordGapDepth w j.succ k d 0)
    (k : Fin m) {t : ℝ} (ht : 2 * (w.length : ℝ) ≤ t) :
    positiveRectilinearWordJoined w L d k t =
      positiveRectilinearWordGapDepth w (Fin.last w.length) k d
        (positiveWordClip (t - 2 * w.length)) := by
  unfold positiveRectilinearWordJoined
  rw [finiteSmoothPathConcat_final _ _ _ _ (fun _ => by linarith)
    (fun p u hu => doublePiece_end w L d hL₁ p k hu) (fun j => by
      have hj : (j.val : ℝ) + 1 ≤ w.length := by exact_mod_cast j.isLt
      linarith)]
  abel

/-- The first-stage letters meet their moving connector endpoints exactly. -/
theorem positiveRectilinearWordLiftLetter_endpoints {m : ℕ} (w : PositiveAdjacentWord m)
    (s : ℝ) (j : Fin w.length) (k : Fin m) :
    positiveRectilinearWordLiftLetter w j k s 0 =
        positiveRectilinearWordGapDepth w j.castSucc k s 1 ∧
      positiveRectilinearWordLiftLetter w j k s 1 =
        positiveRectilinearWordGapDepth w j.succ k s 0 := by
  have hh := positiveGridDepthLift_endpoints w[j.val] ((positiveWordPrefix w j.val).symm k) s
  constructor
  · simp [positiveRectilinearWordLiftLetter, hh.1, positiveRectilinearWordGapDepth,
      positiveRectilinearWordDepth]
  · simp only [positiveRectilinearWordLiftLetter, hh.2,
      positiveRectilinearWordGapDepth, Fin.val_succ, sub_zero, one_mul, zero_mul,
      add_zero, positiveRectilinearWordGapInitial_succ, positiveRectilinearWordDepth,
      ← positiveWordPrefix_succ_symm w j.val j.isLt k]
    push_cast
    congr 1
    ring

/-- The straightening stage fixes the connector endpoint configurations. -/
theorem positiveRectilinearWordStraightenLetter_endpoints {m : ℕ}
    (w : PositiveAdjacentWord m) (s : ℝ) (j : Fin w.length) (k : Fin m) :
    positiveRectilinearWordStraightenLetter w j k s 0 =
        positiveRectilinearWordGapDepth w j.castSucc k 1 1 ∧
      positiveRectilinearWordStraightenLetter w j k s 1 =
        positiveRectilinearWordGapDepth w j.succ k 1 0 := by
  have hh := positiveGridRectilinearDeformation_endpoints w[j.val]
    ((positiveWordPrefix w j.val).symm k) s
  constructor
  · simp [positiveRectilinearWordStraightenLetter, hh.1, positiveRectilinearWordGapDepth,
      positiveRectilinearWordDepth]
  · simp only [positiveRectilinearWordStraightenLetter, hh.2,
      positiveRectilinearWordGapDepth, Fin.val_succ, sub_zero, one_mul, zero_mul,
      add_zero, positiveRectilinearWordGapInitial_succ, positiveRectilinearWordDepth,
      ← positiveWordPrefix_succ_symm w j.val j.isLt k]
    push_cast
    congr 1
    ring

/-- Both whole-word stages agree in the identical parametrization at their common time. -/
theorem positiveRectilinearWordLift_one {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (t : ℝ) :
    positiveRectilinearWordLift w k 1 t = positiveRectilinearWordStraighten w k 0 t := by
  have he : (fun j k t => positiveRectilinearWordLiftLetter w j k 1 t) =
      (fun j k t => positiveRectilinearWordStraightenLetter w j k 0 t) := by
    funext j k t
    simp only [positiveRectilinearWordLiftLetter, positiveGridDepthLift_one,
      positiveRectilinearWordStraightenLetter]
  simp only [positiveRectilinearWordLift, positiveRectilinearWordStraighten, he]

/-- The literal whole-word polygonal carrier, with the same corner data used for the grid. -/
def positiveRectilinearWordCarrier {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (t : ℝ) : ℝ × ℂ :=
  positiveRectilinearWordJoined w (positiveRectilinearWordLetter w) 1 k t

/-- The final deformation endpoint is exactly the previously marked carrier. -/
theorem positiveRectilinearWordStraighten_one {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (t : ℝ) :
    positiveRectilinearWordStraighten w k 1 t = positiveRectilinearWordCarrier w k t := by
  have he : (fun j k t => positiveRectilinearWordStraightenLetter w j k 1 t) =
      positiveRectilinearWordLetter w := by
    funext j k t
    simp only [positiveRectilinearWordStraightenLetter, positiveGridRectilinearDeformation_one,
      positiveRectilinearWordLetter]
  simp only [positiveRectilinearWordStraighten, positiveRectilinearWordCarrier, he]

/-- Whole-word depth lifting has the exact local first-stage formula on every letter. -/
theorem positiveRectilinearWordLift_letter {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) (k : Fin m) (s : ℝ) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2)) :
    positiveRectilinearWordLift w k s t =
      positiveRectilinearWordLiftLetter w j k s (t - (2 * j.val + 1)) :=
  positiveRectilinearWordJoined_letter w _ s
    (fun j k => (positiveRectilinearWordLiftLetter_endpoints w s j k).1)
    (fun j k => (positiveRectilinearWordLiftLetter_endpoints w s j k).2) j k ht

/-- Whole-word straightening has the exact local second-stage formula on every letter. -/
theorem positiveRectilinearWordStraighten_letter {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) (k : Fin m) (s : ℝ) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2)) :
    positiveRectilinearWordStraighten w k s t =
      positiveRectilinearWordStraightenLetter w j k s (t - (2 * j.val + 1)) :=
  positiveRectilinearWordJoined_letter w _ 1
    (fun j k => (positiveRectilinearWordStraightenLetter_endpoints w s j k).1)
    (fun j k => (positiveRectilinearWordStraightenLetter_endpoints w s j k).2) j k ht

/-- The initial letter parametrization is the canonical positive generator in the same
prefix labels, now separated by the explicit connectors. -/
theorem positiveRectilinearWordLift_zero_letter {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) (k : Fin m) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2)) :
    positiveRectilinearWordLift w k 0 t =
      (t, positiveGridWord w k ((j.val : ℝ) + (t - (2 * j.val + 1)))) := by
  rw [positiveRectilinearWordLift_letter w j k 0 ht]
  have hu : (j.val : ℝ) + (t - (2 * j.val + 1)) ∈ Icc (j.val : ℝ) (j.val + 1) :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [positiveGridWord_stage w j.val j.isLt k hu]
  have he : (j.val : ℝ) + (t - (2 * j.val + 1)) - j.val = t - (2 * j.val + 1) := by ring
  rw [he]
  simp only [positiveRectilinearWordLiftLetter, positiveGridDepthLift_zero]
  exact Prod.ext (by ring) rfl

/-- Joint continuity of finite word joining, including the changing seam configurations. -/
theorem positiveRectilinearWordJoined_continuous {m : ℕ} (w : PositiveAdjacentWord m)
    (L : Fin w.length → Fin m → ℝ → ℝ → ℝ × ℂ) (d : ℝ → ℝ)
    (hd : Continuous d)
    (hL : ∀ j k, Continuous (fun p : ℝ × ℝ => L j k p.1 p.2)) (k : Fin m) :
    Continuous (fun p : ℝ × ℝ =>
      positiveRectilinearWordJoined w (fun j k t => L j k p.1 t) (d p.1) k p.2) := by
  have hgap (j : Fin (w.length + 1)) (f : ℝ × ℝ → ℝ) (hf : Continuous f) :
      Continuous (fun p : ℝ × ℝ => positiveRectilinearWordGapDepth w j k (d p.1) (f p)) :=
    (positiveRectilinearWordGapDepth_continuous w j k).comp
      ((hd.comp continuous_fst).prodMk hf)
  have hletter (j : Fin w.length) (f : ℝ × ℝ → ℝ) (hf : Continuous f) :
      Continuous (fun p : ℝ × ℝ => L j k p.1 (f p)) :=
    (hL j k).comp (continuous_fst.prodMk hf)
  unfold positiveRectilinearWordJoined finiteSmoothPathConcat positiveRectilinearWordDoublePiece
  apply Continuous.add
  · apply Continuous.add
    · exact hgap 0 _ continuous_const
    · apply continuous_finsetSum
      intro j _
      apply Continuous.sub
      · apply Continuous.sub
        · apply Continuous.add
          · apply hgap j.castSucc
            exact positiveWordClip_continuous.comp (by fun_prop)
          · apply hletter j
            exact positiveWordClip_continuous.comp (by fun_prop)
        · exact hgap j.castSucc _ continuous_const
      · exact hgap j.castSucc _ continuous_const
  · apply Continuous.sub
    · apply hgap (Fin.last w.length)
      exact positiveWordClip_continuous.comp (by fun_prop)
    · exact hgap (Fin.last w.length) _ continuous_const

theorem positiveRectilinearWordLift_continuous {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) : Continuous (fun p : ℝ × ℝ => positiveRectilinearWordLift w k p.1 p.2) :=
  positiveRectilinearWordJoined_continuous w (positiveRectilinearWordLiftLetter w) id
    continuous_id (positiveRectilinearWordLiftLetter_continuous w) k

theorem positiveRectilinearWordStraighten_continuous {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) :
    Continuous (fun p : ℝ × ℝ => positiveRectilinearWordStraighten w k p.1 p.2) :=
  positiveRectilinearWordJoined_continuous w (positiveRectilinearWordStraightenLetter w)
    (fun _ => 1) continuous_const (positiveRectilinearWordStraightenLetter_continuous w) k

/-- The whole joined curve has its fixed initial strand configuration. -/
theorem positiveRectilinearWordJoined_initial {m : ℕ} (w : PositiveAdjacentWord m)
    (L : Fin w.length → Fin m → ℝ → ℝ × ℂ) (d : ℝ)
    (hL₀ : ∀ j k, L j k 0 = positiveRectilinearWordGapDepth w j.castSucc k d 1)
    (k : Fin m) {t : ℝ} (ht : t ≤ 0) :
    positiveRectilinearWordJoined w L d k t = (0, (k.val : ℂ)) := by
  unfold positiveRectilinearWordJoined
  rw [finiteSmoothPathConcat_initial _ _ _ _ (fun _ => by linarith)
    (fun p u hu => doublePiece_start w L d hL₀ p k hu) (fun j => by
      have := Nat.cast_nonneg (α := ℝ) j.val
      linarith),
    positiveWordClip_of_nonpos (by have := Nat.cast_nonneg (α := ℝ) w.length; linarith),
    sub_self, add_zero]
  simp [positiveRectilinearWordGapDepth, Equiv.Perm.one_def]

/-- The whole joined curve has the fixed terminal word permutation. -/
theorem positiveRectilinearWordJoined_final {m : ℕ} (w : PositiveAdjacentWord m)
    (L : Fin w.length → Fin m → ℝ → ℝ × ℂ) (d : ℝ)
    (hL₁ : ∀ j k, L j k 1 = positiveRectilinearWordGapDepth w j.succ k d 0)
    (k : Fin m) {t : ℝ} (ht : 2 * (w.length : ℝ) + 1 ≤ t) :
    positiveRectilinearWordJoined w L d k t =
      (2 * (w.length : ℝ) + 1, ((w.permutation.symm k).val : ℂ)) := by
  rw [positiveRectilinearWordJoined_last_gap w L d hL₁ k (by linarith),
    positiveWordClip_of_one_le (by linarith)]
  simp [positiveRectilinearWordGapDepth]

/-- Both endpoint configurations remain fixed throughout the first deformation. -/
theorem positiveRectilinearWordLift_endpoints {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (s : ℝ) :
    positiveRectilinearWordLift w k s 0 = (0, (k.val : ℂ)) ∧
      positiveRectilinearWordLift w k s (2 * (w.length : ℝ) + 1) =
        (2 * (w.length : ℝ) + 1, ((w.permutation.symm k).val : ℂ)) := by
  exact ⟨positiveRectilinearWordJoined_initial w _ s
    (fun j k => (positiveRectilinearWordLiftLetter_endpoints w s j k).1) k le_rfl,
    positiveRectilinearWordJoined_final w _ s
      (fun j k => (positiveRectilinearWordLiftLetter_endpoints w s j k).2) k le_rfl⟩

/-- Both endpoint configurations remain fixed throughout the second deformation. -/
theorem positiveRectilinearWordStraighten_endpoints {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (s : ℝ) :
    positiveRectilinearWordStraighten w k s 0 = (0, (k.val : ℂ)) ∧
      positiveRectilinearWordStraighten w k s (2 * (w.length : ℝ) + 1) =
        (2 * (w.length : ℝ) + 1, ((w.permutation.symm k).val : ℂ)) := by
  exact ⟨positiveRectilinearWordJoined_initial w _ 1
    (fun j k => (positiveRectilinearWordStraightenLetter_endpoints w s j k).1) k le_rfl,
    positiveRectilinearWordJoined_final w _ 1
      (fun j k => (positiveRectilinearWordStraightenLetter_endpoints w s j k).2) k le_rfl⟩

/-- Closing the horizontal drawing coordinate into one base-circle period. -/
def positiveRectilinearCylinderPoint {m : ℕ} (w : PositiveAdjacentWord m)
    (p : ℝ × ℂ) : Circle × ℂ :=
  (Circle.exp (2 * Real.pi * p.1 / (2 * (w.length : ℝ) + 1)), p.2)

/-- The cylinder seam closes by exactly the terminal word permutation in the first stage. -/
theorem positiveRectilinearWordLift_cyclic {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (s : ℝ) :
    positiveRectilinearCylinderPoint w
      (positiveRectilinearWordLift w k s (2 * (w.length : ℝ) + 1)) =
      positiveRectilinearCylinderPoint w
        (positiveRectilinearWordLift w (w.permutation.symm k) s 0) := by
  rw [(positiveRectilinearWordLift_endpoints w k s).2,
    (positiveRectilinearWordLift_endpoints w (w.permutation.symm k) s).1]
  simp [positiveRectilinearCylinderPoint,
    mul_div_cancel_right₀ _ (show 2 * (w.length : ℝ) + 1 ≠ 0 by positivity)]

/-- The same exact cylinder seam is retained through straightening. -/
theorem positiveRectilinearWordStraighten_cyclic {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (s : ℝ) :
    positiveRectilinearCylinderPoint w
      (positiveRectilinearWordStraighten w k s (2 * (w.length : ℝ) + 1)) =
      positiveRectilinearCylinderPoint w
        (positiveRectilinearWordStraighten w (w.permutation.symm k) s 0) := by
  rw [(positiveRectilinearWordStraighten_endpoints w k s).2,
    (positiveRectilinearWordStraighten_endpoints w (w.permutation.symm k) s).1]
  simp [positiveRectilinearCylinderPoint,
    mul_div_cancel_right₀ _ (show 2 * (w.length : ℝ) + 1 ≠ 0 by positivity)]

end OnLeConjecture.KnotTheory
