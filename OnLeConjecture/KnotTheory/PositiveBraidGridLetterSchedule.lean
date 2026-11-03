/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordSequence
public import OnLeConjecture.KnotTheory.PositiveBraidGridWordModel
public import OnLeConjecture.KnotTheory.PositiveBraidGridRoundedWordLift

/-! # Ordered schedules for the literal positive generators

Each generator retains its prefix labelling and its exact smooth complex path.
Successive intervals may meet at their common endpoint. No conclusion here
identifies words with geometric knots merely from their permutations.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology ContDiff
open OnLeConjecture.Analytic

namespace OnLeConjecture.KnotTheory

/-- A word traversed on the specified ordered generator intervals. -/
def positiveGridScheduledWord {m : ℕ} (w : PositiveAdjacentWord m)
    (left right : Fin w.length → ℝ) (k : Fin m) : ℝ → ℂ :=
  finiteSmoothPathConcat (fun j : Fin (w.length + 1) =>
      (((positiveWordPrefix w j.val).symm k).val : ℂ))
    (fun j t => positiveGridGenerator w[j.val] ((positiveWordPrefix w j.val).symm k) t)
    left right

private theorem scheduledGenerator_start {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (j : Fin w.length) {t : ℝ} (ht : t ≤ 0) :
    positiveGridGenerator w[j.val] ((positiveWordPrefix w j.val).symm k) t =
      (((positiveWordPrefix w j.castSucc.val).symm k).val : ℂ) :=
  (positiveGridGenerator_endpoints _ _).1 t ht

private theorem scheduledGenerator_end {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (j : Fin w.length) {t : ℝ} (ht : 1 ≤ t) :
    positiveGridGenerator w[j.val] ((positiveWordPrefix w j.val).symm k) t =
      (((positiveWordPrefix w j.succ.val).symm k).val : ℂ) := by
  rw [(positiveGridGenerator_endpoints _ _).2 t ht, Fin.val_succ,
    positiveWordPrefix_succ_symm w j.val j.isLt]

/-- Exact formula on one generator interval, with adjacent endpoints allowed to touch. -/
theorem positiveGridScheduledWord_stage {m : ℕ} (w : PositiveAdjacentWord m)
    (left right : Fin w.length → ℝ) (hlt : ∀ j, left j < right j)
    (hsep : ∀ j q, j < q → right j ≤ left q) (k : Fin m) (j : Fin w.length)
    {t : ℝ} (ht : t ∈ Icc (left j) (right j)) :
    positiveGridScheduledWord w left right k t =
      positiveGridGenerator w[j.val] ((positiveWordPrefix w j.val).symm k)
        ((t - left j) / (right j - left j)) := by
  exact finiteSmoothPathConcat_stage _ _ left right hlt hsep
    (fun j _ hv => scheduledGenerator_start w k j hv)
    (fun j _ hv => scheduledGenerator_end w k j hv) j ht

/-- Every event-free gap is the corresponding prefix rank configuration. -/
theorem positiveGridScheduledWord_gap {m : ℕ} (w : PositiveAdjacentWord m)
    (b d : ℝ) (left right : Fin w.length → ℝ) (hlt : ∀ j, left j < right j)
    (hsep : ∀ j q, j < q → right j ≤ left q) (k : Fin m) (i : Fin (w.length + 1))
    {t : ℝ} (ht : t ∈ Icc (braidModelGapLeft b right i) (braidModelGapRight d left i)) :
    positiveGridScheduledWord w left right k t =
      (((positiveWordPrefix w i.val).symm k).val : ℂ) := by
  apply finiteSmoothPathConcat_cut _ _ left right hlt
    (fun j _ hv => scheduledGenerator_start w k j hv)
    (fun j _ hv => scheduledGenerator_end w k j hv) i
  · intro j hji
    obtain ⟨q, rfl⟩ := Fin.exists_succ_eq.mpr (show i ≠ 0 by intro he; subst i; simp at hji)
    have hjq : j ≤ q := by
      change j.val ≤ q.val
      simpa only [Fin.val_succ] using Nat.le_of_lt_succ hji
    rcases lt_or_eq_of_le hjq with h | rfl
    · exact (hsep j q h).trans ((hlt q).le.trans ht.1)
    · exact ht.1
  · intro j hij
    let q : Fin w.length := ⟨i.val, lt_of_le_of_lt hij j.isLt⟩
    have hi : i = q.castSucc := Fin.ext rfl
    rw [hi, braidModelGapRight_castSucc] at ht
    rcases lt_or_eq_of_le (show q ≤ j from hij) with h | heq
    · exact ht.2.trans ((hlt q).le.trans (hsep q j h))
    · exact ht.2.trans (le_of_eq (congrArg left heq))

/-- The literal scheduled word has distinct heights on every real fibre. -/
theorem positiveGridScheduledWord_injective {m : ℕ} (w : PositiveAdjacentWord m)
    (left right : Fin w.length → ℝ) (hlt : ∀ j, left j < right j)
    (hsep : ∀ j q, j < q → right j ≤ left q) (t : ℝ) :
    Function.Injective (fun k => positiveGridScheduledWord w left right k t) := by
  rcases braidModel_intervals_cover t t left right (t := t) ⟨le_rfl, le_rfl⟩ with
    ⟨j, hj⟩ | ⟨i, hi⟩
  · simp_rw [positiveGridScheduledWord_stage w left right hlt hsep _ j hj]
    exact (positiveGridGenerator_injective _ _).comp (positiveWordPrefix w j.val).symm.injective
  · simp_rw [positiveGridScheduledWord_gap w t t left right hlt hsep _ i hi]
    exact fun k q he =>
      (positiveWordPrefix w i.val).symm.injective (Fin.ext (Nat.cast_injective he))

theorem positiveGridScheduledWord_initial {m : ℕ} (w : PositiveAdjacentWord m)
    (left right : Fin w.length → ℝ) (hlt : ∀ j, left j < right j)
    (k : Fin m) {t : ℝ} (ht : ∀ j, t ≤ left j) :
    positiveGridScheduledWord w left right k t = (k.val : ℂ) := by
  have h := finiteSmoothPathConcat_initial
    (fun j : Fin (w.length + 1) => (((positiveWordPrefix w j.val).symm k).val : ℂ))
    (fun j t => positiveGridGenerator w[j.val] ((positiveWordPrefix w j.val).symm k) t)
    left right hlt
    (fun j _ hv => scheduledGenerator_start w k j hv) ht
  unfold positiveGridScheduledWord
  exact h.trans (by simp; rfl)

theorem positiveGridScheduledWord_final {m : ℕ} (w : PositiveAdjacentWord m)
    (left right : Fin w.length → ℝ) (hlt : ∀ j, left j < right j)
    (k : Fin m) {t : ℝ} (ht : ∀ j, right j ≤ t) :
    positiveGridScheduledWord w left right k t = ((w.permutation.symm k).val : ℂ) := by
  have h := finiteSmoothPathConcat_final
    (fun j : Fin (w.length + 1) => (((positiveWordPrefix w j.val).symm k).val : ℂ))
    (fun j t => positiveGridGenerator w[j.val] ((positiveWordPrefix w j.val).symm k) t)
    left right hlt
    (fun j _ hv => scheduledGenerator_end w k j hv) ht
  unfold positiveGridScheduledWord
  simpa only [Fin.val_last, positiveWordPrefix_length] using h

/-- Joint smoothness for smoothly moving intervals of positive length. -/
theorem positiveGridScheduledWord_contDiff {m : ℕ} (w : PositiveAdjacentWord m)
    (left right : Fin w.length → ℝ → ℝ)
    (hl : ∀ j, ContDiff ℝ ∞ (left j)) (hr : ∀ j, ContDiff ℝ ∞ (right j))
    (hlt : ∀ j s, left j s < right j s) (k : Fin m) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      positiveGridScheduledWord w (fun j => left j p.1) (fun j => right j p.1) k p.2) := by
  unfold positiveGridScheduledWord finiteSmoothPathConcat
  apply contDiff_const.add
  apply ContDiff.sum
  intro j _
  apply ContDiff.sub _ contDiff_const
  apply (positiveGridGenerator_contDiff _ _).comp
  exact (contDiff_snd.sub ((hl j).comp contDiff_fst)).div
    (((hr j).comp contDiff_fst).sub ((hl j).comp contDiff_fst))
    (fun p => sub_ne_zero.mpr (hlt j p.1).ne')

/-- The ordinary contiguous word is exactly the unit-interval schedule. -/
theorem positiveGridScheduledWord_unit_eq {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (t : ℝ) :
    positiveGridScheduledWord w (fun j => (j.val : ℝ)) (fun j => (j.val : ℝ) + 1) k t =
      positiveGridWord w k t := by
  have hlt (j : Fin w.length) : (j.val : ℝ) < j.val + 1 := by linarith
  have hsep (j q : Fin w.length) (hjq : j < q) : (j.val : ℝ) + 1 ≤ q.val := by
    exact_mod_cast (show j.val + 1 ≤ q.val from hjq)
  by_cases ht0 : t ≤ 0
  · rw [positiveGridScheduledWord_initial w _ _ hlt k
      (fun j => ht0.trans (by positivity)), positiveGridWord_of_nonpos w k ht0]
  by_cases ht1 : (w.length : ℝ) ≤ t
  · rw [positiveGridScheduledWord_final w _ _ hlt k
      (fun j => (show (j.val : ℝ) + 1 ≤ w.length by exact_mod_cast j.isLt).trans ht1),
      positiveGridWord_of_length_le w k ht1]
  let j := Nat.floor t
  have hj : j < w.length := (Nat.floor_lt (le_of_not_ge ht0)).mpr (lt_of_not_ge ht1)
  have htj : t ∈ Icc (j : ℝ) ((j : ℝ) + 1) :=
    ⟨Nat.floor_le (le_of_not_ge ht0), (Nat.lt_floor_add_one t).le⟩
  rw [positiveGridScheduledWord_stage w _ _ hlt hsep k ⟨j, hj⟩ htj,
    positiveGridWord_stage w j hj k htj]
  congr 1
  simp

/-- Prefix labels factor exactly through an already traversed word. -/
theorem positiveWordPrefix_append_offset {m : ℕ} (u v : PositiveAdjacentWord m) (j : ℕ) :
    positiveWordPrefix (u ++ v) (u.length + j) =
      u.permutation * positiveWordPrefix v j := by
  unfold positiveWordPrefix
  rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left]
  exact PositiveAdjacentWord.permutation_append _ _

/-- Before the first word ends, appending another word leaves every prefix unchanged. -/
theorem positiveWordPrefix_append_left {m : ℕ} (u v : PositiveAdjacentWord m)
    {j : ℕ} (hj : j ≤ u.length) :
    positiveWordPrefix (u ++ v) j = positiveWordPrefix u j := by
  unfold positiveWordPrefix
  rw [List.take_append_of_le_length hj]

end OnLeConjecture.KnotTheory
