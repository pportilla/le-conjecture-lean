/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridEventLetterIndex

/-! # Literal identification of the retained event schedule

The original event model is exactly a flattened letter schedule. The individual
intervals are obtained by solving its already defined affine time parameter for
each local integer cut. Empty event words contribute no intervals.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff BigOperators
open OnLeConjecture.Analytic

namespace OnLeConjecture.KnotTheory

/-- Initial time of a retained local generator. -/
def positiveEventLetterLeft {m N : ℕ} (w : Fin N → PositiveAdjacentWord m)
    (left right : Fin N → ℝ) (e : PositiveEventLetter w) : ℝ :=
  left e.1 + (right e.1 - left e.1) / 3 * (1 + (e.2.val : ℝ) / (w e.1).length)

/-- Terminal time of the same generator. -/
def positiveEventLetterRight {m N : ℕ} (w : Fin N → PositiveAdjacentWord m)
    (left right : Fin N → ℝ) (e : PositiveEventLetter w) : ℝ :=
  left e.1 + (right e.1 - left e.1) / 3 * (1 + ((e.2.val : ℝ) + 1) / (w e.1).length)

/-- Generator intervals indexed by their literal positions in the flattened word. -/
def positiveFlattenedEventLeft {m N : ℕ} (w : Fin N → PositiveAdjacentWord m)
    (left right : Fin N → ℝ) (j : Fin (List.ofFn w).flatten.length) : ℝ :=
  positiveEventLetterLeft w left right ((positiveEventLetterEquiv w).symm j)

def positiveFlattenedEventRight {m N : ℕ} (w : Fin N → PositiveAdjacentWord m)
    (left right : Fin N → ℝ) (j : Fin (List.ofFn w).flatten.length) : ℝ :=
  positiveEventLetterRight w left right ((positiveEventLetterEquiv w).symm j)

/-- The local generator time is exactly the original event time minus its local index. -/
theorem positiveEventLetter_time {m N : ℕ} (w : Fin N → PositiveAdjacentWord m)
    (left right : Fin N → ℝ) (hlt : ∀ j, left j < right j)
    (e : PositiveEventLetter w) (t : ℝ) :
    (t - positiveEventLetterLeft w left right e) /
        (positiveEventLetterRight w left right e - positiveEventLetterLeft w left right e) =
      (w e.1).length * (3 * ((t - left e.1) / (right e.1 - left e.1)) - 1) - e.2.val := by
  have hn : ((w e.1).length : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) e.2.isLt))
  have hd : right e.1 - left e.1 ≠ 0 := sub_ne_zero.mpr (hlt e.1).ne'
  have hden : positiveEventLetterRight w left right e - positiveEventLetterLeft w left right e =
      (right e.1 - left e.1) / (3 * (w e.1).length) := by
    unfold positiveEventLetterLeft positiveEventLetterRight
    field_simp
    ring
  rw [hden]
  unfold positiveEventLetterLeft
  field_simp [hn, hd]
  ring

/-- Every retained local letter occupies an interval of positive length. -/
theorem positiveEventLetter_left_lt_right {m N : ℕ} (w : Fin N → PositiveAdjacentWord m)
    (left right : Fin N → ℝ) (hlt : ∀ j, left j < right j) (e : PositiveEventLetter w) :
    positiveEventLetterLeft w left right e < positiveEventLetterRight w left right e := by
  have hn : (0 : ℝ) < (w e.1).length := by
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) e.2.isLt)
  unfold positiveEventLetterLeft positiveEventLetterRight
  apply add_lt_add_right
  apply mul_lt_mul_of_pos_left _ (div_pos (sub_pos.mpr (hlt e.1)) (by norm_num))
  apply add_lt_add_right
  exact (div_lt_div_iff_of_pos_right hn).mpr (by linarith)

/-- Letter intervals lie strictly inside their original outer event intervals. -/
theorem positiveEventLetter_inside {m N : ℕ} (w : Fin N → PositiveAdjacentWord m)
    (left right : Fin N → ℝ) (hlt : ∀ j, left j < right j) (e : PositiveEventLetter w) :
    left e.1 < positiveEventLetterLeft w left right e ∧
      positiveEventLetterRight w left right e < right e.1 := by
  have hn : (0 : ℝ) < (w e.1).length := by
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) e.2.isLt)
  have hwidth := hlt e.1
  have hq : 0 ≤ (e.2.val : ℝ) / (w e.1).length := div_nonneg (by positivity) hn.le
  have hq' : ((e.2.val : ℝ) + 1) / (w e.1).length ≤ 1 := by
    apply (div_le_one hn).mpr
    exact_mod_cast e.2.isLt
  constructor
  · change left e.1 < left e.1 + _
    exact lt_add_of_pos_right _ (mul_pos (div_pos (sub_pos.mpr hwidth) (by norm_num))
      (by linarith))
  · have hm := mul_le_mul_of_nonneg_left (show
      1 + ((e.2.val : ℝ) + 1) / (w e.1).length ≤ 2 by linarith)
        (show 0 ≤ (right e.1 - left e.1) / 3 by positivity)
    change left e.1 + _ < right e.1
    linarith

/-- Adjacent letters within an event meet only at their common time cut. -/
theorem positiveEventLetter_order_same {m N : ℕ} (w : Fin N → PositiveAdjacentWord m)
    (left right : Fin N → ℝ) (hlt : ∀ j, left j < right j)
    (j : Fin N) (h k : Fin (w j).length) (hhk : h < k) :
    positiveEventLetterRight w left right ⟨j, h⟩ ≤ positiveEventLetterLeft w left right ⟨j, k⟩ := by
  have hn : (0 : ℝ) < (w j).length := by
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) h.isLt)
  unfold positiveEventLetterLeft positiveEventLetterRight
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (sub_nonneg.mpr (hlt j).le) (by norm_num))
  apply add_le_add_right
  exact (div_le_div_iff_of_pos_right hn).mpr (by exact_mod_cast hhk)

/-- Ordering of the old event intervals induces the required flattened letter ordering. -/
theorem positiveEventLetter_order {m N : ℕ} (w : Fin N → PositiveAdjacentWord m)
    (left right : Fin N → ℝ) (hlt : ∀ j, left j < right j)
    (hsep : ∀ j q, j < q → right j < left q)
    (e f : PositiveEventLetter w)
    (hef : positiveEventLetterIndex w e < positiveEventLetterIndex w f) :
    positiveEventLetterRight w left right e ≤ positiveEventLetterLeft w left right f := by
  rcases lt_trichotomy e.1 f.1 with h | h | h
  · exact ((positiveEventLetter_inside w left right hlt e).2.trans
      ((hsep _ _ h).trans (positiveEventLetter_inside w left right hlt f).1)).le
  · rcases e with ⟨j, h⟩
    rcases f with ⟨q, k⟩
    dsimp only at h
    subst q
    apply positiveEventLetter_order_same w left right hlt j h k
    change positiveEventLetterOffset w j.val + h.val <
      positiveEventLetterOffset w j.val + k.val at hef
    exact Nat.lt_of_add_lt_add_left hef
  · exact False.elim ((positiveEventLetterIndex_lt_of_event_lt w f e h).not_ge hef.le)

/-- All flattened intervals have positive length. -/
theorem positiveFlattenedEvent_left_lt_right {m N : ℕ} (w : Fin N → PositiveAdjacentWord m)
    (left right : Fin N → ℝ) (hlt : ∀ j, left j < right j)
    (i : Fin (List.ofFn w).flatten.length) :
    positiveFlattenedEventLeft w left right i < positiveFlattenedEventRight w left right i :=
  positiveEventLetter_left_lt_right w left right hlt _

/-- The flattened schedule permits touching adjacent letters but no overlap. -/
theorem positiveFlattenedEvent_order {m N : ℕ} (w : Fin N → PositiveAdjacentWord m)
    (left right : Fin N → ℝ) (hlt : ∀ j, left j < right j)
    (hsep : ∀ j q, j < q → right j < left q)
    (i j : Fin (List.ofFn w).flatten.length) (hij : i < j) :
    positiveFlattenedEventRight w left right i ≤ positiveFlattenedEventLeft w left right j := by
  apply positiveEventLetter_order w left right hlt hsep
  simpa only [← positiveEventLetterEquiv_apply, Equiv.apply_symm_apply] using hij

/-- A contiguous word is the exact sum of its generator increments. -/
theorem positiveGridWord_sum_generator_increments {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (t : ℝ) :
    (∑ j : Fin w.length,
      (positiveGridGenerator w[j.val] ((positiveWordPrefix w j.val).symm k) (t - j.val) -
        (((positiveWordPrefix w j.val).symm k).val : ℂ))) = positiveGridWord w k t - k.val := by
  have h := positiveGridScheduledWord_unit_eq w k t
  unfold positiveGridScheduledWord finiteSmoothPathConcat at h
  have hzero : (((positiveWordPrefix w (0 : Fin (w.length + 1)).val).symm k).val : ℂ) =
      k.val := by simp; rfl
  simp only [hzero, add_sub_cancel_left, div_one, Fin.val_castSucc] at h
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h)

/-- Exact equality with the original global event model, on the entire real line.
No assumption of geometric equivalence or additional separation is used. -/
theorem positiveGridGlobalWordModel_eq_flattened_schedule {m N : ℕ}
    (left right : Fin N → ℝ) (σ : Fin (N + 1) → Equiv.Perm (Fin m))
    (w : Fin N → PositiveAdjacentWord m) (hlt : ∀ j, left j < right j)
    (hp : ∀ j, σ j.castSucc * (w j).permutation = σ j.succ) (k : Fin m) (t : ℝ) :
    positiveGridGlobalWordModel left right σ w k t =
      positiveGridScheduledWord (List.ofFn w).flatten (positiveFlattenedEventLeft w left right)
        (positiveFlattenedEventRight w left right) ((σ 0).symm k) t := by
  let A : Fin (List.ofFn w).flatten.length → ℂ := fun j =>
    positiveGridGenerator (List.ofFn w).flatten[j.val]
        ((positiveWordPrefix (List.ofFn w).flatten j.val).symm ((σ 0).symm k))
        ((t - positiveFlattenedEventLeft w left right j) /
          (positiveFlattenedEventRight w left right j -
            positiveFlattenedEventLeft w left right j)) -
      (((positiveWordPrefix (List.ofFn w).flatten j.val).symm ((σ 0).symm k)).val : ℂ)
  have hA (e : PositiveEventLetter w) :
      A (positiveEventLetterEquiv w e) =
        positiveGridGenerator (w e.1)[e.2.val]
          ((positiveWordPrefix (w e.1) e.2.val).symm ((σ e.1.castSucc).symm k))
          ((w e.1).length * (3 * ((t - left e.1) / (right e.1 - left e.1)) - 1) - e.2.val) -
        (((positiveWordPrefix (w e.1) e.2.val).symm ((σ e.1.castSucc).symm k)).val : ℂ) := by
    dsimp only [A, positiveFlattenedEventLeft, positiveFlattenedEventRight]
    rw [Equiv.symm_apply_apply, positiveEventLetterEquiv_apply,
      positiveEventLetterIndex_letter, positiveEventLetterIndex_label σ w hp,
      positiveEventLetter_time w left right hlt]
  have hsum : (∑ j, A j) = ∑ j : Fin N, (positiveGridWord (w j) ((σ j.castSucc).symm k)
      ((w j).length * (3 * ((t - left j) / (right j - left j)) - 1)) -
        (((σ j.castSucc).symm k).val : ℂ)) := by
    rw [← (positiveEventLetterEquiv w).sum_comp A, Fintype.sum_sigma]
    simp_rw [hA, positiveGridWord_sum_generator_increments]
  unfold positiveGridScheduledWord finiteSmoothPathConcat
  change positiveGridGlobalWordModel left right σ w k t =
    (((positiveWordPrefix (List.ofFn w).flatten 0).symm ((σ 0).symm k)).val : ℂ) + ∑ j, A j
  have hz : (((positiveWordPrefix (List.ofFn w).flatten 0).symm ((σ 0).symm k)).val : ℂ) =
      (((σ 0).symm k).val : ℂ) := by simp; rfl
  rw [hz, hsum]
  rfl

end OnLeConjecture.KnotTheory
