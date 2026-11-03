/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridWordFlattening
public import Mathlib.Data.List.Flatten
public import Mathlib.Data.Fintype.EquivFin

/-! # Ordered indices of letters in the retained event words

The index is the number of letters in preceding events plus the local letter
index. The proved equivalence covers empty event words without introducing
artificial letters.
-/

@[expose] public noncomputable section
open Set
open scoped BigOperators

namespace OnLeConjecture.KnotTheory

/-- Number of letters before the indicated event cut. -/
def positiveEventLetterOffset {m N : ℕ} (w : Fin N → PositiveAdjacentWord m) (j : ℕ) : ℕ :=
  ((List.ofFn w).take j).flatten.length

theorem positiveEventLetterOffset_mono {m N : ℕ} (w : Fin N → PositiveAdjacentWord m) :
    Monotone (positiveEventLetterOffset w) := by
  intro i j hij
  exact ((List.take_sublist_take_left hij).flatten).length_le

theorem positiveEventLetterOffset_succ {m N : ℕ} (w : Fin N → PositiveAdjacentWord m)
    (j : Fin N) :
    positiveEventLetterOffset w (j.val + 1) = positiveEventLetterOffset w j.val + (w j).length := by
  unfold positiveEventLetterOffset
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_ofFn] using j.isLt),
    List.flatten_append, List.flatten_singleton, List.length_append]
  simp

@[simp] theorem positiveEventLetterOffset_zero {m N : ℕ} (w : Fin N → PositiveAdjacentWord m) :
    positiveEventLetterOffset w 0 = 0 := by simp [positiveEventLetterOffset]

@[simp] theorem positiveEventLetterOffset_last {m N : ℕ} (w : Fin N → PositiveAdjacentWord m) :
    positiveEventLetterOffset w N = (List.ofFn w).flatten.length := by
  unfold positiveEventLetterOffset
  rw [List.take_of_length_le (by simp)]

/-- Event index and local letter index, with no points for an empty event word. -/
abbrev PositiveEventLetter {m N : ℕ} (w : Fin N → PositiveAdjacentWord m) :=
  Σ j : Fin N, Fin (w j).length

/-- Its literal position in the flattened word. -/
def positiveEventLetterIndex {m N : ℕ} (w : Fin N → PositiveAdjacentWord m)
    (e : PositiveEventLetter w) : Fin (List.ofFn w).flatten.length :=
  ⟨positiveEventLetterOffset w e.1.val + e.2.val, by
    have hnext := positiveEventLetterOffset_mono w (show e.1.val + 1 ≤ N from e.1.isLt)
    rw [positiveEventLetterOffset_succ, positiveEventLetterOffset_last] at hnext
    omega⟩

@[simp] theorem positiveEventLetterIndex_val {m N : ℕ} (w : Fin N → PositiveAdjacentWord m)
    (e : PositiveEventLetter w) :
    (positiveEventLetterIndex w e).val = positiveEventLetterOffset w e.1.val + e.2.val := rfl

/-- Every letter of an earlier event precedes every letter of a later event. -/
theorem positiveEventLetterIndex_lt_of_event_lt {m N : ℕ}
    (w : Fin N → PositiveAdjacentWord m) (e f : PositiveEventLetter w) (hef : e.1 < f.1) :
    positiveEventLetterIndex w e < positiveEventLetterIndex w f := by
  have hnext := positiveEventLetterOffset_mono w (show e.1.val + 1 ≤ f.1.val from hef)
  rw [positiveEventLetterOffset_succ] at hnext
  change positiveEventLetterOffset w e.1.val + e.2.val <
    positiveEventLetterOffset w f.1.val + f.2.val
  have he := e.2.isLt
  omega

theorem positiveEventLetterIndex_injective {m N : ℕ} (w : Fin N → PositiveAdjacentWord m) :
    Function.Injective (positiveEventLetterIndex w) := by
  rintro ⟨i, h⟩ ⟨j, k⟩ heq
  have hij : i = j := by
    rcases lt_trichotomy i j with hij | hij | hij
    · exact False.elim ((positiveEventLetterIndex_lt_of_event_lt w ⟨i, h⟩ ⟨j, k⟩ hij).ne heq)
    · exact hij
    · exact False.elim ((positiveEventLetterIndex_lt_of_event_lt w ⟨j, k⟩ ⟨i, h⟩ hij).ne heq.symm)
  subst j
  have hh := congrArg Fin.val heq
  have hk : h = k := Fin.ext (Nat.add_left_cancel hh)
  subst k
  rfl

/-- The explicit ordered index is a bijection onto all flattened letters. -/
def positiveEventLetterEquiv {m N : ℕ} (w : Fin N → PositiveAdjacentWord m) :
    PositiveEventLetter w ≃ Fin (List.ofFn w).flatten.length :=
  Equiv.ofBijective (positiveEventLetterIndex w)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨positiveEventLetterIndex_injective w, by
        simp only [Fintype.card_sigma, Fintype.card_fin, positiveWordSequence_length]⟩)

@[simp] theorem positiveEventLetterEquiv_apply {m N : ℕ} (w : Fin N → PositiveAdjacentWord m)
    (e : PositiveEventLetter w) : positiveEventLetterEquiv w e = positiveEventLetterIndex w e := rfl

/-- The flattened letter is literally the retained local generator. -/
theorem positiveEventLetterIndex_letter {m N : ℕ} (w : Fin N → PositiveAdjacentWord m)
    (e : PositiveEventLetter w) :
    (List.ofFn w).flatten[(positiveEventLetterIndex w e).val] = (w e.1)[e.2.val] := by
  let j : Fin (List.ofFn w).length := ⟨e.1.val, by simpa only [List.length_ofFn] using e.1.isLt⟩
  have hd := positiveWord_flatten_decomposition (List.ofFn w) j
  have hget : (List.ofFn w)[j.val] = w e.1 := by simp [j]
  rw [hget] at hd
  have hi : positiveEventLetterOffset w e.1.val + e.2.val <
      (((List.ofFn w).take e.1.val).flatten ++ w e.1).length := by
    simp only [List.length_append]
    exact Nat.add_lt_add_left e.2.isLt _
  change ((List.ofFn w).flatten)[positiveEventLetterOffset w e.1.val + e.2.val]'
    (positiveEventLetterIndex w e).isLt = _
  simp only [j] at hd
  simp only [hd]
  rw [List.getElem_append_left hi]
  simp only [positiveEventLetterOffset, List.getElem_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]

/-- The same prefix identifies the exact source labels of the local generator. -/
theorem positiveEventLetterIndex_label {m N : ℕ}
    (σ : Fin (N + 1) → Equiv.Perm (Fin m)) (w : Fin N → PositiveAdjacentWord m)
    (hp : ∀ j, σ j.castSucc * (w j).permutation = σ j.succ)
    (e : PositiveEventLetter w) (k : Fin m) :
    (positiveWordPrefix (List.ofFn w).flatten (positiveEventLetterIndex w e).val).symm
      ((σ 0).symm k) = (positiveWordPrefix (w e.1) e.2.val).symm ((σ e.1.castSucc).symm k) := by
  let j : Fin (List.ofFn w).length := ⟨e.1.val, by simpa only [List.length_ofFn] using e.1.isLt⟩
  have hget : (List.ofFn w)[j.val] = w e.1 := by simp [j]
  have hprefix := positiveWordPrefix_flatten_subword (List.ofFn w) j
    (h := e.2.val) (by rw [hget]; exact e.2.isLt.le)
  have hprefix' : positiveWordPrefix (List.ofFn w).flatten (positiveEventLetterIndex w e).val =
      PositiveAdjacentWord.permutation ((List.ofFn w).take e.1.val).flatten *
        positiveWordPrefix (w e.1) e.2.val := by
    simpa only [j, hget, positiveEventLetterIndex_val, positiveEventLetterOffset] using hprefix
  rw [hprefix']
  change (positiveWordPrefix (w e.1) e.2.val).symm
    ((PositiveAdjacentWord.permutation ((List.ofFn w).take e.1.val).flatten).symm
      ((σ 0).symm k)) = _
  have hl := positiveWord_flatten_take_label σ w hp e.1.castSucc k
  simp only [Fin.val_castSucc] at hl
  exact congrArg (positiveWordPrefix (w e.1) e.2.val).symm hl

end OnLeConjecture.KnotTheory
