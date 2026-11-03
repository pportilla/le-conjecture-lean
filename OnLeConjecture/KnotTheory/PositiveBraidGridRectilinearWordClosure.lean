/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRectilinearWord
public import Mathlib.Data.Fintype.Sort
import all OnLeConjecture.KnotTheory.BraidPermutationCycles

/-! # Cyclic horizontal matching of the rectilinear word corners

The intermediate half-integer row in each letter joins its two lower-strand
vertical moves. At an integer row, the outgoing vertical move joins the next
letter involving that row, with the last such letter joined to the first.
The permutation constructed here acts on the actual finite set of corners.
Untouched integer rows are absent from this corner set, so identifying this
construction with the whole braid also requires that every strand rank occurs.
-/

@[expose] public noncomputable section

open Set

namespace OnLeConjecture.KnotTheory

/-- Occurrences of an integer row among the letters, ordered by their word positions. -/
abbrev PositiveRectilinearRowOccurrences {m : ℕ} (w : PositiveAdjacentWord m) (r : Fin m) :=
  {j : Fin w.length // r = adjacentLower w[j.val] ∨ r = adjacentUpper w[j.val]}

/-- A half-integer middle arc, or an integer-row arc following a specified occurrence. -/
abbrev PositiveRectilinearHorizontalArc {m : ℕ} (w : PositiveAdjacentWord m) :=
  Fin w.length ⊕ Σ r : Fin m, PositiveRectilinearRowOccurrences w r

/-- The unperturbed row of a horizontal arc. -/
def positiveRectilinearHorizontalArcRow {m : ℕ} (w : PositiveAdjacentWord m) :
    PositiveRectilinearHorizontalArc w → ℝ
  | Sum.inl j => (w[j.val].val : ℝ) + 1 / 2
  | Sum.inr p => p.1.val

private theorem adjacentLower_ne_upper {m : ℕ} (i : Fin (m - 1)) :
    adjacentLower i ≠ adjacentUpper i := by
  intro h
  have hh := congrArg Fin.val h
  change i.val = i.val + 1 at hh
  omega

/-- The outgoing corner determines its horizontal arc. -/
def positiveRectilinearOutgoingArc {m : ℕ} (w : PositiveAdjacentWord m) :
    (Fin w.length × Fin 3) ≃ PositiveRectilinearHorizontalArc w where
  toFun p := if p.2 = 0 then Sum.inl p.1 else if p.2 = 1 then
    Sum.inr ⟨adjacentLower w[p.1.val], p.1, Or.inl rfl⟩ else
    Sum.inr ⟨adjacentUpper w[p.1.val], p.1, Or.inr rfl⟩
  invFun p := match p with
    | Sum.inl j => (j, 0)
    | Sum.inr ⟨r, j⟩ => (j.val, if r = adjacentLower w[j.val.val] then 1 else 2)
  left_inv p := by
    rcases p with ⟨j, c⟩
    fin_cases c <;> simp [Ne.symm (adjacentLower_ne_upper _)]
  right_inv p := by
    rcases p with j | ⟨r, ⟨j, hj⟩⟩
    · simp
    · rcases hj with rfl | rfl
      · simp
      · simp [Ne.symm (adjacentLower_ne_upper _)]

/-- Incoming corners are indexed by the same row occurrences. Their local column numbering
is shifted because the upper vertical move lies between the two lower moves. -/
def positiveRectilinearIncomingArc {m : ℕ} (w : PositiveAdjacentWord m) :
    (Fin w.length × Fin 3) ≃ PositiveRectilinearHorizontalArc w :=
  (Equiv.prodCongr (Equiv.refl _) (finRotate 3)).trans (positiveRectilinearOutgoingArc w)

@[simp] theorem positiveRectilinearOutgoingArc_zero {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) : positiveRectilinearOutgoingArc w (j, 0) = Sum.inl j := rfl

@[simp] theorem positiveRectilinearOutgoingArc_one {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) : positiveRectilinearOutgoingArc w (j, 1) =
      Sum.inr ⟨adjacentLower w[j.val], j, Or.inl rfl⟩ := rfl

@[simp] theorem positiveRectilinearOutgoingArc_two {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) : positiveRectilinearOutgoingArc w (j, 2) =
      Sum.inr ⟨adjacentUpper w[j.val], j, Or.inr rfl⟩ := rfl

@[simp] theorem positiveRectilinearIncomingArc_zero {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) : positiveRectilinearIncomingArc w (j, 0) =
      Sum.inr ⟨adjacentLower w[j.val], j, Or.inl rfl⟩ := rfl

@[simp] theorem positiveRectilinearIncomingArc_one {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) : positiveRectilinearIncomingArc w (j, 1) =
      Sum.inr ⟨adjacentUpper w[j.val], j, Or.inr rfl⟩ := rfl

@[simp] theorem positiveRectilinearIncomingArc_two {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) : positiveRectilinearIncomingArc w (j, 2) = Sum.inl j := rfl

/-- Cyclic successor in the actual increasing order of a finite ordered type. -/
def positiveRectilinearSortedSuccessor (α : Type*) [Fintype α] [LinearOrder α] :
    Equiv.Perm α :=
  (monoEquivOfFin α rfl).symm.toEquiv.trans
    ((finRotate (Fintype.card α)).trans (monoEquivOfFin α rfl).toEquiv)

private theorem finRotate_next_spec {n : ℕ} (i : Fin n) :
    (i < finRotate n i ∧ ∀ j, i < j → finRotate n i ≤ j) ∨
      (finRotate n i ≤ i ∧ ∀ j, finRotate n i ≤ j ∧ j ≤ i) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    by_cases hi : i.val < n
    · have he : finRotate (n + 1) i = ⟨i.val + 1, by omega⟩ := finRotate_of_lt hi
      rw [he]
      left
      constructor
      · change i.val < i.val + 1
        omega
      · intro j hj
        change i.val + 1 ≤ j.val
        exact hj
    · have he : i = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
      subst i
      rw [finRotate_last]
      exact Or.inr ⟨Fin.zero_le _, fun _ => ⟨Fin.zero_le _, Fin.le_last _⟩⟩

/-- The sorted successor is the least larger element, or wraps to the minimum.
This characterizes the geometric order used in the cyclic corner matching. -/
theorem positiveRectilinearSortedSuccessor_next (α : Type*) [Fintype α] [LinearOrder α]
    (a : α) :
    (a < positiveRectilinearSortedSuccessor α a ∧
      ∀ b, a < b → positiveRectilinearSortedSuccessor α a ≤ b) ∨
    (positiveRectilinearSortedSuccessor α a ≤ a ∧
      ∀ b, positiveRectilinearSortedSuccessor α a ≤ b ∧ b ≤ a) := by
  let e := monoEquivOfFin α rfl
  change (a < e (finRotate _ (e.symm a)) ∧ ∀ b, a < b → e (finRotate _ (e.symm a)) ≤ b) ∨
    (e (finRotate _ (e.symm a)) ≤ a ∧ ∀ b, e (finRotate _ (e.symm a)) ≤ b ∧ b ≤ a)
  rcases finRotate_next_spec (e.symm a) with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · left
    constructor
    · simpa using e.strictMono ha
    · intro b hab
      simpa using e.monotone (hb (e.symm b) (e.symm.strictMono hab))
  · right
    constructor
    · simpa using e.monotone ha
    · intro b
      constructor
      · simpa using e.monotone (hb (e.symm b)).1
      · simpa using e.monotone (hb (e.symm b)).2

/-- Rotation of the integer-row occurrences, leaving each middle arc within its own letter. -/
def positiveRectilinearHorizontalRotation {m : ℕ} (w : PositiveAdjacentWord m) :
    Equiv.Perm (PositiveRectilinearHorizontalArc w) :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sigmaCongrRight fun r =>
    positiveRectilinearSortedSuccessor (PositiveRectilinearRowOccurrences w r))

/-- The literal cyclic horizontal matching from terminal `O` corners to initial `X` corners. -/
def positiveRectilinearWordMatching {m : ℕ} (w : PositiveAdjacentWord m) :
    Equiv.Perm (Fin w.length × Fin 3) :=
  (positiveRectilinearOutgoingArc w).trans
    ((positiveRectilinearHorizontalRotation w).trans (positiveRectilinearIncomingArc w).symm)

theorem positiveRectilinearHorizontalRotation_row {m : ℕ} (w : PositiveAdjacentWord m)
    (a : PositiveRectilinearHorizontalArc w) :
    positiveRectilinearHorizontalArcRow w (positiveRectilinearHorizontalRotation w a) =
      positiveRectilinearHorizontalArcRow w a := by
  rcases a with j | ⟨r, j⟩ <;> rfl

/-- The outgoing arc row is exactly the previously constructed `O` corner row. -/
theorem positiveRectilinearOutgoingArc_row {m : ℕ} (w : PositiveAdjacentWord m)
    (p : Fin w.length × Fin 3) :
    positiveRectilinearHorizontalArcRow w (positiveRectilinearOutgoingArc w p) =
      (positiveRectilinearWordOCorner w p.1 p.2).2 := by
  rcases p with ⟨j, c⟩
  change _ = positiveGridRectilinearRows w[j.val] (Equiv.swap 0 1 c)
  fin_cases c <;> norm_num [positiveRectilinearHorizontalArcRow,
    positiveGridRectilinearRows,
    adjacentLower, adjacentUpper, Equiv.swap_apply_def, Fin.ext_iff, Matrix.cons_val_two]
  simp [adjacentUpper]

/-- The incoming arc row is exactly the previously constructed `X` corner row. -/
theorem positiveRectilinearIncomingArc_row {m : ℕ} (w : PositiveAdjacentWord m)
    (p : Fin w.length × Fin 3) :
    positiveRectilinearHorizontalArcRow w (positiveRectilinearIncomingArc w p) =
      (positiveRectilinearWordXCorner w p.1 p.2).2 := by
  rcases p with ⟨j, c⟩
  change _ = positiveGridRectilinearRows w[j.val] (Equiv.swap 1 2 c)
  fin_cases c <;> norm_num [positiveRectilinearHorizontalArcRow,
    positiveGridRectilinearRows, adjacentLower, adjacentUpper,
    Equiv.swap_apply_def, Fin.ext_iff, Matrix.cons_val_two]
  exact congrArg (positiveRectilinearHorizontalArcRow w)
    (positiveRectilinearIncomingArc_two w j)

/-- Matched corners have the identical unperturbed row. -/
theorem positiveRectilinearWordMatching_row {m : ℕ} (w : PositiveAdjacentWord m)
    (p : Fin w.length × Fin 3) :
    (positiveRectilinearWordOCorner w p.1 p.2).2 =
      (positiveRectilinearWordXCorner w (positiveRectilinearWordMatching w p).1
        (positiveRectilinearWordMatching w p).2).2 := by
  rw [← positiveRectilinearOutgoingArc_row, ← positiveRectilinearIncomingArc_row]
  simp [positiveRectilinearWordMatching, positiveRectilinearHorizontalRotation_row]

/-- Every vertical segment has distinct endpoint rows. -/
theorem positiveRectilinearWord_corner_rows_ne {m : ℕ} (w : PositiveAdjacentWord m)
    (p : Fin w.length × Fin 3) :
    (positiveRectilinearWordOCorner w p.1 p.2).2 ≠
      (positiveRectilinearWordXCorner w p.1 p.2).2 := by
  intro he
  have hh := (positiveGridRectilinearRows_strictMono w[p.1.val]).injective he
  exact positiveGridRectilinearDiagram.disjoint p.2 hh

/-- The cyclic horizontal matching never joins the two ends of one vertical segment. -/
theorem positiveRectilinearWordMatching_ne_self {m : ℕ} (w : PositiveAdjacentWord m)
    (p : Fin w.length × Fin 3) : positiveRectilinearWordMatching w p ≠ p := by
  intro he
  have hr := positiveRectilinearWordMatching_row w p
  rw [he] at hr
  exact positiveRectilinearWord_corner_rows_ne w p hr

/-- The half-integer arc joins column zero to column two of the same letter. -/
theorem positiveRectilinearWordMatching_middle {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) : positiveRectilinearWordMatching w (j, 0) = (j, 2) := by
  apply (positiveRectilinearIncomingArc w).injective
  simp [positiveRectilinearWordMatching, positiveRectilinearIncomingArc,
    positiveRectilinearHorizontalRotation, positiveRectilinearOutgoingArc]

/-- On integer rows, matching is precisely the sorted cyclic successor, including its wrap. -/
theorem positiveRectilinearWordMatching_occurrence {m : ℕ} (w : PositiveAdjacentWord m)
    (r : Fin m) (j : PositiveRectilinearRowOccurrences w r) :
    positiveRectilinearWordMatching w
        ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, j⟩)) =
      (positiveRectilinearIncomingArc w).symm (Sum.inr ⟨r,
        positiveRectilinearSortedSuccessor (PositiveRectilinearRowOccurrences w r) j⟩) := by
  simp [positiveRectilinearWordMatching, positiveRectilinearHorizontalRotation]

/-- A rank keeps its original label while no intervening letter involves that rank. -/
theorem positiveRectilinearWordPrefix_constant {m : ℕ} (w : PositiveAdjacentWord m)
    (r : Fin m) {u v : ℕ} (huv : u ≤ v) (hv : v ≤ w.length)
    (hno : ∀ j : Fin w.length, u ≤ j.val → j.val < v →
      r ≠ adjacentLower w[j.val] ∧ r ≠ adjacentUpper w[j.val]) :
    positiveWordPrefix w u r = positiveWordPrefix w v r := by
  induction v, huv using Nat.le_induction with
  | base => rfl
  | succ v huv ih =>
    have hvl : v < w.length := by omega
    have hh := hno ⟨v, hvl⟩ huv (show v < v + 1 from Nat.lt_succ_self v)
    have hs : adjacentSwap w[v] r = r := by
      rw [adjacentSwap.eq_def]
      exact Equiv.swap_apply_of_ne_of_ne hh.1 hh.2
    rw [positiveWordPrefix_succ w v hvl, Equiv.Perm.mul_apply, hs]
    exact ih (by omega) (fun j hju hjv => hno j hju (by omega))

/-- Consecutive occurrences of a row have the same strand label between their vertical
moves. The wrapping case changes labels by exactly the whole word permutation. -/
theorem positiveRectilinearWordMatching_labels {m : ℕ} (w : PositiveAdjacentWord m)
    (r : Fin m) (j : PositiveRectilinearRowOccurrences w r) :
    let q := positiveRectilinearSortedSuccessor (PositiveRectilinearRowOccurrences w r) j
    (j.val < q.val ∧
      positiveWordPrefix w (j.val.val + 1) r = positiveWordPrefix w q.val.val r) ∨
    (q.val ≤ j.val ∧
      positiveWordPrefix w (j.val.val + 1) r = w.permutation
        (positiveWordPrefix w q.val.val r)) := by
  let q := positiveRectilinearSortedSuccessor (PositiveRectilinearRowOccurrences w r) j
  change (j.val < q.val ∧ _) ∨ (q.val ≤ j.val ∧ _)
  rcases positiveRectilinearSortedSuccessor_next
      (PositiveRectilinearRowOccurrences w r) j with ⟨hjq, hleast⟩ | ⟨hqj, hbounds⟩
  · left
    refine ⟨hjq, positiveRectilinearWordPrefix_constant w r hjq q.val.isLt.le ?_⟩
    intro k hjk hkq
    constructor
    · intro he
      have hh := hleast ⟨k, Or.inl he⟩ (show j.val.val < k.val from hjk)
      exact (not_le_of_gt hkq) hh
    · intro he
      have hh := hleast ⟨k, Or.inr he⟩ (show j.val.val < k.val from hjk)
      exact (not_le_of_gt hkq) hh
  · right
    refine ⟨hqj, ?_⟩
    have htail : positiveWordPrefix w (j.val.val + 1) r = w.permutation r := by
      rw [← positiveWordPrefix_length]
      apply positiveRectilinearWordPrefix_constant w r j.val.isLt (le_refl _)
      intro k hjk _
      constructor
      · intro he
        have hh := (hbounds ⟨k, Or.inl he⟩).2
        exact (not_le_of_gt hjk) hh
      · intro he
        have hh := (hbounds ⟨k, Or.inr he⟩).2
        exact (not_le_of_gt hjk) hh
    have hhead : positiveWordPrefix w q.val.val r = r := by
      have hh := positiveRectilinearWordPrefix_constant w r (Nat.zero_le q.val.val)
        q.val.isLt.le (fun k _ hkq => ?_)
      · simpa only [positiveWordPrefix_zero, Equiv.Perm.one_apply] using hh.symm
      · constructor
        · intro he
          have hqk := (hbounds ⟨k, Or.inl he⟩).1
          exact (not_le_of_gt hkq) hqk
        · intro he
          have hqk := (hbounds ⟨k, Or.inr he⟩).1
          exact (not_le_of_gt hkq) hqk
    rw [htail, hhead]

end OnLeConjecture.KnotTheory
