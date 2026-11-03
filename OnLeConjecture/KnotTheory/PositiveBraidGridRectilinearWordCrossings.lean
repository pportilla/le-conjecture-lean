/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRectilinearWordClosure

/-! # Horizontal arc incidence in the cyclic rectilinear word

The open cyclic interval from a terminal corner to its matched initial corner
contains no other corner on the same row. This is the endpoint incidence
condition needed when separating repeated horizontal rows.
-/

@[expose] public noncomputable section

open Set

namespace OnLeConjecture.KnotTheory

/-- Strict cyclic betweenness in the horizontal drawing coordinate. -/
def PositiveRectilinearCyclicBetween (a b x : ℝ) : Prop :=
  if a < b then a < x ∧ x < b else a < x ∨ x < b

/-- The initial horizontal coordinate of an arc, at its outgoing vertical corner. -/
def positiveRectilinearHorizontalArcStart {m : ℕ} (w : PositiveAdjacentWord m)
    (a : PositiveRectilinearHorizontalArc w) : ℝ :=
  let p := (positiveRectilinearOutgoingArc w).symm a
  positiveRectilinearWordColumn w p.1 p.2

/-- The terminal horizontal coordinate, at the next incoming vertical corner. -/
def positiveRectilinearHorizontalArcEnd {m : ℕ} (w : PositiveAdjacentWord m)
    (a : PositiveRectilinearHorizontalArc w) : ℝ :=
  let p := (positiveRectilinearIncomingArc w).symm (positiveRectilinearHorizontalRotation w a)
  positiveRectilinearWordColumn w p.1 p.2

/-- Incoming column of an integer row in one of its occurrences. -/
def positiveRectilinearIntegerRowIn {m : ℕ} (w : PositiveAdjacentWord m)
    (r : Fin m) (j : PositiveRectilinearRowOccurrences w r) : ℝ :=
  positiveRectilinearWordColumn w j.val (if r = adjacentLower w[j.val.val] then 0 else 1)

/-- Outgoing column of an integer row in one of its occurrences. -/
def positiveRectilinearIntegerRowOut {m : ℕ} (w : PositiveAdjacentWord m)
    (r : Fin m) (j : PositiveRectilinearRowOccurrences w r) : ℝ :=
  positiveRectilinearWordColumn w j.val (if r = adjacentLower w[j.val.val] then 1 else 2)

@[simp] theorem positiveRectilinearHorizontalArcStart_middle {m : ℕ}
    (w : PositiveAdjacentWord m) (j : Fin w.length) :
    positiveRectilinearHorizontalArcStart w (Sum.inl j) =
      positiveRectilinearWordColumn w j 0 := rfl

@[simp] theorem positiveRectilinearHorizontalArcStart_integer {m : ℕ}
    (w : PositiveAdjacentWord m) (r : Fin m) (j : PositiveRectilinearRowOccurrences w r) :
    positiveRectilinearHorizontalArcStart w (Sum.inr ⟨r, j⟩) =
      positiveRectilinearIntegerRowOut w r j := rfl

@[simp] theorem positiveRectilinearHorizontalArcEnd_middle {m : ℕ}
    (w : PositiveAdjacentWord m) (j : Fin w.length) :
    positiveRectilinearHorizontalArcEnd w (Sum.inl j) =
      positiveRectilinearWordColumn w j 2 := by
  change positiveRectilinearWordColumn w
    ((positiveRectilinearIncomingArc w).symm (Sum.inl j)).1
    ((positiveRectilinearIncomingArc w).symm (Sum.inl j)).2 = _
  rw [← positiveRectilinearIncomingArc_two w j, Equiv.symm_apply_apply]

@[simp] theorem positiveRectilinearHorizontalArcEnd_integer {m : ℕ}
    (w : PositiveAdjacentWord m) (r : Fin m) (j : PositiveRectilinearRowOccurrences w r) :
    positiveRectilinearHorizontalArcEnd w (Sum.inr ⟨r, j⟩) =
      positiveRectilinearIntegerRowIn w r
        (positiveRectilinearSortedSuccessor (PositiveRectilinearRowOccurrences w r) j) := by
  let q := positiveRectilinearSortedSuccessor (PositiveRectilinearRowOccurrences w r) j
  change positiveRectilinearWordColumn w
    ((positiveRectilinearIncomingArc w).symm (Sum.inr ⟨r, q⟩)).1
    ((positiveRectilinearIncomingArc w).symm (Sum.inr ⟨r, q⟩)).2 = _
  change positiveRectilinearWordColumn w
    ((positiveRectilinearIncomingArc w).symm (Sum.inr ⟨r, q⟩)).1
    ((positiveRectilinearIncomingArc w).symm (Sum.inr ⟨r, q⟩)).2 =
      positiveRectilinearIntegerRowIn w r q
  rcases q.property with h | h
  · have he : (Sum.inr ⟨r, q⟩ : PositiveRectilinearHorizontalArc w) =
        positiveRectilinearIncomingArc w (q.val, 0) := by
      rw [positiveRectilinearIncomingArc_zero]
      exact congrArg Sum.inr (Sigma.subtype_ext h rfl)
    rw [he, Equiv.symm_apply_apply]
    simp only [positiveRectilinearIntegerRowIn, if_pos h]
  · have hn : r ≠ adjacentLower w[q.val.val] := by
      intro he
      have hv := congrArg Fin.val (he.symm.trans h)
      change w[q.val.val].val = w[q.val.val].val + 1 at hv
      exact (ne_of_lt (show w[q.val.val].val < w[q.val.val].val + 1 from
        Nat.lt_succ_self _)) hv
    have he : (Sum.inr ⟨r, q⟩ : PositiveRectilinearHorizontalArc w) =
        positiveRectilinearIncomingArc w (q.val, 1) := by
      rw [positiveRectilinearIncomingArc_one]
      exact congrArg Sum.inr (Sigma.subtype_ext h rfl)
    rw [he, Equiv.symm_apply_apply]
    simp only [positiveRectilinearIntegerRowIn, if_neg hn]

/-- In any letter, an integer row's incoming corner precedes its outgoing corner. -/
theorem positiveRectilinearIntegerRowIn_lt_out {m : ℕ}
    (w : PositiveAdjacentWord m) (r : Fin m) (j : PositiveRectilinearRowOccurrences w r) :
    positiveRectilinearIntegerRowIn w r j < positiveRectilinearIntegerRowOut w r j := by
  unfold positiveRectilinearIntegerRowIn positiveRectilinearIntegerRowOut
  split_ifs <;> norm_num [positiveRectilinearWordColumn, positiveGridRectilinearColumns,
    Matrix.cons_val_two]

/-- All endpoints of an earlier occurrence precede those of a later occurrence. -/
theorem positiveRectilinearIntegerRowOut_lt_in {m : ℕ}
    (w : PositiveAdjacentWord m) (r : Fin m)
    {j k : PositiveRectilinearRowOccurrences w r} (hjk : j < k) :
    positiveRectilinearIntegerRowOut w r j < positiveRectilinearIntegerRowIn w r k :=
  positiveRectilinearWordColumn_lt w hjk _ _

private theorem sorted_successor_gap_excludes_intervals
    (α : Type*) [Fintype α] [LinearOrder α] (A B : α → ℝ)
    (hAB : ∀ j, A j < B j) (hsep : ∀ j k, j < k → B j < A k)
    (j k : α) {x : ℝ} (hx : x ∈ Icc (A k) (B k)) :
    ¬ PositiveRectilinearCyclicBetween (B j)
      (A (positiveRectilinearSortedSuccessor α j)) x := by
  have hAm : Monotone A := by
    intro p q hpq
    rcases hpq.lt_or_eq with h | rfl
    · exact (lt_trans (hAB p) (hsep p q h)).le
    · rfl
  have hBm : Monotone B := by
    intro p q hpq
    rcases hpq.lt_or_eq with h | rfl
    · exact (lt_trans (hsep p q h) (hAB q)).le
    · rfl
  rcases positiveRectilinearSortedSuccessor_next α j with ⟨hjq, hleast⟩ | ⟨hqj, hbounds⟩
  · rw [PositiveRectilinearCyclicBetween, if_pos (hsep _ _ hjq)]
    intro hcross
    rcases le_or_gt k j with hkj | hjk
    · have hh := hBm hkj
      linarith [hx.2]
    · have hh := hAm (hleast k hjk)
      linarith [hx.1]
  · have hnot : ¬ B j < A (positiveRectilinearSortedSuccessor α j) := by
      have hh := hAm hqj
      linarith [hAB j]
    rw [PositiveRectilinearCyclicBetween, if_neg hnot]
    intro hcross
    have hleft := hAm (hbounds k).1
    have hright := hBm (hbounds k).2
    rcases hcross with h | h <;> linarith [hx.1, hx.2]

/-- No endpoint of another occurrence lies inside the horizontal arc joining consecutive
integer-row occurrences, including the closing arc across the seam. -/
theorem positiveRectilinearIntegerRow_arc_excludes_occurrence {m : ℕ}
    (w : PositiveAdjacentWord m) (r : Fin m)
    (j k : PositiveRectilinearRowOccurrences w r) {x : ℝ}
    (hx : x ∈ Icc (positiveRectilinearIntegerRowIn w r k)
      (positiveRectilinearIntegerRowOut w r k)) :
    ¬ PositiveRectilinearCyclicBetween
      (positiveRectilinearHorizontalArcStart w (Sum.inr ⟨r, j⟩))
      (positiveRectilinearHorizontalArcEnd w (Sum.inr ⟨r, j⟩)) x := by
  rw [positiveRectilinearHorizontalArcStart_integer, positiveRectilinearHorizontalArcEnd_integer]
  exact sorted_successor_gap_excludes_intervals _ _ _
    (positiveRectilinearIntegerRowIn_lt_out w r)
    (fun _ _ h => positiveRectilinearIntegerRowOut_lt_in w r h) j k hx

private theorem word_X_rows {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) (c : Fin 3) :
    (positiveRectilinearWordXCorner w j c).2 =
      ![(w[j.val].val : ℝ), (w[j.val].val : ℝ) + 1, (w[j.val].val : ℝ) + 1 / 2] c := by
  change positiveGridRectilinearRows w[j.val] (Equiv.swap 1 2 c) = _
  fin_cases c <;> norm_num [positiveGridRectilinearRows, Equiv.swap_apply_def,
    Fin.ext_iff, Matrix.cons_val_two]

private theorem word_O_rows {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) (c : Fin 3) :
    (positiveRectilinearWordOCorner w j c).2 =
      ![(w[j.val].val : ℝ) + 1 / 2, (w[j.val].val : ℝ), (w[j.val].val : ℝ) + 1] c := by
  change positiveGridRectilinearRows w[j.val] (Equiv.swap 0 1 c) = _
  fin_cases c <;> norm_num [positiveGridRectilinearRows, Equiv.swap_apply_def,
    Fin.ext_iff, Matrix.cons_val_two]

private theorem nat_add_half_ne_nat (i r : ℕ) : (i : ℝ) + 1 / 2 ≠ r := by
  intro h
  have hh : ((2 * i + 1 : ℕ) : ℝ) = ((2 * r : ℕ) : ℝ) := by
    push_cast
    linarith
  have hn : 2 * i + 1 = 2 * r := Nat.cast_injective hh
  omega

private theorem integer_interval_lower {m : ℕ} (w : PositiveAdjacentWord m)
    (r : Fin m) (j : Fin w.length) (h : r = adjacentLower w[j.val])
    (c : Fin 3) (hc : c = 0 ∨ c = 1) :
    positiveRectilinearWordColumn w j c ∈
      Icc (positiveRectilinearIntegerRowIn w r ⟨j, Or.inl h⟩)
        (positiveRectilinearIntegerRowOut w r ⟨j, Or.inl h⟩) := by
  rcases hc with rfl | rfl <;>
    norm_num [positiveRectilinearIntegerRowIn, positiveRectilinearIntegerRowOut,
      h, positiveRectilinearWordColumn, positiveGridRectilinearColumns]

private theorem integer_interval_upper {m : ℕ} (w : PositiveAdjacentWord m)
    (r : Fin m) (j : Fin w.length) (h : r = adjacentUpper w[j.val])
    (c : Fin 3) (hc : c = 1 ∨ c = 2) :
    positiveRectilinearWordColumn w j c ∈
      Icc (positiveRectilinearIntegerRowIn w r ⟨j, Or.inr h⟩)
        (positiveRectilinearIntegerRowOut w r ⟨j, Or.inr h⟩) := by
  have hn : r ≠ adjacentLower w[j.val] := by
    intro he
    have hh := congrArg Fin.val (he.symm.trans h)
    exact Nat.ne_of_lt (Nat.lt_succ_self _) hh
  rcases hc with rfl | rfl <;>
    norm_num [positiveRectilinearIntegerRowIn, positiveRectilinearIntegerRowOut,
      hn, positiveRectilinearWordColumn, positiveGridRectilinearColumns, Matrix.cons_val_two]

/-- Every vertical endpoint on an integer row belongs to the corresponding occurrence's
closed incoming-to-outgoing interval. -/
theorem positiveRectilinearIntegerRow_corner_occurrence {m : ℕ}
    (w : PositiveAdjacentWord m) (r : Fin m) (p : Fin w.length × Fin 3)
    (hr : (positiveRectilinearWordXCorner w p.1 p.2).2 = r.val ∨
      (positiveRectilinearWordOCorner w p.1 p.2).2 = r.val) :
    ∃ k : PositiveRectilinearRowOccurrences w r, k.val = p.1 ∧
      positiveRectilinearWordColumn w p.1 p.2 ∈
        Icc (positiveRectilinearIntegerRowIn w r k) (positiveRectilinearIntegerRowOut w r k) := by
  rcases p with ⟨j, c⟩
  rw [word_X_rows, word_O_rows] at hr
  fin_cases c
  · change (w[j.val].val : ℝ) = r.val ∨ (w[j.val].val : ℝ) + 1 / 2 = r.val at hr
    rcases hr with h | h
    · have he : r = adjacentLower w[j.val] := Fin.ext (Nat.cast_injective h.symm)
      exact ⟨⟨j, Or.inl he⟩, rfl, integer_interval_lower w r j he 0 (Or.inl rfl)⟩
    · exact (nat_add_half_ne_nat _ _ h).elim
  · change (w[j.val].val : ℝ) + 1 = r.val ∨ (w[j.val].val : ℝ) = r.val at hr
    rcases hr with h | h
    · have hv : r.val = w[j.val].val + 1 := by exact_mod_cast h.symm
      have he : r = adjacentUpper w[j.val] := Fin.ext hv
      exact ⟨⟨j, Or.inr he⟩, rfl, integer_interval_upper w r j he 1 (Or.inl rfl)⟩
    · have he : r = adjacentLower w[j.val] := Fin.ext (Nat.cast_injective h.symm)
      exact ⟨⟨j, Or.inl he⟩, rfl, integer_interval_lower w r j he 1 (Or.inr rfl)⟩
  · change (w[j.val].val : ℝ) + 1 / 2 = r.val ∨ (w[j.val].val : ℝ) + 1 = r.val at hr
    rcases hr with h | h
    · exact (nat_add_half_ne_nat _ _ h).elim
    · have hv : r.val = w[j.val].val + 1 := by exact_mod_cast h.symm
      have he : r = adjacentUpper w[j.val] := Fin.ext hv
      exact ⟨⟨j, Or.inr he⟩, rfl, integer_interval_upper w r j he 2 (Or.inr rfl)⟩

/-- An integer horizontal arc contains no projected vertical endpoint on its own row. -/
theorem positiveRectilinearIntegerRow_arc_endpoint_ne {m : ℕ}
    (w : PositiveAdjacentWord m) (r : Fin m)
    (j : PositiveRectilinearRowOccurrences w r) (p : Fin w.length × Fin 3)
    (hx : PositiveRectilinearCyclicBetween
      (positiveRectilinearHorizontalArcStart w (Sum.inr ⟨r, j⟩))
      (positiveRectilinearHorizontalArcEnd w (Sum.inr ⟨r, j⟩))
      (positiveRectilinearWordColumn w p.1 p.2)) :
    (positiveRectilinearWordXCorner w p.1 p.2).2 ≠ r.val ∧
      (positiveRectilinearWordOCorner w p.1 p.2).2 ≠ r.val := by
  have hn : ¬ ((positiveRectilinearWordXCorner w p.1 p.2).2 = r.val ∨
      (positiveRectilinearWordOCorner w p.1 p.2).2 = r.val) := by
    intro hr
    obtain ⟨k, _, hk⟩ := positiveRectilinearIntegerRow_corner_occurrence w r p hr
    exact positiveRectilinearIntegerRow_arc_excludes_occurrence w r j k hk hx
  exact not_or.mp hn

/-- The only vertical column inside a middle horizontal arc is the upper vertical
column of that same letter. -/
theorem positiveRectilinearMiddleArc_column_iff {m : ℕ}
    (w : PositiveAdjacentWord m) (j : Fin w.length) (p : Fin w.length × Fin 3) :
    PositiveRectilinearCyclicBetween
      (positiveRectilinearHorizontalArcStart w (Sum.inl j))
      (positiveRectilinearHorizontalArcEnd w (Sum.inl j))
      (positiveRectilinearWordColumn w p.1 p.2) ↔ p = (j, 1) := by
  have h02 : positiveRectilinearWordColumn w j 0 < positiveRectilinearWordColumn w j 2 := by
    norm_num [positiveRectilinearWordColumn, positiveGridRectilinearColumns, Matrix.cons_val_two]
  rw [positiveRectilinearHorizontalArcStart_middle, positiveRectilinearHorizontalArcEnd_middle,
    PositiveRectilinearCyclicBetween, if_pos h02]
  constructor
  · intro hp
    rcases p with ⟨k, c⟩
    have hkj : k = j := by
      rcases lt_trichotomy k j with h | h | h
      · have hh := positiveRectilinearWordColumn_lt w h c 0
        exact (not_lt_of_gt hp.1 hh).elim
      · exact h
      · have hh := positiveRectilinearWordColumn_lt w h 2 c
        exact (not_lt_of_gt hp.2 hh).elim
    subst k
    have hc : c = 1 := by
      fin_cases c
      · exact (lt_irrefl _ hp.1).elim
      · rfl
      · exact (lt_irrefl _ hp.2).elim
    simp [hc]
  · rintro rfl
    norm_num [positiveRectilinearWordColumn, positiveGridRectilinearColumns, Matrix.cons_val_two]

/-- No horizontal arc contains a projected vertical endpoint on its own row.
This includes all closing arcs across the word seam. -/
theorem positiveRectilinearHorizontalArc_endpoint_ne {m : ℕ}
    (w : PositiveAdjacentWord m) (a : PositiveRectilinearHorizontalArc w)
    (p : Fin w.length × Fin 3)
    (hx : PositiveRectilinearCyclicBetween (positiveRectilinearHorizontalArcStart w a)
      (positiveRectilinearHorizontalArcEnd w a) (positiveRectilinearWordColumn w p.1 p.2)) :
    (positiveRectilinearWordXCorner w p.1 p.2).2 ≠ positiveRectilinearHorizontalArcRow w a ∧
      (positiveRectilinearWordOCorner w p.1 p.2).2 ≠ positiveRectilinearHorizontalArcRow w a := by
  rcases a with j | ⟨r, j⟩
  · have hp := (positiveRectilinearMiddleArc_column_iff w j p).mp hx
    subst p
    rw [word_X_rows, word_O_rows]
    change (w[j.val].val : ℝ) + 1 ≠ (w[j.val].val : ℝ) + 1 / 2 ∧
      (w[j.val].val : ℝ) ≠ (w[j.val].val : ℝ) + 1 / 2
    constructor <;> linarith
  · exact positiveRectilinearIntegerRow_arc_endpoint_ne w r j p hx

private theorem integer_not_between_vertical_rows {m : ℕ}
    (w : PositiveAdjacentWord m) (r : Fin m) (p : Fin w.length × Fin 3) :
    ¬ (((positiveRectilinearWordXCorner w p.1 p.2).2 < r.val ∧
      (r.val : ℝ) < (positiveRectilinearWordOCorner w p.1 p.2).2) ∨
      ((positiveRectilinearWordOCorner w p.1 p.2).2 < r.val ∧
      (r.val : ℝ) < (positiveRectilinearWordXCorner w p.1 p.2).2)) := by
  have hb : (positiveRectilinearWordXCorner w p.1 p.2).2 ∈
        Icc (w[p.1.val].val : ℝ) ((w[p.1.val].val : ℝ) + 1) ∧
      (positiveRectilinearWordOCorner w p.1 p.2).2 ∈
        Icc (w[p.1.val].val : ℝ) ((w[p.1.val].val : ℝ) + 1) := by
    rw [word_X_rows, word_O_rows]
    rcases p with ⟨j, c⟩
    fin_cases c <;> norm_num [Matrix.cons_val_two]
  intro h
  have hlo : (w[p.1.val].val : ℝ) < r.val := by
    rcases h with h | h <;> linarith [hb.1.1, hb.2.1]
  have hhi : (r.val : ℝ) < (w[p.1.val].val : ℝ) + 1 := by
    rcases h with h | h <;> linarith [hb.1.2, hb.2.2]
  have hlo' : w[p.1.val].val < r.val := by exact_mod_cast hlo
  have hhi' : r.val < w[p.1.val].val + 1 := by exact_mod_cast hhi
  omega

/-- The full unperturbed corner diagram has precisely the designated one crossing per letter. -/
theorem positiveRectilinearHorizontalArc_crossing_iff {m : ℕ}
    (w : PositiveAdjacentWord m) (a : PositiveRectilinearHorizontalArc w)
    (p : Fin w.length × Fin 3) :
    (PositiveRectilinearCyclicBetween (positiveRectilinearHorizontalArcStart w a)
      (positiveRectilinearHorizontalArcEnd w a) (positiveRectilinearWordColumn w p.1 p.2) ∧
      (((positiveRectilinearWordXCorner w p.1 p.2).2 < positiveRectilinearHorizontalArcRow w a ∧
        positiveRectilinearHorizontalArcRow w a < (positiveRectilinearWordOCorner w p.1 p.2).2) ∨
       ((positiveRectilinearWordOCorner w p.1 p.2).2 < positiveRectilinearHorizontalArcRow w a ∧
        positiveRectilinearHorizontalArcRow w a < (positiveRectilinearWordXCorner w p.1 p.2).2))) ↔
      ∃ j : Fin w.length, a = Sum.inl j ∧ p = (j, 1) := by
  constructor
  · rintro ⟨hx, hr⟩
    rcases a with j | ⟨r, j⟩
    · exact ⟨j, rfl, (positiveRectilinearMiddleArc_column_iff w j p).mp hx⟩
    · exact (integer_not_between_vertical_rows w r p hr).elim
  · rintro ⟨j, rfl, rfl⟩
    refine ⟨(positiveRectilinearMiddleArc_column_iff w j (j, 1)).mpr rfl, Or.inr ?_⟩
    rw [word_X_rows, word_O_rows]
    change (w[j.val].val : ℝ) < (w[j.val].val : ℝ) + 1 / 2 ∧
      (w[j.val].val : ℝ) + 1 / 2 < (w[j.val].val : ℝ) + 1
    constructor <;> linarith

end OnLeConjecture.KnotTheory
