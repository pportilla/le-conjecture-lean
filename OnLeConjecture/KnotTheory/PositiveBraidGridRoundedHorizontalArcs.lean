/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRoundedRowSeparation
public import OnLeConjecture.KnotTheory.PositiveBraidGridUnknot

/-! # The horizontal straight portions of the retained rounded word

The connector intervals and the horizontal portions of each letter project into
the same closed horizontal arcs used to construct the smooth row offset. The
cyclic interval at the period seam is included.
-/

@[expose] public noncomputable section
open Set
open scoped Topology ContDiff

namespace OnLeConjecture.KnotTheory

private theorem exists_sorted_closed_gap
    (α : Type*) [Fintype α] [LinearOrder α] [Nonempty α] (A B : α → ℝ)
    (hAB : ∀ j, A j < B j) (hsep : ∀ j k, j < k → B j < A k)
    (x : ℝ) (hx : ∀ j, x ≤ A j ∨ B j ≤ x) :
    ∃ j, PositiveRectilinearClosedCyclicBetween (B j)
      (A (positiveRectilinearSortedSuccessor α j)) x := by
  classical
  let s : Finset α := Finset.univ.filter (fun j => B j ≤ x)
  by_cases hs : s.Nonempty
  · let j := s.max' hs
    have hj : j ∈ s := Finset.max'_mem s hs
    have hBj : B j ≤ x := (Finset.mem_filter.mp hj).2
    refine ⟨j, ?_⟩
    rcases positiveRectilinearSortedSuccessor_next α j with ⟨hjs, _⟩ | ⟨hjs, _⟩
    · have hBs : ¬ B (positiveRectilinearSortedSuccessor α j) ≤ x := by
        intro h
        have hmem : positiveRectilinearSortedSuccessor α j ∈ s :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
        exact hjs.not_ge (Finset.le_max' s _ hmem)
      rw [PositiveRectilinearClosedCyclicBetween, if_pos (hsep _ _ hjs)]
      exact ⟨hBj, (hx _).resolve_right hBs⟩
    · have hnot : ¬ B j < A (positiveRectilinearSortedSuccessor α j) := by
        rcases hjs.lt_or_eq with h | h
        · exact not_lt.mpr (le_of_lt (((hAB _).trans (hsep _ _ h)).trans (hAB j)))
        · rw [h]
          exact (hAB j).not_gt
      rw [PositiveRectilinearClosedCyclicBetween, if_neg hnot]
      exact Or.inl hBj
  · let j := Finset.univ.max' (Finset.univ_nonempty : (Finset.univ : Finset α).Nonempty)
    refine ⟨j, ?_⟩
    have hlast (k : α) : k ≤ j := Finset.le_max' _ k (Finset.mem_univ k)
    have hAs : x ≤ A (positiveRectilinearSortedSuccessor α j) := by
      apply (hx _).resolve_right
      intro h
      apply hs
      exact ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
    rcases positiveRectilinearSortedSuccessor_next α j with ⟨hjs, _⟩ | ⟨hjs, _⟩
    · exact (hjs.not_ge (hlast _)).elim
    · have hnot : ¬ B j < A (positiveRectilinearSortedSuccessor α j) := by
        rcases hjs.lt_or_eq with h | h
        · exact not_lt.mpr (le_of_lt (((hAB _).trans (hsep _ _ h)).trans (hAB j)))
        · rw [h]
          exact (hAB j).not_gt
      rw [PositiveRectilinearClosedCyclicBetween, if_neg hnot]
      exact Or.inr hAs

/-- Integer-row points outside all vertical occurrence intervals belong to an
actual closed horizontal arc on that row, including the closing arc. -/
theorem exists_positiveRectilinearIntegerArc_mem {m : ℕ} (w : PositiveAdjacentWord m)
    (r : Fin m) (hr : Nonempty (PositiveRectilinearRowOccurrences w r)) {x : ℝ}
    (hx : x ∈ Icc 0 (2 * (w.length : ℝ) + 1))
    (hex : ∀ j : PositiveRectilinearRowOccurrences w r,
      x ≤ positiveRectilinearIntegerRowIn w r j ∨ positiveRectilinearIntegerRowOut w r j ≤ x) :
    ∃ j : PositiveRectilinearRowOccurrences w r,
      ((Circle.exp (2 * Real.pi * x / (2 * (w.length : ℝ) + 1)) : ℂ), (r.val : ℝ)) ∈
        positiveRectilinearHorizontalArcSet w (Sum.inr ⟨r, j⟩) := by
  let := hr
  obtain ⟨j, hj⟩ := exists_sorted_closed_gap (PositiveRectilinearRowOccurrences w r)
    (positiveRectilinearIntegerRowIn w r) (positiveRectilinearIntegerRowOut w r)
    (positiveRectilinearIntegerRowIn_lt_out w r)
    (fun _ _ h => positiveRectilinearIntegerRowOut_lt_in w r h) x hex
  refine ⟨j, x, ⟨hx, ?_⟩, rfl⟩
  simpa only [positiveRectilinearHorizontalArcStart_integer,
    positiveRectilinearHorizontalArcEnd_integer, mem_ofPred_eq] using hj

private theorem wordColumn_in_letter {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) (c : Fin 3) :
    positiveRectilinearWordColumn w j c ∈ Ioo (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2) := by
  fin_cases c <;>
    norm_num [positiveRectilinearWordColumn, positiveGridRectilinearColumns, Matrix.cons_val_two]
  all_goals linarith

private theorem integer_gap_excludes {m : ℕ} (w : PositiveAdjacentWord m)
    (r : Fin m) (j : Fin (w.length + 1)) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ)) (2 * (j.val : ℝ) + 1))
    (k : PositiveRectilinearRowOccurrences w r) :
    t ≤ positiveRectilinearIntegerRowIn w r k ∨ positiveRectilinearIntegerRowOut w r k ≤ t := by
  by_cases hkj : k.val.val < j.val
  · have hkj' : (k.val.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hkj
    have hb := wordColumn_in_letter w k.val
      (if r = adjacentLower w[k.val.val] then 1 else 2)
    right
    change positiveRectilinearWordColumn w _ _ ≤ t
    linarith [hb.2, ht.1]
  · have hkj' : (j.val : ℝ) ≤ k.val.val := by exact_mod_cast Nat.le_of_not_gt hkj
    have hb := wordColumn_in_letter w k.val
      (if r = adjacentLower w[k.val.val] then 0 else 1)
    left
    change t ≤ positiveRectilinearWordColumn w _ _
    linarith [hb.1, ht.2]

/-- Every connector of the SAME rounded word lies on its actual integer-row arc.
The varying smooth depth does not change its projected base and row. -/
theorem positiveRoundedWord_gap_mem_horizontalArc {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (hrows : ∀ r : Fin m, Nonempty (PositiveRectilinearRowOccurrences w r))
    (k : Fin m) (s : ℝ) (j : Fin (w.length + 1)) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ)) (2 * (j.val : ℝ) + 1)) :
    ∃ a : PositiveRectilinearHorizontalArc w,
      (((positiveRectilinearCylinderPoint w (positiveRoundedWord w l u k s t)).1 : ℂ),
        (positiveRoundedWord w l u k s t).2.re) ∈ positiveRectilinearHorizontalArcSet w a := by
  have hj : (j.val : ℝ) ≤ w.length := by exact_mod_cast Nat.le_of_lt_succ j.isLt
  have hj0 : (0 : ℝ) ≤ j.val := by positivity
  obtain ⟨q, hq⟩ := exists_positiveRectilinearIntegerArc_mem w
    ((positiveWordPrefix w j.val).symm k) (hrows _)
    ⟨by linarith [ht.1], by linarith [ht.2]⟩ (integer_gap_excludes w _ j ht)
  refine ⟨Sum.inr ⟨_, q⟩, ?_⟩
  rw [positiveRoundedWord_gap w hl hu hU k s j ht]
  simpa [positiveRectilinearCylinderPoint] using hq

private theorem letter_mem_period {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) {x : ℝ}
    (hx : x ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2)) :
    x ∈ Icc 0 (2 * (w.length : ℝ) + 1) := by
  have hj : (j.val : ℝ) + 1 ≤ w.length := by exact_mod_cast j.isLt
  have hj0 : (0 : ℝ) ≤ j.val := by positivity
  constructor <;> linarith [hx.1, hx.2]

private theorem lower_ne_upper' {m : ℕ} (i : Fin (m - 1)) :
    adjacentLower i ≠ adjacentUpper i := by
  intro h
  have he := congrArg Fin.val h
  change i.val = i.val + 1 at he
  omega

/-- The horizontal parts of an integer row within a letter lie on an actual arc.
The two displayed inequalities are the exact intervals outside that letter's
vertical move on the row. -/
theorem exists_positiveRectilinearIntegerArc_mem_of_letter {m : ℕ}
    (w : PositiveAdjacentWord m) (r : Fin m)
    (hr : Nonempty (PositiveRectilinearRowOccurrences w r)) (j : Fin w.length) {x : ℝ}
    (hx : x ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2))
    (hlo : r = adjacentLower w[j.val] →
      x ≤ positiveRectilinearWordColumn w j 0 ∨ positiveRectilinearWordColumn w j 1 ≤ x)
    (hup : r = adjacentUpper w[j.val] →
      x ≤ positiveRectilinearWordColumn w j 1 ∨ positiveRectilinearWordColumn w j 2 ≤ x) :
    ∃ a : PositiveRectilinearHorizontalArc w,
      ((Circle.exp (2 * Real.pi * x / (2 * (w.length : ℝ) + 1)) : ℂ), (r.val : ℝ)) ∈
        positiveRectilinearHorizontalArcSet w a := by
  have hex (k : PositiveRectilinearRowOccurrences w r) :
      x ≤ positiveRectilinearIntegerRowIn w r k ∨
        positiveRectilinearIntegerRowOut w r k ≤ x := by
    rcases lt_trichotomy k.val j with h | h | h
    · have h' : (k.val.val : ℝ) + 1 ≤ j.val := by exact_mod_cast h
      have hb := wordColumn_in_letter w k.val
        (if r = adjacentLower w[k.val.val] then 1 else 2)
      right
      change positiveRectilinearWordColumn w _ _ ≤ x
      linarith [hb.2, hx.1]
    · have he : k.val.val = j.val := congrArg Fin.val h
      rcases k.property with hk | hk
      · have hr' : r = adjacentLower w[j.val] := by simpa only [he] using hk
        simpa only [positiveRectilinearIntegerRowIn, positiveRectilinearIntegerRowOut,
          h, if_pos hr'] using hlo hr'
      · have hr' : r = adjacentUpper w[j.val] := by simpa only [he] using hk
        have hn : r ≠ adjacentLower w[k.val.val] := fun h =>
          lower_ne_upper' _ (h.symm.trans hk)
        have hn' : r ≠ adjacentLower w[j.val] := by simpa only [he] using hn
        simpa only [positiveRectilinearIntegerRowIn, positiveRectilinearIntegerRowOut,
          h, if_neg hn'] using hup hr'
    · have h' : (j.val : ℝ) + 1 ≤ k.val.val := by exact_mod_cast h
      have hb := wordColumn_in_letter w k.val
        (if r = adjacentLower w[k.val.val] then 0 else 1)
      left
      change x ≤ positiveRectilinearWordColumn w _ _
      linarith [hb.1, hx.2]
  obtain ⟨q, hq⟩ := exists_positiveRectilinearIntegerArc_mem w r hr
    (letter_mem_period w j hx) hex
  exact ⟨Sum.inr ⟨r, q⟩, hq⟩

/-- The inactive strands of each rounded letter lie on the actual horizontal arcs,
including parameters inside the rounding neighborhoods of other strands. -/
theorem positiveRoundedWord_fixed_letter_mem_horizontalArc {m : ℕ}
    (w : PositiveAdjacentWord m) {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (hrows : ∀ r : Fin m, Nonempty (PositiveRectilinearRowOccurrences w r))
    (k : Fin m) (s : ℝ) (j : Fin w.length) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2))
    (hk₀ : (positiveWordPrefix w j.val).symm k ≠ adjacentLower w[j.val])
    (hk₁ : (positiveWordPrefix w j.val).symm k ≠ adjacentUpper w[j.val]) :
    ∃ a : PositiveRectilinearHorizontalArc w,
      (((positiveRectilinearCylinderPoint w (positiveRoundedWord w l u k s t)).1 : ℂ),
        (positiveRoundedWord w l u k s t).2.re) ∈ positiveRectilinearHorizontalArcSet w a := by
  obtain ⟨a, ha⟩ := exists_positiveRectilinearIntegerArc_mem_of_letter w
    ((positiveWordPrefix w j.val).symm k) (hrows _) j ht
    (fun h => (hk₀ h).elim) (fun h => (hk₁ h).elim)
  refine ⟨a, ?_⟩
  rw [positiveRoundedWord_letter w hl hu hU k s j ht,
    positiveGridRoundedDeformation_fixed w[j.val] (l j) (u j) _ hk₀ hk₁]
  simpa [positiveRectilinearCylinderPoint] using ha

/-- The five horizontal plateaus of the two moving polygonal strands. -/
def PositiveGridMovingHorizontalTime {m : ℕ} (i : Fin (m - 1)) (k : Fin m) (t : ℝ) : Prop :=
  (k = adjacentLower i ∧
    (t ∈ Icc 0 (1 / 6) ∨ t ∈ Icc (5 / 12) (7 / 12) ∨ t ∈ Icc (5 / 6) 1)) ∨
  (k = adjacentUpper i ∧ (t ∈ Icc 0 (1 / 4) ∨ t ∈ Icc (3 / 4) 1))

/-- Each literal horizontal plateau has the closed arc prescribed by the word's
cyclic corner matching. The middle plateau belongs to the half-integer arc. -/
theorem positiveRectilinear_letter_horizontal_mem {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) (k : Fin m) {t : ℝ}
    (ht : PositiveGridMovingHorizontalTime w[j.val] k t) :
    ∃ a : PositiveRectilinearHorizontalArc w,
      ((Circle.exp (2 * Real.pi *
        (2 * (j.val : ℝ) + 1 + (positiveGridRectilinear w[j.val] k t).1) /
          (2 * (w.length : ℝ) + 1)) : ℂ),
        (positiveGridRectilinear w[j.val] k t).2.re) ∈ positiveRectilinearHorizontalArcSet w a := by
  let P : ℝ × ℝ → ℂ × ℝ := fun p =>
    ((Circle.exp (2 * Real.pi * (2 * (j.val : ℝ) + 1 + p.1) /
      (2 * (w.length : ℝ) + 1)) : ℂ), p.2)
  change ∃ a, P (positiveGridRectilinearProjection (positiveGridRectilinear w[j.val] k t)) ∈ _
  have hlo : Nonempty (PositiveRectilinearRowOccurrences w (adjacentLower w[j.val])) :=
    ⟨⟨j, Or.inl rfl⟩⟩
  have hup : Nonempty (PositiveRectilinearRowOccurrences w (adjacentUpper w[j.val])) :=
    ⟨⟨j, Or.inr rfl⟩⟩
  rcases ht with ⟨rfl, ht | ht | ht⟩ | ⟨rfl, ht | ht⟩
  · rw [(positiveGridRectilinear_lower_segments w[j.val]).1 t ht]
    exact exists_positiveRectilinearIntegerArc_mem_of_letter w (adjacentLower w[j.val]) hlo j
      (by constructor <;> linarith [ht.1, ht.2])
      (fun _ => Or.inl (by
        norm_num [positiveRectilinearWordColumn, positiveGridRectilinearColumns,
          Matrix.cons_val_two]
        linarith [ht.2])) (fun h => (lower_ne_upper' _ h).elim)
  · rw [(positiveGridRectilinear_lower_segments w[j.val]).2.2.1 t ht]
    dsimp only [P]
    let x := 2 * (j.val : ℝ) + 1 + (2 * t - 1 / 2)
    have hx : x ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2) := by
      dsimp [x]
      constructor <;> linarith [ht.1, ht.2]
    refine ⟨Sum.inl j, x, ⟨letter_mem_period w j hx, ?_⟩, rfl⟩
    change PositiveRectilinearClosedCyclicBetween _ _ x
    rw [positiveRectilinearHorizontalArcStart_middle, positiveRectilinearHorizontalArcEnd_middle]
    have hcol : positiveRectilinearWordColumn w j 0 < positiveRectilinearWordColumn w j 2 := by
      norm_num [positiveRectilinearWordColumn, positiveGridRectilinearColumns, Matrix.cons_val_two]
    rw [PositiveRectilinearClosedCyclicBetween, if_pos hcol]
    norm_num [positiveRectilinearWordColumn, positiveGridRectilinearColumns, Matrix.cons_val_two, x]
    constructor <;> linarith [ht.1, ht.2]
  · rw [(positiveGridRectilinear_lower_segments w[j.val]).2.2.2.2 t ht]
    have he := exists_positiveRectilinearIntegerArc_mem_of_letter w (adjacentUpper w[j.val]) hup j
      (x := 2 * (j.val : ℝ) + 1 + (2 * t - 1))
      (by constructor <;> linarith [ht.1, ht.2])
      (fun h => (lower_ne_upper' _ h.symm).elim)
      (fun _ => Or.inr (by
        norm_num [positiveRectilinearWordColumn, positiveGridRectilinearColumns,
          Matrix.cons_val_two]
        linarith [ht.1]))
    simpa only [P, adjacentUpper, Nat.cast_add, Nat.cast_one] using he
  · rw [(positiveGridRectilinear_upper_segments w[j.val]).1 t ht]
    have he := exists_positiveRectilinearIntegerArc_mem_of_letter w (adjacentUpper w[j.val]) hup j
      (x := 2 * (j.val : ℝ) + 1 + 2 * t)
      (by constructor <;> linarith [ht.1, ht.2])
      (fun h => (lower_ne_upper' _ h.symm).elim)
      (fun _ => Or.inl (by
        norm_num [positiveRectilinearWordColumn, positiveGridRectilinearColumns,
          Matrix.cons_val_two]
        linarith [ht.2]))
    simpa only [P, adjacentUpper, Nat.cast_add, Nat.cast_one] using he
  · rw [(positiveGridRectilinear_upper_segments w[j.val]).2.2 t ht]
    exact exists_positiveRectilinearIntegerArc_mem_of_letter w (adjacentLower w[j.val]) hlo j
      (by constructor <;> linarith [ht.1, ht.2])
      (fun _ => Or.inr (by
        norm_num [positiveRectilinearWordColumn, positiveGridRectilinearColumns,
          Matrix.cons_val_two]
        linarith [ht.1])) (fun h => (lower_ne_upper' _ h).elim)

/-- On the five moving horizontal portions, the retained rounded word belongs to
its actual closed horizontal arc. The parameter is exactly the existing rounding
progress, and only the prescribed corner neighborhood is omitted. -/
theorem positiveRoundedWord_moving_letter_mem_horizontalArc {m : ℕ}
    (w : PositiveAdjacentWord m) {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (k : Fin m) (j : Fin w.length) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2))
    (hout : positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2 ∉ U)
    (hh : PositiveGridMovingHorizontalTime w[j.val] ((positiveWordPrefix w j.val).symm k)
      (positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2)) :
    ∃ a : PositiveRectilinearHorizontalArc w,
      (((positiveRectilinearCylinderPoint w (positiveRoundedWord w l u k 1 t)).1 : ℂ),
        (positiveRoundedWord w l u k 1 t).2.re) ∈ positiveRectilinearHorizontalArcSet w a := by
  have hk : (positiveWordPrefix w j.val).symm k = adjacentLower w[j.val] ∨
      (positiveWordPrefix w j.val).symm k = adjacentUpper w[j.val] :=
    hh.imp And.left And.left
  rw [positiveRoundedWord_letter w hl hu hU k 1 j ht,
    positiveGridRoundedDeformation_one_eq_polygon w[j.val] (hl j) (hu j) _ hout hk]
  exact positiveRectilinear_letter_horizontal_mem w j _ hh

/-- Parameters of the projected horizontal straight portions: all connectors,
all inactive letter strands, and the five moving plateaus away from the retained
rounding neighborhoods. The word's existing source parameter is used throughout. -/
def PositiveRoundedWordHorizontalParameter {m : ℕ} (w : PositiveAdjacentWord m)
    (U : Set ℝ) (k : Fin m) (t : ℝ) : Prop :=
  (∃ j : Fin (w.length + 1), t ∈ Icc (2 * (j.val : ℝ)) (2 * (j.val : ℝ) + 1)) ∨
  ∃ j : Fin w.length, t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2) ∧
    (((positiveWordPrefix w j.val).symm k ≠ adjacentLower w[j.val] ∧
       (positiveWordPrefix w j.val).symm k ≠ adjacentUpper w[j.val]) ∨
     (positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2 ∉ U ∧
       PositiveGridMovingHorizontalTime w[j.val] ((positiveWordPrefix w j.val).symm k)
         (positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2)))

/-- The proved endpoint rotation supplies all integer-row occurrences. No
additional row-coverage or geometric arc-membership assumption is needed. -/
theorem positiveRoundedWord_horizontal_mem_of_endpoint_rotation {m : ℕ} (hm : 2 ≤ m)
    (w : PositiveAdjacentWord m) (before after : Equiv.Perm (Fin m))
    (hw : before * w.permutation = after) (hc : after.trans (finRotate m) = before)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (k : Fin m) {t : ℝ} (ht : PositiveRoundedWordHorizontalParameter w U k t) :
    ∃ a : PositiveRectilinearHorizontalArc w,
      (((positiveRectilinearCylinderPoint w (positiveRoundedWord w l u k 1 t)).1 : ℂ),
        (positiveRoundedWord w l u k 1 t).2.re) ∈ positiveRectilinearHorizontalArcSet w a := by
  have hgen := OnLeConjecture.Analytic.braid_word_generatorIndices_eq_univ_of_endpoint_rotation
    (by omega : 0 < m) before after w.toSigned hw hc
  have hrows := positiveRectilinearWord_all_rows_occur hm w hgen
  rcases ht with ⟨j, ht⟩ | ⟨j, ht, hfixed | ⟨hout, hh⟩⟩
  · exact positiveRoundedWord_gap_mem_horizontalArc w hl hu hU hrows k 1 j ht
  · exact positiveRoundedWord_fixed_letter_mem_horizontalArc w hl hu hU hrows k 1 j ht
      hfixed.1 hfixed.2
  · exact positiveRoundedWord_moving_letter_mem_horizontalArc w hl hu hU k j ht hout hh

/-- The constructed row shear is exactly the assigned translation on each
literal horizontal straight portion of the retained rounded word. Its phase and
crossing depth remain unchanged. -/
theorem positiveRoundedWord_horizontal_shear_of_endpoint_rotation {m : ℕ} (hm : 2 ≤ m)
    (w : PositiveAdjacentWord m) (before after : Equiv.Perm (Fin m))
    (hw : before * w.permutation = after) (hc : after.trans (finRotate m) = before)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (g : Fin w.length × Fin 3 → ℝ) {q : ℂ × ℝ → ℝ}
    (hq : ∀ a p, p ∈ positiveRectilinearHorizontalArcSet w a →
      q p = g ((positiveRectilinearOutgoingArc w).symm a) -
        positiveRectilinearHorizontalArcRow w a)
    (k : Fin m) {t : ℝ} (ht : PositiveRoundedWordHorizontalParameter w U k t) :
    ∃ a : PositiveRectilinearHorizontalArc w,
      (((positiveRectilinearCylinderPoint w (positiveRoundedWord w l u k 1 t)).1 : ℂ),
        (positiveRoundedWord w l u k 1 t).2.re) ∈ positiveRectilinearHorizontalArcSet w a ∧
      let p := positiveRectilinearCylinderPoint w (positiveRoundedWord w l u k 1 t)
      (positiveGridRowShearCylinder q 1 p).1 = p.1 ∧
        (positiveGridRowShearCylinder q 1 p).2.re = g ((positiveRectilinearOutgoingArc w).symm a) ∧
        (positiveGridRowShearCylinder q 1 p).2.im = p.2.im := by
  obtain ⟨a, ha⟩ := positiveRoundedWord_horizontal_mem_of_endpoint_rotation hm w before after
    hw hc hl hu hU k ht
  exact ⟨a, ha, positiveRectilinearHorizontalArc_shear_row w g hq a _ ha⟩

/-- In the exceptional one-strand case the same rounded formula is exactly the
straight zero-height carrier, so its closure remains the coordinate unknot. -/
theorem positiveRoundedWord_one_strand (w : PositiveAdjacentWord 1)
    (l u : Fin w.length → ℝ → ℝ) (k : Fin 1) (s t : ℝ) :
    positiveRoundedWord w l u k s t = (t, 0) := by
  have hw := positiveAdjacentWord_one_eq_nil w
  subst w
  have hk : k = 0 := Subsingleton.elim _ _
  subst k
  have hgap (j : Fin 1) :
      positiveRectilinearWordGapFinal ([] : PositiveAdjacentWord 1) j 0 = 0 := by
    fin_cases j
    rfl
  simp [positiveRoundedWord, positiveRoundedWordDepth, positiveRoundedWordDepthNode,
    positiveRoundedWordDepthPath, hgap, positiveRoundedWordRankNode,
    OnLeConjecture.Analytic.finiteSmoothPathConcat, positiveWordPrefix]

/-- The one-strand rounded sphere curve is literally the coordinate great circle;
no interpretation of the empty marking set is used. -/
theorem positiveRoundedWord_one_strand_sphere (w : PositiveAdjacentWord 1)
    (l u : Fin w.length → ℝ → ℝ) (k : Fin 1) (i : Fin 2) (θ : ℝ) :
    OnLeConjecture.Analytic.planeSolidTorusMap i
      (positiveRectilinearCylinderPoint w
        (positiveRoundedWord w l u k 1 (positiveRoundedWordPeriodTime w θ))) =
      coordinateUnknotCircle i (Circle.exp θ) := by
  rw [positiveRoundedWord_one_strand, coordinateUnknotCircle_eq_solidTorus]
  congr 1
  apply Prod.ext
  · change Circle.exp (2 * Real.pi * positiveRoundedWordPeriodTime w θ /
      (2 * (w.length : ℝ) + 1)) = Circle.exp θ
    congr 1
    unfold positiveRoundedWordPeriodTime
    have hT : (2 * (w.length : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  · rfl

end OnLeConjecture.KnotTheory
