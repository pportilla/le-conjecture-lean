/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRectilinearWordMarkings
public import OnLeConjecture.KnotTheory.PositiveBraidGridRectilinearWordClosed

/-! # The actual compact horizontal arcs on the cylinder

Both endpoints of each horizontal arc are retained. The closing arc uses the
same base circle, so its two intervals at the period seam belong to one set.
-/

@[expose] public noncomputable section
open Set
open scoped Topology

namespace OnLeConjecture.KnotTheory

/-- Membership in the closed cyclic interval directed from `a` to `b`. -/
def PositiveRectilinearClosedCyclicBetween (a b x : ℝ) : Prop :=
  if a < b then a ≤ x ∧ x ≤ b else a ≤ x ∨ x ≤ b

theorem positiveRectilinearClosedCyclicBetween_isClosed (a b : ℝ) :
    IsClosed {x | PositiveRectilinearClosedCyclicBetween a b x} := by
  by_cases h : a < b
  · simpa only [PositiveRectilinearClosedCyclicBetween, if_pos h, inter_def, mem_Ici, mem_Iic] using
      (isClosed_Ici.inter isClosed_Iic : IsClosed (Ici a ∩ Iic b))
  · simpa only [PositiveRectilinearClosedCyclicBetween, if_neg h, union_def, mem_Ici, mem_Iic] using
      (isClosed_Ici.union isClosed_Iic : IsClosed (Ici a ∪ Iic b))

theorem positiveRectilinearClosedCyclicBetween_seam {T a b : ℝ}
    (ha : a ∈ Ioo 0 T) (hb : b ∈ Ioo 0 T) :
    PositiveRectilinearClosedCyclicBetween a b 0 ↔
      PositiveRectilinearClosedCyclicBetween a b T := by
  unfold PositiveRectilinearClosedCyclicBetween
  split_ifs <;> constructor <;> intro h
  · exact (ha.1.not_ge h.1).elim
  · exact (hb.2.not_ge h.2).elim
  · exact Or.inl ha.2.le
  · exact Or.inr hb.1.le

private theorem sorted_closed_gap_disjoint_of_lt
    (α : Type*) [Fintype α] [LinearOrder α] (A B : α → ℝ)
    (hAB : ∀ j, A j < B j) (hsep : ∀ j k, j < k → B j < A k)
    {j k : α} (hjk : j < k) :
    Disjoint {x | PositiveRectilinearClosedCyclicBetween (B j)
      (A (positiveRectilinearSortedSuccessor α j)) x}
      {x | PositiveRectilinearClosedCyclicBetween (B k)
        (A (positiveRectilinearSortedSuccessor α k)) x} := by
  have hAm : Monotone A := by
    intro p q hpq
    rcases hpq.lt_or_eq with h | rfl
    · exact ((hAB p).trans (hsep p q h)).le
    · exact le_rfl
  rcases positiveRectilinearSortedSuccessor_next α j with ⟨hjs, hleast⟩ | ⟨_, hb⟩
  swap
  · exact (hjk.not_ge (hb k).2).elim
  have hBj : B j < A (positiveRectilinearSortedSuccessor α j) := hsep _ _ hjs
  apply Set.disjoint_left.mpr
  intro x hxj hxk
  change PositiveRectilinearClosedCyclicBetween _ _ x at hxj hxk
  rw [PositiveRectilinearClosedCyclicBetween, if_pos hBj] at hxj
  have hxB : x < B k :=
    (hxj.2.trans (hAm (hleast k hjk))).trans_lt (hAB k)
  rcases positiveRectilinearSortedSuccessor_next α k with ⟨hks, _⟩ | ⟨hsk, hb⟩
  · rw [PositiveRectilinearClosedCyclicBetween, if_pos (hsep _ _ hks)] at hxk
    exact hxB.not_ge hxk.1
  · have hn : ¬ B k < A (positiveRectilinearSortedSuccessor α k) :=
      not_lt.mpr ((hAm hsk).trans (hAB k).le)
    rw [PositiveRectilinearClosedCyclicBetween, if_neg hn] at hxk
    rcases hxk with h | h
    · exact hxB.not_ge h
    · have hxj' : x < B j := (h.trans (hAm (hb j).1)).trans_lt (hAB j)
      exact hxj'.not_ge hxj.1

/-- The closed horizontal gaps between disjoint ordered occurrence intervals are disjoint. -/
theorem sorted_closed_gap_disjoint
    (α : Type*) [Fintype α] [LinearOrder α] (A B : α → ℝ)
    (hAB : ∀ j, A j < B j) (hsep : ∀ j k, j < k → B j < A k)
    {j k : α} (hjk : j ≠ k) :
    Disjoint {x | PositiveRectilinearClosedCyclicBetween (B j)
      (A (positiveRectilinearSortedSuccessor α j)) x}
      {x | PositiveRectilinearClosedCyclicBetween (B k)
        (A (positiveRectilinearSortedSuccessor α k)) x} := by
  rcases lt_or_gt_of_ne hjk with h | h
  · exact sorted_closed_gap_disjoint_of_lt α A B hAB hsep h
  · exact (sorted_closed_gap_disjoint_of_lt α A B hAB hsep h).symm

/-- The source parameters of one literal closed horizontal arc. -/
def positiveRectilinearHorizontalArcParameters {m : ℕ} (w : PositiveAdjacentWord m)
    (a : PositiveRectilinearHorizontalArc w) : Set ℝ :=
  Icc 0 (2 * (w.length : ℝ) + 1) ∩
    {x | PositiveRectilinearClosedCyclicBetween (positiveRectilinearHorizontalArcStart w a)
      (positiveRectilinearHorizontalArcEnd w a) x}

/-- Projected base and row coordinates of the entire horizontal arc. -/
def positiveRectilinearHorizontalArcSet {m : ℕ} (w : PositiveAdjacentWord m)
    (a : PositiveRectilinearHorizontalArc w) : Set (ℂ × ℝ) :=
  (fun x : ℝ => ((Circle.exp (2 * Real.pi * x / (2 * (w.length : ℝ) + 1)) : ℂ),
    positiveRectilinearHorizontalArcRow w a)) '' positiveRectilinearHorizontalArcParameters w a

theorem positiveRectilinearHorizontalArcSet_isCompact {m : ℕ} (w : PositiveAdjacentWord m)
    (a : PositiveRectilinearHorizontalArc w) :
    IsCompact (positiveRectilinearHorizontalArcSet w a) := by
  have hpar : IsCompact (positiveRectilinearHorizontalArcParameters w a) :=
    isCompact_Icc.inter_right (positiveRectilinearClosedCyclicBetween_isClosed _ _)
  apply hpar.image
  exact ((continuous_subtype_val.comp Circle.exp.continuous).comp
    ((continuous_const.mul continuous_id).div_const _)).prodMk continuous_const

theorem positiveRectilinearWordColumn_mem_period {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) (c : Fin 3) :
    positiveRectilinearWordColumn w j c ∈ Ioo 0 (2 * (w.length : ℝ) + 1) := by
  have hj : (j.val : ℝ) + 1 ≤ w.length := by exact_mod_cast j.isLt
  have hj0 : (0 : ℝ) ≤ j.val := by positivity
  fin_cases c <;> norm_num [positiveRectilinearWordColumn, positiveGridRectilinearColumns]
  all_goals constructor <;> linarith

theorem positiveRectilinearHorizontalArc_endpoints_mem_period {m : ℕ}
    (w : PositiveAdjacentWord m) (a : PositiveRectilinearHorizontalArc w) :
    positiveRectilinearHorizontalArcStart w a ∈ Ioo 0 (2 * (w.length : ℝ) + 1) ∧
      positiveRectilinearHorizontalArcEnd w a ∈ Ioo 0 (2 * (w.length : ℝ) + 1) :=
  ⟨positiveRectilinearWordColumn_mem_period w _ _, positiveRectilinearWordColumn_mem_period w _ _⟩

private theorem half_integer_row_ne {n k : ℕ} : (n : ℝ) + 1 / 2 ≠ k := by
  intro h
  have he : 2 * n + 1 = 2 * k := by
    have he' : (2 : ℝ) * n + 1 = 2 * k := by linarith
    exact_mod_cast he'
  omega

/-- Distinct horizontal arcs with the same old row have disjoint closed parameter sets. -/
theorem positiveRectilinearHorizontalArcParameters_disjoint_of_row_eq {m : ℕ}
    (w : PositiveAdjacentWord m) {a b : PositiveRectilinearHorizontalArc w}
    (hab : a ≠ b) (hrow : positiveRectilinearHorizontalArcRow w a =
      positiveRectilinearHorizontalArcRow w b) :
    Disjoint (positiveRectilinearHorizontalArcParameters w a)
      (positiveRectilinearHorizontalArcParameters w b) := by
  rcases a with j | ⟨r, j⟩ <;> rcases b with k | ⟨s, k⟩
  · have hjk : j ≠ k := fun h => hab (congrArg Sum.inl h)
    have hinterval (i : Fin w.length) :
        positiveRectilinearWordColumn w i 0 < positiveRectilinearWordColumn w i 2 := by
      norm_num [positiveRectilinearWordColumn, positiveGridRectilinearColumns, Matrix.cons_val_two]
    have hdis : Disjoint (Icc (positiveRectilinearWordColumn w j 0)
        (positiveRectilinearWordColumn w j 2))
        (Icc (positiveRectilinearWordColumn w k 0) (positiveRectilinearWordColumn w k 2)) := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      rcases lt_or_gt_of_ne hjk with h | h
      · exact (positiveRectilinearWordColumn_lt w h 2 0).not_ge (hy.1.trans hx.2)
      · exact (positiveRectilinearWordColumn_lt w h 2 0).not_ge (hx.1.trans hy.2)
    apply hdis.mono
    all_goals
      intro x hx
      simpa only [positiveRectilinearHorizontalArcParameters, mem_inter_iff,
        positiveRectilinearHorizontalArcStart_middle, positiveRectilinearHorizontalArcEnd_middle,
        PositiveRectilinearClosedCyclicBetween, if_pos (hinterval _), mem_Icc,
        mem_ofPred_eq] using hx.2
  · exact (half_integer_row_ne hrow).elim
  · exact (half_integer_row_ne hrow.symm).elim
  · have hrs : r = s := Fin.ext (Nat.cast_injective hrow)
    subst s
    have hjk : j ≠ k := by
      intro h
      subst k
      exact hab rfl
    apply (sorted_closed_gap_disjoint (PositiveRectilinearRowOccurrences w r)
      (positiveRectilinearIntegerRowIn w r) (positiveRectilinearIntegerRowOut w r)
      (positiveRectilinearIntegerRowIn_lt_out w r)
      (fun _ _ h => positiveRectilinearIntegerRowOut_lt_in w r h) hjk).mono
    all_goals
      intro x hx
      simpa only [positiveRectilinearHorizontalArcStart_integer,
        positiveRectilinearHorizontalArcEnd_integer] using hx.2

/-- The actual closed horizontal arcs are pairwise disjoint on the base-row cylinder.
The two endpoints of the base period are explicitly identified. -/
theorem positiveRectilinearHorizontalArcSet_disjoint {m : ℕ}
    (w : PositiveAdjacentWord m) {a b : PositiveRectilinearHorizontalArc w} (hab : a ≠ b) :
    Disjoint (positiveRectilinearHorizontalArcSet w a)
      (positiveRectilinearHorizontalArcSet w b) := by
  apply Set.disjoint_left.mpr
  intro p hp hq
  obtain ⟨x, hx, rfl⟩ := hp
  obtain ⟨y, hy, he⟩ := hq
  have hrow : positiveRectilinearHorizontalArcRow w a = positiveRectilinearHorizontalArcRow w b :=
    (congrArg Prod.snd he).symm
  have hd := positiveRectilinearHorizontalArcParameters_disjoint_of_row_eq w hab hrow
  have hphase : Circle.exp (2 * Real.pi * x / (2 * (w.length : ℝ) + 1)) =
      Circle.exp (2 * Real.pi * y / (2 * (w.length : ℝ) + 1)) :=
    Subtype.ext (congrArg Prod.fst he).symm
  rcases (circle_exp_scaled_eq_iff (by positivity) hx.1 hy.1).mp hphase with
    hxy | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · subst y
    exact Set.disjoint_left.mp hd hx hy
  · have hs := positiveRectilinearHorizontalArc_endpoints_mem_period w b
    have hb0 := (positiveRectilinearClosedCyclicBetween_seam hs.1 hs.2).mpr hy.2
    exact Set.disjoint_left.mp hd hx ⟨hx.1, hb0⟩
  · have hs := positiveRectilinearHorizontalArc_endpoints_mem_period w b
    have hbT := (positiveRectilinearClosedCyclicBetween_seam hs.1 hs.2).mp hy.2
    exact Set.disjoint_left.mp hd hx ⟨hx.1, hbT⟩

end OnLeConjecture.KnotTheory
