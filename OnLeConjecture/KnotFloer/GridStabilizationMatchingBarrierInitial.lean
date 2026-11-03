/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingBarrier
public import OnLeConjecture.KnotFloer.GridStabilizationMatchingCenterPath

/-! # The barrier formed by the first two internal matching rectangles -/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti

private theorem earlier_point_ne {n : ℕ} {b L p c : Fin n}
    (hL : L ∈ Grid.cIoo b p) (hc : c ∈ Grid.cIoo b L) : c ≠ p :=
  Grid.ne_right_of_mem_cIoo (Grid.cIoo_subset_cIoo_right_of_mem_cIoo hL hc)

private theorem later_point_ne {n : ℕ} {b p R c : Fin n}
    (hp : p ∈ Grid.cIoo b R) (hc : c ∈ Grid.cIoo R b) : c ≠ p := by
  simp only [Grid.mem_cIoo, ne_eq, Fin.ext_iff] at *
  split_ifs at * <;> omega

private theorem outer_final_mem {n : ℕ} {b L R c : Fin n}
    (hL : L ∈ Grid.cIoo b R) (hc : c ∈ Grid.cIoo R b) : c ∈ Grid.cIoo R L := by
  simp only [Grid.mem_cIoo, ne_eq, Fin.ext_iff] at *
  split_ifs at * <;> omega

private theorem low_not_high {n : ℕ} (q : Fin n) {u v w : Fin (n + 1)}
    (hu : u ∈ Grid.cIoo q.succ v) (hw : w ∈ Grid.cIoo q.succ u) :
    w ∉ Grid.cIoo v q.castSucc := by
  simp only [Grid.mem_cIoo, ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc] at *
  split_ifs at * <;> omega

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- Points off the two rectangle columns and the matching rows remain unchanged. -/
theorem stabilizationMatchingTransition_apply_of_ne
    (x z : StabilizationMatchingNode G s)
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z))
    (c : Fin (n + 1))
    (h0 : c ≠ x.val.transpose (G.X s).castSucc)
    (h1 : c ≠ x.val.transpose (G.X s).succ)
    (hl : c ≠ r.left) (hr : c ≠ r.right) : z.val c = x.val c := by
  have hv0 : x.val c ≠ (G.X s).castSucc := fun h =>
    h0 ((x.val.transpose_apply_apply c).symm.trans (congrArg x.val.transpose h))
  have hv1 : x.val c ≠ (G.X s).succ := fun h =>
    h1 ((x.val.transpose_apply_apply c).symm.trans (congrArg x.val.transpose h))
  have h := r.map_of_ne c hl hr
  change Equiv.swap (G.X s).castSucc (G.X s).succ (z.val c) = x.val c at h
  rwa [Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne hv0 hv1] at h

/-- The first advance turns the old lower-row point into a fixed lower barrier. -/
theorem stabilizationMatchingEntry_advance_lower
    (a : GridState n) (x z : StabilizationMatchingNode G s) (hxz : x ≠ z)
    (e : GridRectangleBetween (a.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s x))
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z))
    (he : e.IsEmpty) (hr : r.IsEmpty) (ht : r.top = (G.X s).castSucc) :
    x.val.transpose (G.X s).castSucc ∈
        Grid.cIoo s.succ (z.val.transpose (G.X s).castSucc) ∧
      (∀ c, c = x.val.transpose (G.X s).castSucc ∨
        c ∈ Grid.cIoo s.succ (x.val.transpose (G.X s).castSucc) →
        z.val c ∉ Grid.cIoo (G.X s).succ (z.val s.succ)) ∧
      z.val (x.val.transpose (G.X s).castSucc) = r.bottom := by
  have rc := stabilizationMatchingTransition_advancing_columns G s x z hxz r ht
  have hxcols := (stabilizationMatchingNode_row_columns_interior G s x).1
  have hzcols := (stabilizationMatchingNode_row_columns_interior G s z).1
  have hL : x.val.transpose (G.X s).castSucc ∈
      Grid.cIoo s.succ (z.val.transpose (G.X s).castSucc) := by
    simpa only [rc.2.2] using hxcols
  have hLR := Grid.cIoo_subset_cIoo_right_of_mem_cIoo hzcols hL
  have hb0 : r.bottom ≠ (G.X s).castSucc := fun h => r.bottom_ne_top (h.trans ht.symm)
  have hb1 : r.bottom ≠ (G.X s).succ := fun h =>
    stabilizationMatchingTransition_not_both_rows G s x z hxz r (Or.inr ht) (Or.inl h)
  have hv : z.val (x.val.transpose (G.X s).castSucc) = r.bottom := by
    have h := r.map_right
    change Equiv.swap (G.X s).castSucc (G.X s).succ (z.val r.right) = r.bottom at h
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne hb0 hb1, rc.1] at h
    exact h
  have hu := stabilizationMatchingTransition_newColumn G s x z r
  have hhigh := stabilizationMatchingTransition_advancing_height G s x z hxz r hr ht
  refine ⟨hL, ?_, hv⟩
  intro c hc
  rcases hc with rfl | hc
  · rw [hv, ← hu]
    exact Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap _ _)
      (Grid.mem_cIoo_cyclic_left hhigh)
  · have hfixed : z.val c = x.val c := by
      apply stabilizationMatchingTransition_apply_of_ne G s x z r c
        (Grid.ne_right_of_mem_cIoo hc) (earlier_point_ne hxcols hc)
      · rw [rc.2.1]
        exact earlier_point_ne hLR hc
      · rw [rc.1]
        exact Grid.ne_right_of_mem_cIoo hc
    rw [hfixed, ← hu]
    exact stabilizationMatchingEntry_empty_region G s a x e he c hc

/-- An entry followed by an advance and a retreat forms the persistent two-point barrier. -/
theorem stabilizationMatchingBarrier_of_entry_advance_retreat
    (a : GridState n) (x z w : StabilizationMatchingNode G s)
    (hxz : x ≠ z) (hzw : z ≠ w)
    (e : GridRectangleBetween (a.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s x))
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z))
    (t : GridRectangleBetween z.val (stabilizationMatchingTargetState G s w))
    (he : e.IsEmpty) (hr : r.IsEmpty) (ht : t.IsEmpty)
    (hrt : r.top = (G.X s).castSucc) (htb : t.bottom = (G.X s).succ) :
    StabilizationMatchingBarrier G s (x.val.transpose (G.X s).castSucc)
      (z.val.transpose (G.X s).succ) w := by
  let L := x.val.transpose (G.X s).castSucc
  let R := z.val.transpose (G.X s).succ
  change StabilizationMatchingBarrier G s L R w
  have rc := stabilizationMatchingTransition_advancing_columns G s x z hxz r hrt
  have tc := stabilizationMatchingTransition_retreating_columns G s z w hzw t htb
  have hlow := stabilizationMatchingEntry_advance_lower G s a x z hxz e r he hr hrt
  have hL : L ∈ Grid.cIoo s.succ (z.val.transpose (G.X s).castSucc) := hlow.1
  have hclear : ∀ c, c = L ∨ c ∈ Grid.cIoo s.succ L →
      z.val c ∉ Grid.cIoo (G.X s).succ (z.val s.succ) := hlow.2.1
  have hzLR : L ∈ Grid.cIoo s.succ R :=
    Grid.cIoo_subset_cIoo_right_of_mem_cIoo
      (stabilizationMatchingNode_row_columns_interior G s z).1 hL
  have hz0R : z.val.transpose (G.X s).castSucc ∈ Grid.cIoo s.succ R :=
    (stabilizationMatchingNode_row_columns_interior G s z).1
  have hupper : w.val.transpose (G.X s).succ ∈ Grid.cIoo s.succ R := by
    simpa only [tc.2.2] using hz0R
  have hw0R : w.val.transpose (G.X s).castSucc ∈ Grid.cIoo s.succ R :=
    Grid.cIoo_subset_cIoo_right_of_mem_cIoo hupper
      (stabilizationMatchingNode_row_columns_interior G s w).1
  have hu := stabilizationMatchingTransition_newColumn G s z w t
  have hwfixed := stabilizationMatchingTransition_fixed_initial_interval
    G s z w hzw t ht L hL hclear
  have hwL : w.val L = r.bottom := (hwfixed L (Or.inl rfl)).trans hlow.2.2
  have tt0 : t.top ≠ (G.X s).castSucc := fun h =>
    stabilizationMatchingTransition_not_both_rows G s z w hzw t (Or.inr h) (Or.inl htb)
  have tt1 : t.top ≠ (G.X s).succ := fun h => t.bottom_ne_top (htb.trans h.symm)
  have hwR : w.val R = t.top := by
    have h := t.map_left
    change Equiv.swap (G.X s).castSucc (G.X s).succ (w.val t.left) = t.top at h
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne tt0 tt1, tc.1] at h
    exact h
  have hhigh := stabilizationMatchingTransition_advancing_height G s x z hxz r hr hrt
  have htlow := stabilizationMatchingTransition_retreating_height G s z w hzw t ht htb
  refine ⟨stabilizationMatchingTransition_preserves_lower_barrier
      G s z w hzw t ht L hL hclear, hupper, ?_, ?_, ?_⟩
  · intro c hc
    simpa only [hwfixed c hc, ← hu] using hclear c hc
  · intro c hc
    rw [hwL]
    rcases hc with rfl | hc
    · rw [hwR]
      apply low_not_high (G.X s) hhigh
      simpa only [stabilizationMatchingTransition_newColumn G s x z r] using htlow
    · have hwc : w.val c = z.val c := by
        apply stabilizationMatchingTransition_apply_of_ne G s z w t c
          (later_point_ne hz0R hc) (Grid.ne_left_of_mem_cIoo hc)
        · rw [tc.1]
          exact Grid.ne_left_of_mem_cIoo hc
        · rw [tc.2.1]
          exact later_point_ne hw0R hc
      have hxc : z.val c = x.val c := by
        have hx1R : x.val.transpose (G.X s).succ ∈ Grid.cIoo s.succ R := by
          simpa only [rc.2.2] using hz0R
        apply stabilizationMatchingTransition_apply_of_ne G s x z r c
          (later_point_ne hzLR hc) (later_point_ne hx1R hc)
        · rw [rc.2.1]
          exact Grid.ne_left_of_mem_cIoo hc
        · rw [rc.1]
          exact later_point_ne hzLR hc
      rw [hwc, hxc]
      have hc' : c ∈ Grid.cIoo r.left r.right := by
        simpa only [rc.1, rc.2.1] using outer_final_mem hzLR hc
      have hh := (r.isEmpty_iff_forall_notMem_cIoo.mp hr) c hc'
      simpa only [hrt] using hh
  · simpa only [hwR, ← hu] using htlow

/-- Two internal rectangles after an empty entry already create a persistent barrier. -/
theorem stabilizationMatchingBarrier_of_entry_two_steps
    (a : GridState n) (x z w : StabilizationMatchingNode G s)
    (hxz : x ≠ z) (hzw : z ≠ w)
    (e : GridRectangleBetween (a.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s x))
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z))
    (t : GridRectangleBetween z.val (stabilizationMatchingTargetState G s w))
    (he : e.IsEmpty) (hr : r.IsEmpty) (ht : t.IsEmpty) :
    StabilizationMatchingBarrier G s (x.val.transpose (G.X s).castSucc)
      (z.val.transpose (G.X s).succ) w := by
  have hrt := stabilizationMatchingEntry_advancing G s a x z hxz e r he hr
  have htb : t.bottom = (G.X s).succ := by
    rcases stabilizationMatchingTransition_oriented_row_edge G s z w hzw t ht with h | h
    · exact False.elim (stabilizationMatchingTransition_not_two_advancing
        G s x z w hxz hzw r t hr ht hrt h)
    · exact h
  exact stabilizationMatchingBarrier_of_entry_advance_retreat
    G s a x z w hxz hzw e r t he hr ht hrt htb

end OnLeConjecture.KnotFloer.GridFull
