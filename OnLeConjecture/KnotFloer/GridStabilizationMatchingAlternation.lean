/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingHeight

/-!
# Successive internal matching transitions

Empty internal rectangles cannot move the matching-row positions twice in the
same direction. The proof locates the two other corner points in the two rectangles.
-/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti

private theorem three_cuts {n : ℕ} {a p q k l : Fin n}
    (h1 : a ∈ Grid.cIco q p) (h2 : a ∈ Grid.cIco k q)
    (h3 : a ∈ Grid.cIco l k) :
    l ∈ Grid.cIoo k p ∧ p ∈ Grid.cIoo l q := by
  simp only [Grid.mem_cIco, Grid.mem_cIoo, ne_eq, Fin.ext_iff] at *
  split_ifs at * <;> omega

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- Two consecutive empty nonmatching transitions cannot both advance the row positions. -/
theorem stabilizationMatchingTransition_not_two_advancing
    (x z w : StabilizationMatchingNode G s) (hxz : x ≠ z) (hzw : z ≠ w)
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z))
    (t : GridRectangleBetween z.val (stabilizationMatchingTargetState G s w))
    (hr : r.IsEmpty) (ht : t.IsEmpty)
    (hrtop : r.top = (G.X s).castSucc) (httop : t.top = (G.X s).castSucc) : False := by
  have rc := stabilizationMatchingTransition_advancing_columns G s x z hxz r hrtop
  have tc := stabilizationMatchingTransition_advancing_columns G s z w hzw t httop
  have hxs := x.property.1
  have hzs := z.property.1
  have hws := w.property.1
  change s.castSucc ∈ Grid.cIco (x.val.transpose (G.X s).succ)
    (x.val.transpose (G.X s).castSucc) at hxs
  change s.castSucc ∈ Grid.cIco (z.val.transpose (G.X s).succ)
    (z.val.transpose (G.X s).castSucc) at hzs
  change s.castSucc ∈ Grid.cIco (w.val.transpose (G.X s).succ)
    (w.val.transpose (G.X s).castSucc) at hws
  rw [rc.2.2] at hzs
  rw [tc.2.2] at hws
  have hc := three_cuts hxs hzs hws
  have htl : t.left ∈ Grid.cIoo r.left r.right := by
    simpa only [rc.1, rc.2.1, tc.2.1] using hc.1
  have hrr : r.right ∈ Grid.cIoo t.left t.right := by
    simpa only [rc.1, tc.2.1, tc.1, rc.2.2] using hc.2
  have rb0 : r.bottom ≠ (G.X s).castSucc := fun h => r.bottom_ne_top (h.trans hrtop.symm)
  have rb1 : r.bottom ≠ (G.X s).succ := fun h =>
    stabilizationMatchingTransition_not_both_rows G s x z hxz r (Or.inr hrtop) (Or.inl h)
  have tb0 : t.bottom ≠ (G.X s).castSucc := fun h => t.bottom_ne_top (h.trans httop.symm)
  have tb1 : t.bottom ≠ (G.X s).succ := fun h =>
    stabilizationMatchingTransition_not_both_rows G s z w hzw t (Or.inr httop) (Or.inl h)
  have hzr : z.val r.right = r.bottom := by
    have h := r.map_right
    change Equiv.swap (G.X s).castSucc (G.X s).succ (z.val r.right) = r.bottom at h
    rwa [Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne rb0 rb1] at h
  have hxl : x.val t.left = t.bottom := by
    have h := r.map_of_ne t.left (Grid.ne_left_of_mem_cIoo htl) (Grid.ne_right_of_mem_cIoo htl)
    change Equiv.swap (G.X s).castSucc (G.X s).succ (z.val t.left) = x.val t.left at h
    change Equiv.swap (G.X s).castSucc (G.X s).succ t.bottom = x.val t.left at h
    rw [Equiv.swap_apply_of_ne_of_ne tb0 tb1] at h
    exact h.symm
  have htr : t.bottom ≠ r.bottom := by
    intro h
    have heq : z.val t.left = z.val r.right := h.trans hzr.symm
    exact Grid.ne_left_of_mem_cIoo hrr (z.val.toPerm.injective heq).symm
  have hnot_t : t.bottom ∉ Grid.cIoo r.bottom (G.X s).castSucc := by
    have h := (r.isEmpty_iff_forall_notMem_cIoo.mp hr) t.left htl
    simpa only [hxl, ← r.bottom_def, ← r.top_def, hrtop] using h
  have hnot_r : r.bottom ∉ Grid.cIoo t.bottom (G.X s).castSucc := by
    have h := (t.isEmpty_iff_forall_notMem_cIoo.mp ht) r.right hrr
    simpa only [hzr, ← t.bottom_def, ← t.top_def, httop] using h
  exact hnot_r (Grid.mem_cIoo_cyclic_left
    (Grid.mem_cIoo_swap_of_notMem rb0 htr tb0 hnot_t))

/-- Two consecutive empty nonmatching transitions cannot both retreat the row positions. -/
theorem stabilizationMatchingTransition_not_two_retreating
    (x z w : StabilizationMatchingNode G s) (hxz : x ≠ z) (hzw : z ≠ w)
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z))
    (t : GridRectangleBetween z.val (stabilizationMatchingTargetState G s w))
    (hr : r.IsEmpty) (ht : t.IsEmpty)
    (hrbot : r.bottom = (G.X s).succ) (htbot : t.bottom = (G.X s).succ) : False := by
  have rc := stabilizationMatchingTransition_retreating_columns G s x z hxz r hrbot
  have tc := stabilizationMatchingTransition_retreating_columns G s z w hzw t htbot
  have hxs := x.property.1
  have hzs := z.property.1
  have hws := w.property.1
  change s.castSucc ∈ Grid.cIco (x.val.transpose (G.X s).succ)
    (x.val.transpose (G.X s).castSucc) at hxs
  change s.castSucc ∈ Grid.cIco (z.val.transpose (G.X s).succ)
    (z.val.transpose (G.X s).castSucc) at hzs
  change s.castSucc ∈ Grid.cIco (w.val.transpose (G.X s).succ)
    (w.val.transpose (G.X s).castSucc) at hws
  rw [rc.2.2] at hzs
  rw [tc.2.2] at hws
  have hc := three_cuts hws hzs hxs
  have htr : t.right ∈ Grid.cIoo r.left r.right := by
    simpa only [rc.1, rc.2.1, tc.2.1] using hc.2
  have hrl : r.left ∈ Grid.cIoo t.left t.right := by
    simpa only [rc.1, tc.2.1, tc.1, rc.2.2] using hc.1
  have rt0 : r.top ≠ (G.X s).castSucc := fun h =>
    stabilizationMatchingTransition_not_both_rows G s x z hxz r (Or.inr h) (Or.inl hrbot)
  have rt1 : r.top ≠ (G.X s).succ := fun h => r.bottom_ne_top (hrbot.trans h.symm)
  have tt0 : t.top ≠ (G.X s).castSucc := fun h =>
    stabilizationMatchingTransition_not_both_rows G s z w hzw t (Or.inr h) (Or.inl htbot)
  have tt1 : t.top ≠ (G.X s).succ := fun h => t.bottom_ne_top (htbot.trans h.symm)
  have hzl : z.val r.left = r.top := by
    have h := r.map_left
    change Equiv.swap (G.X s).castSucc (G.X s).succ (z.val r.left) = r.top at h
    rwa [Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne rt0 rt1] at h
  have hxr : x.val t.right = t.top := by
    have h := r.map_of_ne t.right (Grid.ne_left_of_mem_cIoo htr) (Grid.ne_right_of_mem_cIoo htr)
    change Equiv.swap (G.X s).castSucc (G.X s).succ (z.val t.right) = x.val t.right at h
    change Equiv.swap (G.X s).castSucc (G.X s).succ t.top = x.val t.right at h
    rw [Equiv.swap_apply_of_ne_of_ne tt0 tt1] at h
    exact h.symm
  have htr_ne : t.top ≠ r.top := by
    intro h
    have heq : z.val t.right = z.val r.left := h.trans hzl.symm
    exact Grid.ne_right_of_mem_cIoo hrl (z.val.toPerm.injective heq).symm
  have hnot_t : t.top ∉ Grid.cIoo (G.X s).succ r.top := by
    have h := (r.isEmpty_iff_forall_notMem_cIoo.mp hr) t.right htr
    simpa only [hxr, ← r.bottom_def, ← r.top_def, hrbot] using h
  have hnot_r : r.top ∉ Grid.cIoo (G.X s).succ t.top := by
    have h := (t.isEmpty_iff_forall_notMem_cIoo.mp ht) r.left hrl
    simpa only [hzl, ← t.bottom_def, ← t.top_def, htbot] using h
  exact hnot_r (Grid.mem_cIoo_cyclic_right
    (Grid.mem_cIoo_swap_of_notMem (Ne.symm rt1) tt1 htr_ne hnot_t))

/-- Every pair of consecutive empty nonmatching transitions has opposite orientations. -/
theorem stabilizationMatchingTransition_alternates
    (x z w : StabilizationMatchingNode G s) (hxz : x ≠ z) (hzw : z ≠ w)
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z))
    (t : GridRectangleBetween z.val (stabilizationMatchingTargetState G s w))
    (hr : r.IsEmpty) (ht : t.IsEmpty) :
    (r.top = (G.X s).castSucc ∧ t.bottom = (G.X s).succ) ∨
      (r.bottom = (G.X s).succ ∧ t.top = (G.X s).castSucc) := by
  rcases stabilizationMatchingTransition_oriented_row_edge G s x z hxz r hr with h | h
  · rcases stabilizationMatchingTransition_oriented_row_edge G s z w hzw t ht with k | k
    · exact False.elim (stabilizationMatchingTransition_not_two_advancing
        G s x z w hxz hzw r t hr ht h k)
    · exact Or.inl ⟨h, k⟩
  · rcases stabilizationMatchingTransition_oriented_row_edge G s z w hzw t ht with k | k
    · exact Or.inr ⟨h, k⟩
    · exact False.elim (stabilizationMatchingTransition_not_two_retreating
        G s x z w hxz hzw r t hr ht h k)

end OnLeConjecture.KnotFloer.GridFull
