/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingShortRectangle

/-!
# The matching entry determined by an admissible center rectangle

Every admissible rectangle containing the inserted center determines an actual
internal matching node and an empty entry rectangle ending at its matching target.
-/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti

private theorem predecessor_mem_cIco_of_successor_mem {n : ℕ} (q : Fin n)
    {v u : Fin (n + 1)} (h : q.succ ∈ Grid.cIoo v u) : q.castSucc ∈ Grid.cIco v u := by
  simp only [Grid.mem_cIoo, Grid.mem_cIco, ne_eq, Fin.ext_iff,
    Fin.val_castSucc, Fin.val_succ] at *
  split_ifs at * <;> omega

private theorem cut_mem_after_outer_point {n : ℕ} (a : Fin n) {l p q : Fin (n + 1)}
    (hb : a.succ ∈ Grid.cIoo l p) (hq : q ∉ Grid.cIoo l p) (hqp : q ≠ p) :
    a.castSucc ∈ Grid.cIco q p := by
  simp only [Grid.mem_cIoo, Grid.mem_cIco, ne_eq, Fin.ext_iff,
    Fin.val_castSucc, Fin.val_succ] at *
  split_ifs at * <;> omega

private theorem transpose_eq_of_apply_eq {n : ℕ} (x : GridState n) {c q : Fin n}
    (h : x c = q) : x.transpose q = c :=
  (congrArg x.transpose h.symm).trans (x.transpose_apply_apply c)

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) {x y : GridState n}
variable (r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
  (y.insertPoint s.succ (G.X s).succ))

/-- The first internal state, before verifying its matching-source conditions. -/
def stabilizationRectangleEntryState : GridState (n + 1) :=
  ((x.insertPoint s.succ (G.X s).succ).swapColumns s.succ r.right).swapRows
    (G.X s).castSucc (G.X s).succ

/-- The lower matching row occurs at the terminal side of the original rectangle. -/
theorem stabilizationRectangleEntryState_lowerColumn :
    (stabilizationRectangleEntryState G s r).transpose (G.X s).castSucc = r.right := by
  apply transpose_eq_of_apply_eq
  simp only [stabilizationRectangleEntryState, GridState.swapRows_apply,
    GridState.swapColumns_apply, Equiv.swap_apply_right,
    GridState.insertPoint_apply_newColumn]

variable (ha : StabilizationAdmissibleRectangle G s r)
  (hi : (s.succ, (G.X s).succ) ∈ r.toGridRectangle.interior)

include hi in
/-- The top side misses both matching rows when the inserted center lies inside. -/
theorem stabilizationRectangle_top_ne_matching_rows :
    r.top ≠ (G.X s).castSucc ∧ r.top ≠ (G.X s).succ := by
  have hrow := ((GridRectangleBetween.mem_toGridRectangle_interior r).mp hi).2
  change (G.X s).succ ∈ Grid.cIoo r.bottom r.top at hrow
  have hpred := predecessor_mem_cIco_of_successor_mem (G.X s) hrow
  exact ⟨fun h => Grid.right_notMem_cIco _ _ (h ▸ hpred),
    Ne.symm (Grid.ne_right_of_mem_cIoo hrow)⟩

include ha hi in
/-- The lower-row point of the source is not an interior column of the admissible rectangle. -/
theorem stabilizationRectangle_lower_point_not_interior :
    (x.insertPoint s.succ (G.X s).succ).transpose (G.X s).castSucc ∉
      Grid.cIoo r.left r.right := by
  intro hc
  have hrow := ((GridRectangleBetween.mem_toGridRectangle_interior r).mp hi).2
  change (G.X s).succ ∈ Grid.cIoo r.bottom r.top at hrow
  have hpred := predecessor_mem_cIco_of_successor_mem (G.X s) hrow
  have hbot : (G.X s).castSucc ≠ r.bottom := by
    intro h
    have hp := transpose_eq_of_apply_eq (x.insertPoint s.succ (G.X s).succ) h.symm
    exact Grid.ne_left_of_mem_cIoo hc hp
  have hp := ha _ hc (by
    simpa only [GridState.apply_transpose_apply, ← r.bottom_def, ← r.top_def] using
      Grid.mem_cIoo_of_mem_cIco hpred hbot)
  have hv := congrArg (x.insertPoint s.succ (G.X s).succ) hp
  simp only [GridState.apply_transpose_apply, GridState.insertPoint_apply_newColumn] at hv
  exact Fin.castSucc_lt_succ.ne hv

include hi in
/-- The upper matching row occurs at the original source's lower-row column. -/
theorem stabilizationRectangleEntryState_upperColumn :
    (stabilizationRectangleEntryState G s r).transpose (G.X s).succ =
      (x.insertPoint s.succ (G.X s).succ).transpose (G.X s).castSucc := by
  let X := x.insertPoint s.succ (G.X s).succ
  have hn := stabilizationRectangle_top_ne_matching_rows G s r hi
  have hqb : X.transpose (G.X s).castSucc ≠ s.succ := by
    intro h
    have hv := congrArg X h
    simp only [X, GridState.apply_transpose_apply, GridState.insertPoint_apply_newColumn] at hv
    exact Fin.castSucc_lt_succ.ne hv
  have hqp : X.transpose (G.X s).castSucc ≠ r.right := by
    intro h
    have hv := congrArg X h
    rw [GridState.apply_transpose_apply] at hv
    exact hn.1 hv.symm
  dsimp only [X] at hqb hqp
  apply transpose_eq_of_apply_eq
  simp only [stabilizationRectangleEntryState, GridState.swapRows_apply,
    GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hqb hqp,
    GridState.apply_transpose_apply, Equiv.swap_apply_left]

include hi in
/-- The new-column point of the entry node is the original top row. -/
theorem stabilizationRectangleEntryState_newColumn :
    stabilizationRectangleEntryState G s r s.succ = r.top := by
  have hn := stabilizationRectangle_top_ne_matching_rows G s r hi
  simp only [stabilizationRectangleEntryState, GridState.swapRows_apply,
    GridState.swapColumns_apply, Equiv.swap_apply_left, ← r.top_def,
    Equiv.swap_apply_of_ne_of_ne hn.1 hn.2]

include ha hi in
/-- The entry state satisfies the row-matching source condition. -/
theorem stabilizationRectangleEntryState_source :
    RowMatchingSource s (G.X s) (stabilizationRectangleEntryState G s r) := by
  change s.castSucc ∈ Grid.cIco _ _
  rw [stabilizationRectangleEntryState_lowerColumn,
    stabilizationRectangleEntryState_upperColumn G s r hi]
  apply cut_mem_after_outer_point s
    ((GridRectangleBetween.mem_toGridRectangle_interior r).mp hi).1
    (stabilizationRectangle_lower_point_not_interior G s r ha hi)
  intro h
  have hv := congrArg (x.insertPoint s.succ (G.X s).succ) h
  rw [GridState.apply_transpose_apply] at hv
  exact (stabilizationRectangle_top_ne_matching_rows G s r hi).1 hv.symm

/-- The concrete first node of the matching path associated to the admissible rectangle. -/
noncomputable def stabilizationRectangleEntryNode : StabilizationMatchingNode G s :=
  ⟨stabilizationRectangleEntryState G s r,
    stabilizationRectangleEntryState_source G s r ha hi,
    fun h => (stabilizationRectangle_top_ne_matching_rows G s r hi).1
      ((stabilizationRectangleEntryState_newColumn G s r hi).symm.trans h)⟩

@[simp]
theorem stabilizationRectangleEntryNode_lowerColumn :
    (stabilizationRectangleEntryNode G s r ha hi).val.transpose (G.X s).castSucc = r.right :=
  stabilizationRectangleEntryState_lowerColumn G s r

@[simp]
theorem stabilizationRectangleEntryNode_upperColumn :
    (stabilizationRectangleEntryNode G s r ha hi).val.transpose (G.X s).succ =
      (x.insertPoint s.succ (G.X s).succ).transpose (G.X s).castSucc :=
  stabilizationRectangleEntryState_upperColumn G s r hi

@[simp]
theorem stabilizationRectangleEntryNode_newColumn :
    (stabilizationRectangleEntryNode G s r ha hi).val s.succ = r.top :=
  stabilizationRectangleEntryState_newColumn G s r hi

/-- The matching target is the center state with the new and terminal columns exchanged. -/
theorem stabilizationRectangleEntryNode_target :
    stabilizationMatchingTargetState G s (stabilizationRectangleEntryNode G s r ha hi) =
      (x.insertPoint s.succ (G.X s).succ).swapColumns s.succ r.right := by
  change (((x.insertPoint s.succ (G.X s).succ).swapColumns s.succ r.right).swapRows
    (G.X s).castSucc (G.X s).succ).swapRows (G.X s).castSucc (G.X s).succ = _
  exact GridState.swapRows_swapRows _ _ _

/-- The actual entry rectangle determined by the admissible original rectangle. -/
noncomputable def stabilizationRectangleEntry :
    GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s (stabilizationRectangleEntryNode G s r ha hi)) :=
  GridRectangleBetween.ofSwapColumns _ _ s.succ r.right
    (Grid.ne_right_of_mem_cIoo ((GridRectangleBetween.mem_toGridRectangle_interior r).mp hi).1)
    (stabilizationRectangleEntryNode_target G s r ha hi)

@[simp]
theorem stabilizationRectangleEntry_left :
    (stabilizationRectangleEntry G s r ha hi).left = s.succ := by
  simp only [stabilizationRectangleEntry, GridRectangleBetween.ofSwapColumns_left]

@[simp]
theorem stabilizationRectangleEntry_right :
    (stabilizationRectangleEntry G s r ha hi).right = r.right := by
  simp only [stabilizationRectangleEntry, GridRectangleBetween.ofSwapColumns_right]

@[simp]
theorem stabilizationRectangleEntry_bottom :
    (stabilizationRectangleEntry G s r ha hi).bottom = (G.X s).succ := by
  simp only [stabilizationRectangleEntry, GridRectangleBetween.ofSwapColumns_bottom,
    GridState.insertPoint_apply_newColumn]

@[simp]
theorem stabilizationRectangleEntry_top :
    (stabilizationRectangleEntry G s r ha hi).top = r.top := by
  simp only [stabilizationRectangleEntry, GridRectangleBetween.ofSwapColumns_top, r.top_def]

/-- The canonical entry is empty because every interior point would be an extra point of r. -/
theorem stabilizationRectangleEntry_isEmpty :
    (stabilizationRectangleEntry G s r ha hi).IsEmpty := by
  rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo]
  intro c hc hv
  have hcol := ((GridRectangleBetween.mem_toGridRectangle_interior r).mp hi).1
  have hrow := ((GridRectangleBetween.mem_toGridRectangle_interior r).mp hi).2
  simp only [stabilizationRectangleEntry_left, stabilizationRectangleEntry_right] at hc
  simp only [stabilizationRectangleEntry_bottom, stabilizationRectangleEntry_top, r.top_def] at hv
  have hp := ha c (Grid.cIoo_subset_cIoo_left_of_mem_cIoo hcol hc)
    (Grid.cIoo_subset_cIoo_left_of_mem_cIoo hrow hv)
  exact Grid.ne_left_of_mem_cIoo hc hp

end OnLeConjecture.KnotFloer.GridFull
