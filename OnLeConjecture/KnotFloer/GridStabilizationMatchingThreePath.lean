/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingEntryFromRectangle
public import OnLeConjecture.KnotFloer.GridStabilizationMatchingThreeRectangle

/-!
# The matching advance and exit determined by an admissible rectangle

When the original bottom is not the lower matching row, its lower-row point lies
outside the column interval. The canonical entry is followed by one advancing
rectangle and an exit to the original target center.
-/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti

private theorem cut_mem_before_outer_point {n : ℕ} (a : Fin n) {l p q : Fin (n + 1)}
    (hb : a.succ ∈ Grid.cIoo l p) (hq : q ∈ Grid.cIoo p l) :
    a.castSucc ∈ Grid.cIco l q := by
  simp only [Grid.mem_cIoo, Grid.mem_cIco, ne_eq, Fin.ext_iff,
    Fin.val_castSucc, Fin.val_succ] at *
  split_ifs at * <;> omega

private theorem transpose_eq_of_apply_eq {n : ℕ} (x : GridState n) {c q : Fin n}
    (h : x c = q) : x.transpose q = c :=
  (congrArg x.transpose h.symm).trans (x.transpose_apply_apply c)

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) {x y : GridState n}
variable (r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
  (y.insertPoint s.succ (G.X s).succ))

/-- The last internal state is obtained by reversing the eventual exit column exchange. -/
def stabilizationRectangleExitState : GridState (n + 1) :=
  (y.insertPoint s.succ (G.X s).succ).swapColumns r.left s.succ

theorem stabilizationRectangleExitState_upperColumn :
    (stabilizationRectangleExitState G s r).transpose (G.X s).succ = r.left := by
  apply transpose_eq_of_apply_eq
  simp only [stabilizationRectangleExitState, GridState.swapColumns_apply,
    Equiv.swap_apply_left, GridState.insertPoint_apply_newColumn]

theorem stabilizationRectangleExitState_newColumn :
    stabilizationRectangleExitState G s r s.succ = r.top := by
  simp only [stabilizationRectangleExitState, GridState.swapColumns_apply,
    Equiv.swap_apply_right]
  exact r.map_left

variable (ha : StabilizationAdmissibleRectangle G s r)
  (hi : (s.succ, (G.X s).succ) ∈ r.toGridRectangle.interior)
  (hb : r.bottom ≠ (G.X s).castSucc)

include hi hb in
/-- The lower-row column differs from both original sides and from the new column. -/
theorem stabilizationRectangle_lowerColumn_ne_sides :
    (x.insertPoint s.succ (G.X s).succ).transpose (G.X s).castSucc ≠ r.left ∧
      (x.insertPoint s.succ (G.X s).succ).transpose (G.X s).castSucc ≠ r.right ∧
      (x.insertPoint s.succ (G.X s).succ).transpose (G.X s).castSucc ≠ s.succ := by
  have htop := (stabilizationRectangle_top_ne_matching_rows G s r hi).1
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hv := congrArg (x.insertPoint s.succ (G.X s).succ) h
    rw [GridState.apply_transpose_apply] at hv
    exact hb hv.symm
  · intro h
    have hv := congrArg (x.insertPoint s.succ (G.X s).succ) h
    rw [GridState.apply_transpose_apply] at hv
    exact htop hv.symm
  · intro h
    have hv := congrArg (x.insertPoint s.succ (G.X s).succ) h
    simp only [GridState.apply_transpose_apply, GridState.insertPoint_apply_newColumn] at hv
    exact Fin.castSucc_lt_succ.ne hv

include hi hb in
theorem stabilizationRectangleExitState_lowerColumn :
    (stabilizationRectangleExitState G s r).transpose (G.X s).castSucc =
      (x.insertPoint s.succ (G.X s).succ).transpose (G.X s).castSucc := by
  have hn := stabilizationRectangle_lowerColumn_ne_sides G s r hi hb
  apply transpose_eq_of_apply_eq
  simp only [stabilizationRectangleExitState, GridState.swapColumns_apply,
    Equiv.swap_apply_of_ne_of_ne hn.1 hn.2.2]
  rw [r.map_of_ne _ hn.1 hn.2.1, GridState.apply_transpose_apply]

include ha hi hb in
theorem stabilizationRectangleExitState_source :
    RowMatchingSource s (G.X s) (stabilizationRectangleExitState G s r) := by
  have hn := stabilizationRectangle_lowerColumn_ne_sides G s r hi hb
  have hq := Grid.mem_cIoo_swap_of_notMem r.left_ne_right hn.1 hn.2.1
    (stabilizationRectangle_lower_point_not_interior G s r ha hi)
  change s.castSucc ∈ Grid.cIco _ _
  rw [stabilizationRectangleExitState_upperColumn,
    stabilizationRectangleExitState_lowerColumn G s r hi hb]
  exact cut_mem_before_outer_point s
    ((GridRectangleBetween.mem_toGridRectangle_interior r).mp hi).1 hq

/-- The final internal node of the three-rectangle matching path. -/
noncomputable def stabilizationRectangleExitNode : StabilizationMatchingNode G s :=
  ⟨stabilizationRectangleExitState G s r,
    stabilizationRectangleExitState_source G s r ha hi hb,
    fun h => (stabilizationRectangle_top_ne_matching_rows G s r hi).1
      ((stabilizationRectangleExitState_newColumn G s r).symm.trans h)⟩

@[simp]
theorem stabilizationRectangleExitNode_upperColumn :
    (stabilizationRectangleExitNode G s r ha hi hb).val.transpose (G.X s).succ = r.left :=
  stabilizationRectangleExitState_upperColumn G s r

@[simp]
theorem stabilizationRectangleExitNode_lowerColumn :
    (stabilizationRectangleExitNode G s r ha hi hb).val.transpose (G.X s).castSucc =
      (x.insertPoint s.succ (G.X s).succ).transpose (G.X s).castSucc :=
  stabilizationRectangleExitState_lowerColumn G s r hi hb

@[simp]
theorem stabilizationRectangleExitNode_newColumn :
    (stabilizationRectangleExitNode G s r ha hi hb).val s.succ = r.top :=
  stabilizationRectangleExitState_newColumn G s r

/-- The two canonical internal nodes are distinct in the three-rectangle case. -/
theorem stabilizationRectangleEntryNode_ne_exitNode :
    stabilizationRectangleEntryNode G s r ha hi ≠
      stabilizationRectangleExitNode G s r ha hi hb := by
  intro h
  have hv := congrArg (fun z : StabilizationMatchingNode G s =>
    z.val.transpose (G.X s).castSucc) h
  rw [stabilizationRectangleEntryNode_lowerColumn, stabilizationRectangleExitNode_lowerColumn] at hv
  exact (stabilizationRectangle_lowerColumn_ne_sides G s r hi hb).2.1 hv.symm

/-- The middle advancing rectangle has the two original side columns. -/
noncomputable def stabilizationRectangleMiddle :
    GridRectangleBetween (stabilizationRectangleEntryNode G s r ha hi).val
      (stabilizationMatchingTargetState G s (stabilizationRectangleExitNode G s r ha hi hb)) := by
  have hcol := ((GridRectangleBetween.mem_toGridRectangle_interior r).mp hi).1
  have hbl := Grid.ne_left_of_mem_cIoo hcol
  have hbp := Grid.ne_right_of_mem_cIoo hcol
  refine { left := r.left
           right := r.right
           left_ne_right := r.left_ne_right
           map_left := ?_
           map_right := ?_
           map_of_ne := ?_ }
  · simp only [stabilizationMatchingTargetState, stabilizationRectangleExitNode,
      stabilizationRectangleExitState, stabilizationRectangleEntryNode,
      stabilizationRectangleEntryState, GridState.swapRows_apply, GridState.swapColumns_apply,
      Equiv.swap_apply_left, Equiv.swap_apply_right, GridState.insertPoint_apply_newColumn]
  · change Equiv.swap (G.X s).castSucc (G.X s).succ
        ((y.insertPoint s.succ (G.X s).succ).swapColumns r.left s.succ r.right) =
      Equiv.swap (G.X s).castSucc (G.X s).succ
        ((x.insertPoint s.succ (G.X s).succ).swapColumns s.succ r.right r.left)
    simp only [GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm r.left_ne_right) (Ne.symm hbp),
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hbl) r.left_ne_right, r.map_right]
  · intro c hcl hcp
    by_cases hcb : c = s.succ
    · subst c
      change Equiv.swap (G.X s).castSucc (G.X s).succ
          ((y.insertPoint s.succ (G.X s).succ).swapColumns r.left s.succ s.succ) =
        Equiv.swap (G.X s).castSucc (G.X s).succ
          ((x.insertPoint s.succ (G.X s).succ).swapColumns s.succ r.right s.succ)
      simp only [GridState.swapColumns_apply, Equiv.swap_apply_right, Equiv.swap_apply_left,
        r.map_left]
    · change Equiv.swap (G.X s).castSucc (G.X s).succ
          ((y.insertPoint s.succ (G.X s).succ).swapColumns r.left s.succ c) =
        Equiv.swap (G.X s).castSucc (G.X s).succ
          ((x.insertPoint s.succ (G.X s).succ).swapColumns s.succ r.right c)
      simp only [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hcl hcb,
        Equiv.swap_apply_of_ne_of_ne hcb hcp, r.map_of_ne c hcl hcp]

@[simp]
theorem stabilizationRectangleMiddle_left :
    (stabilizationRectangleMiddle G s r ha hi hb).left = r.left := rfl

@[simp]
theorem stabilizationRectangleMiddle_right :
    (stabilizationRectangleMiddle G s r ha hi hb).right = r.right := rfl

@[simp]
theorem stabilizationRectangleMiddle_top :
    (stabilizationRectangleMiddle G s r ha hi hb).top = (G.X s).castSucc := by
  change stabilizationRectangleEntryState G s r r.right = _
  simp only [stabilizationRectangleEntryState, GridState.swapRows_apply,
    GridState.swapColumns_apply, Equiv.swap_apply_right, GridState.insertPoint_apply_newColumn]

@[simp]
theorem stabilizationRectangleMiddle_bottom :
    (stabilizationRectangleMiddle G s r ha hi hb).bottom = r.bottom := by
  have hcol := ((GridRectangleBetween.mem_toGridRectangle_interior r).mp hi).1
  have hrow := ((GridRectangleBetween.mem_toGridRectangle_interior r).mp hi).2
  have hb1 : r.bottom ≠ (G.X s).succ := Ne.symm (Grid.ne_left_of_mem_cIoo hrow)
  change stabilizationRectangleEntryState G s r r.left = _
  simp only [stabilizationRectangleEntryState, GridState.swapRows_apply,
    GridState.swapColumns_apply,
    Equiv.swap_apply_of_ne_of_ne (Ne.symm (Grid.ne_left_of_mem_cIoo hcol)) r.left_ne_right,
    ← r.bottom_def, Equiv.swap_apply_of_ne_of_ne hb hb1]

private theorem predecessor_mem_cIoo_of_successor_mem {n : ℕ} (q : Fin n)
    {v u : Fin (n + 1)} (h : q.succ ∈ Grid.cIoo v u) (hv : v ≠ q.castSucc) :
    q.castSucc ∈ Grid.cIoo v u := by
  simp only [Grid.mem_cIoo, ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at *
  split_ifs at * <;> omega

/-- The canonical advancing rectangle is empty. -/
theorem stabilizationRectangleMiddle_isEmpty :
    (stabilizationRectangleMiddle G s r ha hi hb).IsEmpty := by
  rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo]
  intro c hc hv
  have hrow := ((GridRectangleBetween.mem_toGridRectangle_interior r).mp hi).2
  have hpred := predecessor_mem_cIoo_of_successor_mem (G.X s) hrow hb
  simp only [stabilizationRectangleMiddle_left, stabilizationRectangleMiddle_right] at hc
  simp only [stabilizationRectangleMiddle_bottom, stabilizationRectangleMiddle_top] at hv
  have hv' := Grid.cIoo_subset_cIoo_right_of_mem_cIoo hpred hv
  by_cases hcb : c = s.succ
  · subst c
    rw [stabilizationRectangleEntryNode_newColumn] at hv'
    exact Grid.right_notMem_cIoo _ _ hv'
  · have hcp : c ≠ (stabilizationRectangleEntryNode G s r ha hi).val.transpose
        (G.X s).castSucc := by
      simpa only [stabilizationRectangleEntryNode_lowerColumn] using Grid.ne_right_of_mem_cIoo hc
    have hcq : c ≠ (stabilizationRectangleEntryNode G s r ha hi).val.transpose
        (G.X s).succ := by
      rw [stabilizationRectangleEntryNode_upperColumn]
      intro h
      exact stabilizationRectangle_lower_point_not_interior G s r ha hi (h ▸ hc)
    have hsame := stabilizationMatchingEntry_center_apply_of_ne G s x
      (stabilizationRectangleEntryNode G s r ha hi) (stabilizationRectangleEntry G s r ha hi)
      (stabilizationRectangleEntry_isEmpty G s r ha hi) c hcb hcp hcq
    rw [← hsame] at hv'
    exact hcb (ha c hc hv')

/-- The exit rectangle reverses the terminal column exchange. -/
noncomputable def stabilizationRectangleThreeExit :
    GridRectangleBetween (stabilizationRectangleExitNode G s r ha hi hb).val
      (y.insertPoint s.succ (G.X s).succ) :=
  GridRectangleBetween.ofSwapColumns _ _ r.left s.succ
    (Ne.symm (Grid.ne_left_of_mem_cIoo
      ((GridRectangleBetween.mem_toGridRectangle_interior r).mp hi).1))
    (GridState.swapColumns_swapColumns _ _ _).symm

@[simp]
theorem stabilizationRectangleThreeExit_left :
    (stabilizationRectangleThreeExit G s r ha hi hb).left = r.left := by
  simp only [stabilizationRectangleThreeExit, stabilizationRectangleExitNode,
    stabilizationRectangleExitState,
    GridRectangleBetween.ofSwapColumns_left]

@[simp]
theorem stabilizationRectangleThreeExit_right :
    (stabilizationRectangleThreeExit G s r ha hi hb).right = s.succ := by
  simp only [stabilizationRectangleThreeExit, stabilizationRectangleExitNode,
    stabilizationRectangleExitState,
    GridRectangleBetween.ofSwapColumns_right]

@[simp]
theorem stabilizationRectangleThreeExit_bottom :
    (stabilizationRectangleThreeExit G s r ha hi hb).bottom = (G.X s).succ := by
  simp only [stabilizationRectangleThreeExit, GridRectangleBetween.ofSwapColumns_bottom,
    stabilizationRectangleExitNode, stabilizationRectangleExitState,
    GridState.swapColumns_apply, Equiv.swap_apply_left, GridState.insertPoint_apply_newColumn]

@[simp]
theorem stabilizationRectangleThreeExit_top :
    (stabilizationRectangleThreeExit G s r ha hi hb).top = r.top := by
  simp only [stabilizationRectangleThreeExit, stabilizationRectangleExitNode,
    stabilizationRectangleExitState, GridRectangleBetween.ofSwapColumns_top,
    GridState.swapColumns_apply, Equiv.swap_apply_right, r.map_left, r.top_def]

/-- The canonical final exit is empty. -/
theorem stabilizationRectangleThreeExit_isEmpty :
    (stabilizationRectangleThreeExit G s r ha hi hb).IsEmpty := by
  rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo]
  intro c hc hv
  have hcol := ((GridRectangleBetween.mem_toGridRectangle_interior r).mp hi).1
  have hrow := ((GridRectangleBetween.mem_toGridRectangle_interior r).mp hi).2
  simp only [stabilizationRectangleThreeExit_left, stabilizationRectangleThreeExit_right] at hc
  simp only [stabilizationRectangleThreeExit_bottom, stabilizationRectangleThreeExit_top] at hv
  have hc' := Grid.cIoo_subset_cIoo_right_of_mem_cIoo hcol hc
  have hcl := Grid.ne_left_of_mem_cIoo hc
  have hcb := Grid.ne_right_of_mem_cIoo hc
  have hcp := Grid.ne_right_of_mem_cIoo hc'
  have hsame : (stabilizationRectangleExitNode G s r ha hi hb).val c =
      x.insertPoint s.succ (G.X s).succ c := by
    simp only [stabilizationRectangleExitNode, stabilizationRectangleExitState,
      GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hcl hcb, r.map_of_ne c hcl hcp]
  rw [hsame] at hv
  exact hcb (ha c hc' (Grid.cIoo_subset_cIoo_left_of_mem_cIoo hrow hv))

/-- Reconstruction from the three canonical matching rectangles returns the original rectangle. -/
theorem stabilizationRectangleThree_reconstruct :
    stabilizationMatchingThreeCenterRectangle G s x y
      (stabilizationRectangleEntryNode G s r ha hi)
      (stabilizationRectangleExitNode G s r ha hi hb)
      (stabilizationRectangleEntryNode_ne_exitNode G s r ha hi hb)
      (stabilizationRectangleEntry G s r ha hi)
      (stabilizationRectangleEntry_isEmpty G s r ha hi)
      (stabilizationRectangleMiddle G s r ha hi hb)
      (stabilizationRectangleMiddle_top G s r ha hi hb)
      (stabilizationRectangleThreeExit G s r ha hi hb)
      (stabilizationRectangleThreeExit_isEmpty G s r ha hi hb) = r := by
  apply GridRectangleBetween.ext <;> simp only [stabilizationMatchingThreeCenterRectangle_left,
    stabilizationMatchingThreeCenterRectangle_right, stabilizationRectangleExitNode_upperColumn,
    stabilizationRectangleEntryNode_lowerColumn]

end OnLeConjecture.KnotFloer.GridFull
