/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingGeometry

/-!
# Empty rectangles between center states and internal matching states

An empty rectangle entering an internal matching state starts on the new column.
An empty rectangle leaving an internal matching state ends on that column.
The opposite orientations contain the point on the lower matching row and are
therefore excluded by emptiness.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

private theorem transpose_eq_of_apply_eq {n : ℕ} (x : GridState n) {c q : Fin n}
    (h : x c = q) : x.transpose q = c :=
  (congrArg x.transpose h.symm).trans (x.transpose_apply_apply c)

private theorem predecessor_mem_before_successor {n : ℕ} (q : Fin n)
    {u : Fin (n + 1)} (hu0 : u ≠ q.castSucc) (hu1 : u ≠ q.succ) :
    q.castSucc ∈ Grid.cIoo u q.succ := by
  simp only [Grid.mem_cIoo, ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at *
  split_ifs <;> omega

private theorem predecessor_not_mem_after_successor {n : ℕ} (q : Fin n)
    (u : Fin (n + 1)) : q.castSucc ∉ Grid.cIoo q.succ u := by
  simp only [Grid.mem_cIoo, ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> omega

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- Neither matching-row point of an internal node lies on the new column. -/
theorem stabilizationMatchingNode_row_columns_ne_newColumn
    (z : StabilizationMatchingNode G s) :
    z.val.transpose (G.X s).castSucc ≠ s.succ ∧
      z.val.transpose (G.X s).succ ≠ s.succ := by
  constructor
  · intro h
    have hv := congrArg z.val h
    rw [GridState.apply_transpose_apply] at hv
    exact z.property.2 hv.symm
  · intro h
    have hv := congrArg z.val h
    rw [GridState.apply_transpose_apply] at hv
    exact stabilizationMatchingNode_ne_newRow G s z hv.symm

/-- The matching-row points occur in this cyclic order after the new column. -/
theorem stabilizationMatchingNode_row_columns_interior
    (z : StabilizationMatchingNode G s) :
    z.val.transpose (G.X s).castSucc ∈
        Grid.cIoo s.succ (z.val.transpose (G.X s).succ) ∧
      z.val.transpose (G.X s).succ ∈
        Grid.cIoo (z.val.transpose (G.X s).castSucc) s.succ := by
  have h := z.property.1
  have hn := stabilizationMatchingNode_row_columns_ne_newColumn G s z
  change s.castSucc ∈ Grid.cIco (z.val.transpose (G.X s).succ)
    (z.val.transpose (G.X s).castSucc) at h
  simp only [Grid.mem_cIco, Grid.mem_cIoo, ne_eq, Fin.ext_iff,
    Fin.val_castSucc, Fin.val_succ] at *
  split_ifs at * <;> omega

/-- A rectangle entering a matching target has the new column as one of its sides. -/
theorem stabilizationMatchingEntry_newColumn_corner (x : GridState n)
    (z : StabilizationMatchingNode G s)
    (r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s z)) :
    s.succ = r.left ∨ s.succ = r.right := by
  by_contra h
  push Not at h
  have hv := r.map_of_ne s.succ h.1 h.2
  rw [stabilizationMatchingTargetState_newColumn,
    GridState.insertPoint_apply_newColumn] at hv
  exact stabilizationMatchingNode_ne_newRow G s z hv

/-- The opposite orientation of an entry rectangle contains a matching-row point. -/
theorem stabilizationMatchingEntry_right_ne_newColumn (x : GridState n)
    (z : StabilizationMatchingNode G s)
    (r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s z)) (he : r.IsEmpty) :
    r.right ≠ s.succ := by
  intro hr
  have ht : r.top = (G.X s).succ := by
    rw [r.top_def, hr, GridState.insertPoint_apply_newColumn]
  have hb : r.bottom = z.val s.succ := by
    have h := r.map_right
    rw [hr, stabilizationMatchingTargetState_newColumn] at h
    exact h.symm
  have hp := transpose_eq_of_apply_eq _ (r.map_left.trans ht)
  simp only [stabilizationMatchingTargetState, GridState.swapRows_transpose,
    GridState.swapColumns_apply, Equiv.swap_apply_right] at hp
  have hc := (stabilizationMatchingNode_row_columns_interior G s z).2
  rw [hp] at hc
  have hc' : z.val.transpose (G.X s).succ ∈ Grid.cIoo r.left r.right := by
    simpa only [hr] using hc
  have hv : stabilizationMatchingTargetState G s z
      (z.val.transpose (G.X s).succ) = (G.X s).castSucc := by
    simp only [stabilizationMatchingTargetState, GridState.swapRows_apply,
      GridState.apply_transpose_apply, Equiv.swap_apply_right]
  have hh := (r.isEmpty_iff_forall_notMem_cIoo_target.mp he) _ hc'
  rw [r.map_right, r.map_left, ← r.bottom_def, ← r.top_def, hb, ht, hv] at hh
  exact hh (predecessor_mem_before_successor (G.X s) z.property.2
    (stabilizationMatchingNode_ne_newRow G s z))

/-- All four sides of an empty rectangle entering an internal matching target. -/
theorem stabilizationMatchingEntry_shape (x : GridState n)
    (z : StabilizationMatchingNode G s)
    (r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s z)) (he : r.IsEmpty) :
    r.left = s.succ ∧ r.bottom = (G.X s).succ ∧
      r.right = z.val.transpose (G.X s).castSucc ∧ r.top = z.val s.succ := by
  have hl : r.left = s.succ := by
    rcases stabilizationMatchingEntry_newColumn_corner G s x z r with h | h
    · exact h.symm
    · exact False.elim (stabilizationMatchingEntry_right_ne_newColumn G s x z r he h.symm)
  have hb : r.bottom = (G.X s).succ := by
    rw [r.bottom_def, hl, GridState.insertPoint_apply_newColumn]
  have hp := transpose_eq_of_apply_eq _ (r.map_right.trans hb)
  simp only [stabilizationMatchingTargetState, GridState.swapRows_transpose,
    GridState.swapColumns_apply, Equiv.swap_apply_right] at hp
  have ht : r.top = z.val s.succ := by
    have h := r.map_left
    rw [hl, stabilizationMatchingTargetState_newColumn] at h
    exact h.symm
  exact ⟨hl, hb, hp.symm, ht⟩

/-- A rectangle leaving an internal node has the new column as one of its sides. -/
theorem stabilizationMatchingExit_newColumn_corner (z : StabilizationMatchingNode G s)
    (x : GridState n)
    (r : GridRectangleBetween z.val (x.insertPoint s.succ (G.X s).succ)) :
    s.succ = r.left ∨ s.succ = r.right := by
  by_contra h
  push Not at h
  have hv := r.map_of_ne s.succ h.1 h.2
  rw [GridState.insertPoint_apply_newColumn] at hv
  exact stabilizationMatchingNode_ne_newRow G s z hv.symm

/-- The opposite orientation of an exit rectangle contains a matching-row point. -/
theorem stabilizationMatchingExit_left_ne_newColumn (z : StabilizationMatchingNode G s)
    (x : GridState n)
    (r : GridRectangleBetween z.val (x.insertPoint s.succ (G.X s).succ))
    (he : r.IsEmpty) : r.left ≠ s.succ := by
  intro hl
  have hb : r.bottom = z.val s.succ := by rw [r.bottom_def, hl]
  have ht : r.top = (G.X s).succ := by
    have h := r.map_left
    rw [hl, GridState.insertPoint_apply_newColumn] at h
    exact h.symm
  have hp := transpose_eq_of_apply_eq z.val ht
  have hc := (stabilizationMatchingNode_row_columns_interior G s z).1
  rw [hp] at hc
  have hc' : z.val.transpose (G.X s).castSucc ∈ Grid.cIoo r.left r.right := by
    simpa only [hl] using hc
  have hh := (r.isEmpty_iff_forall_notMem_cIoo.mp he) _ hc'
  rw [GridState.apply_transpose_apply, hb, ht] at hh
  exact hh (predecessor_mem_before_successor (G.X s) z.property.2
    (stabilizationMatchingNode_ne_newRow G s z))

/-- All four sides of an empty rectangle leaving an internal matching node. -/
theorem stabilizationMatchingExit_shape (z : StabilizationMatchingNode G s)
    (x : GridState n)
    (r : GridRectangleBetween z.val (x.insertPoint s.succ (G.X s).succ))
    (he : r.IsEmpty) :
    r.right = s.succ ∧ r.top = z.val s.succ ∧
      r.left = z.val.transpose (G.X s).succ ∧ r.bottom = (G.X s).succ := by
  have hr : r.right = s.succ := by
    rcases stabilizationMatchingExit_newColumn_corner G s z x r with h | h
    · exact False.elim (stabilizationMatchingExit_left_ne_newColumn G s z x r he h.symm)
    · exact h.symm
  have ht : r.top = z.val s.succ := by rw [r.top_def, hr]
  have hb : r.bottom = (G.X s).succ := by
    have h := r.map_right
    rw [hr, GridState.insertPoint_apply_newColumn] at h
    exact h.symm
  have hp := transpose_eq_of_apply_eq z.val hb
  exact ⟨hr, ht, hp.symm, hb⟩

/-- Entry emptiness excludes internal-node points in the initial column interval. -/
theorem stabilizationMatchingEntry_empty_region (x : GridState n)
    (z : StabilizationMatchingNode G s)
    (r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s z)) (he : r.IsEmpty) :
    ∀ c ∈ Grid.cIoo s.succ (z.val.transpose (G.X s).castSucc),
      z.val c ∉ Grid.cIoo (G.X s).succ (z.val s.succ) := by
  obtain ⟨hl, hb, hr, ht⟩ := stabilizationMatchingEntry_shape G s x z r he
  intro c hc hmem
  have hc' : c ∈ Grid.cIoo r.left r.right := by simpa only [hl, hr] using hc
  have h0 : z.val c ≠ (G.X s).castSucc := by
    intro h
    apply predecessor_not_mem_after_successor (G.X s) (z.val s.succ)
    exact (congrArg (fun v => v ∈ Grid.cIoo (G.X s).succ (z.val s.succ)) h).mp hmem
  have h1 : z.val c ≠ (G.X s).succ := Grid.ne_left_of_mem_cIoo hmem
  have hh := (r.isEmpty_iff_forall_notMem_cIoo_target.mp he) c hc'
  rw [r.map_right, r.map_left, ← r.bottom_def, ← r.top_def, hb, ht] at hh
  apply hh
  simpa only [stabilizationMatchingTargetState, GridState.swapRows_apply,
    Equiv.swap_apply_of_ne_of_ne h0 h1] using hmem

/-- Exit emptiness excludes internal-node points in the final column interval. -/
theorem stabilizationMatchingExit_empty_region (z : StabilizationMatchingNode G s)
    (x : GridState n)
    (r : GridRectangleBetween z.val (x.insertPoint s.succ (G.X s).succ))
    (he : r.IsEmpty) :
    ∀ c ∈ Grid.cIoo (z.val.transpose (G.X s).succ) s.succ,
      z.val c ∉ Grid.cIoo (G.X s).succ (z.val s.succ) := by
  obtain ⟨hr, ht, hl, hb⟩ := stabilizationMatchingExit_shape G s z x r he
  intro c hc
  have hc' : c ∈ Grid.cIoo r.left r.right := by simpa only [hl, hr] using hc
  have hh := (r.isEmpty_iff_forall_notMem_cIoo.mp he) c hc'
  simpa only [hb, ht] using hh

end OnLeConjecture.KnotFloer.GridFull
