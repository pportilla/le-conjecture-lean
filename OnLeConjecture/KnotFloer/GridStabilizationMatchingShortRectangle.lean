/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingCenterEdges
public import OnLeConjecture.KnotFloer.GridStabilizationStandardDecomposition

/-!
# The rectangle determined by a matching entry and exit

A full entry rectangle and a full exit rectangle through the same internal node
determine a center-to-center rectangle whose bottom is the lower matching row.
-/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti
variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

private theorem after_successor_mem {n : ℕ} (q : Fin n) {u v : Fin (n + 1)}
    (h : u ∈ Grid.cIoo q.castSucc v) (hu : u ≠ q.succ) : u ∈ Grid.cIoo q.succ v := by
  have hu' : u.val ≠ q.val + 1 := fun h => hu (Fin.ext h)
  simp only [Grid.mem_cIoo, ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at *
  split_ifs at * <;> omega

/-- Away from the three specified columns, a center entry preserves the internal state. -/
theorem stabilizationMatchingEntry_center_apply_of_ne (x : GridState n)
    (z : StabilizationMatchingNode G s)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s z)) (he : e.IsEmpty)
    (c : Fin (n + 1)) (hcb : c ≠ s.succ)
    (hcp : c ≠ z.val.transpose (G.X s).castSucc)
    (hcq : c ≠ z.val.transpose (G.X s).succ) :
    x.insertPoint s.succ (G.X s).succ c = z.val c := by
  have hs := stabilizationMatchingEntry_shape G s x z e he
  have hv := e.map_of_ne c (by simpa only [hs.1] using hcb) (by simpa only [hs.2.2.1] using hcp)
  have h0 : z.val c ≠ (G.X s).castSucc := by
    intro h
    exact hcp ((z.val.transpose_apply_apply c).symm.trans (congrArg z.val.transpose h))
  have h1 : z.val c ≠ (G.X s).succ := by
    intro h
    exact hcq ((z.val.transpose_apply_apply c).symm.trans (congrArg z.val.transpose h))
  simp only [stabilizationMatchingTargetState, GridState.swapRows_apply,
    Equiv.swap_apply_of_ne_of_ne h0 h1] at hv
  exact hv.symm

/-- The center entry places the fixed new-column row on the lower-row column. -/
theorem stabilizationMatchingEntry_center_lowerColumn (x : GridState n)
    (z : StabilizationMatchingNode G s)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s z)) (he : e.IsEmpty) :
    x.insertPoint s.succ (G.X s).succ (z.val.transpose (G.X s).castSucc) = z.val s.succ := by
  have hs := stabilizationMatchingEntry_shape G s x z e he
  have hv := e.map_left
  rw [hs.1, hs.2.2.1, stabilizationMatchingTargetState_newColumn] at hv
  exact hv.symm

/-- The center entry leaves the lower matching row on the upper-row column. -/
theorem stabilizationMatchingEntry_center_upperColumn (x : GridState n)
    (z : StabilizationMatchingNode G s)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s z)) (he : e.IsEmpty) :
    x.insertPoint s.succ (G.X s).succ (z.val.transpose (G.X s).succ) = (G.X s).castSucc := by
  have hs := stabilizationMatchingEntry_shape G s x z e he
  have hn := stabilizationMatchingNode_row_columns_ne_newColumn G s z
  have hqp : z.val.transpose (G.X s).succ ≠ z.val.transpose (G.X s).castSucc :=
    fun h => Fin.castSucc_lt_succ.ne (z.val.transpose.toPerm.injective h).symm
  have hv := e.map_of_ne _ (by simpa only [hs.1] using hn.2) (by simpa only [hs.2.2.1] using hqp)
  simpa only [stabilizationMatchingTargetState, GridState.swapRows_apply,
    GridState.apply_transpose_apply, Equiv.swap_apply_right] using hv.symm

/-- The center rectangle reconstructed from an entry and exit at one internal node. -/
noncomputable def stabilizationMatchingTwoCenterRectangle (x y : GridState n)
    (z : StabilizationMatchingNode G s)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s z)) (he : e.IsEmpty)
    (f : GridRectangleBetween z.val (y.insertPoint s.succ (G.X s).succ)) (hf : f.IsEmpty) :
    GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (y.insertPoint s.succ (G.X s).succ) := by
  have fs := stabilizationMatchingExit_shape G s z y f hf
  have hn := stabilizationMatchingNode_row_columns_ne_newColumn G s z
  have hpq : z.val.transpose (G.X s).castSucc ≠ z.val.transpose (G.X s).succ :=
    fun h => Fin.castSucc_lt_succ.ne (z.val.transpose.toPerm.injective h)
  refine { left := z.val.transpose (G.X s).succ
           right := z.val.transpose (G.X s).castSucc
           left_ne_right := Ne.symm hpq
           map_left := ?_
           map_right := ?_
           map_of_ne := ?_ }
  · rw [stabilizationMatchingEntry_center_lowerColumn G s x z e he]
    have h := f.map_left
    simpa only [fs.1, fs.2.2.1] using h
  · rw [stabilizationMatchingEntry_center_upperColumn G s x z e he]
    have h := f.map_of_ne (z.val.transpose (G.X s).castSucc)
      (by simpa only [fs.2.2.1] using hpq) (by simpa only [fs.1] using hn.1)
    simpa only [GridState.apply_transpose_apply] using h
  · intro c hcq hcp
    by_cases hcb : c = s.succ
    · subst c
      simp only [GridState.insertPoint_apply_newColumn]
    · have h := f.map_of_ne c (by simpa only [fs.2.2.1] using hcq) (by simpa only [fs.1] using hcb)
      exact h.trans (stabilizationMatchingEntry_center_apply_of_ne G s x z e he c hcb hcp hcq).symm

@[simp]
theorem stabilizationMatchingTwoCenterRectangle_left (x y : GridState n)
    (z : StabilizationMatchingNode G s)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s z)) (he : e.IsEmpty)
    (f : GridRectangleBetween z.val (y.insertPoint s.succ (G.X s).succ)) (hf : f.IsEmpty) :
    (stabilizationMatchingTwoCenterRectangle G s x y z e he f hf).left =
      z.val.transpose (G.X s).succ := rfl

@[simp]
theorem stabilizationMatchingTwoCenterRectangle_right (x y : GridState n)
    (z : StabilizationMatchingNode G s)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s z)) (he : e.IsEmpty)
    (f : GridRectangleBetween z.val (y.insertPoint s.succ (G.X s).succ)) (hf : f.IsEmpty) :
    (stabilizationMatchingTwoCenterRectangle G s x y z e he f hf).right =
      z.val.transpose (G.X s).castSucc := rfl

@[simp]
theorem stabilizationMatchingTwoCenterRectangle_bottom (x y : GridState n)
    (z : StabilizationMatchingNode G s)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s z)) (he : e.IsEmpty)
    (f : GridRectangleBetween z.val (y.insertPoint s.succ (G.X s).succ)) (hf : f.IsEmpty) :
    (stabilizationMatchingTwoCenterRectangle G s x y z e he f hf).bottom =
      (G.X s).castSucc :=
  stabilizationMatchingEntry_center_upperColumn G s x z e he

@[simp]
theorem stabilizationMatchingTwoCenterRectangle_top (x y : GridState n)
    (z : StabilizationMatchingNode G s)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s z)) (he : e.IsEmpty)
    (f : GridRectangleBetween z.val (y.insertPoint s.succ (G.X s).succ)) (hf : f.IsEmpty) :
    (stabilizationMatchingTwoCenterRectangle G s x y z e he f hf).top = z.val s.succ :=
  stabilizationMatchingEntry_center_lowerColumn G s x z e he

/-- The reconstructed two-rectangle domain contains the inserted center. -/
theorem stabilizationMatchingTwoCenterRectangle_center_mem (x y : GridState n)
    (z : StabilizationMatchingNode G s)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s z)) (he : e.IsEmpty)
    (f : GridRectangleBetween z.val (y.insertPoint s.succ (G.X s).succ)) (hf : f.IsEmpty) :
    (s.succ, (G.X s).succ) ∈
      (stabilizationMatchingTwoCenterRectangle G s x y z e he f hf).toGridRectangle.interior := by
  rw [GridRectangleBetween.mem_toGridRectangle_interior,
    stabilizationMatchingTwoCenterRectangle_left, stabilizationMatchingTwoCenterRectangle_right]
  constructor
  · exact Grid.mem_cIoo_cyclic_right (stabilizationMatchingNode_row_columns_interior G s z).1
  · rw [stabilizationMatchingEntry_center_upperColumn G s x z e he,
      stabilizationMatchingEntry_center_lowerColumn G s x z e he]
    have h0 := z.property.2
    have h1 := stabilizationMatchingNode_ne_newRow G s z
    simp only [Grid.mem_cIoo, ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc] at *
    split_ifs <;> omega

/-- The reconstructed rectangle has no interior state point other than the inserted center. -/
theorem stabilizationMatchingTwoCenterRectangle_admissible (x y : GridState n)
    (z : StabilizationMatchingNode G s)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s z)) (he : e.IsEmpty)
    (f : GridRectangleBetween z.val (y.insertPoint s.succ (G.X s).succ)) (hf : f.IsEmpty) :
    StabilizationAdmissibleRectangle G s
      (stabilizationMatchingTwoCenterRectangle G s x y z e he f hf) := by
  intro c hc hr
  by_contra hcb
  change c ∈ Grid.cIoo (z.val.transpose (G.X s).succ)
    (z.val.transpose (G.X s).castSucc) at hc
  have hcq := Grid.ne_left_of_mem_cIoo hc
  have hcp := Grid.ne_right_of_mem_cIoo hc
  change x.insertPoint s.succ (G.X s).succ c ∈ Grid.cIoo
    (x.insertPoint s.succ (G.X s).succ (z.val.transpose (G.X s).succ))
    (x.insertPoint s.succ (G.X s).succ (z.val.transpose (G.X s).castSucc)) at hr
  rw [stabilizationMatchingEntry_center_upperColumn G s x z e he,
    stabilizationMatchingEntry_center_lowerColumn G s x z e he,
    stabilizationMatchingEntry_center_apply_of_ne G s x z e he c hcb hcp hcq] at hr
  have h1 : z.val c ≠ (G.X s).succ := by
    intro h
    exact hcq ((z.val.transpose_apply_apply c).symm.trans (congrArg z.val.transpose h))
  have hrow := after_successor_mem (G.X s) hr h1
  have hb := Grid.mem_cIoo_cyclic_right
    (stabilizationMatchingNode_row_columns_interior G s z).1
  rw [← Grid.cIoo_union_insert_cIoo_eq_cIoo_of_mem_cIoo hb] at hc
  rcases Finset.mem_union.mp hc with hout | hin
  · exact stabilizationMatchingExit_empty_region G s z y f hf c hout hrow
  · rcases Finset.mem_insert.mp hin with h | hin
    · exact hcb h
    · exact stabilizationMatchingEntry_empty_region G s x z e he c hin hrow

/-- Every entry-exit pair reconstructs a genuine old empty rectangle. -/
theorem exists_old_rectangle_of_matching_entry_exit (x y : GridState n)
    (z : StabilizationMatchingNode G s)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s z)) (he : e.IsEmpty)
    (f : GridRectangleBetween z.val (y.insertPoint s.succ (G.X s).succ)) (hf : f.IsEmpty) :
    ∃ r : GridRectangleBetween x y, r.IsEmpty ∧
      r.insertPoint s.succ (G.X s).succ =
        stabilizationMatchingTwoCenterRectangle G s x y z e he f hf := by
  obtain ⟨r, hr⟩ := GridRectangleBetween.exists_insertPoint_eq
    (stabilizationMatchingTwoCenterRectangle G s x y z e he f hf)
  refine ⟨r, ?_, hr⟩
  apply (stabilizationAdmissibleRectangle_insertPoint_iff G s r).mp
  rw [hr]
  exact stabilizationMatchingTwoCenterRectangle_admissible G s x y z e he f hf

/-- The lower-row column determines the internal node of an entry from a fixed center. -/
theorem stabilizationMatchingEntry_node_eq_of_lowerColumn_eq (x : GridState n)
    (z w : StabilizationMatchingNode G s)
    (e : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s z)) (he : e.IsEmpty)
    (f : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s w)) (hf : f.IsEmpty)
    (hc : z.val.transpose (G.X s).castSucc = w.val.transpose (G.X s).castSucc) : z = w := by
  apply stabilizationMatchingTargetState_injective G s
  have es := stabilizationMatchingEntry_shape G s x z e he
  have fs := stabilizationMatchingEntry_shape G s x w f hf
  rw [e.target_eq_swapColumns, f.target_eq_swapColumns, es.1, fs.1,
    es.2.2.1, fs.2.2.1, hc]

end OnLeConjecture.KnotFloer.GridFull
