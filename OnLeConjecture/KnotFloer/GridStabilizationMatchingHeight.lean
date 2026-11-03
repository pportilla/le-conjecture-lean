/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingGeometry

/-!
# Heights of internal matching transitions

Every internal rectangle crosses the new column in its interior. Emptiness
therefore bounds its other corner row relative to the fixed new-column point.
-/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti

private theorem ordered_outer_mem {n : ℕ} {a p q k : Fin n}
    (h1 : a ∈ Grid.cIco q p) (h2 : a ∈ Grid.cIco k q) : a ∈ Grid.cIco k p := by
  simp only [Grid.mem_cIco, ne_eq, Fin.ext_iff] at *
  split_ifs at * <;> omega

private theorem successor_interior_of_mem {n : ℕ} (a : Fin n) {l r : Fin (n + 1)}
    (ha : a.castSucc ∈ Grid.cIco l r) (hr : a.succ ≠ r) :
    a.succ ∈ Grid.cIoo l r := by
  have hr' : a.val + 1 ≠ r.val := fun h => hr (Fin.ext h)
  simp only [Grid.mem_cIco, Grid.mem_cIoo, ne_eq, Fin.ext_iff,
    Fin.val_castSucc, Fin.val_succ] at *
  split_ifs at * <;> omega

private theorem transpose_eq_of_apply_eq {n : ℕ} (x : GridState n) {c q : Fin n}
    (h : x c = q) : x.transpose q = c :=
  (congrArg x.transpose h.symm).trans (x.transpose_apply_apply c)

private theorem after_successor_mem {n : ℕ} (q : Fin n) {u v : Fin (n + 1)}
    (h : u ∈ Grid.cIoo q.castSucc v) (hu : u ≠ q.succ) : u ∈ Grid.cIoo q.succ v := by
  have hu' : u.val ≠ q.val + 1 := fun h => hu (Fin.ext h)
  simp only [Grid.mem_cIoo, ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at *
  split_ifs at * <;> omega

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- The new column is never a vertical side of an internal matching rectangle. -/
theorem stabilizationMatchingTransition_newColumn_not_corner
    (x z : StabilizationMatchingNode G s)
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z)) :
    s.succ ≠ r.left ∧ s.succ ≠ r.right := by
  have hc : stabilizationMatchingTargetState G s z s.succ = x.val s.succ :=
    (stabilizationMatchingTargetState_newColumn G s z).trans
      (stabilizationMatchingTransition_newColumn G s x z r).symm
  constructor
  · intro h
    have hv := r.map_left
    rw [← h, hc] at hv
    exact r.left_ne_right (h.symm.trans (x.val.toPerm.injective hv))
  · intro h
    have hv := r.map_right
    rw [← h, hc] at hv
    exact r.left_ne_right ((x.val.toPerm.injective hv).symm.trans h)

/-- Every empty nonmatching transition crosses the new column in its interior. -/
theorem stabilizationMatchingTransition_newColumn_mem_interior
    (x z : StabilizationMatchingNode G s) (hxz : x ≠ z)
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z))
    (he : r.IsEmpty) : s.succ ∈ Grid.cIoo r.left r.right := by
  apply successor_interior_of_mem s _
    (stabilizationMatchingTransition_newColumn_not_corner G s x z r).2
  have hsx := x.property.1
  have hsz := z.property.1
  change s.castSucc ∈ Grid.cIco (x.val.transpose (G.X s).succ)
    (x.val.transpose (G.X s).castSucc) at hsx
  change s.castSucc ∈ Grid.cIco (z.val.transpose (G.X s).succ)
    (z.val.transpose (G.X s).castSucc) at hsz
  rcases stabilizationMatchingTransition_oriented_row_edge G s x z hxz r he with ht | hb
  · have hp := transpose_eq_of_apply_eq x.val ht
    have hk := transpose_eq_of_apply_eq _ (r.map_left.trans ht)
    simp only [stabilizationMatchingTargetState, GridState.swapRows_transpose,
      GridState.swapColumns_apply, Equiv.swap_apply_left] at hk
    have hq : z.val.transpose (G.X s).castSucc = x.val.transpose (G.X s).succ := by
      rcases stabilizationMatchingTransition_row_positions G s x z hxz r with h | h
      · exact h
      · exact False.elim (r.left_ne_right (hk.symm.trans (h.trans hp)))
    rw [hp] at hsx
    rw [hq, hk] at hsz
    exact ordered_outer_mem hsx hsz
  · have hp := transpose_eq_of_apply_eq x.val hb
    have hk := transpose_eq_of_apply_eq _ (r.map_right.trans hb)
    simp only [stabilizationMatchingTargetState, GridState.swapRows_transpose,
      GridState.swapColumns_apply, Equiv.swap_apply_right] at hk
    have hq : z.val.transpose (G.X s).succ = x.val.transpose (G.X s).castSucc := by
      rcases stabilizationMatchingTransition_row_positions G s x z hxz r with h | h
      · exact False.elim (r.left_ne_right (hk.symm.trans (h.trans hp)).symm)
      · exact h
    rw [hp] at hsx
    rw [hq, hk] at hsz
    exact ordered_outer_mem hsz hsx

/-- A transition advancing the matching-row positions uses a point above the fixed point. -/
theorem stabilizationMatchingTransition_advancing_height
    (x z : StabilizationMatchingNode G s) (hxz : x ≠ z)
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z))
    (he : r.IsEmpty) (ht : r.top = (G.X s).castSucc) :
    x.val s.succ ∈ Grid.cIoo (G.X s).succ r.bottom := by
  have hc := stabilizationMatchingTransition_newColumn_mem_interior G s x z hxz r he
  have hn := stabilizationMatchingTransition_newColumn_not_corner G s x z r
  have hub : x.val s.succ ≠ r.bottom :=
    fun h => hn.1 (x.val.toPerm.injective h)
  have hout : x.val s.succ ∉ Grid.cIoo r.bottom (G.X s).castSucc := by
    simpa only [← r.bottom_def, ← r.top_def, ht] using
      (r.isEmpty_iff_forall_notMem_cIoo.mp he) _ hc
  apply after_successor_mem (G.X s) _ (stabilizationMatchingNode_ne_newRow G s x)
  exact Grid.mem_cIoo_swap_of_notMem
    (fun h => r.bottom_ne_top (h.trans ht.symm)) hub x.property.2 hout

/-- A transition retreating the matching-row positions uses a point below the fixed point. -/
theorem stabilizationMatchingTransition_retreating_height
    (x z : StabilizationMatchingNode G s) (hxz : x ≠ z)
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z))
    (he : r.IsEmpty) (hb : r.bottom = (G.X s).succ) :
    r.top ∈ Grid.cIoo (G.X s).succ (x.val s.succ) := by
  have hc := stabilizationMatchingTransition_newColumn_mem_interior G s x z hxz r he
  have hn := stabilizationMatchingTransition_newColumn_not_corner G s x z r
  have hut : x.val s.succ ≠ r.top :=
    fun h => hn.2 (x.val.toPerm.injective h)
  have hout : x.val s.succ ∉ Grid.cIoo (G.X s).succ r.top := by
    rw [← hb]
    exact (r.isEmpty_iff_forall_notMem_cIoo.mp he) _ hc
  exact Grid.mem_cIoo_cyclic_right (Grid.mem_cIoo_swap_of_notMem
    (fun h => r.bottom_ne_top (hb.trans h))
    (stabilizationMatchingNode_ne_newRow G s x) hut hout)

/-- The columns of an advancing transition are the old lower-row and new upper-row positions. -/
theorem stabilizationMatchingTransition_advancing_columns
    (x z : StabilizationMatchingNode G s) (hxz : x ≠ z)
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z))
    (ht : r.top = (G.X s).castSucc) :
    r.right = x.val.transpose (G.X s).castSucc ∧
      r.left = z.val.transpose (G.X s).succ ∧
      z.val.transpose (G.X s).castSucc = x.val.transpose (G.X s).succ := by
  have hp := transpose_eq_of_apply_eq x.val ht
  have hk := transpose_eq_of_apply_eq _ (r.map_left.trans ht)
  simp only [stabilizationMatchingTargetState, GridState.swapRows_transpose,
    GridState.swapColumns_apply, Equiv.swap_apply_left] at hk
  refine ⟨hp.symm, hk.symm, ?_⟩
  rcases stabilizationMatchingTransition_row_positions G s x z hxz r with h | h
  · exact h
  · exact False.elim (r.left_ne_right (hk.symm.trans (h.trans hp)))

/-- The columns of a retreating transition are the old upper-row and new lower-row positions. -/
theorem stabilizationMatchingTransition_retreating_columns
    (x z : StabilizationMatchingNode G s) (hxz : x ≠ z)
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z))
    (hb : r.bottom = (G.X s).succ) :
    r.left = x.val.transpose (G.X s).succ ∧
      r.right = z.val.transpose (G.X s).castSucc ∧
      z.val.transpose (G.X s).succ = x.val.transpose (G.X s).castSucc := by
  have hp := transpose_eq_of_apply_eq x.val hb
  have hk := transpose_eq_of_apply_eq _ (r.map_right.trans hb)
  simp only [stabilizationMatchingTargetState, GridState.swapRows_transpose,
    GridState.swapColumns_apply, Equiv.swap_apply_right] at hk
  refine ⟨hp.symm, hk.symm, ?_⟩
  rcases stabilizationMatchingTransition_row_positions G s x z hxz r with h | h
  · exact False.elim (r.left_ne_right (hk.symm.trans (h.trans hp)).symm)
  · exact h

end OnLeConjecture.KnotFloer.GridFull
