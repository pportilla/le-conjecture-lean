/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingTransition

/-!
# The positions of the matching rows along an internal transition

The two matching-row points are ordered after cutting the column circle at the
new column. An internal transition leaves the point in the new column fixed and
moves exactly one of the two matching-row points past the other.
-/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti

private theorem transpose_eq_of_no_corner {n : ℕ} {x y : GridState n}
    (r : GridRectangleBetween x y) (q : Fin n)
    (hb : r.bottom ≠ q) (ht : r.top ≠ q) : y.transpose q = x.transpose q := by
  have hv := x.apply_transpose_apply q
  have hl : x.transpose q ≠ r.left := fun h => hb ((congrArg x h).symm.trans hv)
  have hr : x.transpose q ≠ r.right := fun h => ht ((congrArg x h).symm.trans hv)
  have h := (r.map_of_ne _ hl hr).trans hv
  exact (congrArg y.transpose h.symm).trans (y.transpose_apply_apply _)

private theorem ordered_middle_mem {n : ℕ} {a p q k : Fin n}
    (h1 : a ∈ Grid.cIco q p) (h2 : a ∈ Grid.cIco k q) : q ∈ Grid.cIoo p k := by
  simp only [Grid.mem_cIco, Grid.mem_cIoo, ne_eq, Fin.ext_iff] at *
  split_ifs at * <;> omega

private theorem transpose_eq_of_apply_eq {n : ℕ} (x : GridState n) {c q : Fin n}
    (h : x c = q) : x.transpose q = c :=
  (congrArg x.transpose h.symm).trans (x.transpose_apply_apply c)

/-- A matching source cannot place the upper matching row in the new column. -/
theorem rowMatchingSource_ne_newRow {n : ℕ} (a q : Fin n) (x : GridState (n + 1))
    (hx : RowMatchingSource a q x) : x a.succ ≠ q.succ := by
  intro heq
  have hp : x.transpose q.succ = a.succ :=
    (congrArg x.transpose heq.symm).trans (x.transpose_apply_apply _)
  change a.castSucc ∈ Grid.cIco (x.transpose q.succ) (x.transpose q.castSucc) at hx
  rw [hp] at hx
  have ht : x.transpose q.castSucc ≠ a.succ := by
    intro h
    exact Fin.castSucc_lt_succ.ne (x.transpose.toPerm.injective (h.trans hp.symm))
  exact Finset.disjoint_left.mp (Grid.disjoint_cIco_swap _ _) hx
    (Grid.castSucc_mem_cIco_succ ht)

/-- Changing source status requires a corner on one of the two matching rows. -/
theorem matching_status_change_has_row_corner {n : ℕ} (a q : Fin n)
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y)
    (hx : RowMatchingSource a q x) (hy : ¬RowMatchingSource a q y) :
    r.bottom = q.castSucc ∨ r.top = q.castSucc ∨
      r.bottom = q.succ ∨ r.top = q.succ := by
  by_contra h
  push Not at h
  apply hy
  simpa only [RowMatchingSource,
    transpose_eq_of_no_corner r q.castSucc h.1 h.2.1,
    transpose_eq_of_no_corner r q.succ h.2.2.1 h.2.2.2] using hx

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- The upper matching row also misses the new column at every internal node. -/
theorem stabilizationMatchingNode_ne_newRow (x : StabilizationMatchingNode G s) :
    x.val s.succ ≠ (G.X s).succ :=
  rowMatchingSource_ne_newRow s (G.X s) x.val x.property.1

/-- Swapping the matching rows does not change the new-column point of an internal node. -/
theorem stabilizationMatchingTargetState_newColumn (x : StabilizationMatchingNode G s) :
    stabilizationMatchingTargetState G s x s.succ = x.val s.succ := by
  rw [stabilizationMatchingTargetState, GridState.swapRows_apply,
    Equiv.swap_apply_of_ne_of_ne x.property.2 (stabilizationMatchingNode_ne_newRow G s x)]

/-- An internal full rectangle never changes the point in the new column. -/
theorem stabilizationMatchingTransition_newColumn
    (x z : StabilizationMatchingNode G s)
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z)) :
    x.val s.succ = z.val s.succ := by
  have hn : ¬RowMatchingSource s (G.X s) (stabilizationMatchingTargetState G s z) :=
    fun h => (rowMatchingSource_swapRows G s z.val).mp h z.property.1
  have hc := matching_status_change_has_row_corner s (G.X s) r x.property.1 hn
  have hleft : s.succ ≠ r.left := by
    intro heq
    have hb0 : r.bottom ≠ (G.X s).castSucc := by
      change x.val r.left ≠ _
      rw [← heq]
      exact x.property.2
    have hb1 : r.bottom ≠ (G.X s).succ := by
      change x.val r.left ≠ _
      rw [← heq]
      exact stabilizationMatchingNode_ne_newRow G s x
    have ht0 : r.top ≠ (G.X s).castSucc := by
      have hh := r.map_left
      rw [← heq, stabilizationMatchingTargetState_newColumn] at hh
      exact fun h => z.property.2 (hh.trans h)
    have ht1 : r.top ≠ (G.X s).succ := by
      have hh := r.map_left
      rw [← heq, stabilizationMatchingTargetState_newColumn] at hh
      exact fun h => stabilizationMatchingNode_ne_newRow G s z (hh.trans h)
    rcases hc with h | h | h | h
    · exact hb0 h
    · exact ht0 h
    · exact hb1 h
    · exact ht1 h
  have hright : s.succ ≠ r.right := by
    intro heq
    have ht0 : r.top ≠ (G.X s).castSucc := by
      change x.val r.right ≠ _
      rw [← heq]
      exact x.property.2
    have ht1 : r.top ≠ (G.X s).succ := by
      change x.val r.right ≠ _
      rw [← heq]
      exact stabilizationMatchingNode_ne_newRow G s x
    have hb0 : r.bottom ≠ (G.X s).castSucc := by
      have hh := r.map_right
      rw [← heq, stabilizationMatchingTargetState_newColumn] at hh
      exact fun h => z.property.2 (hh.trans h)
    have hb1 : r.bottom ≠ (G.X s).succ := by
      have hh := r.map_right
      rw [← heq, stabilizationMatchingTargetState_newColumn] at hh
      exact fun h => stabilizationMatchingNode_ne_newRow G s z (hh.trans h)
    rcases hc with h | h | h | h
    · exact hb0 h
    · exact ht0 h
    · exact hb1 h
    · exact ht1 h
  exact (r.map_of_ne _ hleft hright).symm.trans
    (stabilizationMatchingTargetState_newColumn G s z)

/-- After cutting immediately before the new column, the lower row precedes the upper row. -/
theorem stabilizationMatchingNode_column_order (x : StabilizationMatchingNode G s) :
    Grid.cyclicPosition s.castSucc (x.val.transpose (G.X s).castSucc) <
      Grid.cyclicPosition s.castSucc (x.val.transpose (G.X s).succ) := by
  have hne : x.val.transpose (G.X s).castSucc ≠ x.val.transpose (G.X s).succ :=
    fun h => Fin.castSucc_lt_succ.ne (x.val.transpose.toPerm.injective h)
  apply Grid.cyclicPosition_lt_of_notMem_cIco hne
  intro h
  exact Finset.disjoint_left.mp (Grid.disjoint_cIco_swap _ _) h x.property.1

/-- A nonmatching internal rectangle cannot use both matching rows as its corner rows. -/
theorem stabilizationMatchingTransition_not_both_rows
    (x z : StabilizationMatchingNode G s) (hxz : x ≠ z)
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z))
    (h0 : r.bottom = (G.X s).castSucc ∨ r.top = (G.X s).castSucc) :
    ¬(r.bottom = (G.X s).succ ∨ r.top = (G.X s).succ) := by
  intro h1
  have hs : stabilizationMatchingTargetState G s z =
      x.val.swapRows (G.X s).castSucc (G.X s).succ := by
    rcases h0 with hb | ht <;> rcases h1 with hb' | ht'
    · exact False.elim (Fin.castSucc_lt_succ.ne (hb.symm.trans hb'))
    · exact r.target_eq_swapRows.trans (by rw [← r.bottom_def, ← r.top_def, hb, ht'])
    · rw [r.target_eq_swapRows, ← r.bottom_def, ← r.top_def, hb', ht]
      ext c
      simp only [GridState.swapRows_apply, Equiv.swap_comm (G.X s).succ (G.X s).castSucc]
    · exact False.elim (Fin.castSucc_lt_succ.ne (ht.symm.trans ht'))
  have h := congrArg (fun w : GridState (n + 1) =>
    w.swapRows (G.X s).castSucc (G.X s).succ) hs
  simp only [stabilizationMatchingTargetState, GridState.swapRows_swapRows] at h
  exact hxz (Subtype.ext h.symm)

/-- An internal nonmatching step moves the two ordered row positions to the right or left. -/
theorem stabilizationMatchingTransition_row_positions
    (x z : StabilizationMatchingNode G s) (hxz : x ≠ z)
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z)) :
    z.val.transpose (G.X s).castSucc = x.val.transpose (G.X s).succ ∨
      z.val.transpose (G.X s).succ = x.val.transpose (G.X s).castSucc := by
  by_cases h0 : r.bottom = (G.X s).castSucc ∨ r.top = (G.X s).castSucc
  · left
    have h1 := stabilizationMatchingTransition_not_both_rows G s x z hxz r h0
    have h := transpose_eq_of_no_corner r (G.X s).succ
      (fun hb => h1 (Or.inl hb)) (fun ht => h1 (Or.inr ht))
    simpa only [stabilizationMatchingTargetState, GridState.swapRows_transpose,
      GridState.swapColumns_apply, Equiv.swap_apply_right] using h
  · right
    have h := transpose_eq_of_no_corner r (G.X s).castSucc
      (fun hb => h0 (Or.inl hb)) (fun ht => h0 (Or.inr ht))
    simpa only [stabilizationMatchingTargetState, GridState.swapRows_transpose,
      GridState.swapColumns_apply, Equiv.swap_apply_left] using h

/-- The ordered positions strictly advance together or retreat together at each internal step. -/
theorem stabilizationMatchingTransition_ordered_positions
    (x z : StabilizationMatchingNode G s) (hxz : x ≠ z)
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z)) :
    (z.val.transpose (G.X s).castSucc = x.val.transpose (G.X s).succ ∧
      Grid.cyclicPosition s.castSucc (x.val.transpose (G.X s).succ) <
        Grid.cyclicPosition s.castSucc (z.val.transpose (G.X s).succ)) ∨
    (z.val.transpose (G.X s).succ = x.val.transpose (G.X s).castSucc ∧
      Grid.cyclicPosition s.castSucc (z.val.transpose (G.X s).castSucc) <
        Grid.cyclicPosition s.castSucc (x.val.transpose (G.X s).castSucc)) := by
  have hz := stabilizationMatchingNode_column_order G s z
  rcases stabilizationMatchingTransition_row_positions G s x z hxz r with h | h
  · exact Or.inl ⟨h, h ▸ hz⟩
  · exact Or.inr ⟨h, h ▸ hz⟩

/-- The lower matching row can only be the top edge of an empty nonmatching transition. -/
theorem stabilizationMatchingTransition_bottom_ne_lower
    (x z : StabilizationMatchingNode G s) (hxz : x ≠ z)
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z))
    (he : r.IsEmpty) : r.bottom ≠ (G.X s).castSucc := by
  intro hb
  have hn := stabilizationMatchingTransition_not_both_rows G s x z hxz r (Or.inl hb)
  have ht1 : r.top ≠ (G.X s).succ := fun h => hn (Or.inr h)
  have hp : x.val.transpose (G.X s).castSucc = r.left := transpose_eq_of_apply_eq x.val hb
  have hq := transpose_eq_of_no_corner r (G.X s).succ
    (fun h => hn (Or.inl h)) ht1
  simp only [stabilizationMatchingTargetState, GridState.swapRows_transpose,
    GridState.swapColumns_apply, Equiv.swap_apply_right] at hq
  have hk := transpose_eq_of_apply_eq _ (r.map_right.trans hb)
  simp only [stabilizationMatchingTargetState, GridState.swapRows_transpose,
    GridState.swapColumns_apply, Equiv.swap_apply_left] at hk
  have hsx := x.property.1
  have hsz := z.property.1
  change s.castSucc ∈ Grid.cIco (x.val.transpose (G.X s).succ)
    (x.val.transpose (G.X s).castSucc) at hsx
  change s.castSucc ∈ Grid.cIco (z.val.transpose (G.X s).succ)
    (z.val.transpose (G.X s).castSucc) at hsz
  rw [hp] at hsx
  rw [hq, hk] at hsz
  have hc := ordered_middle_mem hsx hsz
  have hr : (G.X s).succ ∈ Grid.cIoo r.bottom r.top := by
    rw [hb, Grid.mem_cIoo]
    have h0 : (G.X s).castSucc ≠ r.top := fun h => r.bottom_ne_top (hb.trans h)
    have h0v : (G.X s).val ≠ r.top.val := fun h => h0 (Fin.ext h)
    have h1v : (G.X s).val + 1 ≠ r.top.val := fun h => ht1 (Fin.ext h.symm)
    simp only [Fin.val_castSucc, Fin.val_succ]
    refine ⟨h0, ?_⟩
    split_ifs <;> omega
  exact (r.isEmpty_iff_forall_notMem_cIoo.mp he) _ hc
    (by simpa only [GridState.apply_transpose_apply, ← r.bottom_def, ← r.top_def] using hr)

/-- The upper matching row can only be the bottom edge of an empty nonmatching transition. -/
theorem stabilizationMatchingTransition_top_ne_upper
    (x z : StabilizationMatchingNode G s) (hxz : x ≠ z)
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z))
    (he : r.IsEmpty) : r.top ≠ (G.X s).succ := by
  intro ht
  have h0 : ¬(r.bottom = (G.X s).castSucc ∨ r.top = (G.X s).castSucc) :=
    fun h => stabilizationMatchingTransition_not_both_rows G s x z hxz r h (Or.inr ht)
  have hb0 : r.bottom ≠ (G.X s).castSucc := fun h => h0 (Or.inl h)
  have hp : x.val.transpose (G.X s).succ = r.right := transpose_eq_of_apply_eq x.val ht
  have hq := transpose_eq_of_no_corner r (G.X s).castSucc hb0
    (fun h => h0 (Or.inr h))
  simp only [stabilizationMatchingTargetState, GridState.swapRows_transpose,
    GridState.swapColumns_apply, Equiv.swap_apply_left] at hq
  have hk := transpose_eq_of_apply_eq _ (r.map_left.trans ht)
  simp only [stabilizationMatchingTargetState, GridState.swapRows_transpose,
    GridState.swapColumns_apply, Equiv.swap_apply_right] at hk
  have hsx := x.property.1
  have hsz := z.property.1
  change s.castSucc ∈ Grid.cIco (x.val.transpose (G.X s).succ)
    (x.val.transpose (G.X s).castSucc) at hsx
  change s.castSucc ∈ Grid.cIco (z.val.transpose (G.X s).succ)
    (z.val.transpose (G.X s).castSucc) at hsz
  rw [hp] at hsx
  rw [hq, hk] at hsz
  have hc := ordered_middle_mem hsz hsx
  have hr : (G.X s).castSucc ∈ Grid.cIoo r.bottom r.top := by
    rw [ht]
    exact Grid.mem_cIoo_of_mem_cIco
      (Grid.castSucc_mem_cIco_succ (fun h => r.bottom_ne_top (h.trans ht.symm)))
      (Ne.symm hb0)
  exact (r.isEmpty_iff_forall_notMem_cIoo.mp he) _ hc
    (by simpa only [GridState.apply_transpose_apply, ← r.bottom_def, ← r.top_def] using hr)

/-- Every empty nonmatching transition has exactly one of the two possible oriented row edges. -/
theorem stabilizationMatchingTransition_oriented_row_edge
    (x z : StabilizationMatchingNode G s) (hxz : x ≠ z)
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z))
    (he : r.IsEmpty) : r.top = (G.X s).castSucc ∨ r.bottom = (G.X s).succ := by
  have hn : ¬RowMatchingSource s (G.X s) (stabilizationMatchingTargetState G s z) :=
    fun h => (rowMatchingSource_swapRows G s z.val).mp h z.property.1
  rcases matching_status_change_has_row_corner s (G.X s) r x.property.1 hn
    with h | h | h | h
  · exact False.elim (stabilizationMatchingTransition_bottom_ne_lower G s x z hxz r he h)
  · exact Or.inl h
  · exact Or.inr h
  · exact False.elim (stabilizationMatchingTransition_top_ne_upper G s x z hxz r he h)

end OnLeConjecture.KnotFloer.GridFull
