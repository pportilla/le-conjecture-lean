/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationProjectionSupport

/-!
# Row matching at an arbitrary column

These rectangle lemmas also cover the last column. This permits the row matching to
be based at either of the two new markings in a stabilization.
-/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull.RowMatchingAt
open TauCeti

/-- The source condition for the row matching at a specified square. -/
def Source {n : ℕ} (a : Fin (n + 1)) (q : Fin n) (x : GridState (n + 1)) : Prop :=
  a ∈ Grid.cIco (x.transpose q.succ) (x.transpose q.castSucc)

private theorem outside_column_arc {n : ℕ} {a l r c : Fin n}
    (ha : a ∈ Grid.cIco l r) (hc : c ∉ Grid.cIoo l r)
    (hcl : c ≠ l) (hcr : c ≠ r) :
    a ∉ Grid.cIco c l ∧ a ∈ Grid.cIco c r ∧
      a ∉ Grid.cIco r c ∧ a ∈ Grid.cIco l c := by
  have hclv : c.val ≠ l.val := fun h => hcl (Fin.ext h)
  have hcrv : c.val ≠ r.val := fun h => hcr (Fin.ext h)
  have hlrv : l.val ≠ r.val := by
    intro h
    have heq : l = r := Fin.ext h
    simp only [heq, Grid.cIco_self, Finset.notMem_empty] at ha
  simp only [Grid.mem_cIco, Grid.mem_cIoo, ne_eq, Fin.ext_iff] at *
  split_ifs at * <;> omega

private theorem transpose_eq_of_apply_eq {n : ℕ} (x : GridState n) {c q : Fin n}
    (h : x c = q) : x.transpose q = c :=
  (congrArg x.transpose h.symm).trans (x.transpose_apply_apply c)

private theorem successor_interior {n : ℕ} (q : Fin n) {t : Fin (n + 1)}
    (h0 : q.castSucc ≠ t) (h1 : q.succ ≠ t) : q.succ ∈ Grid.cIoo q.castSucc t := by
  have h0v : q.val ≠ t.val := fun h => h0 (Fin.ext h)
  have h1v : q.val + 1 ≠ t.val := fun h => h1 (Fin.ext h)
  rw [Grid.mem_cIoo]
  refine ⟨h0, ?_⟩
  simp only [Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> omega

/-- A rectangle beginning in the lower matching row changes a nonsource to a source. -/
theorem source_of_rectangle_bottom {n : ℕ} (a : Fin (n + 1)) (q : Fin n)
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y)
    (he : r.IsEmpty) (ha : (a, q.castSucc) ∈ r.toGridRectangle.coveredSquares)
    (hb : r.bottom = q.castSucc) : ¬Source a q x ∧ Source a q y := by
  classical
  have hac : a ∈ Grid.cIco r.left r.right :=
    (GridRectangle.mem_coveredSquares _ _).mp ha |>.1
  have hxl : x.transpose q.castSucc = r.left := transpose_eq_of_apply_eq x hb
  have hyr : y.transpose q.castSucc = r.right :=
    transpose_eq_of_apply_eq y (r.map_right.trans hb)
  by_cases ht : r.top = q.succ
  · have hxr : x.transpose q.succ = r.right := transpose_eq_of_apply_eq x ht
    have hyl : y.transpose q.succ = r.left :=
      transpose_eq_of_apply_eq y (r.map_left.trans ht)
    simp only [Source, hxl, hyr, hxr, hyl]
    exact ⟨fun h => Finset.disjoint_left.mp (Grid.disjoint_cIco_swap _ _) hac h, hac⟩
  · let c := x.transpose q.succ
    have hcvalue : x c = q.succ := x.apply_transpose_apply _
    have hcl : c ≠ r.left := by
      intro h
      exact Fin.castSucc_lt_succ.ne ((hb.symm.trans (congrArg x h.symm)).trans hcvalue)
    have hcr : c ≠ r.right := by
      intro h
      exact ht ((congrArg x h.symm).trans hcvalue)
    have hrow : x c ∈ Grid.cIoo (x r.left) (x r.right) := by
      change x c ∈ Grid.cIoo r.bottom r.top
      rw [hcvalue, hb]
      exact successor_interior q (fun h => r.bottom_ne_top (hb.trans h)) (Ne.symm ht)
    have hcnot : c ∉ Grid.cIoo r.left r.right := fun hc =>
      (r.isEmpty_iff_forall_notMem_cIoo.mp he) c hc hrow
    have hyc : y.transpose q.succ = c :=
      transpose_eq_of_apply_eq y ((r.map_of_ne c hcl hcr).trans hcvalue)
    obtain ⟨hno, hyes, _, _⟩ := outside_column_arc hac hcnot hcl hcr
    simpa only [Source, hxl, hyr, hyc] using And.intro hno hyes

/-- A rectangle ending in the upper matching row changes a nonsource to a source. -/
theorem source_of_rectangle_top {n : ℕ} (a : Fin (n + 1)) (q : Fin n)
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y)
    (he : r.IsEmpty) (ha : (a, q.castSucc) ∈ r.toGridRectangle.coveredSquares)
    (ht : r.top = q.succ) : ¬Source a q x ∧ Source a q y := by
  classical
  by_cases hb : r.bottom = q.castSucc
  · exact source_of_rectangle_bottom a q r he ha hb
  have hac : a ∈ Grid.cIco r.left r.right :=
    (GridRectangle.mem_coveredSquares _ _).mp ha |>.1
  have haq : q.castSucc ∈ Grid.cIco r.bottom r.top :=
    (GridRectangle.mem_coveredSquares _ _).mp ha |>.2
  have hxr : x.transpose q.succ = r.right := transpose_eq_of_apply_eq x ht
  have hyl : y.transpose q.succ = r.left :=
    transpose_eq_of_apply_eq y (r.map_left.trans ht)
  let c := x.transpose q.castSucc
  have hcvalue : x c = q.castSucc := x.apply_transpose_apply _
  have hcl : c ≠ r.left := by
    intro h
    exact hb ((congrArg x h.symm).trans hcvalue)
  have hcr : c ≠ r.right := by
    intro h
    exact Fin.castSucc_lt_succ.ne (hcvalue.symm.trans ((congrArg x h).trans ht))
  have hcnot : c ∉ Grid.cIoo r.left r.right := by
    intro hc
    have hrow := Grid.mem_cIoo_of_mem_cIco haq (Ne.symm hb)
    rw [← hcvalue] at hrow
    exact (r.isEmpty_iff_forall_notMem_cIoo.mp he) c hc hrow
  have hyc : y.transpose q.castSucc = c :=
    transpose_eq_of_apply_eq y ((r.map_of_ne c hcl hcr).trans hcvalue)
  obtain ⟨_, _, hno, hyes⟩ := outside_column_arc hac hcnot hcl hcr
  simpa only [Source, hxr, hyl, hyc] using And.intro hno hyes

/-- If the matching status agrees at the two ends, neither matching row is a corner row. -/
theorem source_same_no_corner {n : ℕ} (a : Fin (n + 1)) (q : Fin n)
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y)
    (he : r.IsEmpty) (ha : (a, q.castSucc) ∈ r.toGridRectangle.coveredSquares)
    (hs : Source a q x ↔ Source a q y) :
    r.bottom ≠ q.castSucc ∧ r.bottom ≠ q.succ ∧
      r.top ≠ q.castSucc ∧ r.top ≠ q.succ := by
  have hrow : q.castSucc ∈ Grid.cIco r.bottom r.top :=
    (GridRectangle.mem_coveredSquares _ _).mp ha |>.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hb
    have h := source_of_rectangle_bottom a q r he ha hb
    exact h.1 (hs.mpr h.2)
  · intro hb
    rw [hb] at hrow
    have ht : r.top ≠ q.succ := fun h => r.bottom_ne_top (hb.trans h.symm)
    exact Finset.disjoint_left.mp (Grid.disjoint_cIco_swap _ _) hrow
      (Grid.castSucc_mem_cIco_succ ht)
  · intro ht
    exact Grid.right_notMem_cIco _ _ (ht ▸ hrow)
  · intro ht
    have h := source_of_rectangle_top a q r he ha ht
    exact h.1 (hs.mpr h.2)

private theorem transpose_eq_of_not_corner {n : ℕ} {x y : GridState n}
    (r : GridRectangleBetween x y) (q : Fin n)
    (hb : r.bottom ≠ q) (ht : r.top ≠ q) : y.transpose q = x.transpose q := by
  apply transpose_eq_of_apply_eq y
  have hc := x.apply_transpose_apply q
  have hl : x.transpose q ≠ r.left := fun h => hb ((congrArg x h).symm.trans hc)
  have hr : x.transpose q ≠ r.right := fun h => ht ((congrArg x h).symm.trans hc)
  exact (r.map_of_ne _ hl hr).trans hc

/-- Crossing the matching square cannot change a matching source into a nonsource. -/
theorem source_rectangle_preserves {n : ℕ} (a : Fin (n + 1)) (q : Fin n)
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y)
    (he : r.IsEmpty) (ha : (a, q.castSucc) ∈ r.toGridRectangle.coveredSquares)
    (hx : Source a q x) : Source a q y := by
  by_cases hb : r.bottom = q.castSucc
  · exact (source_of_rectangle_bottom a q r he ha hb).2
  by_cases ht : r.top = q.succ
  · exact (source_of_rectangle_top a q r he ha ht).2
  have hrow : q.castSucc ∈ Grid.cIco r.bottom r.top :=
    (GridRectangle.mem_coveredSquares _ _).mp ha |>.2
  have ht0 : r.top ≠ q.castSucc := fun h => Grid.right_notMem_cIco _ _ (h ▸ hrow)
  have hb1 : r.bottom ≠ q.succ := by
    intro h
    rw [h] at hrow
    exact Finset.disjoint_left.mp (Grid.disjoint_cIco_swap _ _) hrow
      (Grid.castSucc_mem_cIco_succ ht)
  simpa only [Source, transpose_eq_of_not_corner r q.castSucc hb ht0,
    transpose_eq_of_not_corner r q.succ hb1 ht] using hx


/-- A source on the northwest corner cannot start an empty rectangle through the square. -/
theorem not_cover_of_source_northwest {n : ℕ} (a : Fin (n + 1)) (q : Fin n)
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y) (he : r.IsEmpty)
    (hx : x a = q.succ) : (a, q.castSucc) ∉ r.toGridRectangle.coveredSquares := by
  intro ha
  obtain ⟨hcol, hrow⟩ := (GridRectangle.mem_coveredSquares _ _).mp ha
  have har : a ≠ r.right := fun h => Grid.right_notMem_cIco _ _ (h ▸ hcol)
  have ht : q.succ ≠ r.top := by
    intro h
    apply har
    exact x.toPerm.injective (hx.trans h)
  have hr : q.succ ∈ Grid.cIoo r.bottom r.top := by
    have htv : q.val + 1 ≠ r.top.val := fun h => ht (Fin.ext h)
    simp only [GridRectangle.mem_coveredRows, GridRectangleBetween.toGridRectangle_bottom,
      GridRectangleBetween.toGridRectangle_top, Grid.mem_cIco, Fin.val_castSucc] at hrow
    simp only [Grid.mem_cIoo, Fin.val_succ]
    split_ifs at * <;> omega
  have hal : a ≠ r.left := by
    intro h
    have hbottom : r.bottom = q.succ := (congrArg x h).symm.trans hx
    rw [hbottom] at hr
    exact Grid.left_notMem_cIoo _ _ hr
  have hc : a ∈ Grid.cIoo r.left r.right := Grid.mem_cIoo_of_mem_cIco hcol hal
  exact (r.isEmpty_iff_forall_notMem_cIoo.mp he) a hc (hx ▸ hr)

/-- No empty rectangle through the square ends at a southwest-corner target. -/
theorem not_cover_of_target_southwest {n : ℕ} (a : Fin (n + 1)) (q : Fin n)
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y) (he : r.IsEmpty)
    (hy : y a = q.castSucc) : (a, q.castSucc) ∉ r.toGridRectangle.coveredSquares := by
  intro ha
  obtain ⟨hcol, hrow⟩ := (GridRectangle.mem_coveredSquares _ _).mp ha
  have har : a ≠ r.right := fun h => Grid.right_notMem_cIco _ _ (h ▸ hcol)
  have hal : a ≠ r.left := by
    intro h
    have htop : r.top = q.castSucc := r.map_left.symm.trans ((congrArg y h).symm.trans hy)
    change q.castSucc ∈ Grid.cIco r.bottom r.top at hrow
    rw [htop] at hrow
    exact Grid.right_notMem_cIco _ _ hrow
  have hbottom : q.castSucc ≠ r.bottom := by
    intro h
    apply har
    exact y.toPerm.injective (hy.trans (h.trans r.map_right.symm))
  have hc : a ∈ Grid.cIoo r.left r.right := Grid.mem_cIoo_of_mem_cIco hcol hal
  have hr : y a ∈ Grid.cIoo (y r.right) (y r.left) := by
    rw [r.map_right, r.map_left, hy]
    exact Grid.mem_cIoo_of_mem_cIco hrow hbottom
  exact (r.isEmpty_iff_forall_notMem_cIoo_target.mp he) a hc hr

/-- A southwest-corner source crosses to a row-matching source. -/
theorem source_of_southwest {n : ℕ} (a : Fin (n + 1)) (q : Fin n)
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y) (he : r.IsEmpty)
    (hx : x a = q.castSucc) (ha : (a, q.castSucc) ∈ r.toGridRectangle.coveredSquares) :
    Source a q y := by
  obtain ⟨hcol, hrow⟩ := (GridRectangle.mem_coveredSquares _ _).mp ha
  have hal : a = r.left := by
    by_contra h
    have hc : a ∈ Grid.cIoo r.left r.right := Grid.mem_cIoo_of_mem_cIco hcol h
    have hb : q.castSucc ≠ r.bottom := fun heq => h (x.toPerm.injective (hx.trans heq))
    exact (r.isEmpty_iff_forall_notMem_cIoo.mp he) a hc
      (hx ▸ Grid.mem_cIoo_of_mem_cIco hrow hb)
  exact (source_of_rectangle_bottom a q r he ha ((congrArg x hal).symm.trans hx)).2


/-- A source-to-northwest-target rectangle cannot contain the matching square. -/
theorem not_cover_of_source_target_northwest {n : ℕ} (a : Fin (n + 1)) (q : Fin n)
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y) (he : r.IsEmpty)
    (hx : Source a q x) (hy : y a = q.succ) :
    (a, q.castSucc) ∉ r.toGridRectangle.coveredSquares := by
  intro ha
  have hcol := ((GridRectangle.mem_coveredSquares _ _).mp ha).1
  have har : a ≠ r.right := fun h => Grid.right_notMem_cIco _ _ (h ▸ hcol)
  by_cases hal : a = r.left
  · have ht : r.top = q.succ := r.map_left.symm.trans ((congrArg y hal).symm.trans hy)
    exact (source_of_rectangle_top a q r he ha ht).1 hx
  · have hxa : x a = q.succ := (r.map_of_ne a hal har).symm.trans hy
    exact not_cover_of_source_northwest a q r he hxa ha

/-- Moving the column through its successor changes arc membership only at the endpoints. -/
theorem adjacent_column_arc {n : ℕ} (a : Fin n) (l r : Fin (n + 1)) :
    (a.castSucc ∈ Grid.cIco l r ∨ a.succ = l) ↔
      (a.succ ∈ Grid.cIco l r ∨ a.succ = r) := by
  simp only [Grid.mem_cIco, Fin.val_castSucc, Fin.val_succ, Fin.ext_iff]
  split_ifs <;> omega

/-- The two row-matching kernel supports agree after adjoining their opposite critical sets. -/
theorem adjacent_source_or_corner {n : ℕ} (a q : Fin n) (x : GridState (n + 1)) :
    (RowMatchingSource a q x ∨ x a.succ = q.succ) ↔
      (Source a.succ q x ∨ x a.succ = q.castSucc) := by
  have hv (r : Fin (n + 1)) : x a.succ = r ↔ a.succ = x.transpose r := by
    constructor
    · intro h
      exact (x.transpose_apply_apply a.succ).symm.trans (congrArg x.transpose h)
    · intro h
      exact (congrArg x h).trans (x.apply_transpose_apply r)
  rw [hv, hv]
  exact adjacent_column_arc a (x.transpose q.succ) (x.transpose q.castSucc)

end OnLeConjecture.KnotFloer.GridFull.RowMatchingAt
