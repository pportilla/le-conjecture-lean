/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationCriticalGenerators
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Rectangle.Relabeling

/-!
# Rectangles through a square and the adjacent-row matching

These geometric lemmas concern empty rectangles containing the square immediately
below the two matching rows. There is no restriction on X crossings.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

/-- The source condition for the row matching at a specified square. -/
def RowMatchingSource {n : ℕ} (a q : Fin n) (x : GridState (n + 1)) : Prop :=
  a.castSucc ∈ Grid.cIco (x.transpose q.succ) (x.transpose q.castSucc)

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
theorem rowMatchingSource_of_rectangle_bottom {n : ℕ} (a q : Fin n)
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y)
    (he : r.IsEmpty) (ha : (a.castSucc, q.castSucc) ∈ r.toGridRectangle.coveredSquares)
    (hb : r.bottom = q.castSucc) : ¬RowMatchingSource a q x ∧ RowMatchingSource a q y := by
  classical
  have hac : a.castSucc ∈ Grid.cIco r.left r.right :=
    (GridRectangle.mem_coveredSquares _ _).mp ha |>.1
  have hxl : x.transpose q.castSucc = r.left := transpose_eq_of_apply_eq x hb
  have hyr : y.transpose q.castSucc = r.right :=
    transpose_eq_of_apply_eq y (r.map_right.trans hb)
  by_cases ht : r.top = q.succ
  · have hxr : x.transpose q.succ = r.right := transpose_eq_of_apply_eq x ht
    have hyl : y.transpose q.succ = r.left :=
      transpose_eq_of_apply_eq y (r.map_left.trans ht)
    simp only [RowMatchingSource, hxl, hyr, hxr, hyl]
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
    simpa only [RowMatchingSource, hxl, hyr, hyc] using And.intro hno hyes

/-- A rectangle ending in the upper matching row changes a nonsource to a source. -/
theorem rowMatchingSource_of_rectangle_top {n : ℕ} (a q : Fin n)
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y)
    (he : r.IsEmpty) (ha : (a.castSucc, q.castSucc) ∈ r.toGridRectangle.coveredSquares)
    (ht : r.top = q.succ) : ¬RowMatchingSource a q x ∧ RowMatchingSource a q y := by
  classical
  by_cases hb : r.bottom = q.castSucc
  · exact rowMatchingSource_of_rectangle_bottom a q r he ha hb
  have hac : a.castSucc ∈ Grid.cIco r.left r.right :=
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
  simpa only [RowMatchingSource, hxr, hyl, hyc] using And.intro hno hyes

/-- If the matching status agrees at the two ends, neither matching row is a corner row. -/
theorem rowMatchingSource_same_no_corner {n : ℕ} (a q : Fin n)
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y)
    (he : r.IsEmpty) (ha : (a.castSucc, q.castSucc) ∈ r.toGridRectangle.coveredSquares)
    (hs : RowMatchingSource a q x ↔ RowMatchingSource a q y) :
    r.bottom ≠ q.castSucc ∧ r.bottom ≠ q.succ ∧
      r.top ≠ q.castSucc ∧ r.top ≠ q.succ := by
  have hrow : q.castSucc ∈ Grid.cIco r.bottom r.top :=
    (GridRectangle.mem_coveredSquares _ _).mp ha |>.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hb
    have h := rowMatchingSource_of_rectangle_bottom a q r he ha hb
    exact h.1 (hs.mpr h.2)
  · intro hb
    rw [hb] at hrow
    have ht : r.top ≠ q.succ := fun h => r.bottom_ne_top (hb.trans h.symm)
    exact Finset.disjoint_left.mp (Grid.disjoint_cIco_swap _ _) hrow
      (Grid.castSucc_mem_cIco_succ ht)
  · intro ht
    exact Grid.right_notMem_cIco _ _ (ht ▸ hrow)
  · intro ht
    have h := rowMatchingSource_of_rectangle_top a q r he ha ht
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
theorem rowMatchingSource_rectangle_preserves {n : ℕ} (a q : Fin n)
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y)
    (he : r.IsEmpty) (ha : (a.castSucc, q.castSucc) ∈ r.toGridRectangle.coveredSquares)
    (hx : RowMatchingSource a q x) : RowMatchingSource a q y := by
  by_cases hb : r.bottom = q.castSucc
  · exact (rowMatchingSource_of_rectangle_bottom a q r he ha hb).2
  by_cases ht : r.top = q.succ
  · exact (rowMatchingSource_of_rectangle_top a q r he ha ht).2
  have hrow : q.castSucc ∈ Grid.cIco r.bottom r.top :=
    (GridRectangle.mem_coveredSquares _ _).mp ha |>.2
  have ht0 : r.top ≠ q.castSucc := fun h => Grid.right_notMem_cIco _ _ (h ▸ hrow)
  have hb1 : r.bottom ≠ q.succ := by
    intro h
    rw [h] at hrow
    exact Finset.disjoint_left.mp (Grid.disjoint_cIco_swap _ _) hrow
      (Grid.castSucc_mem_cIco_succ ht)
  simpa only [RowMatchingSource, transpose_eq_of_not_corner r q.castSucc hb ht0,
    transpose_eq_of_not_corner r q.succ hb1 ht] using hx

private theorem successor_mem_open_of_predecessor_mem {n : ℕ} (q : Fin n)
    {b t : Fin (n + 1)} (h : q.castSucc ∈ Grid.cIoo b t) (ht : q.succ ≠ t) :
    q.succ ∈ Grid.cIoo b t := by
  have htv : q.val + 1 ≠ t.val := fun heq => ht (Fin.ext heq)
  rw [Grid.mem_cIoo] at h ⊢
  refine ⟨h.1, ?_⟩
  simp only [Fin.val_castSucc, Fin.val_succ] at h ⊢
  split_ifs at * <;> omega

/-- The two matching rows lie in the interior of a status-preserving crossing rectangle. -/
theorem rowMatchingSource_same_rows_interior {n : ℕ} (a q : Fin n)
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y)
    (he : r.IsEmpty) (ha : (a.castSucc, q.castSucc) ∈ r.toGridRectangle.coveredSquares)
    (hs : RowMatchingSource a q x ↔ RowMatchingSource a q y) :
    q.castSucc ∈ Grid.cIoo r.bottom r.top ∧ q.succ ∈ Grid.cIoo r.bottom r.top := by
  have hn := rowMatchingSource_same_no_corner a q r he ha hs
  have hrow : q.castSucc ∈ Grid.cIco r.bottom r.top :=
    (GridRectangle.mem_coveredSquares _ _).mp ha |>.2
  have h0 := Grid.mem_cIoo_of_mem_cIco hrow hn.1.symm
  exact ⟨h0, successor_mem_open_of_predecessor_mem q h0 hn.2.2.2.symm⟩

/-- Swapping the two matching rows leaves the rectangle region unchanged. -/
theorem rowMatchingSource_same_relabel_shape {n : ℕ} (a q : Fin n)
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y)
    (he : r.IsEmpty) (ha : (a.castSucc, q.castSucc) ∈ r.toGridRectangle.coveredSquares)
    (hs : RowMatchingSource a q x ↔ RowMatchingSource a q y) :
    (GridRectangleBetween.relabelRowsEquiv (Equiv.swap q.castSucc q.succ) x y r).toGridRectangle =
      r.toGridRectangle := by
  have hn := rowMatchingSource_same_no_corner a q r he ha hs
  apply GridRectangle.ext
  · exact GridRectangleBetween.relabelRowsEquiv_apply_left _ r
  · exact GridRectangleBetween.relabelRowsEquiv_apply_right _ r
  · rw [GridRectangleBetween.toGridRectangle_bottom,
      GridRectangleBetween.relabelRowsEquiv_apply_bottom]
    exact Equiv.swap_apply_of_ne_of_ne hn.1 hn.2.1
  · rw [GridRectangleBetween.toGridRectangle_top,
      GridRectangleBetween.relabelRowsEquiv_apply_top]
    exact Equiv.swap_apply_of_ne_of_ne hn.2.2.1 hn.2.2.2

/-- The same row swap preserves emptiness for a status-preserving crossing rectangle. -/
theorem rowMatchingSource_same_relabel_empty {n : ℕ} (a q : Fin n)
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y)
    (he : r.IsEmpty) (ha : (a.castSucc, q.castSucc) ∈ r.toGridRectangle.coveredSquares)
    (hs : RowMatchingSource a q x ↔ RowMatchingSource a q y) :
    (GridRectangleBetween.relabelRowsEquiv (Equiv.swap q.castSucc q.succ) x y r).IsEmpty := by
  have hm := rowMatchingSource_same_rows_interior a q r he ha hs
  rw [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
    rowMatchingSource_same_relabel_shape a q r he ha hs,
    GridRectangle.isEmptyFor_iff_forall_notMem_cIoo]
  intro c hc hr
  have hswap : Equiv.swap q.castSucc q.succ (x c) ∈ Grid.cIoo r.bottom r.top →
      x c ∈ Grid.cIoo r.bottom r.top := by
    intro h
    by_cases h0 : x c = q.castSucc
    · exact h0 ▸ hm.1
    by_cases h1 : x c = q.succ
    · exact h1 ▸ hm.2
    simpa only [Equiv.swap_apply_of_ne_of_ne h0 h1] using h
  exact (r.isEmpty_iff_forall_notMem_cIoo.mp he) c hc (hswap hr)

/-- Swapping the adjacent rows interchanges matching sources and nonsources. -/
theorem rowMatchingSource_relabel_swap {n : ℕ} (a q : Fin n) (x : GridState (n + 1)) :
    RowMatchingSource a q (x.relabelRows (Equiv.swap q.castSucc q.succ)) ↔
      ¬RowMatchingSource a q x := by
  simp only [RowMatchingSource, GridState.relabelRows_transpose,
    GridState.relabelColumns_apply, Equiv.symm_swap, Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  have hne : x.transpose q.castSucc ≠ x.transpose q.succ :=
    x.transpose.toPerm.injective.ne Fin.castSucc_lt_succ.ne
  constructor
  · exact fun h h' => Finset.disjoint_left.mp (Grid.disjoint_cIco_swap _ _) h h'
  · intro h
    have hm : a.castSucc ∈ Grid.cIco (x.transpose q.castSucc) (x.transpose q.succ) ∪
        Grid.cIco (x.transpose q.succ) (x.transpose q.castSucc) := by
      rw [Grid.cIco_union_swap hne]
      exact Finset.mem_univ _
    exact (Finset.mem_union.mp hm).resolve_right h

/-- Row interchange gives a bijection on crossing empty rectangles with equal endpoint status. -/
theorem rowMatchingSource_same_relabel_crossing_iff {n : ℕ} (a q : Fin n)
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y)
    (hs : RowMatchingSource a q x ↔ RowMatchingSource a q y) :
    let E := GridRectangleBetween.relabelRowsEquiv (Equiv.swap q.castSucc q.succ) x y
    (E r).IsEmpty ∧ (a.castSucc, q.castSucc) ∈ (E r).toGridRectangle.coveredSquares ↔
      r.IsEmpty ∧ (a.castSucc, q.castSucc) ∈ r.toGridRectangle.coveredSquares := by
  dsimp only
  let ρ := Equiv.swap q.castSucc q.succ
  let E := GridRectangleBetween.relabelRowsEquiv ρ x y
  have hs' : RowMatchingSource a q (x.relabelRows ρ) ↔
      RowMatchingSource a q (y.relabelRows ρ) := by
    simp only [ρ, rowMatchingSource_relabel_swap]
    exact not_congr hs
  constructor
  · rintro ⟨he, ha⟩
    have he2 := rowMatchingSource_same_relabel_empty a q (E r) he ha hs'
    have hshape := rowMatchingSource_same_relabel_shape a q (E r) he ha hs'
    have hdouble :
        (GridRectangleBetween.relabelRowsEquiv ρ (x.relabelRows ρ) (y.relabelRows ρ)
          (E r)).toGridRectangle = r.toGridRectangle := by
      ext <;> simp only [E, ρ, GridRectangleBetween.toGridRectangle_left,
        GridRectangleBetween.toGridRectangle_right, GridRectangleBetween.toGridRectangle_bottom,
        GridRectangleBetween.toGridRectangle_top, GridRectangleBetween.relabelRowsEquiv_apply_left,
        GridRectangleBetween.relabelRowsEquiv_apply_right,
        GridRectangleBetween.relabelRowsEquiv_apply_bottom,
        GridRectangleBetween.relabelRowsEquiv_apply_top, Equiv.swap_apply_self]
    have hempty : r.IsEmpty := by
      simpa only [E, ρ, GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo,
        GridRectangleBetween.relabelRowsEquiv_apply_left,
        GridRectangleBetween.relabelRowsEquiv_apply_right,
        GridRectangleBetween.relabelRowsEquiv_apply_bottom,
        GridRectangleBetween.relabelRowsEquiv_apply_top, GridState.relabelRows_apply,
        Equiv.swap_apply_self] using he2
    change (GridRectangleBetween.relabelRowsEquiv ρ (x.relabelRows ρ) (y.relabelRows ρ)
      (E r)).toGridRectangle = (E r).toGridRectangle at hshape
    rw [hdouble] at hshape
    exact ⟨hempty, by simpa only [hshape] using ha⟩
  · rintro ⟨he, ha⟩
    exact ⟨rowMatchingSource_same_relabel_empty a q r he ha hs,
      by simpa only [rowMatchingSource_same_relabel_shape a q r he ha hs] using ha⟩

/-- The square-derivative coefficient is invariant under row swap when endpoint status agrees. -/
theorem squareDerivative_coefficient_rowSwap {n : ℕ} (a q : Fin n)
    {S : Type*} [CommSemiring S] (w : Fin (n + 1) × Fin (n + 1) → S)
    (x y : GridState (n + 1)) (hs : RowMatchingSource a q x ↔ RowMatchingSource a q y) :
    (squareWeightedCoefficient (deformAtSquare w a.castSucc q.castSucc)
      (x.relabelRows (Equiv.swap q.castSucc q.succ))
      (y.relabelRows (Equiv.swap q.castSucc q.succ))).coeff 1 =
        (squareWeightedCoefficient (deformAtSquare w a.castSucc q.castSucc) x y).coeff 1 := by
  classical
  rw [coeff_one_squareWeightedCoefficient_deformAtSquare,
    coeff_one_squareWeightedCoefficient_deformAtSquare]
  symm
  let E := GridRectangleBetween.relabelRowsEquiv (Equiv.swap q.castSucc q.succ) x y
  have hmem (r : GridRectangleBetween x y) :
      E r ∈ (GridRectangleBetween.emptyRectangles _ _).filter
        (fun r => (a.castSucc, q.castSucc) ∈ r.toGridRectangle.coveredSquares) ↔
      r ∈ (GridRectangleBetween.emptyRectangles x y).filter
        (fun r => (a.castSucc, q.castSucc) ∈ r.toGridRectangle.coveredSquares) := by
    simp only [Finset.mem_filter, GridRectangleBetween.mem_emptyRectangles]
    exact rowMatchingSource_same_relabel_crossing_iff a q r hs
  apply Finset.sum_nbij E
  · intro r hr
    exact (hmem r).mpr hr
  · intro r _ r' _ h
    exact E.injective h
  · intro r hr
    refine ⟨E.symm r, ?_, E.apply_symm_apply r⟩
    apply (hmem _).mp
    simpa only [E.apply_symm_apply, Finset.mem_coe] using hr
  · intro r hr
    obtain ⟨he, ha⟩ := Finset.mem_filter.mp hr
    have he' := (GridRectangleBetween.mem_emptyRectangles r).mp he
    exact (congrArg (squareWeight w)
      (rowMatchingSource_same_relabel_shape a q r he' ha hs)).symm

/-- A square derivative has no coefficient from a matching source to a nonsource. -/
theorem squareDerivative_coefficient_eq_zero_of_source {n : ℕ} (a q : Fin n)
    {S : Type*} [CommSemiring S] (w : Fin (n + 1) × Fin (n + 1) → S)
    (x y : GridState (n + 1)) (hx : RowMatchingSource a q x) (hy : ¬RowMatchingSource a q y) :
    (squareWeightedCoefficient (deformAtSquare w a.castSucc q.castSucc) x y).coeff 1 = 0 := by
  classical
  rw [coeff_one_squareWeightedCoefficient_deformAtSquare]
  apply Finset.sum_eq_zero
  intro r hr
  obtain ⟨he, ha⟩ := Finset.mem_filter.mp hr
  exact False.elim (hy (rowMatchingSource_rectangle_preserves a q r
    ((GridRectangleBetween.mem_emptyRectangles r).mp he) ha hx))

private theorem successor_interior_or_right {n : ℕ} (a : Fin n) {l r : Fin (n + 1)}
    (h : a.castSucc ∈ Grid.cIco l r) : a.succ ∈ Grid.cIoo l r ∨ a.succ = r := by
  by_cases hr : a.succ = r
  · exact Or.inr hr
  left
  have hlr : l ≠ r := by
    intro heq
    simp only [heq, Grid.cIco_self, Finset.notMem_empty] at h
  have hrv : a.val + 1 ≠ r.val := fun heq => hr (Fin.ext heq)
  rw [Grid.mem_cIoo]
  refine ⟨hlr, ?_⟩
  rw [Grid.mem_cIco] at h
  simp only [Fin.val_castSucc, Fin.val_succ] at h ⊢
  split_ifs at * <;> omega

private theorem predecessor_not_in_successor_arc {n : ℕ} (a : Fin n) (r : Fin (n + 1)) :
    a.castSucc ∉ Grid.cIco a.succ r := by
  by_cases hr : r = a.succ
  · simp only [hr, Grid.cIco_self, Finset.notMem_empty, not_false_eq_true]
  · exact fun h => Finset.disjoint_left.mp (Grid.disjoint_cIco_swap _ _) h
      (Grid.castSucc_mem_cIco_succ hr)

/-- An empty rectangle cannot cover a square whose southeast corner belongs to its source. -/
theorem not_cover_square_of_source_southeast {n : ℕ} (a q : Fin n)
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y)
    (he : r.IsEmpty) (hx : x a.succ = q.castSucc) :
    (a.castSucc, q.castSucc) ∉ r.toGridRectangle.coveredSquares := by
  intro ha
  obtain ⟨hc, hr⟩ := (GridRectangle.mem_coveredSquares _ _).mp ha
  rcases successor_interior_or_right a hc with hci | hce
  · by_cases hb : r.bottom = q.castSucc
    · have hl : r.left = a.succ := x.toPerm.injective (hb.trans hx.symm)
      exact predecessor_not_in_successor_arc a r.right (hl ▸ hc)
    · have hri := Grid.mem_cIoo_of_mem_cIco hr (Ne.symm hb)
      have hpoint : x a.succ ∈ Grid.cIoo r.bottom r.top := hx ▸ hri
      exact (r.isEmpty_iff_forall_notMem_cIoo.mp he) _ hci hpoint
  · have ht : r.top = q.castSucc := (congrArg x hce.symm).trans hx
    exact Grid.right_notMem_cIco _ _ (ht ▸ hr)

/-- An empty rectangle cannot cover a square whose northeast corner belongs to its target. -/
theorem not_cover_square_of_target_northeast {n : ℕ} (a q : Fin n)
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y)
    (he : r.IsEmpty) (hy : y a.succ = q.succ) :
    (a.castSucc, q.castSucc) ∉ r.toGridRectangle.coveredSquares := by
  intro ha
  obtain ⟨hc, hr⟩ := (GridRectangle.mem_coveredSquares _ _).mp ha
  rcases successor_interior_or_right a hc with hci | hce
  · rcases successor_interior_or_right q hr with hri | hre
    · have hpoint : y a.succ ∈ Grid.cIoo r.bottom r.top := hy ▸ hri
      have hempty := r.isEmpty_iff_forall_notMem_cIoo_target.mp he
      simp only [r.map_right, r.map_left] at hempty
      exact hempty _ hci hpoint
    · have hl : r.left = a.succ := y.toPerm.injective (r.map_left.trans (hre.symm.trans hy.symm))
      exact predecessor_not_in_successor_arc a r.right (hl ▸ hc)
  · have hb : r.bottom = q.succ := r.map_right.symm.trans ((congrArg y hce.symm).trans hy)
    exact predecessor_not_in_successor_arc q r.top (hb ▸ hr)

/-- The derivative vanishes on a source with a southeast point at the selected square. -/
theorem squareDerivative_coefficient_eq_zero_of_source_southeast {n : ℕ} (a q : Fin n)
    {S : Type*} [CommSemiring S] (w : Fin (n + 1) × Fin (n + 1) → S)
    (x y : GridState (n + 1)) (hx : x a.succ = q.castSucc) :
    (squareWeightedCoefficient (deformAtSquare w a.castSucc q.castSucc) x y).coeff 1 = 0 := by
  classical
  rw [coeff_one_squareWeightedCoefficient_deformAtSquare]
  apply Finset.sum_eq_zero
  intro r hr
  obtain ⟨he, ha⟩ := Finset.mem_filter.mp hr
  exact False.elim (not_cover_square_of_source_southeast a q r
    ((GridRectangleBetween.mem_emptyRectangles r).mp he) hx ha)

/-- The derivative has no target with a northeast point at the selected square. -/
theorem squareDerivative_coefficient_eq_zero_of_target_northeast {n : ℕ} (a q : Fin n)
    {S : Type*} [CommSemiring S] (w : Fin (n + 1) × Fin (n + 1) → S)
    (x y : GridState (n + 1)) (hy : y a.succ = q.succ) :
    (squareWeightedCoefficient (deformAtSquare w a.castSucc q.castSucc) x y).coeff 1 = 0 := by
  classical
  rw [coeff_one_squareWeightedCoefficient_deformAtSquare]
  apply Finset.sum_eq_zero
  intro r hr
  obtain ⟨he, ha⟩ := Finset.mem_filter.mp hr
  exact False.elim (not_cover_square_of_target_northeast a q r
    ((GridRectangleBetween.mem_emptyRectangles r).mp he) hy ha)

end OnLeConjecture.KnotFloer.GridFull
