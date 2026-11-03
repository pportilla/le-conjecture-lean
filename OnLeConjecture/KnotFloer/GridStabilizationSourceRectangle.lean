/-
Copyright (c) 2026 The Tau Ceti contributors and Pablo Portilla Cuadrado.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Adapted from Tau Ceti (https://github.com/TauCetiProject/TauCeti); see THIRD_PARTY_NOTICES.md.
Authors: The Tau Ceti contributors, Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingSupport

/-!
# The crossing rectangle from a matching source

For a source of the stabilization row matching, an empty rectangle ending at a
center state and crossing the southeast X is necessarily the height-one matching
rectangle. This removes all other such rectangle contributions even when crossings
of the remaining X markings are allowed.

The height-one O-weight argument is adapted from
`stabilizeXRowSwapRectangle_mem_filter_XHomotopyRectangles` in
`TauCeti/KnotTheory/Grid/Stabilization/Comparison.lean`, commit
`eb4dd2412a1cd62f73128361bfd3cb422df32e37`, retrieved 2026-10-29.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

private theorem between_successor_and_right_of_predecessor_mem {n : ℕ} (a : Fin n)
    {c d : Fin (n + 1)} (hc : c ≠ a.succ) (hd : d ≠ a.succ)
    (h : a.castSucc ∈ Grid.cIco c d) : d ∈ Grid.cIoo a.succ c := by
  have hcv : c.val ≠ a.val + 1 := fun h => hc (Fin.ext h)
  have hdv : d.val ≠ a.val + 1 := fun h => hd (Fin.ext h)
  rw [Grid.mem_cIoo]
  refine ⟨hc.symm, ?_⟩
  rw [Grid.mem_cIco] at h
  simp only [Fin.val_succ, Fin.val_castSucc] at h ⊢
  split_ifs at * <;> omega

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- A source-to-center crossing rectangle is the height-one row matching rectangle. -/
theorem localComparisonRectangle_matching_source_shape
    (i : G.StabilizeXOffCenterState s) (x : GridState n)
    (hi : G.StabilizeXMatchingSource s (.inl i))
    (r : GridRectangleBetween i.val (x.insertPoint s.succ (G.X s).succ))
    (hr : r ∈ localComparisonRectangles G s (.inl i) (.inr x)) :
    r.left = s.succ ∧ r.bottom = (G.X s).castSucc ∧ r.top = (G.X s).succ := by
  classical
  have hm := Finset.mem_filter.mp hr
  have he := (GridRectangleBetween.mem_emptyRectangles r).mp hm.1
  have hsquare : (s.succ, (G.X s).castSucc) ∈ r.toGridRectangle.coveredSquares := by
    have hh := hm.2.1
    change (s.succ, (G.stabilizeX s.castSucc (G.X s).castSucc s).X s.succ) ∈
      r.toGridRectangle.coveredSquares at hh
    rw [GridDiagram.stabilizeX_castSucc_X, GridState.insertPoint_apply_newColumn] at hh
    exact hh
  have hcols := (GridRectangle.mem_coveredSquares _ _).mp hsquare |>.1
  have hrows := (GridRectangle.mem_coveredSquares _ _).mp hsquare |>.2
  have hb : s.succ ≠ r.right := by
    intro h
    simp only [GridRectangle.mem_coveredColumns,
      GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, h, Grid.right_notMem_cIco] at hcols
  have hl : r.left = s.succ := by
    by_contra h
    have heq := r.map_of_ne s.succ (Ne.symm h) hb
    rw [GridState.insertPoint_apply_newColumn] at heq
    exact i.2 heq.symm
  have ht : r.top = (G.X s).succ := by
    have h := r.map_left
    rw [hl, GridState.insertPoint_apply_newColumn] at h
    exact h.symm
  refine ⟨hl, ?_, ht⟩
  by_contra hbottom
  let d := i.val.transpose (G.X s).castSucc
  have hdvalue : i.val d = (G.X s).castSucc := i.val.apply_transpose_apply _
  have hd : d ≠ s.succ := by
    intro h
    apply hbottom
    change i.val r.left = (G.X s).castSucc
    exact (congrArg i.val hl).trans ((congrArg i.val h.symm).trans hdvalue)
  have hc : r.right ≠ s.succ := hb.symm
  have hright : i.val.transpose (G.X s).succ = r.right := by
    exact (congrArg i.val.transpose ht.symm).trans
      (i.val.transpose_apply_apply r.right)
  have hsrc : s.castSucc ∈ Grid.cIco r.right d := by
    have hi' := hi
    rw [G.stabilizeXMatchingSource_iff_notMem_cIco s,
      GridDiagram.stabilizeXConeStateEquiv_apply_inl, hright] at hi'
    have hdc : d ≠ r.right := by
      intro h
      have hv := (congrArg i.val h).symm.trans hdvalue
      exact Fin.castSucc_lt_succ.ne (hv.symm.trans ht)
    have hm : s.castSucc ∈ Grid.cIco d r.right ∪ Grid.cIco r.right d := by
      rw [Grid.cIco_union_swap hdc]
      exact Finset.mem_univ _
    exact (Finset.mem_union.mp hm).resolve_left hi'
  have hdcol : d ∈ Grid.cIoo r.left r.right := by
    rw [hl]
    exact between_successor_and_right_of_predecessor_mem s hc hd hsrc
  have hdrow : i.val d ∈ Grid.cIoo (i.val r.left) (i.val r.right) := by
    rw [hdvalue]
    exact Grid.mem_cIoo_of_mem_cIco hrows (Ne.symm hbottom)
  exact (r.isEmpty_iff_forall_notMem_cIoo.mp he) d hdcol hdrow

/-- The target of a source-to-center crossing is exactly the matching partner. -/
theorem localComparisonRectangle_matching_source_target
    (i : G.StabilizeXOffCenterState s) (x : GridState n)
    (hi : G.StabilizeXMatchingSource s (.inl i))
    (r : GridRectangleBetween i.val (x.insertPoint s.succ (G.X s).succ))
    (hr : r ∈ localComparisonRectangles G s (.inl i) (.inr x)) :
    G.stabilizeXMatching s (.inl i) = .inr x := by
  obtain ⟨_, hb, ht⟩ := localComparisonRectangle_matching_source_shape G s i x hi r hr
  apply (G.stabilizeXConeStateEquiv s).injective
  rw [G.stabilizeXConeStateEquiv_apply_stabilizeXMatching,
    GridDiagram.stabilizeXConeStateEquiv_apply_inl,
    GridDiagram.stabilizeXConeStateEquiv_apply_inr]
  exact (r.target_eq_swapRows.trans (by rw [← r.bottom_def, ← r.top_def, hb, ht])).symm

/-- A matching source contributes at most one rectangle to any fixed center state. -/
theorem localComparisonRectangles_matching_source_subsingleton
    (i : G.StabilizeXOffCenterState s) (x : GridState n)
    (hi : G.StabilizeXMatchingSource s (.inl i)) :
    ∀ r ∈ localComparisonRectangles G s (.inl i) (.inr x),
      ∀ r' ∈ localComparisonRectangles G s (.inl i) (.inr x), r = r' := by
  intro r hr r' hr'
  apply GridRectangleBetween.left_injective
  exact (localComparisonRectangle_matching_source_shape G s i x hi r hr).1.trans
    (localComparisonRectangle_matching_source_shape G s i x hi r' hr').1.symm

/-- The only crossing rectangle from a matching source covers no O markings. -/
theorem localComparisonRectangle_matching_source_OColumns
    (i : G.StabilizeXOffCenterState s) (x : GridState n)
    (hi : G.StabilizeXMatchingSource s (.inl i))
    (r : GridRectangleBetween i.val (x.insertPoint s.succ (G.X s).succ))
    (hr : r ∈ localComparisonRectangles G s (.inl i) (.inr x)) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle = ∅ := by
  classical
  obtain ⟨hl, hb, ht⟩ := localComparisonRectangle_matching_source_shape G s i x hi r hr
  have hrow : r.toGridRectangle.coveredRows = {(G.X s).castSucc} :=
    Grid.cIco_eq_singleton_iff.mpr ⟨hb,
      ht.trans (by rw [finRotate_apply, Fin.coeSucc_eq_succ]), by
        rw [GridRectangleBetween.toGridRectangle_bottom,
          GridRectangleBetween.toGridRectangle_top, hb, ht]
        exact Fin.castSucc_lt_succ.ne⟩
  refine Finset.eq_empty_iff_forall_notMem.mpr fun c hc => ?_
  rw [GridDiagram.mem_OColumns, GridRectangle.mem_coveredSquares, hrow,
    Finset.mem_singleton, GridDiagram.stabilizeX_O,
    GridDiagram.stabilizeX_O_eq_castSucc_iff] at hc
  obtain ⟨hc, rfl⟩ := hc
  simp only [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
    GridRectangleBetween.toGridRectangle_right, hl] at hc
  exact Finset.disjoint_left.mp (Grid.disjoint_cIco_swap _ _) hc
    (Grid.castSucc_mem_cIco_succ (fun h => r.left_ne_right (hl.trans h.symm)))

/-- If the matching partner is a center state, its crossing rectangle exists. -/
theorem localComparisonRectangles_nonempty_of_matching_partner
    (i : G.StabilizeXOffCenterState s) (x : GridState n)
    (hi : G.StabilizeXMatchingSource s (.inl i))
    (hx : G.stabilizeXMatching s (.inl i) = .inr x) :
    (localComparisonRectangles G s (.inl i) (.inr x)).Nonempty := by
  classical
  have hc := G.stabilizeXReducedCone_single_apply_stabilizeXMatching s (ZMod 2) (.inl i) hi
  rw [hx, LinearMap.sumMappingCone_single_inl_apply_inr,
    GridDiagram.constantCoeffReduction_stabilizeXOffCenterToCenter_single_apply,
    one_mul] at hc
  have hn : (((G.stabilizeX s.castSucc (G.X s).castSucc s).XHomotopyRectangles s.succ
      i.val (x.insertPoint s.succ (G.X s).succ)).filter fun r =>
        (G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle = ∅).card ≠ 0 := by
    intro hzero
    rw [hzero, Nat.cast_zero] at hc
    exact zero_ne_one hc
  obtain ⟨r, hr⟩ := Finset.card_ne_zero.mp hn
  exact ⟨r, comparisonConeRectangles_subset_localComparisonRectangles G s (.inl i) (.inr x)
    (Finset.mem_filter.mp hr).1⟩

/-- The full comparison coefficient on a source is exactly the matching-partner indicator. -/
theorem fullStabilizationTransferredRetraction_proj_source_coefficient_eq
    (R : Type*) [CommRing R] [CharP R 2]
    (i : G.StabilizeXOffCenterState s)
    (hi : G.StabilizeXMatchingSource s (.inl i)) (x : GridState n) :
    ((fullStabilizationTransferredRetraction G s R).proj (single i.val 1)).1 x =
      if G.stabilizeXMatching s (.inl i) = .inr x then 1 else 0 := by
  classical
  rw [fullStabilizationTransferredRetraction_proj_source_coefficient G s R i hi x]
  split_ifs with hx
  · obtain ⟨r, hr⟩ := localComparisonRectangles_nonempty_of_matching_partner G s i x hi hx
    have hset : localComparisonRectangles G s (.inl i) (.inr x) = {r} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨hr, fun r' hr' =>
        localComparisonRectangles_matching_source_subsingleton G s i x hi r' hr' r hr⟩
    rw [hset, Finset.sum_singleton]
    dsimp only [comparisonConeState] at r hr ⊢
    rw [localComparisonRectangle_matching_source_OColumns G s i x hi r hr,
      Finset.card_empty, Nat.cast_zero, LaurentPolynomial.T_zero]
  · apply Finset.sum_eq_zero
    intro r hr
    exact False.elim (hx (localComparisonRectangle_matching_source_target G s i x hi r hr))

end OnLeConjecture.KnotFloer.GridFull
