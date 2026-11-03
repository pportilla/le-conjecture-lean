/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationXPartner
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Rectangle.Count

/-!
# The matching coefficients of the full stabilization differential

For a matching source outside the critical partner set, exactly one empty rectangle
joins it to its row-swapped state. This rectangle covers no O marking, so its full
Laurent coefficient is one. No X-avoidance is imposed.
-/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti Finsupp
variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- The thin row rectangle at a matching source avoids the new O and hence every O. -/
theorem stabilizationRowRectangle_source_OColumns (x : GridState (n + 1))
    (hx : RowMatchingSource s (G.X s) x) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
      (G.stabilizeXRowSwapRectangle s x).toGridRectangle = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  rw [GridDiagram.mem_OColumns, GridRectangle.mem_coveredSquares,
    G.coveredRows_stabilizeXRowSwapRectangle, Finset.mem_singleton,
    GridDiagram.stabilizeX_O, GridDiagram.stabilizeX_O_eq_castSucc_iff] at hc
  obtain ⟨hcol, rfl⟩ := hc
  change s.castSucc ∈ Grid.cIco (G.stabilizeXRowSwapRectangle s x).left
    (G.stabilizeXRowSwapRectangle s x).right at hcol
  rw [G.stabilizeXRowSwapRectangle_left, G.stabilizeXRowSwapRectangle_right] at hcol
  exact Finset.disjoint_left.mp (Grid.disjoint_cIco_swap _ _) hcol hx

/-- At a noncritical source the complementary row-swap rectangle is not empty. -/
theorem stabilizationRowRectangle_swapSides_not_empty (x : GridState (n + 1))
    (hx : RowMatchingSource s (G.X s) x) (hcritical : x s.succ ≠ (G.X s).castSucc) :
    ¬(G.stabilizeXRowSwapRectangle s x).swapSides.IsEmpty := by
  classical
  intro he
  let H := G.stabilizeX s.castSucc (G.X s).castSucc s
  let r := G.stabilizeXRowSwapRectangle s x
  have hthin := H.maslovO_sub_two_mul_card_OColumns_eq_maslovO_sub_one
    (G.isEmpty_stabilizeXRowSwapRectangle s x)
  have hother := H.maslovO_sub_two_mul_card_OColumns_eq_maslovO_sub_one he
  rw [stabilizationRowRectangle_source_OColumns G s x hx, Finset.card_empty,
    Nat.cast_zero, mul_zero, sub_zero] at hthin
  have hcard : (H.OColumns r.swapSides.toGridRectangle).card = 0 := by
    have hq : ((H.OColumns r.swapSides.toGridRectangle).card : ℚ) = 0 := by
      change H.maslovO (x.swapRows (G.X s).castSucc (G.X s).succ) -
        2 * ((H.OColumns r.swapSides.toGridRectangle).card : ℚ) = H.maslovO x - 1 at hother
      linarith
    exact_mod_cast hq
  have hempty : H.OColumns r.swapSides.toGridRectangle = ∅ := Finset.card_eq_zero.mp hcard
  have hcols : r.swapSides.toGridRectangle.coveredColumns = {s.castSucc} := by
    apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
    constructor
    · exact ⟨r.swapSides.left, Grid.left_mem_cIco r.swapSides.left_ne_right⟩
    · intro c hc
      by_contra hca
      have hO : H.O c ≠ (G.X s).castSucc := by
        change (G.stabilizeX s.castSucc (G.X s).castSucc s).O c ≠ (G.X s).castSucc
        rw [GridDiagram.stabilizeX_O, ne_eq, G.stabilizeX_O_eq_castSucc_iff s c]
        exact hca
      have hrow : H.O c ∈ r.swapSides.toGridRectangle.coveredRows := by
        rw [GridRectangle.mem_coveredRows, GridRectangleBetween.toGridRectangle_bottom,
          GridRectangleBetween.toGridRectangle_top, GridRectangleBetween.swapSides_bottom,
          GridRectangleBetween.swapSides_top,
          G.stabilizeXRowSwapRectangle_top, G.stabilizeXRowSwapRectangle_bottom,
          Grid.mem_cIco]
        have hv : (H.O c).val ≠ (G.X s).val := fun h => hO (Fin.ext h)
        simp only [Fin.val_succ, Fin.val_castSucc]
        refine ⟨Fin.castSucc_lt_succ.ne', ?_⟩
        split_ifs <;> omega
      have hmem : c ∈ H.OColumns r.swapSides.toGridRectangle :=
        (GridDiagram.mem_OColumns H).mpr ((GridRectangle.mem_coveredSquares _ _).mpr ⟨hc, hrow⟩)
      rw [hempty] at hmem
      exact Finset.notMem_empty c hmem
  obtain ⟨_, hright, _⟩ := Grid.cIco_eq_singleton_iff.mp hcols
  have hleft : r.left = s.succ := by
    simpa only [GridRectangleBetween.swapSides_toGridRectangle,
      GridRectangleBetween.toGridRectangle_left, GridRectangleBetween.toGridRectangle_right,
      finRotate_apply, Fin.coeSucc_eq_succ] using hright
  apply hcritical
  have h := G.stabilizeXRowSwapRectangle_bottom s x
  change x r.left = (G.X s).castSucc at h
  exact (congrArg x hleft).symm.trans h

/-- The thin row rectangle is the unique full empty rectangle on a noncritical matching edge. -/
theorem emptyRectangles_stabilizationMatching_source (x : GridState (n + 1))
    (hx : RowMatchingSource s (G.X s) x) (hcritical : x s.succ ≠ (G.X s).castSucc) :
    GridRectangleBetween.emptyRectangles x (x.swapRows (G.X s).castSucc (G.X s).succ) =
      {G.stabilizeXRowSwapRectangle s x} := by
  classical
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨(GridRectangleBetween.mem_emptyRectangles _).mpr
    (G.isEmpty_stabilizeXRowSwapRectangle s x), ?_⟩
  intro r hr
  rcases (G.stabilizeXRowSwapRectangle s x).eq_or_eq_swapSides r with rfl | rfl
  · rfl
  · exact False.elim (stabilizationRowRectangle_swapSides_not_empty G s x hx hcritical
      ((GridRectangleBetween.mem_emptyRectangles _).mp hr))

/-- Every noncritical row-matching edge has coefficient one in the full Laurent differential. -/
theorem laurentCoefficient_stabilizationMatching_source (R : Type*) [CommSemiring R]
    (x : GridState (n + 1)) (hx : RowMatchingSource s (G.X s) x)
    (hcritical : x s.succ ≠ (G.X s).castSucc) :
    laurentCoefficient (G.stabilizeX s.castSucc (G.X s).castSucc s) R x
      (x.swapRows (G.X s).castSucc (G.X s).succ) = 1 := by
  rw [laurentCoefficient_eq, emptyRectangles_stabilizationMatching_source G s x hx hcritical,
    Finset.sum_singleton, stabilizationRowRectangle_source_OColumns G s x hx,
    Finset.card_empty, Nat.cast_zero, LaurentPolynomial.T_zero]


variable (R : Type*) [CommRing R] [CharP R 2]

/-- Noncritical matching sources have zero full comparison projection. -/
theorem fullStabilizationTransferredRetraction_proj_noncritical_source
    (x : GridState (n + 1)) (hx : RowMatchingSource s (G.X s) x)
    (hcritical : x s.succ ≠ (G.X s).castSucc) :
    (fullStabilizationTransferredRetraction G s R).proj (single x 1) = 0 := by
  classical
  apply fullStabilizationTransferredRetraction_proj_eq_zero_of_source_support
  · intro y hy
    apply Finsupp.single_eq_of_ne
    intro heq
    exact hy (heq.symm ▸ hx)
  · intro y
    apply Finsupp.single_eq_of_ne
    intro heq
    apply hcritical
    have h := congrArg (fun z : GridState (n + 1) => z s.succ) heq
    simpa only [stabilizationPartnerState, GridState.swapRows_apply,
      GridState.insertPoint_apply_newColumn, Equiv.swap_apply_right] using h.symm

/-- The full projection at a matched nonsource satisfies a concrete rectangle recurrence. -/
theorem fullStabilizationTransferredRetraction_proj_matching_recursion
    (x : GridState (n + 1)) (hx : RowMatchingSource s (G.X s) x)
    (hcritical : x s.succ ≠ (G.X s).castSucc) :
    (fullStabilizationTransferredRetraction G s R).proj
      (single (x.swapRows (G.X s).castSucc (G.X s).succ) 1) =
      ∑ y ∈ Finset.univ.erase (x.swapRows (G.X s).castSucc (G.X s).succ),
        laurentCoefficient (G.stabilizeX s.castSucc (G.X s).castSucc s) R x y •
          (fullStabilizationTransferredRetraction G s R).proj (single y 1) := by
  classical
  let C := fullStabilizationTransferredRetraction G s R
  let H := G.stabilizeX s.castSucc (G.X s).castSucc s
  have h := C.proj_dM_apply (single x 1)
  rw [fullStabilizationTransferredRetraction_proj_noncritical_source G s R x hx hcritical,
    map_zero, laurentDifferential_single, laurentOnGenerator, map_sum] at h
  have hsum : ∑ y : GridState (n + 1), laurentCoefficient H R x y • C.proj (single y 1) = 0 := by
    convert h using 1
    apply Finset.sum_congr rfl
    intro y _
    rw [← map_smul, Finsupp.smul_single_one]
  have hs := Finset.add_sum_erase Finset.univ
    (fun y : GridState (n + 1) => laurentCoefficient H R x y • C.proj (single y 1))
    (Finset.mem_univ (x.swapRows (G.X s).castSucc (G.X s).succ))
  rw [hsum, show laurentCoefficient H R x
      (x.swapRows (G.X s).castSucc (G.X s).succ) = 1 from
        laurentCoefficient_stabilizationMatching_source G s R x hx hcritical, one_smul] at hs
  apply Prod.ext
  · apply Finsupp.ext
    intro y
    have hh := congrArg (fun z : LaurentChain R n × LaurentChain R n => z.1 y) hs
    simp only [Prod.fst_add, Finsupp.add_apply, Prod.fst_zero, Finsupp.zero_apply] at hh
    exact CharTwo.add_eq_zero.mp hh
  · apply Finsupp.ext
    intro y
    have hh := congrArg (fun z : LaurentChain R n × LaurentChain R n => z.2 y) hs
    simp only [Prod.snd_add, Finsupp.add_apply, Prod.snd_zero, Finsupp.zero_apply] at hh
    exact CharTwo.add_eq_zero.mp hh

end OnLeConjecture.KnotFloer.GridFull
