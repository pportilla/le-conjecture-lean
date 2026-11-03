/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationRowMatchingAt

/-!
# The derivative at the new X marking

Changing the row-matching column to the adjacent X exchanges the two critical sets.
The full homotopy has the same kernel and has no output at either critical set.
-/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti Finsupp
variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R]

/-- Count all empty rectangles through the new X in the inserted column. -/
noncomputable def stabilizationXDerivative : Module.End (LaurentPolynomial R)
    (LaurentChain R (n + 1)) :=
  squareDerivative (oSquareWeight (G.stabilizeX s.castSucc (G.X s).castSucc s))
    s.succ (G.X s).castSucc

/-- Every state with the southwest critical point is an explicit center partner. -/
theorem exists_stabilizationPartnerState_of_southwest (x : GridState (n + 1))
    (hx : x s.succ = (G.X s).castSucc) :
    ∃ y : GridState n, (stabilizationPartnerState G s y).val = x := by
  have hs : (x.swapRows (G.X s).castSucc (G.X s).succ) s.succ = (G.X s).succ := by
    rw [GridState.swapRows_apply, hx, Equiv.swap_apply_left]
  obtain ⟨y, hy⟩ := GridState.exists_insertPoint_eq hs
  refine ⟨y, ?_⟩
  change (y.insertPoint s.succ (G.X s).succ).swapRows (G.X s).castSucc (G.X s).succ = x
  rw [hy, GridState.swapRows_swapRows]

/-- The X derivative is the full empty-rectangle count through the chosen square. -/
theorem stabilizationXDerivative_single_apply (x y : GridState (n + 1)) :
    stabilizationXDerivative G s R (single x 1) y =
      ∑ r ∈ (GridRectangleBetween.emptyRectangles x y).filter
        (fun r => (s.succ, (G.X s).castSucc) ∈ r.toGridRectangle.coveredSquares),
        squareWeight (oSquareWeight (R := R)
          (G.stabilizeX s.castSucc (G.X s).castSucc s)) r.toGridRectangle := by
  rw [stabilizationXDerivative, squareDerivative, polynomialCoefficientOperator_apply_apply,
    Finsupp.sum_single_index]
  · rw [one_mul, coeff_one_squareWeightedCoefficient_deformAtSquare]
  · exact zero_mul _

/-- The X derivative sends a matching source at its own column only to such sources. -/
theorem stabilizationXDerivative_single_apply_of_source
    (x y : GridState (n + 1)) (hx : RowMatchingAt.Source s.succ (G.X s) x)
    (hy : ¬RowMatchingAt.Source s.succ (G.X s) y) :
    stabilizationXDerivative G s R (single x 1) y = 0 := by
  classical
  rw [stabilizationXDerivative_single_apply]
  apply Finset.sum_eq_zero
  intro r hr
  obtain ⟨he, ha⟩ := Finset.mem_filter.mp hr
  exact False.elim (hy (RowMatchingAt.source_rectangle_preserves s.succ (G.X s) r
    ((GridRectangleBetween.mem_emptyRectangles r).mp he) ha hx))

/-- The X derivative of a southwest critical state also has source-only output. -/
theorem stabilizationXDerivative_single_apply_of_southwest
    (x y : GridState (n + 1)) (hx : x s.succ = (G.X s).castSucc)
    (hy : ¬RowMatchingAt.Source s.succ (G.X s) y) :
    stabilizationXDerivative G s R (single x 1) y = 0 := by
  classical
  rw [stabilizationXDerivative_single_apply]
  apply Finset.sum_eq_zero
  intro r hr
  obtain ⟨he, ha⟩ := Finset.mem_filter.mp hr
  exact False.elim (hy (RowMatchingAt.source_of_southwest s.succ (G.X s) r
    ((GridRectangleBetween.mem_emptyRectangles r).mp he) hx ha))

/-- The X derivative has zero coefficient at every southwest target. -/
theorem stabilizationXDerivative_apply_southwest
    (c : LaurentChain R (n + 1)) (y : GridState (n + 1))
    (hy : y s.succ = (G.X s).castSucc) :
    stabilizationXDerivative G s R c y = 0 := by
  classical
  rw [finiteEnd_apply_apply]
  apply Finset.sum_eq_zero
  intro x _
  have hz : stabilizationXDerivative G s R (single x 1) y = 0 := by
    rw [stabilizationXDerivative_single_apply]
    apply Finset.sum_eq_zero
    intro r hr
    obtain ⟨he, ha⟩ := Finset.mem_filter.mp hr
    exact False.elim (RowMatchingAt.not_cover_of_target_southwest s.succ (G.X s) r
      ((GridRectangleBetween.mem_emptyRectangles r).mp he) hy ha)
  rw [hz, mul_zero]

/-- From a source at the X column the derivative has no northwest target coefficient. -/
theorem stabilizationXDerivative_single_apply_northwest_of_source
    (x y : GridState (n + 1)) (hx : RowMatchingAt.Source s.succ (G.X s) x)
    (hy : y s.succ = (G.X s).succ) :
    stabilizationXDerivative G s R (single x 1) y = 0 := by
  classical
  rw [stabilizationXDerivative_single_apply]
  apply Finset.sum_eq_zero
  intro r hr
  obtain ⟨he, ha⟩ := Finset.mem_filter.mp hr
  exact False.elim (RowMatchingAt.not_cover_of_source_target_northwest s.succ (G.X s) r
    ((GridRectangleBetween.mem_emptyRectangles r).mp he) hx hy ha)

/-- The X derivative sends the homotopy kernel into sources for the X-column matching. -/
theorem stabilizationXDerivative_apply_of_mem_kernelSupport
    (c : LaurentChain R (n + 1)) (hc : c ∈ stabilizationHomotopyKernelSupport G s R)
    (y : GridState (n + 1)) (hy : ¬RowMatchingAt.Source s.succ (G.X s) y) :
    stabilizationXDerivative G s R c y = 0 := by
  classical
  rw [finiteEnd_apply_apply]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : RowMatchingSource s (G.X s) x ∨ x s.succ = (G.X s).succ
  · rcases (RowMatchingAt.adjacent_source_or_corner s (G.X s) x).mp hx with hs | hsw
    · rw [stabilizationXDerivative_single_apply_of_source G s R x y hs hy, mul_zero]
    · rw [stabilizationXDerivative_single_apply_of_southwest G s R x y hsw hy, mul_zero]
  · rw [(Finsupp.mem_supported' _ _).mp hc x hx, zero_mul]

variable [CharP R 2]

/-- The full homotopy has source-only output also for the X-column matching. -/
theorem fullStabilizationTransferredRetraction_homotopy_apply_of_not_X_source
    (c : LaurentChain R (n + 1)) (x : GridState (n + 1))
    (hx : ¬RowMatchingAt.Source s.succ (G.X s) x) :
    (fullStabilizationTransferredRetraction G s R).homotopy c x = 0 := by
  by_cases hs : RowMatchingSource s (G.X s) x
  · have hsw := ((RowMatchingAt.adjacent_source_or_corner s (G.X s) x).mp
      (Or.inl hs)).resolve_left hx
    obtain ⟨y, rfl⟩ := exists_stabilizationPartnerState_of_southwest G s x hsw
    exact fullStabilizationTransferredRetraction_homotopy_apply_partner G s R c y
  · exact fullStabilizationTransferredRetraction_homotopy_apply_of_not_source G s R c x hs

/-- The X derivative preserves the exact kernel of the full homotopy. -/
theorem fullStabilizationTransferredRetraction_homotopy_XDerivative_eq_zero
    (c : LaurentChain R (n + 1))
    (hc : (fullStabilizationTransferredRetraction G s R).homotopy c = 0) :
    (fullStabilizationTransferredRetraction G s R).homotopy
      (stabilizationXDerivative G s R c) = 0 := by
  apply fullStabilizationTransferredRetraction_homotopy_eq_zero_of_mem_kernelSupport
  apply (Finsupp.mem_supported' _ _).mpr
  intro y hy
  apply stabilizationXDerivative_apply_of_mem_kernelSupport G s R c
    ((fullStabilizationTransferredRetraction_homotopy_eq_zero_iff_kernelSupport G s R c).mp hc)
  intro hs
  exact hy ((RowMatchingAt.adjacent_source_or_corner s (G.X s) y).mpr (Or.inl hs))

/-- The X derivative of a homotopy output has no coefficient at any center. -/
theorem stabilizationXDerivative_homotopy_apply_center
    (c : LaurentChain R (n + 1)) (y : GridState (n + 1))
    (hy : y s.succ = (G.X s).succ) :
    stabilizationXDerivative G s R
      ((fullStabilizationTransferredRetraction G s R).homotopy c) y = 0 := by
  classical
  rw [finiteEnd_apply_apply]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hs : RowMatchingAt.Source s.succ (G.X s) x
  · rw [stabilizationXDerivative_single_apply_northwest_of_source G s R x y hs hy, mul_zero]
  · rw [fullStabilizationTransferredRetraction_homotopy_apply_of_not_X_source G s R c x hs,
      zero_mul]

/-- The X derivative of the homotopy image has zero full comparison projection. -/
theorem fullStabilizationTransferredRetraction_proj_XDerivative_homotopy
    (c : LaurentChain R (n + 1)) :
    (fullStabilizationTransferredRetraction G s R).proj
      (stabilizationXDerivative G s R
        ((fullStabilizationTransferredRetraction G s R).homotopy c)) = 0 := by
  apply fullStabilizationTransferredRetraction_proj_eq_zero_of_source_support
  · intro y hy
    by_cases hcenter : y s.succ = (G.X s).succ
    · exact stabilizationXDerivative_homotopy_apply_center G s R c y hcenter
    · apply stabilizationXDerivative_apply_of_mem_kernelSupport G s R _
        (fullStabilizationTransferredRetraction_homotopy_mem_kernelSupport G s R c) y
      intro hs
      exact hy (((RowMatchingAt.adjacent_source_or_corner s (G.X s) y).mpr
        (Or.inl hs)).resolve_right hcenter)
  · intro y
    apply stabilizationXDerivative_apply_southwest
    simp only [stabilizationPartnerState, GridState.swapRows_apply,
      GridState.insertPoint_apply_newColumn, Equiv.swap_apply_right]


/-- The full X derivative commutes with the full stabilized differential. -/
theorem stabilizationXDerivative_chain :
    laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R ∘ₗ
        stabilizationXDerivative G s R =
      stabilizationXDerivative G s R ∘ₗ
        laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R := by
  have h := squareDerivative_homotopy
    (oSquareWeight (R := R) (G.stabilizeX s.castSucc (G.X s).castSucc s))
    s.succ (G.X s).castSucc
  rw [squareWeightedDifferential_oSquareWeight, oSquareWeight_column,
    oSquareWeight_row, CharTwo.add_self_eq_zero, zero_smul] at h
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro y
  have hh := congrArg (fun f => f c y) h
  simp only [LinearMap.add_apply, Finsupp.add_apply, LinearMap.zero_apply,
    Finsupp.zero_apply] at hh
  exact CharTwo.add_eq_zero.mp hh

/-- The full X derivative commutes with the specified full homotopy. -/
theorem fullStabilizationTransferredRetraction_homotopy_XDerivative_commute :
    (fullStabilizationTransferredRetraction G s R).homotopy ∘ₗ stabilizationXDerivative G s R =
      stabilizationXDerivative G s R ∘ₗ
        (fullStabilizationTransferredRetraction G s R).homotopy := by
  let C := fullStabilizationTransferredRetraction G s R
  let L := stabilizationXDerivative G s R
  let D := laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R
  apply LinearMap.ext
  intro c
  have hh : C.homotopy (C.homotopy c) = 0 :=
    LinearMap.congr_fun C.homotopy_comp_homotopy c
  have hk : C.homotopy (c - D (C.homotopy c)) = 0 := by
    rw [map_sub, MatchingHomotopy.homotopy_d_homotopy C, sub_self]
  have h := fullStabilizationTransferredRetraction_homotopy_XDerivative_eq_zero G s R _ hk
  change C.homotopy (L (c - D (C.homotopy c))) = 0 at h
  rw [map_sub, map_sub] at h
  have hDL : L (D (C.homotopy c)) = D (L (C.homotopy c)) :=
    (LinearMap.congr_fun (stabilizationXDerivative_chain G s R) (C.homotopy c)).symm
  rw [hDL] at h
  have hHL : C.homotopy (L (C.homotopy c)) = 0 :=
    fullStabilizationTransferredRetraction_homotopy_XDerivative_eq_zero G s R _ hh
  have hPL : C.proj (L (C.homotopy c)) = 0 :=
    fullStabilizationTransferredRetraction_proj_XDerivative_homotopy G s R c
  have hr := C.incl_proj_apply (L (C.homotopy c))
  rw [hPL, map_zero, hHL, map_zero, sub_zero] at hr
  have hr' : C.homotopy (D (L (C.homotopy c))) = L (C.homotopy c) :=
    (sub_eq_zero.mp hr.symm).symm
  exact (sub_eq_zero.mp h).trans hr'

/-- Reading a partner coefficient of the corrected inclusion reads its first component. -/
theorem fullStabilizationTransferredRetraction_incl_apply_partner
    (z : LaurentChain R n × LaurentChain R n) (x : GridState n) :
    (fullStabilizationTransferredRetraction G s R).incl z
      (stabilizationPartnerState G s x).val = z.1 x := by
  have h : Finsupp.lapply (stabilizationPartnerState G s x).val ∘ₗ
      (fullStabilizationTransferredRetraction G s R).incl =
      Finsupp.lapply x ∘ₗ LinearMap.fst (LaurentPolynomial R) (LaurentChain R n)
        (LaurentChain R n) := by
    apply LinearMap.prod_ext
    · apply Finsupp.lhom_ext'
      intro y
      apply LinearMap.ext_ring
      change (fullStabilizationTransferredRetraction G s R).incl (single y 1, 0)
        (stabilizationPartnerState G s x).val = single y (1 : LaurentPolynomial R) x
      rw [fullStabilizationTransferredRetraction_incl_first_single, Finsupp.sub_apply,
        fullStabilizationTransferredRetraction_homotopy_apply_partner, sub_zero]
      simp only [Finsupp.single_apply, (stabilizationPartnerState_val_injective G s).eq_iff]
    · apply Finsupp.lhom_ext'
      intro y
      apply LinearMap.ext_ring
      change (fullStabilizationTransferredRetraction G s R).incl (0, single y 1)
        (stabilizationPartnerState G s x).val = 0
      rw [fullStabilizationTransferredRetraction_incl_second,
        laurentStabilizationCenterInclusion_single, Finsupp.sub_apply,
        fullStabilizationTransferredRetraction_homotopy_apply_partner, sub_zero]
      apply Finsupp.single_eq_of_ne
      intro heq
      have hv := congrArg (fun u : GridState (n + 1) => u s.succ) heq
      simp only [stabilizationPartnerState, GridState.swapRows_apply,
        GridState.insertPoint_apply_newColumn, Equiv.swap_apply_right] at hv
      exact Fin.castSucc_lt_succ.ne hv
  exact LinearMap.congr_fun h z

/-- The first projection component kills the entire X derivative. -/
theorem fullStabilizationTransferredRetraction_proj_XDerivative_fst
    (c : LaurentChain R (n + 1)) :
    ((fullStabilizationTransferredRetraction G s R).proj
      (stabilizationXDerivative G s R c)).1 = 0 := by
  apply Finsupp.ext
  intro x
  have h := congrArg (fun z : LaurentChain R (n + 1) => z (stabilizationPartnerState G s x).val)
    ((fullStabilizationTransferredRetraction G s R).incl_proj_apply
      (stabilizationXDerivative G s R c))
  rw [fullStabilizationTransferredRetraction_incl_apply_partner, Finsupp.sub_apply,
    Finsupp.sub_apply, fullStabilizationTransferredRetraction_homotopy_apply_partner,
    sub_zero] at h
  have hL (z : LaurentChain R (n + 1)) :
      stabilizationXDerivative G s R z (stabilizationPartnerState G s x).val = 0 := by
    apply stabilizationXDerivative_apply_southwest
    simp only [stabilizationPartnerState, GridState.swapRows_apply,
      GridState.insertPoint_apply_newColumn, Equiv.swap_apply_right]
  rw [hL] at h
  have hHL := LinearMap.congr_fun
    (fullStabilizationTransferredRetraction_homotopy_XDerivative_commute G s R) c
  simp only [LinearMap.comp_apply] at hHL
  rw [hHL] at h
  have hDL := LinearMap.congr_fun (stabilizationXDerivative_chain G s R)
    ((fullStabilizationTransferredRetraction G s R).homotopy c)
  simp only [LinearMap.comp_apply] at hDL
  rw [hDL, hL, sub_self] at h
  exact h

end OnLeConjecture.KnotFloer.GridFull
