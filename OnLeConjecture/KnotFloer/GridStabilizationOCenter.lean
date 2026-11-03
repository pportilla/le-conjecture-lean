/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationODerivativeSupport

/-!
# The new-O derivative from center states to their partners

Exactly one rectangle through the new O joins an inserted center state to a center
partner. It is the adjacent-row rectangle, and its normalized Laurent weight is one.
-/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti Finsupp
variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- A rectangle through the new O from a center to a partner has adjacent horizontal sides. -/
theorem stabilizationOCenterRectangle_shape (x y : GridState n)
    (r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationPartnerState G s y).val)
    (hr : (s.castSucc, (G.X s).castSucc) ∈ r.toGridRectangle.coveredSquares) :
    r.right = s.succ ∧ r.bottom = (G.X s).castSucc ∧ r.top = (G.X s).succ := by
  have hy : (stabilizationPartnerState G s y).val s.succ = (G.X s).castSucc := by
    simp only [stabilizationPartnerState, GridState.swapRows_apply,
      GridState.insertPoint_apply_newColumn, Equiv.swap_apply_right]
  have hrow := ((GridRectangle.mem_coveredSquares _ _).mp hr).2
  have hl : s.succ ≠ r.left := by
    intro heq
    have ht := r.map_left
    rw [← heq, hy] at ht
    have htop : r.top = (G.X s).castSucc := ht.symm
    simp only [GridRectangle.mem_coveredRows, GridRectangleBetween.toGridRectangle_bottom,
      GridRectangleBetween.toGridRectangle_top, htop, Grid.right_notMem_cIco] at hrow
  have hright : r.right = s.succ := by
    by_contra heq
    have h := r.map_of_ne s.succ hl (Ne.symm heq)
    rw [hy, GridState.insertPoint_apply_newColumn] at h
    exact Fin.castSucc_lt_succ.ne h
  refine ⟨hright, ?_, ?_⟩
  · have h := r.map_right
    rw [hright, hy] at h
    exact h.symm
  · change (x.insertPoint s.succ (G.X s).succ) r.right = _
    rw [hright, GridState.insertPoint_apply_newColumn]

/-- Such a rectangle can only connect the same old state in the two copies. -/
theorem stabilizationOCenterRectangle_target (x y : GridState n)
    (r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationPartnerState G s y).val)
    (hr : (s.castSucc, (G.X s).castSucc) ∈ r.toGridRectangle.coveredSquares) : x = y := by
  obtain ⟨_, hb, ht⟩ := stabilizationOCenterRectangle_shape G s x y r hr
  have h : (stabilizationPartnerState G s y).val = (stabilizationPartnerState G s x).val := by
    exact r.target_eq_swapRows.trans (by rw [← r.bottom_def, ← r.top_def, hb, ht]; rfl)
  have h' := congrArg (fun i : G.StabilizeXOffCenterState s =>
    G.stabilizeXMatching s (.inl i)) (Subtype.ext h)
  rw [stabilizationPartnerState_matching, stabilizationPartnerState_matching] at h'
  exact (Sum.inr.inj h').symm

/-- The adjacent-row rectangle starting at a center contains the new O square. -/
theorem stabilizationRowRectangle_center_contains_O (x : GridState n) :
    (s.castSucc, (G.X s).castSucc) ∈
      (G.stabilizeXRowSwapRectangle s
        (x.insertPoint s.succ (G.X s).succ)).toGridRectangle.coveredSquares := by
  let r := G.stabilizeXRowSwapRectangle s (x.insertPoint s.succ (G.X s).succ)
  have hright : r.right = s.succ := by
    rw [GridDiagram.stabilizeXRowSwapRectangle_right]
    exact (congrArg (x.insertPoint s.succ (G.X s).succ).transpose
      (GridState.insertPoint_apply_newColumn x s.succ (G.X s).succ).symm).trans
        (GridState.transpose_apply_apply _ _)
  apply (GridRectangle.mem_coveredSquares _ _).mpr
  constructor
  · change s.castSucc ∈ Grid.cIco r.left r.right
    rw [hright]
    exact Grid.castSucc_mem_cIco_succ (fun h => r.left_ne_right (h.trans hright.symm))
  · rw [G.coveredRows_stabilizeXRowSwapRectangle]
    exact Finset.mem_singleton_self _

/-- The adjacent-row rectangle from a center contains precisely the new O marking. -/
theorem stabilizationRowRectangle_center_OColumns (x : GridState n) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
      (G.stabilizeXRowSwapRectangle s (x.insertPoint s.succ (G.X s).succ)).toGridRectangle =
      {s.castSucc} := by
  classical
  ext c
  rw [GridDiagram.mem_OColumns, GridRectangle.mem_coveredSquares,
    G.coveredRows_stabilizeXRowSwapRectangle, Finset.mem_singleton,
    GridDiagram.stabilizeX_O, GridDiagram.stabilizeX_O_eq_castSucc_iff,
    Finset.mem_singleton]
  constructor
  · exact And.right
  · intro hc
    subst c
    exact ⟨((GridRectangle.mem_coveredSquares _ _).mp
      (stabilizationRowRectangle_center_contains_O G s x)).1, rfl⟩

variable (R : Type*) [CommRing R]

open Classical in
/-- The normalized O-derivative matrix from center states to partners is the identity. -/
theorem stabilizationODerivative_center_partner_coefficient (x y : GridState n) :
    stabilizationODerivative G s R (single (x.insertPoint s.succ (G.X s).succ) 1)
      (stabilizationPartnerState G s y).val = if x = y then 1 else 0 := by
  classical
  rw [stabilizationODerivative, LinearMap.smul_apply, Finsupp.smul_apply,
    smul_eq_mul, squareDerivative_single_apply,
    coeff_one_squareWeightedCoefficient_deformAtSquare]
  by_cases hxy : x = y
  · subst y
    rw [if_pos rfl]
    let r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
        (stabilizationPartnerState G s x).val :=
      G.stabilizeXRowSwapRectangle s (x.insertPoint s.succ (G.X s).succ)
    have hset : (GridRectangleBetween.emptyRectangles
        (x.insertPoint s.succ (G.X s).succ) (stabilizationPartnerState G s x).val).filter
        (fun t => (s.castSucc, (G.X s).castSucc) ∈ t.toGridRectangle.coveredSquares) = {r} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨Finset.mem_filter.mpr ⟨(GridRectangleBetween.mem_emptyRectangles _).mpr
        (G.isEmpty_stabilizeXRowSwapRectangle s _),
        stabilizationRowRectangle_center_contains_O G s x⟩, ?_⟩
      intro t ht
      obtain ⟨_, hb, _⟩ := stabilizationOCenterRectangle_shape G s x x t
        (Finset.mem_filter.mp ht).2
      apply GridRectangleBetween.left_injective
      apply (x.insertPoint s.succ (G.X s).succ).toPerm.injective
      exact hb.trans (G.stabilizeXRowSwapRectangle_bottom s _).symm
    rw [hset, Finset.sum_singleton, squareWeight_oSquareWeight,
      laurentSpecialization_OMonomial]
    dsimp only [r, stabilizationPartnerState]
    rw [stabilizationRowRectangle_center_OColumns,
      Finset.card_singleton, Nat.cast_one, ← LaurentPolynomial.T_add, neg_add_cancel,
      LaurentPolynomial.T_zero]
  · rw [if_neg hxy]
    have hzero : ∑ r ∈ (GridRectangleBetween.emptyRectangles
        (x.insertPoint s.succ (G.X s).succ) (stabilizationPartnerState G s y).val).filter
        (fun t => (s.castSucc, (G.X s).castSucc) ∈ t.toGridRectangle.coveredSquares),
        squareWeight (oSquareWeight (R := R) (G.stabilizeX s.castSucc (G.X s).castSucc s))
          r.toGridRectangle = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      exact False.elim (hxy (stabilizationOCenterRectangle_target G s x y r
        (Finset.mem_filter.mp hr).2))
    rw [hzero, mul_zero]


/-- Distinct old states have distinct inserted matching partners. -/
theorem stabilizationPartnerState_val_injective :
    Function.Injective (fun x : GridState n => (stabilizationPartnerState G s x).val) := by
  intro x y h
  have h' := congrArg (fun i : G.StabilizeXOffCenterState s =>
    G.stabilizeXMatching s (.inl i)) (Subtype.ext h)
  rw [stabilizationPartnerState_matching, stabilizationPartnerState_matching] at h'
  exact Sum.inr.inj h'

variable [CharP R 2]

/-- The new-O derivative takes the center basis to the first copy under the full projection. -/
theorem fullStabilizationTransferredRetraction_proj_ODerivative_center (x : GridState n) :
    (fullStabilizationTransferredRetraction G s R).proj
      (stabilizationODerivative G s R (single (x.insertPoint s.succ (G.X s).succ) 1)) =
        (single x 1, 0) := by
  classical
  let c := stabilizationODerivative G s R
    (single (x.insertPoint s.succ (G.X s).succ) 1) -
      single (stabilizationPartnerState G s x).val 1
  have hzero : (fullStabilizationTransferredRetraction G s R).proj c = 0 := by
    apply fullStabilizationTransferredRetraction_proj_eq_zero_of_source_support
    · intro y hy
      dsimp only [c]
      rw [Finsupp.sub_apply, stabilizationODerivative_single_apply_of_center G s R _ y
        (GridState.insertPoint_apply_newColumn _ _ _) hy]
      have hne : y ≠ (stabilizationPartnerState G s x).val := by
        intro heq
        apply hy
        rw [heq]
        have hs := (rowMatchingSource_coneState G s (.inl (stabilizationPartnerState G s x))).mpr
          (stabilizationPartnerState_is_matching_source G s x)
        simpa only [G.stabilizeXConeStateEquiv_apply_inl] using hs
      rw [Finsupp.single_eq_of_ne hne, sub_self]
    · intro y
      dsimp only [c]
      simp only [Finsupp.sub_apply, stabilizationODerivative_center_partner_coefficient,
        Finsupp.single_apply, (stabilizationPartnerState_val_injective G s).eq_iff, sub_self]
  change (fullStabilizationTransferredRetraction G s R).proj (_ - _) = 0 at hzero
  rw [map_sub, fullStabilizationTransferredRetraction_proj_partner_single] at hzero
  exact sub_eq_zero.mp hzero

/-- The first-to-second component of the actual transferred differential vanishes on generators. -/
theorem stabilizationTransferredDifferential_first_snd_single (x : GridState n) :
    (stabilizationTransferredDifferential G s R (single x 1, 0)).2 = 0 := by
  let c := single (x.insertPoint s.succ (G.X s).succ) (1 : LaurentPolynomial R)
  have h := (fullStabilizationTransferredRetraction G s R).proj_dM_apply
    (stabilizationODerivative G s R c)
  rw [show (fullStabilizationTransferredRetraction G s R).proj
      (stabilizationODerivative G s R c) = (single x 1, 0) from
        fullStabilizationTransferredRetraction_proj_ODerivative_center G s R x] at h
  have hD := LinearMap.congr_fun (stabilizationODerivative_chain G s R) c
  simp only [LinearMap.comp_apply] at hD
  rw [hD] at h
  exact (congrArg Prod.snd h).symm.trans
    (fullStabilizationTransferredRetraction_proj_ODerivative_snd G s R _)

/-- The first-to-second block of the constructed full transferred differential is zero. -/
theorem stabilizationTransferredDifferential_first_snd :
    LinearMap.snd (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
      stabilizationTransferredDifferential G s R ∘ₗ
        LinearMap.inl (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) = 0 := by
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  exact stabilizationTransferredDifferential_first_snd_single G s R x


/-- The transferred new-O derivative is the standard map from the second copy to the first. -/
theorem fullStabilizationTransferredRetraction_proj_ODerivative_incl :
    (fullStabilizationTransferredRetraction G s R).proj ∘ₗ stabilizationODerivative G s R ∘ₗ
      (fullStabilizationTransferredRetraction G s R).incl =
        LinearMap.inl (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
          LinearMap.snd (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) := by
  apply LinearMap.prod_ext
  · apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    change (fullStabilizationTransferredRetraction G s R).proj
      (stabilizationODerivative G s R
        ((fullStabilizationTransferredRetraction G s R).incl (single x 1, 0))) = (0, 0)
    rw [fullStabilizationTransferredRetraction_incl_first_single, map_sub, map_sub,
      fullStabilizationTransferredRetraction_proj_ODerivative_homotopy]
    have hz := LinearMap.congr_fun (stabilizationODerivative_partnerInclusion G s R) (single x 1)
    simp only [LinearMap.comp_apply, laurentStabilizationPartnerInclusion_single,
      LinearMap.zero_apply] at hz
    rw [hz, map_zero, sub_zero]
    rfl
  · apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    change (fullStabilizationTransferredRetraction G s R).proj
      (stabilizationODerivative G s R
        ((fullStabilizationTransferredRetraction G s R).incl (0, single x 1))) = (single x 1, 0)
    rw [fullStabilizationTransferredRetraction_incl_second,
      laurentStabilizationCenterInclusion_single, map_sub, map_sub,
      fullStabilizationTransferredRetraction_proj_ODerivative_homotopy, sub_zero,
      fullStabilizationTransferredRetraction_proj_ODerivative_center]

/-- The two diagonal components of the actual transferred differential agree. -/
theorem stabilizationTransferredDifferential_diagonal_eq (c : LaurentChain R n) :
    (stabilizationTransferredDifferential G s R (c, 0)).1 =
      (stabilizationTransferredDifferential G s R (0, c)).2 := by
  let C := fullStabilizationTransferredRetraction G s R
  let L := stabilizationODerivative G s R
  let D := laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R
  let d := stabilizationTransferredDifferential G s R
  have hL (z : LaurentChain R n × LaurentChain R n) : C.proj (L (C.incl z)) = (z.2, 0) :=
    LinearMap.congr_fun (fullStabilizationTransferredRetraction_proj_ODerivative_incl G s R) z
  have h := C.proj_dM_apply (L (C.incl (0, c)))
  change C.proj (D (L (C.incl (0, c)))) = d (C.proj (L (C.incl (0, c)))) at h
  rw [hL] at h
  have hDL : D (L (C.incl (0, c))) = L (D (C.incl (0, c))) :=
    LinearMap.congr_fun (stabilizationODerivative_chain G s R) _
  rw [hDL, C.dM_incl_apply, hL] at h
  exact (congrArg Prod.fst h).symm

end OnLeConjecture.KnotFloer.GridFull
