/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationHomotopySupport

/-!
# Support cancellations for the new-O derivative

The derivative sends matching sources to matching sources, with zero coefficients at
center partners. On the full homotopy image its comparison projection therefore vanishes.
-/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti Finsupp
variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R]

/-- The new-O derivative sends a matching source only to matching sources. -/
theorem stabilizationODerivative_single_apply_of_source
    (x y : GridState (n + 1)) (hx : RowMatchingSource s (G.X s) x)
    (hy : ¬RowMatchingSource s (G.X s) y) :
    stabilizationODerivative G s R (single x 1) y = 0 := by
  rw [stabilizationODerivative, LinearMap.smul_apply, Finsupp.smul_apply,
    smul_eq_mul, squareDerivative_single_apply,
    squareDerivative_coefficient_eq_zero_of_source s (G.X s) _ x y hx hy, mul_zero]

/-- On matching sources, the derivative has zero coefficient at each center partner. -/
theorem stabilizationODerivative_single_apply_partner_of_source
    (x : GridState (n + 1)) (y : GridState n) (hx : RowMatchingSource s (G.X s) x) :
    stabilizationODerivative G s R (single x 1) (stabilizationPartnerState G s y).val = 0 := by
  have hy : RowMatchingSource s (G.X s) (stabilizationPartnerState G s y).val := by
    have h := (rowMatchingSource_coneState G s (.inl (stabilizationPartnerState G s y))).mpr
      (stabilizationPartnerState_is_matching_source G s y)
    simpa only [G.stabilizeXConeStateEquiv_apply_inl] using h
  rw [stabilizationODerivative, LinearMap.smul_apply, Finsupp.smul_apply,
    smul_eq_mul, squareDerivative_single_apply,
    ← squareDerivative_coefficient_rowSwap s (G.X s) _ x _ (iff_of_true hx hy),
    squareDerivative_coefficient_eq_zero_of_target_northeast s (G.X s) _ _ _ ?_, mul_zero]
  simp only [stabilizationPartnerState, GridState.relabelRows_apply,
    GridState.swapRows_apply, GridState.insertPoint_apply_newColumn,
    Equiv.swap_apply_right, Equiv.swap_apply_left]

/-- On a center input the derivative also has source-only output. -/
theorem stabilizationODerivative_single_apply_of_center
    (x y : GridState (n + 1)) (hx : x s.succ = (G.X s).succ)
    (hy : ¬RowMatchingSource s (G.X s) y) :
    stabilizationODerivative G s R (single x 1) y = 0 := by
  by_cases hs : RowMatchingSource s (G.X s) x
  · exact stabilizationODerivative_single_apply_of_source G s R x y hs hy
  rw [stabilizationODerivative, LinearMap.smul_apply, Finsupp.smul_apply,
    smul_eq_mul, squareDerivative_single_apply,
    ← squareDerivative_coefficient_rowSwap s (G.X s) _ x y (iff_of_false hs hy),
    squareDerivative_coefficient_eq_zero_of_source_southeast s (G.X s) _ _ _ ?_, mul_zero]
  simp only [GridState.relabelRows_apply, hx, Equiv.swap_apply_right]

/-- The derivative sends the entire homotopy kernel into matching-source chains. -/
theorem stabilizationODerivative_apply_of_mem_kernelSupport
    (c : LaurentChain R (n + 1)) (hc : c ∈ stabilizationHomotopyKernelSupport G s R)
    (y : GridState (n + 1)) (hy : ¬RowMatchingSource s (G.X s) y) :
    stabilizationODerivative G s R c y = 0 := by
  classical
  rw [finiteEnd_apply_apply]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : RowMatchingSource s (G.X s) x ∨ x s.succ = (G.X s).succ
  · rcases hx with hs | hc
    · rw [stabilizationODerivative_single_apply_of_source G s R x y hs hy, mul_zero]
    · rw [stabilizationODerivative_single_apply_of_center G s R x y hc hy, mul_zero]
  · rw [(Finsupp.mem_supported' _ _).mp hc x hx, zero_mul]

variable [CharP R 2]

/-- The derivative preserves the exact kernel of the constructed homotopy. -/
theorem fullStabilizationTransferredRetraction_homotopy_ODerivative_eq_zero
    (c : LaurentChain R (n + 1))
    (hc : (fullStabilizationTransferredRetraction G s R).homotopy c = 0) :
    (fullStabilizationTransferredRetraction G s R).homotopy
      (stabilizationODerivative G s R c) = 0 := by
  apply fullStabilizationTransferredRetraction_homotopy_eq_zero_of_mem_kernelSupport
  apply (Finsupp.mem_supported' _ _).mpr
  intro y hy
  exact stabilizationODerivative_apply_of_mem_kernelSupport G s R c
    ((fullStabilizationTransferredRetraction_homotopy_eq_zero_iff_kernelSupport G s R c).mp hc)
    y (fun hs => hy (Or.inl hs))

/-- A source-supported chain with zero partner coefficients has zero comparison projection. -/
theorem fullStabilizationTransferredRetraction_proj_eq_zero_of_source_support
    (c : LaurentChain R (n + 1))
    (hc : ∀ x, ¬RowMatchingSource s (G.X s) x → c x = 0)
    (hp : ∀ y : GridState n, c (stabilizationPartnerState G s y).val = 0) :
    (fullStabilizationTransferredRetraction G s R).proj c = 0 := by
  classical
  conv_lhs => rw [← Finsupp.sum_single c, map_finsuppSum]
  apply Finset.sum_eq_zero
  intro x hx
  have hs : RowMatchingSource s (G.X s) x := by
    by_contra hs
    exact (Finsupp.mem_support_iff.mp hx) (hc x hs)
  obtain ⟨i, hi⟩ := (G.stabilizeXConeStateEquiv s).surjective x
  cases i with
  | inr y =>
    have hn := G.not_stabilizeXMatchingSource_inr s y
    exact False.elim (hn ((rowMatchingSource_coneState G s (.inr y)).mp (hi ▸ hs)))
  | inl i =>
    have hix : i.val = x := by simpa only [G.stabilizeXConeStateEquiv_apply_inl] using hi
    have hsource : G.StabilizeXMatchingSource s (.inl i) :=
      (rowMatchingSource_coneState G s (.inl i)).mp (hi ▸ hs)
    have hn (y : GridState n) : G.stabilizeXMatching s (.inl i) ≠ .inr y := by
      intro hmatch
      have heq : i = stabilizationPartnerState G s y := by
        have h := hmatch.trans (stabilizationPartnerState_matching G s y).symm
        exact Sum.inl.inj (Function.Involutive.injective (G.stabilizeXMatching_involutive s) h)
      have hz : c x = 0 := by rw [← hix, heq]; exact hp y
      exact (Finsupp.mem_support_iff.mp hx) hz
    have hz : (fullStabilizationTransferredRetraction G s R).proj (single x 1) = 0 := by
      apply Prod.ext
      · apply Finsupp.ext
        intro y
        rw [← hix, fullStabilizationTransferredRetraction_proj_source_coefficient_eq
          G s R i hsource, if_neg (hn y)]
        rfl
      · rw [← hix, fullStabilizationTransferredRetraction_proj_single_of_matching_source
          G s R i hsource]
        rfl
    dsimp only
    rw [← Finsupp.smul_single_one, map_smul, hz, smul_zero]

/-- The new-O derivative of a homotopy output has zero comparison projection. -/
theorem fullStabilizationTransferredRetraction_proj_ODerivative_homotopy
    (c : LaurentChain R (n + 1)) :
    (fullStabilizationTransferredRetraction G s R).proj
      (stabilizationODerivative G s R
        ((fullStabilizationTransferredRetraction G s R).homotopy c)) = 0 := by
  apply fullStabilizationTransferredRetraction_proj_eq_zero_of_source_support G s R
  · intro y hy
    exact stabilizationODerivative_apply_of_mem_kernelSupport G s R _
      (fullStabilizationTransferredRetraction_homotopy_mem_kernelSupport G s R c) y hy
  · intro y
    classical
    rw [finiteEnd_apply_apply]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hs : RowMatchingSource s (G.X s) x
    · rw [stabilizationODerivative_single_apply_partner_of_source G s R x y hs, mul_zero]
    · rw [fullStabilizationTransferredRetraction_homotopy_apply_of_not_source G s R c x hs,
        zero_mul]


/-- The new-O derivative commutes with the constructed full stabilization homotopy. -/
theorem fullStabilizationTransferredRetraction_homotopy_ODerivative_commute :
    (fullStabilizationTransferredRetraction G s R).homotopy ∘ₗ stabilizationODerivative G s R =
      stabilizationODerivative G s R ∘ₗ
        (fullStabilizationTransferredRetraction G s R).homotopy := by
  let C := fullStabilizationTransferredRetraction G s R
  let L := stabilizationODerivative G s R
  let D := laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R
  apply LinearMap.ext
  intro c
  have hh : C.homotopy (C.homotopy c) = 0 :=
    LinearMap.congr_fun C.homotopy_comp_homotopy c
  have hk : C.homotopy (c - D (C.homotopy c)) = 0 := by
    rw [map_sub, MatchingHomotopy.homotopy_d_homotopy C, sub_self]
  have h := fullStabilizationTransferredRetraction_homotopy_ODerivative_eq_zero G s R _ hk
  change C.homotopy (L (c - D (C.homotopy c))) = 0 at h
  rw [map_sub, map_sub] at h
  have hDL : L (D (C.homotopy c)) = D (L (C.homotopy c)) :=
    (LinearMap.congr_fun (stabilizationODerivative_chain G s R) (C.homotopy c)).symm
  rw [hDL] at h
  have hHL : C.homotopy (L (C.homotopy c)) = 0 :=
    fullStabilizationTransferredRetraction_homotopy_ODerivative_eq_zero G s R _ hh
  have hPL : C.proj (L (C.homotopy c)) = 0 :=
    fullStabilizationTransferredRetraction_proj_ODerivative_homotopy G s R c
  have hr := C.incl_proj_apply (L (C.homotopy c))
  rw [hPL, map_zero, hHL, map_zero, sub_zero] at hr
  have hr' : C.homotopy (D (L (C.homotopy c))) = L (C.homotopy c) :=
    (sub_eq_zero.mp hr.symm).symm
  exact (sub_eq_zero.mp h).trans hr'

/-- Reading center coefficients after the corrected inclusion reads its second component. -/
theorem centerProjection_fullStabilizationTransferredRetraction_incl
    (z : LaurentChain R n × LaurentChain R n) :
    laurentStabilizationCenterProjection G s R
      ((fullStabilizationTransferredRetraction G s R).incl z) = z.2 := by
  rw [fullStabilizationTransferredRetraction_incl, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, map_sub,
    centerProjection_localStabilizationRetraction_homotopy, sub_zero,
    localStabilizationRetraction_incl, map_add,
    laurentStabilizationCenterProjection_offCenterInclusion, zero_add]
  exact LinearMap.congr_fun (laurentStabilizationCenterProjection_comp_inclusion G s R) z.2

/-- The second projection component kills the entire new-O derivative. -/
theorem fullStabilizationTransferredRetraction_proj_ODerivative_snd
    (c : LaurentChain R (n + 1)) :
    ((fullStabilizationTransferredRetraction G s R).proj
      (stabilizationODerivative G s R c)).2 = 0 := by
  have h := congrArg (laurentStabilizationCenterProjection G s R)
    ((fullStabilizationTransferredRetraction G s R).incl_proj_apply
      (stabilizationODerivative G s R c))
  rw [centerProjection_fullStabilizationTransferredRetraction_incl, map_sub, map_sub,
    centerProjection_fullStabilizationTransferredRetraction_homotopy] at h
  have hL (z : LaurentChain R (n + 1)) :
      laurentStabilizationCenterProjection G s R (stabilizationODerivative G s R z) = 0 :=
    LinearMap.congr_fun (centerProjection_stabilizationODerivative G s R) z
  rw [hL, sub_zero] at h
  have hHL := LinearMap.congr_fun
    (fullStabilizationTransferredRetraction_homotopy_ODerivative_commute G s R) c
  simp only [LinearMap.comp_apply] at hHL
  rw [hHL] at h
  have hDL := LinearMap.congr_fun (stabilizationODerivative_chain G s R)
    ((fullStabilizationTransferredRetraction G s R).homotopy c)
  simp only [LinearMap.comp_apply] at hDL
  rw [hDL, hL, sub_self] at h
  exact h

end OnLeConjecture.KnotFloer.GridFull
