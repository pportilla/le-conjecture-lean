/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationODerivative
public import OnLeConjecture.KnotFloer.MatchingHomotopyKernel

/-!
# The support of the constructed stabilization homotopy

The homotopy has image among the sources of the row matching. Its kernel consists
of chains supported on these sources and the inserted center states.
-/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti Finsupp
variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R] [CharP R 2]

/-- The native row-source predicate is the one used in the reduced matching. -/
theorem rowMatchingSource_coneState (i : G.StabilizeXOffCenterState s ⊕ GridState n) :
    RowMatchingSource s (G.X s) (G.stabilizeXConeStateEquiv s i) ↔
      G.StabilizeXMatchingSource s i := by
  rw [G.stabilizeXMatchingSource_iff_notMem_cIco]
  let x := G.stabilizeXConeStateEquiv s i
  have hne : x.transpose (G.X s).castSucc ≠ x.transpose (G.X s).succ :=
    fun h => (G.X s).castSucc_lt_succ.ne (x.transpose.toPerm.injective h)
  constructor
  · intro hs hn
    exact Finset.disjoint_left.mp (Grid.disjoint_cIco_swap _ _) hn hs
  · intro hn
    have hmem : s.castSucc ∈ Grid.cIco (x.transpose (G.X s).castSucc)
        (x.transpose (G.X s).succ) ∪ Grid.cIco (x.transpose (G.X s).succ)
        (x.transpose (G.X s).castSucc) := by
      rw [Grid.cIco_union_swap hne]
      exact Finset.mem_univ _
    exact (Finset.mem_union.mp hmem).resolve_left hn

omit [CharP R 2] in
/-- The reverse row matching has no coefficient at a nonsource. -/
theorem reducedConeReverseMatching_apply_of_not_source
    (c : G.StabilizeXOffCenterState s ⊕ GridState n →₀ R)
    (j : G.StabilizeXOffCenterState s ⊕ GridState n)
    (hj : ¬G.StabilizeXMatchingSource s j) :
    reducedConeReverseMatching G s R c j = 0 := by
  classical
  rw [finiteEnd_apply_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hz : reducedConeReverseMatching G s R (single i 1) j = 0 := by
    rw [reducedConeReverseMatching, MatchingContraction.reverseHomotopy_single]
    split_ifs with hi
    · rfl
    · apply Finsupp.single_eq_of_ne
      intro heq
      apply hj
      rw [heq]
      exact (G.stabilizeXMatchingSource_stabilizeXMatching_iff s i).mpr hi
  rw [hz, mul_zero]

/-- Normalization retains the source-only image. -/
theorem reducedStabilizationHomotopy_apply_of_not_source
    (c : G.StabilizeXOffCenterState s ⊕ GridState n →₀ R)
    (j : G.StabilizeXOffCenterState s ⊕ GridState n)
    (hj : ¬G.StabilizeXMatchingSource s j) :
    reducedStabilizationHomotopy G s R c j = 0 := by
  rw [reducedStabilizationHomotopy_eq_normalized, MatchingContraction.normalizedHomotopy,
    Module.End.mul_apply]
  exact reducedConeReverseMatching_apply_of_not_source G s R _ j hj

/-- Coefficient extension and the two comparison perturbations retain that image. -/
theorem localComparisonConeHomotopy_apply_of_not_source
    (c : ReducedConeLaurentChain G s R)
    (j : G.StabilizeXOffCenterState s ⊕ GridState n)
    (hj : ¬G.StabilizeXMatchingSource s j) :
    (localComparisonConeContraction G s R).homotopy c j = 0 := by
  rw [localComparisonConeContraction_homotopy_eq_inverse, Module.End.mul_apply,
    laurentComparisonConeContraction_homotopy_eq_inverse, Module.End.mul_apply,
    laurentReducedConeHomotopy, coefficientExtension_apply_apply]
  simp only [reducedStabilizationHomotopy_apply_of_not_source G s R _ j hj,
    map_zero, mul_zero, Finset.sum_const_zero]

/-- The off-center homotopy has no coefficient at a nonsource. -/
theorem localComparisonOffCenterInverseHomotopy_apply_of_not_source
    (c : G.StabilizeXOffCenterState s →₀ LaurentPolynomial R)
    (j : G.StabilizeXOffCenterState s)
    (hj : ¬G.StabilizeXMatchingSource s (.inl j)) :
    localComparisonOffCenterInverseHomotopy G s R c j = 0 := by
  simp only [localComparisonOffCenterInverseHomotopy, ContractibleSumCone.leftHomotopy,
    LinearMap.comp_apply, LinearMap.inl_apply, ContractibleSumCone.productHomotopy_apply,
    LinearMap.fst_apply, fst_sumFinsuppLEquivProdFinsupp]
  exact localComparisonConeHomotopy_apply_of_not_source G s R _ _ hj

/-- The partially blocked homotopy has source-only support on the actual state basis. -/
theorem localStabilizationRetraction_homotopy_apply_of_not_source
    (c : LaurentChain R (n + 1)) (j : GridState (n + 1))
    (hj : ¬RowMatchingSource s (G.X s) j) :
    (localStabilizationRetraction G s R).homotopy c j = 0 := by
  classical
  obtain ⟨i, rfl⟩ := (G.stabilizeXConeStateEquiv s).surjective j
  cases i with
  | inl i =>
    rw [G.stabilizeXConeStateEquiv_apply_inl] at hj ⊢
    rw [localStabilizationRetraction_homotopy, Finsupp.neg_apply]
    have hs : ¬G.StabilizeXMatchingSource s (.inl i) := by
      rw [← rowMatchingSource_coneState, G.stabilizeXConeStateEquiv_apply_inl]
      exact hj
    have hi := congrArg (fun z => z i) (laurentOffCenterProjection_inclusion G s R
      (localComparisonOffCenterInverseHomotopy G s R (laurentOffCenterProjection G s R c)))
    rw [laurentOffCenterProjection_apply] at hi
    rw [hi, localComparisonOffCenterInverseHomotopy_apply_of_not_source G s R _ i hs, neg_zero]
  | inr x =>
    rw [G.stabilizeXConeStateEquiv_apply_inr]
    have h := congrArg (fun z : LaurentChain R n => z x)
      (centerProjection_localStabilizationRetraction_homotopy G s R c)
    simpa only [laurentStabilizationCenterProjection_apply, Finsupp.zero_apply] using h

/-- The full homotopy still has source-only support. -/
theorem fullStabilizationTransferredRetraction_homotopy_apply_of_not_source
    (c : LaurentChain R (n + 1)) (j : GridState (n + 1))
    (hj : ¬RowMatchingSource s (G.X s) j) :
    (fullStabilizationTransferredRetraction G s R).homotopy c j = 0 := by
  rw [fullStabilizationTransferredRetraction_homotopy, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, Finsupp.sub_apply,
    localStabilizationRetraction_homotopy_apply_of_not_source G s R _ j hj,
    localStabilizationRetraction_homotopy_apply_of_not_source G s R _ j hj, sub_self]

/-- The states killed by the homotopy: row sources together with center states. -/
noncomputable def stabilizationHomotopyKernelSupport :
    Submodule (LaurentPolynomial R) (LaurentChain R (n + 1)) :=
  Finsupp.supported (LaurentPolynomial R) (LaurentPolynomial R)
    {x | RowMatchingSource s (G.X s) x ∨ x s.succ = (G.X s).succ}

/-- Every homotopy output is supported in the specified kernel set. -/
theorem fullStabilizationTransferredRetraction_homotopy_mem_kernelSupport
    (c : LaurentChain R (n + 1)) :
    (fullStabilizationTransferredRetraction G s R).homotopy c ∈
      stabilizationHomotopyKernelSupport G s R := by
  apply (Finsupp.mem_supported' _ _).mpr
  intro x hx
  exact fullStabilizationTransferredRetraction_homotopy_apply_of_not_source G s R c x
    (fun hs => hx (Or.inl hs))

/-- The full homotopy kills any source or center basis vector. -/
theorem fullStabilizationTransferredRetraction_homotopy_single_of_kernelSupport
    (x : GridState (n + 1))
    (hx : RowMatchingSource s (G.X s) x ∨ x s.succ = (G.X s).succ) :
    (fullStabilizationTransferredRetraction G s R).homotopy (single x 1) = 0 := by
  classical
  obtain ⟨i, rfl⟩ := (G.stabilizeXConeStateEquiv s).surjective x
  cases i with
  | inl i =>
    rw [G.stabilizeXConeStateEquiv_apply_inl] at hx ⊢
    apply fullStabilizationTransferredRetraction_homotopy_single_of_matching_source
    rw [← rowMatchingSource_coneState, G.stabilizeXConeStateEquiv_apply_inl]
    exact hx.resolve_right i.property
  | inr x =>
    rw [G.stabilizeXConeStateEquiv_apply_inr,
      ← laurentStabilizationCenterInclusion_single G s R x]
    exact fullStabilizationTransferredRetraction_homotopy_centerInclusion G s R _

/-- The full homotopy vanishes on all chains with the specified support. -/
theorem fullStabilizationTransferredRetraction_homotopy_eq_zero_of_mem_kernelSupport
    (c : LaurentChain R (n + 1)) (hc : c ∈ stabilizationHomotopyKernelSupport G s R) :
    (fullStabilizationTransferredRetraction G s R).homotopy c = 0 := by
  classical
  apply Finsupp.ext
  intro y
  rw [finiteEnd_apply_apply]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : RowMatchingSource s (G.X s) x ∨ x s.succ = (G.X s).succ
  · rw [fullStabilizationTransferredRetraction_homotopy_single_of_kernelSupport G s R x hx,
      Finsupp.zero_apply, mul_zero]
  · rw [(Finsupp.mem_supported' _ _).mp hc x hx, zero_mul]


omit [CharP R 2] in
private theorem map_mem_submodule_of_single {ι M : Type*} [AddCommGroup M]
    [Module (LaurentPolynomial R) M] (f : (ι →₀ LaurentPolynomial R) →ₗ[LaurentPolynomial R] M)
    (S : Submodule (LaurentPolynomial R) M)
    (hf : ∀ i, f (single i 1) ∈ S) (c : ι →₀ LaurentPolynomial R) : f c ∈ S := by
  induction c using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using S.zero_mem
  | add c d hc hd => simpa only [map_add] using S.add_mem hc hd
  | single i a =>
    have hs : single i a = a • single i (1 : LaurentPolynomial R) := by simp
    rw [hs, map_smul]
    exact S.smul_mem a (hf i)

/-- Both corrected inclusion columns have source-or-center support. -/
theorem fullStabilizationTransferredRetraction_incl_mem_kernelSupport
    (z : LaurentChain R n × LaurentChain R n) :
    (fullStabilizationTransferredRetraction G s R).incl z ∈
      stabilizationHomotopyKernelSupport G s R := by
  let S := stabilizationHomotopyKernelSupport G s R
  let I := (fullStabilizationTransferredRetraction G s R).incl
  have hfirst (x : GridState n) : I (single x 1, 0) ∈ S := by
    rw [show I (single x 1, 0) = _ from
      fullStabilizationTransferredRetraction_incl_first_single G s R x]
    apply S.sub_mem
    · apply Finsupp.single_mem_supported
      apply Or.inl
      have hs := (rowMatchingSource_coneState G s (.inl (stabilizationPartnerState G s x))).mpr
        (stabilizationPartnerState_is_matching_source G s x)
      simpa only [G.stabilizeXConeStateEquiv_apply_inl] using hs
    · exact fullStabilizationTransferredRetraction_homotopy_mem_kernelSupport G s R _
  have hsecond (x : GridState n) : I (0, single x 1) ∈ S := by
    rw [show I (0, single x 1) = _ from
      fullStabilizationTransferredRetraction_incl_second G s R (single x 1),
      laurentStabilizationCenterInclusion_single]
    apply S.sub_mem
    · exact Finsupp.single_mem_supported _ _
        (Or.inr (GridState.insertPoint_apply_newColumn _ _ _))
    · exact fullStabilizationTransferredRetraction_homotopy_mem_kernelSupport G s R _
  have h1 := map_mem_submodule_of_single R (I ∘ₗ LinearMap.inl _ _ _) S hfirst z.1
  have h2 := map_mem_submodule_of_single R (I ∘ₗ LinearMap.inr _ _ _) S hsecond z.2
  have hz : z = (z.1, 0) + (0, z.2) := by simp
  rw [hz, map_add]
  exact S.add_mem h1 h2

/-- Exact kernel characterization for the constructed full stabilization homotopy. -/
theorem fullStabilizationTransferredRetraction_homotopy_eq_zero_iff_kernelSupport
    (c : LaurentChain R (n + 1)) :
    (fullStabilizationTransferredRetraction G s R).homotopy c = 0 ↔
      c ∈ stabilizationHomotopyKernelSupport G s R := by
  constructor
  · intro hc
    have h := (fullStabilizationTransferredRetraction G s R).incl_proj_apply c
    rw [hc, map_zero, sub_zero] at h
    have heq : c = (fullStabilizationTransferredRetraction G s R).incl
        ((fullStabilizationTransferredRetraction G s R).proj c) +
        (fullStabilizationTransferredRetraction G s R).homotopy
          (laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R c) := by
      rw [h, sub_add_cancel]
    rw [heq]
    exact (stabilizationHomotopyKernelSupport G s R).add_mem
      (fullStabilizationTransferredRetraction_incl_mem_kernelSupport G s R _)
      (fullStabilizationTransferredRetraction_homotopy_mem_kernelSupport G s R _)
  · exact fullStabilizationTransferredRetraction_homotopy_eq_zero_of_mem_kernelSupport G s R c

end OnLeConjecture.KnotFloer.GridFull
