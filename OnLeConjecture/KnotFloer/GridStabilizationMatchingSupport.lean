/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationTransferredCenter

/-!
# Vanishing perturbation paths at matching sources

The reverse row matching kills its sources. The normalization and all subsequent
perturbations preserve this vanishing. Consequently the full comparison projection
on a matching source has no perturbation correction: it is exactly the original
single-X crossing count. These are coefficients of the constructed comparison maps.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R] [CharP R 2]

/-- The normalized reduced homotopy still kills every matching source. -/
theorem reducedStabilizationHomotopy_single_of_matching_source
    (i : G.StabilizeXOffCenterState s ⊕ GridState n)
    (hi : G.StabilizeXMatchingSource s i) :
    reducedStabilizationHomotopy G s R (single i 1) = 0 := by
  classical
  let d := G.stabilizeXReducedCone s R
  let h := reducedConeReverseMatching G s R
  have hh : h * h = 0 := MatchingContraction.reverseHomotopy_comp_self d
    (G.stabilizeXMatching s) (G.StabilizeXMatchingSource s)
    (G.stabilizeXMatching_involutive s)
    (fun i => by rw [G.stabilizeXMatchingSource_stabilizeXMatching_iff, not_not])
  have hu : IsUnit (d * h + h * d) := by
    have hu := Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero _
      (reducedCone_remainder_locallyNilpotent G s R)
    convert hu using 1
    dsimp only [d, h]
    abel
  have hc : Commute h (d * h + h * d) := by
    simp only [Commute, SemiconjBy, mul_add, add_mul, ← mul_assoc, hh, zero_mul]
    simp only [mul_assoc, hh, mul_zero, add_zero, zero_add]
  have hc' : Commute h (Ring.inverse (d * h + h * d)) := by
    obtain ⟨u, hu⟩ := hu
    rw [← hu, Ring.inverse_unit]
    rw [← hu] at hc
    exact hc.units_inv_right
  have hz : h (single i 1) = 0 := by
    dsimp only [h]
    rw [reducedConeReverseMatching, MatchingContraction.reverseHomotopy_single, if_pos hi]
  rw [reducedStabilizationHomotopy_eq_normalized, MatchingContraction.normalizedHomotopy]
  change (h * Ring.inverse (d * h + h * d)) (single i 1) = 0
  rw [hc'.eq, Module.End.mul_apply, hz, map_zero]

/-- Extending coefficients preserves vanishing at matching sources. -/
theorem laurentReducedConeHomotopy_single_of_matching_source
    (i : G.StabilizeXOffCenterState s ⊕ GridState n)
    (hi : G.StabilizeXMatchingSource s i) :
    laurentReducedConeHomotopy G s R (single i 1) = 0 := by
  ext j
  rw [laurentReducedConeHomotopy, coefficientExtension_single_apply,
    reducedStabilizationHomotopy_single_of_matching_source G s R i hi,
    Finsupp.zero_apply, map_zero, mul_zero, Finsupp.zero_apply]

/-- Restoring the O weights adds no homotopy term on a matching source. -/
theorem laurentComparisonConeHomotopy_single_of_matching_source
    (i : G.StabilizeXOffCenterState s ⊕ GridState n)
    (hi : G.StabilizeXMatchingSource s i) :
    (laurentComparisonConeContraction G s R).homotopy (single i 1) = 0 := by
  rw [laurentComparisonConeContraction_homotopy, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.comp_apply,
    laurentReducedConeHomotopy_single_of_matching_source G s R i hi,
    map_zero, map_zero, sub_self]

/-- Restoring the other X crossings also adds no homotopy term on a matching source. -/
theorem localComparisonConeHomotopy_single_of_matching_source
    (i : G.StabilizeXOffCenterState s ⊕ GridState n)
    (hi : G.StabilizeXMatchingSource s i) :
    (localComparisonConeContraction G s R).homotopy (single i 1) = 0 := by
  rw [localComparisonConeContraction_homotopy, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.comp_apply,
    laurentComparisonConeHomotopy_single_of_matching_source G s R i hi,
    map_zero, map_zero, sub_self]

/-- The off-center inverse homotopy kills a source basis vector. -/
theorem localComparisonOffCenterInverseHomotopy_single_of_matching_source
    (i : G.StabilizeXOffCenterState s)
    (hi : G.StabilizeXMatchingSource s (.inl i)) :
    localComparisonOffCenterInverseHomotopy G s R (single i 1) = 0 := by
  change ContractibleSumCone.leftHomotopy
    (localComparisonConeContraction G s R).homotopy (single i 1) = 0
  simp only [ContractibleSumCone.leftHomotopy, LinearMap.comp_apply, LinearMap.inl_apply,
    ContractibleSumCone.productHomotopy_apply, LinearMap.fst_apply]
  rw [ContractibleSumCone.sumEquiv_symm_single_left]
  rw [localComparisonConeHomotopy_single_of_matching_source G s R (.inl i) hi]
  simp

/-- The partially blocked stabilization homotopy kills a source basis vector. -/
theorem localStabilizationRetraction_homotopy_single_of_matching_source
    (i : G.StabilizeXOffCenterState s)
    (hi : G.StabilizeXMatchingSource s (.inl i)) :
    (localStabilizationRetraction G s R).homotopy (single i.val 1) = 0 := by
  rw [← laurentOffCenterInclusion_single G s R i 1,
    localStabilizationRetraction_homotopy, laurentOffCenterProjection_inclusion,
    localComparisonOffCenterInverseHomotopy_single_of_matching_source G s R i hi,
    map_zero, neg_zero]

/-- The full stabilization homotopy kills the same source basis vectors. -/
theorem fullStabilizationTransferredRetraction_homotopy_single_of_matching_source
    (i : G.StabilizeXOffCenterState s)
    (hi : G.StabilizeXMatchingSource s (.inl i)) :
    (fullStabilizationTransferredRetraction G s R).homotopy (single i.val 1) = 0 := by
  rw [fullStabilizationTransferredRetraction_homotopy, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.comp_apply,
    localStabilizationRetraction_homotopy_single_of_matching_source G s R i hi,
    map_zero, map_zero, sub_self]

/-- On a matching source the full comparison is the uncorrected one-X crossing count. -/
theorem fullStabilizationTransferredRetraction_proj_single_of_matching_source
    (i : G.StabilizeXOffCenterState s)
    (hi : G.StabilizeXMatchingSource s (.inl i)) :
    (fullStabilizationTransferredRetraction G s R).proj (single i.val 1) =
      (localComparisonOffCenterToCenter G s R (single i 1), 0) := by
  rw [fullStabilizationTransferredRetraction_proj, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.comp_apply,
    localStabilizationRetraction_homotopy_single_of_matching_source G s R i hi,
    map_zero, map_zero, sub_zero, ← laurentOffCenterInclusion_single G s R i 1,
    localStabilizationRetraction_proj, laurentOffCenterProjection_inclusion,
    laurentStabilizationCenterProjection_offCenterInclusion]

/-- The nonzero component on a matching source is an explicit finite rectangle sum. -/
theorem fullStabilizationTransferredRetraction_proj_source_coefficient
    (i : G.StabilizeXOffCenterState s)
    (hi : G.StabilizeXMatchingSource s (.inl i)) (x : GridState n) :
    ((fullStabilizationTransferredRetraction G s R).proj (single i.val 1)).1 x =
      ∑ r ∈ localComparisonRectangles G s (.inl i) (.inr x),
        (LaurentPolynomial.T
          (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
            r.toGridRectangle).card : ℤ) : LaurentPolynomial R) := by
  rw [fullStabilizationTransferredRetraction_proj_single_of_matching_source G s R i hi]
  have h := localComparisonCone_single_apply G s R (.inl i) (.inr x)
  simpa only [localComparisonCone, LinearMap.sumMappingCone_single_inl_apply_inr] using h

end OnLeConjecture.KnotFloer.GridFull
