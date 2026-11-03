/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationLocalEquivalence
import Mathlib.Tactic.LinearCombination

/-!
# The off-center comparison is a special retraction

No center generator is a source of the reduced matching. Its reverse matching therefore
has image in the off-center summand. Normalization and both perturbations preserve this
property, strengthening the constructed comparison to a retraction.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R] [CharP R 2]

omit [CharP R 2] in
/-- The reversed matching never ends at a center generator. -/
theorem reducedConeReverseMatching_apply_inr
    (c : G.StabilizeXOffCenterState s ⊕ GridState n →₀ R) (x : GridState n) :
    reducedConeReverseMatching G s R c (.inr x) = 0 := by
  classical
  rw [finiteEnd_apply_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hcoef : reducedConeReverseMatching G s R (single i 1) (.inr x) = 0 := by
    rw [reducedConeReverseMatching, MatchingContraction.reverseHomotopy_single]
    by_cases hi : G.StabilizeXMatchingSource s i
    · rw [if_pos hi, Finsupp.zero_apply]
    · rw [if_neg hi]
      have hne : G.stabilizeXMatching s i ≠ .inr x := by
        intro heq
        have hp := (G.stabilizeXMatchingSource_stabilizeXMatching_iff s i).mpr hi
        rw [heq] at hp
        exact G.not_stabilizeXMatchingSource_inr s x hp
      exact Finsupp.single_eq_of_ne hne.symm
  rw [hcoef, mul_zero]

/-- Normalizing the reverse matching preserves its off-center image. -/
theorem reducedStabilizationHomotopy_apply_inr
    (c : G.StabilizeXOffCenterState s ⊕ GridState n →₀ R) (x : GridState n) :
    reducedStabilizationHomotopy G s R c (.inr x) = 0 := by
  rw [reducedStabilizationHomotopy_eq_normalized, MatchingContraction.normalizedHomotopy,
    Module.End.mul_apply]
  exact reducedConeReverseMatching_apply_inr G s R _ x

/-- Extending the matrix by constant Laurent coefficients preserves its off-center image. -/
theorem laurentReducedConeHomotopy_apply_inr (c : ReducedConeLaurentChain G s R)
    (x : GridState n) : laurentReducedConeHomotopy G s R c (.inr x) = 0 := by
  rw [laurentReducedConeHomotopy, coefficientExtension_apply_apply]
  simp only [reducedStabilizationHomotopy_apply_inr, map_zero, mul_zero, Finset.sum_const_zero]

/-- The positive-O correction preserves the off-center image. -/
theorem laurentComparisonConeContraction_homotopy_apply_inr (c : ReducedConeLaurentChain G s R)
    (x : GridState n) : (laurentComparisonConeContraction G s R).homotopy c (.inr x) = 0 := by
  rw [laurentComparisonConeContraction_homotopy_eq_inverse, Module.End.mul_apply]
  exact laurentReducedConeHomotopy_apply_inr G s R _ x

/-- The extra-X correction also preserves the off-center image. -/
theorem localComparisonConeContraction_homotopy_apply_inr (c : ReducedConeLaurentChain G s R)
    (x : GridState n) : (localComparisonConeContraction G s R).homotopy c (.inr x) = 0 := by
  rw [localComparisonConeContraction_homotopy_eq_inverse, Module.End.mul_apply]
  exact laurentComparisonConeContraction_homotopy_apply_inr G s R _ x

/-- Consequently the old-grid inverse homotopy is identically zero. -/
theorem localComparisonOldInverseHomotopy_eq_zero :
    localComparisonOldInverseHomotopy G s R = 0 := by
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro x
  simp only [localComparisonOldInverseHomotopy, ContractibleSumCone.rightHomotopy,
    LinearMap.comp_apply, LinearMap.snd_apply, LinearMap.inr_apply,
    ContractibleSumCone.productHomotopy_apply, snd_sumFinsuppLEquivProdFinsupp,
    localComparisonConeContraction_homotopy_apply_inr, LinearMap.zero_apply, Finsupp.zero_apply]

/-- The forward comparison composed with its constructed reverse is exactly the identity. -/
theorem localComparisonForward_backward_eq_id :
    localComparisonOffCenterToCenter G s R ∘ₗ localComparisonBackward G s R = LinearMap.id := by
  have h := localComparisonForward_backward G s R
  rw [localComparisonOldInverseHomotopy_eq_zero, LinearMap.comp_zero,
    LinearMap.zero_comp, add_zero] at h
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro x
  have hx := congrArg (fun f => f c x) h
  change c x -
    (localComparisonOffCenterToCenter G s R (localComparisonBackward G s R c)) x = 0 at hx
  exact (sub_eq_zero.mp hx).symm

/-- In product coordinates the constructed cone homotopy has zero second component. -/
theorem localComparisonProductHomotopy_snd
    (z : (G.StabilizeXOffCenterState s →₀ LaurentPolynomial R) × LaurentChain R n) :
    (ContractibleSumCone.productHomotopy
      (localComparisonConeContraction G s R).homotopy z).2 = 0 := by
  apply Finsupp.ext
  intro x
  rw [ContractibleSumCone.productHomotopy_apply, snd_sumFinsuppLEquivProdFinsupp,
    localComparisonConeContraction_homotopy_apply_inr, Finsupp.zero_apply]

/-- The forward comparison kills the off-center inverse homotopy. -/
theorem localComparisonForward_offCenterInverseHomotopy :
    localComparisonOffCenterToCenter G s R ∘ₗ
      localComparisonOffCenterInverseHomotopy G s R = 0 := by
  apply LinearMap.ext
  intro c
  have h := congrArg Prod.snd (ContractibleSumCone.productHomotopy_contracts
    (localComparisonOffCenterDifferential G s R) (laurentXBlockedDifferential G R {s})
    (localComparisonOffCenterToCenter G s R) (localComparisonConeContraction G s R).homotopy
    (localComparisonConeHomotopy_contracts G s R) (c, 0))
  simpa only [LinearMap.mappingCone_apply, Prod.snd_add, localComparisonProductHomotopy_snd,
    map_zero, add_zero, localComparisonOffCenterInverseHomotopy,
    ContractibleSumCone.leftHomotopy, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.inl_apply, LinearMap.zero_apply] using h


/-- The first product column is the off-center inverse homotopy with zero center component. -/
theorem localComparisonProductHomotopy_left
    (c : G.StabilizeXOffCenterState s →₀ LaurentPolynomial R) :
    ContractibleSumCone.productHomotopy (localComparisonConeContraction G s R).homotopy (c, 0) =
      (localComparisonOffCenterInverseHomotopy G s R c, 0) :=
  Prod.ext rfl (localComparisonProductHomotopy_snd G s R (c, 0))

/-- The second product column is the reverse comparison with zero center component. -/
theorem localComparisonProductHomotopy_right (c : LaurentChain R n) :
    ContractibleSumCone.productHomotopy (localComparisonConeContraction G s R).homotopy (0, c) =
      (localComparisonBackward G s R c, 0) :=
  Prod.ext rfl (localComparisonProductHomotopy_snd G s R (0, c))

/-- The off-center inverse homotopy kills the reverse comparison. -/
theorem localComparisonOffCenterInverseHomotopy_backward :
    localComparisonOffCenterInverseHomotopy G s R ∘ₗ localComparisonBackward G s R = 0 := by
  apply LinearMap.ext
  intro c
  have h := congrArg Prod.fst (ContractibleSumCone.productHomotopy_comp_self
    (localComparisonConeContraction G s R).homotopy
    (localComparisonConeContraction G s R).homotopy_comp_homotopy (0, c))
  simpa only [localComparisonProductHomotopy_right, localComparisonProductHomotopy_left,
    LinearMap.comp_apply, LinearMap.zero_apply, Prod.fst_zero] using h

/-- The off-center inverse homotopy squares to zero. -/
theorem localComparisonOffCenterInverseHomotopy_comp_self :
    localComparisonOffCenterInverseHomotopy G s R ∘ₗ
      localComparisonOffCenterInverseHomotopy G s R = 0 := by
  apply LinearMap.ext
  intro c
  have h := congrArg Prod.fst (ContractibleSumCone.productHomotopy_comp_self
    (localComparisonConeContraction G s R).homotopy
    (localComparisonConeContraction G s R).homotopy_comp_homotopy (c, 0))
  simpa only [localComparisonProductHomotopy_left, LinearMap.comp_apply,
    LinearMap.zero_apply, Prod.fst_zero] using h

/-- The actual partially blocked off-center complex retracts to the old split-X-blocked complex. -/
noncomputable def localComparisonRetraction :
    LinearSpecialContraction (localComparisonOffCenterDifferential G s R)
      (laurentXBlockedDifferential G R {s}) where
  incl := localComparisonBackward G s R
  proj := localComparisonOffCenterToCenter G s R
  homotopy := -localComparisonOffCenterInverseHomotopy G s R
  dM_comp_incl := localComparisonBackward_chain G s R
  proj_comp_dM := localComparisonOffCenterToCenter_chain G s R
  proj_comp_incl := localComparisonForward_backward_eq_id G s R
  dM_comp_homotopy_add_homotopy_comp_dM := by
    apply LinearMap.ext
    intro c
    apply Finsupp.ext
    intro x
    have h := congrArg (fun f => f c x) (localComparisonBackward_forward G s R)
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, Finsupp.add_apply, Finsupp.sub_apply] at h
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.neg_apply,
      map_neg, LinearMap.sub_apply, LinearMap.id_apply,
      Finsupp.add_apply, Finsupp.sub_apply, Finsupp.neg_apply]
    linear_combination h
  homotopy_comp_incl := by
    rw [LinearMap.neg_comp, localComparisonOffCenterInverseHomotopy_backward]
    apply LinearMap.ext
    intro c
    apply Finsupp.ext
    intro x
    exact neg_zero
  proj_comp_homotopy := by
    rw [LinearMap.comp_neg, localComparisonForward_offCenterInverseHomotopy]
    apply LinearMap.ext
    intro c
    apply Finsupp.ext
    intro x
    exact neg_zero
  homotopy_comp_homotopy := by
    rw [LinearMap.neg_comp, LinearMap.comp_neg,
      localComparisonOffCenterInverseHomotopy_comp_self]
    apply LinearMap.ext
    intro c
    apply Finsupp.ext
    intro x
    change - -(0 : LaurentPolynomial R) = 0
    simp

end OnLeConjecture.KnotFloer.GridFull
