/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationLocalContraction
public import OnLeConjecture.KnotFloer.ContractibleSumCone

/-!
# Concrete inverse comparison for the partially blocked stabilization

The reverse map and inverse homotopies are components of the constructed contracting
homotopy. Their identities concern the actual off-center differential and the old
differential with the split X blocked.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R] [CharP R 2]

/-- The constructed contracting equation in its identity form. -/
theorem localComparisonConeHomotopy_contracts :
    localComparisonCone G s R ∘ₗ (localComparisonConeContraction G s R).homotopy +
      (localComparisonConeContraction G s R).homotopy ∘ₗ localComparisonCone G s R =
        LinearMap.id := by
  have h := (localComparisonConeContraction G s R).dM_comp_homotopy_add_homotopy_comp_dM
  have hi : (localComparisonConeContraction G s R).incl = 0 := rfl
  rw [hi, LinearMap.zero_comp] at h
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro i
  have hh := congrArg (fun f => f c i) h
  simpa only [LinearMap.sub_apply, LinearMap.zero_apply, Finsupp.sub_apply,
    Finsupp.zero_apply, sub_zero] using hh

/-- The reverse comparison extracted from the concrete cone contraction. -/
noncomputable def localComparisonBackward : LaurentChain R n →ₗ[LaurentPolynomial R]
    (G.StabilizeXOffCenterState s →₀ LaurentPolynomial R) :=
  ContractibleSumCone.backward (localComparisonConeContraction G s R).homotopy

/-- The off-center inverse homotopy extracted from the same contraction. -/
noncomputable def localComparisonOffCenterInverseHomotopy :
    Module.End (LaurentPolynomial R) (G.StabilizeXOffCenterState s →₀ LaurentPolynomial R) :=
  ContractibleSumCone.leftHomotopy (localComparisonConeContraction G s R).homotopy

/-- The old-grid inverse homotopy extracted from the same contraction. -/
noncomputable def localComparisonOldInverseHomotopy : Module.End (LaurentPolynomial R)
    (LaurentChain R n) :=
  ContractibleSumCone.rightHomotopy (localComparisonConeContraction G s R).homotopy

/-- The concrete reverse comparison intertwines the differentials. -/
theorem localComparisonBackward_chain :
    localComparisonOffCenterDifferential G s R ∘ₗ localComparisonBackward G s R =
      localComparisonBackward G s R ∘ₗ laurentXBlockedDifferential G R {s} :=
  ContractibleSumCone.backward_chain (localComparisonOffCenterDifferential G s R)
    (laurentXBlockedDifferential G R {s}) (localComparisonOffCenterToCenter G s R)
    (localComparisonConeContraction G s R).homotopy (localComparisonConeHomotopy_contracts G s R)

/-- The off-center composite is homotopic to its identity by the specified matrix component. -/
theorem localComparisonBackward_forward :
    localComparisonBackward G s R ∘ₗ localComparisonOffCenterToCenter G s R - LinearMap.id =
      localComparisonOffCenterDifferential G s R ∘ₗ
          localComparisonOffCenterInverseHomotopy G s R +
        localComparisonOffCenterInverseHomotopy G s R ∘ₗ
          localComparisonOffCenterDifferential G s R :=
  ContractibleSumCone.backward_forward (localComparisonOffCenterDifferential G s R)
    (laurentXBlockedDifferential G R {s}) (localComparisonOffCenterToCenter G s R)
    (localComparisonConeContraction G s R).homotopy (localComparisonConeHomotopy_contracts G s R)

/-- The old-grid composite is homotopic to its identity by the specified matrix component. -/
theorem localComparisonForward_backward :
    LinearMap.id - localComparisonOffCenterToCenter G s R ∘ₗ localComparisonBackward G s R =
      laurentXBlockedDifferential G R {s} ∘ₗ localComparisonOldInverseHomotopy G s R +
        localComparisonOldInverseHomotopy G s R ∘ₗ laurentXBlockedDifferential G R {s} :=
  ContractibleSumCone.forward_backward (localComparisonOffCenterDifferential G s R)
    (laurentXBlockedDifferential G R {s}) (localComparisonOffCenterToCenter G s R)
    (localComparisonConeContraction G s R).homotopy (localComparisonConeHomotopy_contracts G s R)


/-- Nonzero reverse-comparison coefficients have degree zero and preserve both coordinates. -/
theorem localComparisonBackward_coefficient_bounds (x : GridState n)
    (y : G.StabilizeXOffCenterState s) {k : ℤ}
    (hk : k ∈ (localComparisonBackward G s R (single x 1) y).coeff.support) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ y - 2 * k = G.maslovOℤ x ∧
    -(k : ℚ) ≤ 0 ∧
    (G.stabilizeX s.castSucc (G.X s).castSucc s).alexander y - k ≤ G.alexander x := by
  rw [localComparisonBackward, ContractibleSumCone.backward_single_apply] at hk
  have hM := (localComparisonConeContraction_homotopy_mem_maslovPiece G s R
    (single_one_mem_laurentReducedConeMaslovPiece G s R (.inr x))) (.inl y) k hk
  have hA := (localComparisonConeContraction_homotopy_mem_bifiltrationLevel G s R
    (single_one_mem_laurentReducedConeBifiltrationLevel G s R (.inr x))) (.inl y) k hk
  dsimp only [reducedConeMaslov, reducedConeAlexander] at hM hA
  exact ⟨by omega, hA⟩

/-- The extracted off-center inverse homotopy has degree one and preserves both coordinates. -/
theorem localComparisonOffCenterInverseHomotopy_coefficient_bounds
    (x y : G.StabilizeXOffCenterState s) {k : ℤ}
    (hk : k ∈ (localComparisonOffCenterInverseHomotopy G s R (single x 1) y).coeff.support) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ y - 2 * k =
      (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ x + 1 ∧
    -(k : ℚ) ≤ 0 ∧
    (G.stabilizeX s.castSucc (G.X s).castSucc s).alexander y - k ≤
      (G.stabilizeX s.castSucc (G.X s).castSucc s).alexander x := by
  rw [localComparisonOffCenterInverseHomotopy, ContractibleSumCone.leftHomotopy_single_apply] at hk
  have hM := (localComparisonConeContraction_homotopy_mem_maslovPiece G s R
    (single_one_mem_laurentReducedConeMaslovPiece G s R (.inl x))) (.inl y) k hk
  have hA := (localComparisonConeContraction_homotopy_mem_bifiltrationLevel G s R
    (single_one_mem_laurentReducedConeBifiltrationLevel G s R (.inl x))) (.inl y) k hk
  exact ⟨hM, hA⟩

/-- The extracted old-grid inverse homotopy has degree one and preserves both coordinates. -/
theorem localComparisonOldInverseHomotopy_coefficient_bounds (x y : GridState n) {k : ℤ}
    (hk : k ∈ (localComparisonOldInverseHomotopy G s R (single x 1) y).coeff.support) :
    G.maslovOℤ y - 2 * k = G.maslovOℤ x + 1 ∧
      -(k : ℚ) ≤ 0 ∧ G.alexander y - k ≤ G.alexander x := by
  rw [localComparisonOldInverseHomotopy, ContractibleSumCone.rightHomotopy_single_apply] at hk
  have hM := (localComparisonConeContraction_homotopy_mem_maslovPiece G s R
    (single_one_mem_laurentReducedConeMaslovPiece G s R (.inr x))) (.inr y) k hk
  have hA := (localComparisonConeContraction_homotopy_mem_bifiltrationLevel G s R
    (single_one_mem_laurentReducedConeBifiltrationLevel G s R (.inr x))) (.inr y) k hk
  dsimp only [reducedConeMaslov, reducedConeAlexander] at hM hA
  exact ⟨by omega, hA⟩

/-- The actual forward rectangle comparison has degree zero and preserves both coordinates. -/
theorem localComparisonOffCenterToCenter_coefficient_bounds
    (x : G.StabilizeXOffCenterState s) (y : GridState n) {k : ℤ}
    (hk : k ∈ (localComparisonOffCenterToCenter G s R (single x 1) y).coeff.support) :
    G.maslovOℤ y - 2 * k =
      (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ x ∧
    -(k : ℚ) ≤ 0 ∧
      G.alexander y - k ≤ (G.stabilizeX s.castSucc (G.X s).castSucc s).alexander x := by
  classical
  rw [← LinearMap.sumMappingCone_single_inl_apply_inr
    (localComparisonOffCenterDifferential G s R) (laurentXBlockedDifferential G R {s})] at hk
  change k ∈ (localComparisonCone G s R (single (.inl x) 1) (.inr y)).coeff.support at hk
  rw [localComparisonCone_single_apply, AddMonoidAlgebra.coeff_sum] at hk
  obtain ⟨r, hr, hkr⟩ := Finset.mem_biUnion.mp (support_finsetSum hk)
  change k ∈ (single
    (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle).card : ℤ)
    (1 : R)).support at hkr
  have hk0 := Finset.mem_singleton.mp (support_single_subset hkr)
  subst k
  have hM := localComparisonRectangles_maslov G s hr
  have hA : reducedConeAlexander G s (.inr y) -
      (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle).card : ℚ) ≤
      reducedConeAlexander G s (.inl x) := by
    by_cases hold : r ∈ comparisonConeRectangles G s (.inl x) (.inr y)
    · exact le_of_eq (comparisonConeRectangles_grading G s hold).2
    · have h := localComparisonRectangles_extra_alexander G s hr hold
      linarith
  dsimp only [reducedConeMaslov, reducedConeAlexander] at hM hA
  exact ⟨by omega, by push_cast; exact neg_nonpos.mpr (Nat.cast_nonneg _), hA⟩

end OnLeConjecture.KnotFloer.GridFull
