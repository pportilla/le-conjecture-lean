/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationOCommutation

/-!
# The normalized derivative at the new O marking

Removing the new O factor from rectangles through that marking gives a degree-one
operator commuting with the full differential. It has no center output and kills
the partner generators. Consequently it commutes with the reverse row matching
after the center-partner pairs have been removed.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R]

/-- Count rectangles through the new O marking, omitting that O's Laurent factor. -/
noncomputable def stabilizationODerivative : Module.End (LaurentPolynomial R)
    (LaurentChain R (n + 1)) :=
  (LaurentPolynomial.T (-1) : LaurentPolynomial R) •
    squareDerivative (oSquareWeight (G.stabilizeX s.castSucc (G.X s).castSucc s))
      s.castSucc (G.X s).castSucc

/-- The old state basis inserted at its off-center matching partners. -/
noncomputable def laurentStabilizationPartnerInclusion :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R (n + 1) :=
  Finsupp.linearCombination (LaurentPolynomial R)
    (fun x => single (stabilizationPartnerState G s x).val 1)

@[simp]
theorem laurentStabilizationPartnerInclusion_single (x : GridState n) :
    laurentStabilizationPartnerInclusion G s R (single x 1) =
      single (stabilizationPartnerState G s x).val 1 := by
  simp only [laurentStabilizationPartnerInclusion, Finsupp.linearCombination_single, one_smul]

/-- No rectangle counted by the new-O derivative ends at a center state. -/
theorem centerProjection_stabilizationODerivative :
    laurentStabilizationCenterProjection G s R ∘ₗ stabilizationODerivative G s R = 0 := by
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  ext y
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply,
    laurentStabilizationCenterProjection_apply, stabilizationODerivative,
    LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul,
    squareDerivative_single_apply, LinearMap.zero_apply, Finsupp.zero_apply]
  rw [squareDerivative_coefficient_eq_zero_of_target_northeast s (G.X s) _ _ _
    (GridState.insertPoint_apply_newColumn _ _ _), mul_zero]

/-- The new-O derivative kills every off-center partner generator. -/
theorem stabilizationODerivative_partnerInclusion :
    stabilizationODerivative G s R ∘ₗ laurentStabilizationPartnerInclusion G s R = 0 := by
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  ext y
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply,
    laurentStabilizationPartnerInclusion_single, stabilizationODerivative,
    LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul,
    squareDerivative_single_apply, LinearMap.zero_apply, Finsupp.zero_apply]
  rw [squareDerivative_coefficient_eq_zero_of_source_southeast s (G.X s) _ _ _ ?_, mul_zero]
  simp only [stabilizationPartnerState, GridState.swapRows_apply,
    GridState.insertPoint_apply_newColumn, Equiv.swap_apply_right]

/-- Reverse only the row-matching pairs having neither endpoint at the center. -/
noncomputable def stabilizationReverseMatchingWithoutCenters :
    Module.End (LaurentPolynomial R) (LaurentChain R (n + 1)) :=
  rowReverseMatching s (G.X s) (LaurentPolynomial R) -
    laurentStabilizationPartnerInclusion G s R ∘ₗ laurentStabilizationCenterProjection G s R

/-- The new-O derivative commutes with the reverse matching after removing center pairs. -/
theorem stabilizationReverseMatchingWithoutCenters_ODerivative_commute :
    stabilizationReverseMatchingWithoutCenters G s R ∘ₗ stabilizationODerivative G s R =
      stabilizationODerivative G s R ∘ₗ stabilizationReverseMatchingWithoutCenters G s R := by
  have h := rowReverseMatching_squareDerivative_commute s (G.X s) (LaurentPolynomial R)
    (oSquareWeight (G.stabilizeX s.castSucc (G.X s).castSucc s))
  have hfull : rowReverseMatching s (G.X s) (LaurentPolynomial R) ∘ₗ
      stabilizationODerivative G s R = stabilizationODerivative G s R ∘ₗ
        rowReverseMatching s (G.X s) (LaurentPolynomial R) := by
    rw [stabilizationODerivative, LinearMap.comp_smul, LinearMap.smul_comp, h]
  rw [stabilizationReverseMatchingWithoutCenters, LinearMap.sub_comp, LinearMap.comp_sub,
    LinearMap.comp_assoc, centerProjection_stabilizationODerivative, LinearMap.comp_zero,
    ← LinearMap.comp_assoc, stabilizationODerivative_partnerInclusion, LinearMap.zero_comp]
  exact congrArg (fun f : Module.End (LaurentPolynomial R) (LaurentChain R (n + 1)) => f - 0) hfull

variable [CharP R 2]

/-- The new-O derivative commutes with the actual full stabilized differential. -/
theorem stabilizationODerivative_chain :
    laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R ∘ₗ
        stabilizationODerivative G s R =
      stabilizationODerivative G s R ∘ₗ
        laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R := by
  have h := squareDerivative_homotopy
    (oSquareWeight (R := R) (G.stabilizeX s.castSucc (G.X s).castSucc s))
    s.castSucc (G.X s).castSucc
  rw [squareWeightedDifferential_oSquareWeight, oSquareWeight_column,
    oSquareWeight_row, CharTwo.add_self_eq_zero, zero_smul] at h
  have hc : laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R ∘ₗ
      squareDerivative (oSquareWeight (G.stabilizeX s.castSucc (G.X s).castSucc s))
        s.castSucc (G.X s).castSucc =
      squareDerivative (oSquareWeight (G.stabilizeX s.castSucc (G.X s).castSucc s))
        s.castSucc (G.X s).castSucc ∘ₗ
      laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R := by
    apply LinearMap.ext
    intro c
    apply Finsupp.ext
    intro y
    have hh := congrArg (fun f => f c y) h
    simp only [LinearMap.add_apply, Finsupp.add_apply, LinearMap.zero_apply,
      Finsupp.zero_apply] at hh
    exact CharTwo.add_eq_zero.mp hh
  rw [stabilizationODerivative, LinearMap.comp_smul, LinearMap.smul_comp, hc]

end OnLeConjecture.KnotFloer.GridFull
