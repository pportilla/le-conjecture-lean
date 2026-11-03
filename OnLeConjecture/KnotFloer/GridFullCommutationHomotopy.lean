/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullCommutationReverseGauge
public import OnLeConjecture.KnotFloer.GridFullCommutationHexagonDeformation
import Mathlib.Tactic.LinearCombination

/-!
# Full geometric pentagon inverse homotopies

The opposite-turn pentagon map is inverse up to the actual geometric
hexagon homotopy, with X markings allowed throughout. The single-square
correction and the turn-band identity identify the geometric hexagon
boundary with the two-square curvature equation.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

/-- The corrected deformation expression has boundary `U` minus the opposite-turn composite. -/
theorem adjacentSquareOperator_opposite_homotopy
    (C : GridDiagram.ColumnCommutationData G) (c : LaurentChain R n) :
    let A := adjacentSquareOperator G R C.column C.turnRow 1
    let T := adjacentSquareOperator G R C.column C.oppositeTurnRow 1
    let B := adjacentSquareOperator G R C.column C.turnRow 2
    let L := singleSquareOperator G R (finRotate n C.column) C.turnRow 1
    let P := turnBandMap R C C.oppositeTurnRow
    T (A c) + laurentDifferential G R ((B + L + P ∘ₗ A) c) +
      (B + L + P ∘ₗ A) (laurentDifferential G R c) =
      (LaurentPolynomial.T 1 : LaurentPolynomial R) • c := by
  dsimp only
  apply Finsupp.ext
  intro y
  have hB := congrArg
    (fun f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n => f c y)
    (adjacentSquareOperator_two_homotopy (R := R) G C.toColumnTurn.one_lt
      C.column C.turnRow)
  have hA := congrArg
    (fun f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n =>
      f (adjacentSquareOperator G R C.column C.turnRow 1 c) y)
    (adjacentSquareOperator_turn_change (R := R) G C C.oppositeTurnRow
      C.turnRow_ne_oppositeTurnRow)
  have hL := congrArg
    (fun f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n => f c y)
    (singleSquareOperator_one_chain (R := R) G (finRotate n C.column) C.turnRow)
  have hcomm := congrArg (fun d => turnBandMap R C C.oppositeTurnRow d y)
    (laurentDifferential_adjacentSquareOperator_one G R C c)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.zero_apply, Finsupp.add_apply, Finsupp.zero_apply,
    Finsupp.smul_apply, smul_eq_mul, map_add] at hB hA hL ⊢
  rw [← hcomm]
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hB + hA + hL

/-- The geometric opposite-turn composite and the source hexagon boundary sum to the identity. -/
theorem laurentCommutation_source_homotopy (C : GridDiagram.ColumnCommutationData G)
    (c : LaurentChain R n) :
    laurentReverseCommutationMap G R C (laurentCommutationMap G R C c) +
      laurentDifferential G R (laurentCommutationHexagonMap G R C c) +
      laurentCommutationHexagonMap G R C (laurentDifferential G R c) = c := by
  have h := congrArg (fun d : LaurentChain R n =>
    (LaurentPolynomial.T (-1) : LaurentPolynomial R) • d)
    (adjacentSquareOperator_opposite_homotopy G R C c)
  simp only [smul_add, smul_smul, ← LaurentPolynomial.T_add,
    neg_add_cancel, LaurentPolynomial.T_zero, one_smul] at h
  simpa only [laurentCommutationMap_eq_gauge_operator, LinearMap.comp_apply,
    LinearEquiv.coe_coe, laurentReverseCommutationMap_commutationGauge,
    laurentCommutationHexagonMap_eq_deformation, LinearMap.smul_apply, map_smul] using h

/-- The geometric forward composite and the reverse hexagon boundary sum to the identity. -/
theorem laurentCommutation_target_homotopy (C : GridDiagram.ColumnCommutationData G)
    (c : LaurentChain R n) :
    laurentCommutationMap G R C (laurentReverseCommutationMap G R C c) +
      laurentDifferential (G.swapColumns C.column (finRotate n C.column)) R
        (laurentCommutationHexagonMap
          (G.swapColumns C.column (finRotate n C.column)) R C.reverse c) +
      laurentCommutationHexagonMap (G.swapColumns C.column (finRotate n C.column)) R C.reverse
        (laurentDifferential (G.swapColumns C.column (finRotate n C.column)) R c) = c := by
  have hturn : C.reverse.reverse.toColumnTurn = C.toColumnTurn := by
    ext <;> simp
  have h := laurentCommutation_source_homotopy
    (G.swapColumns C.column (finRotate n C.column)) R C.reverse c
  simpa only [laurentReverseCommutationMap, GridDiagram.ColumnCommutationData.reverse_column,
    GridDiagram.swapColumns_swapColumns, hturn] using h

end OnLeConjecture.KnotFloer.GridFull
