/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullCommutationHexagonRectangle
public import OnLeConjecture.KnotFloer.GridFullCommutationTurnChange
public import OnLeConjecture.KnotFloer.GridSingleSquareDeformation

/-!
# The geometric hexagon map as a corrected deformation coefficient

The quadratic two-square coefficient alone counts additional rectangles. Adding the
single-square derivative at the second turn square and the target row-band correction
selects precisely the two geometric hexagon shapes. The single-square derivative commutes
with the differential, so this correction leaves the homotopy boundary unchanged.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Polynomial

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

/-- The full geometric hexagon coefficient equals the corrected polynomial coefficient. -/
theorem laurentCommutationHexagonCoefficient_eq_deformation
    (C : GridDiagram.ColumnCommutationData G) (x y : GridState n) :
    laurentCommutationHexagonCoefficient G R C x y = LaurentPolynomial.T (-1) *
      ((squareWeightedCoefficient
          (adjacentSquareDeformationWeight G R C.column C.turnRow) x y).coeff 2 +
        (squareWeightedCoefficient
          (singleSquareDeformationWeight G R (finRotate n C.column) C.turnRow) x y).coeff 1 +
        turnBandCoefficient R C C.oppositeTurnRow y *
          (squareWeightedCoefficient
            (adjacentSquareDeformationWeight G R C.column C.turnRow) x y).coeff 1) := by
  classical
  rw [laurentCommutationHexagonCoefficient_eq_rectangle_sum]
  congr 1
  simp only [Finset.sum_filter, squareWeightedCoefficient, finsetSum_coeff, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [coeff_one_squareWeight_singleSquareDeformation]
  exact fullCommutationHexagon_rectangle_weight_decomposition G R C r

/-- The actual full geometric hexagon map is the quadratic operator with the single-square
and row-band corrections, multiplied by `U⁻¹`. -/
theorem laurentCommutationHexagonMap_eq_deformation (C : GridDiagram.ColumnCommutationData G) :
    laurentCommutationHexagonMap G R C = (LaurentPolynomial.T (-1) : LaurentPolynomial R) •
      (adjacentSquareOperator G R C.column C.turnRow 2 +
        singleSquareOperator G R (finRotate n C.column) C.turnRow 1 +
        turnBandMap R C C.oppositeTurnRow ∘ₗ
          adjacentSquareOperator G R C.column C.turnRow 1) := by
  classical
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro y
  simp only [laurentCommutationHexagonMap_apply_apply, LinearMap.smul_apply,
    Finsupp.smul_apply, smul_eq_mul, LinearMap.add_apply, Finsupp.add_apply,
    LinearMap.comp_apply, turnBandMap_apply, adjacentSquareOperator, singleSquareOperator,
    polynomialCoefficientOperator_apply_apply,
    laurentCommutationHexagonCoefficient_eq_deformation, Finsupp.sum]
  simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

end OnLeConjecture.KnotFloer.GridFull
