/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullCommutationFilteredInverse
public import OnLeConjecture.KnotFloer.GridFullCommutationTurnChange
public import OnLeConjecture.KnotFloer.GridFullCommutationAlgebraicInverse

/-!
# The opposite-turn pentagon map and the rectangle operators

The reverse geometric pentagon map is the opposite-turn rectangle
operator after the inverse diagonal gauge, divided by the Laurent
variable. This identifies its concrete polygon count with the operators
used in the deformation homotopy identities.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

/-- Selecting a turn does not alter the rectangle gauge relation. -/
theorem coeff_one_mul_commutationGauge (C : GridDiagram.ColumnTurn n) (t : Fin n)
    (x y : GridState n) :
    LaurentPolynomial.T (commutationGaugeExponent G C x) *
        (squareWeightedCoefficient (adjacentSquareDeformationWeight
          (G.swapColumns C.column (finRotate n C.column)) R C.column t) x y).coeff 1 =
      LaurentPolynomial.T (commutationGaugeExponent G C y) *
        (squareWeightedCoefficient
          (adjacentSquareDeformationWeight G R C.column t) x y).coeff 1 := by
  classical
  rw [coeff_one_squareWeightedCoefficient_adjacentSquareDeformation _ (C.withTurnRow t),
    coeff_one_squareWeightedCoefficient_adjacentSquareDeformation _ (C.withTurnRow t)]
  simp only [Finset.mul_sum, ← LaurentPolynomial.T_add]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  have he := (GridRectangleBetween.mem_emptyRectangles r).mp (Finset.mem_filter.mp hr).1
  have h := commutationGaugeExponent_rectangle G C r he
  omega

/-- Each linear turn operator intertwines the explicit diagonal gauges. -/
theorem adjacentSquareOperator_one_commutationGauge (C : GridDiagram.ColumnTurn n) (t : Fin n)
    (c : LaurentChain R n) :
    adjacentSquareOperator (G.swapColumns C.column (finRotate n C.column)) R C.column t 1
        (commutationGauge G R C c) =
      commutationGauge G R C (adjacentSquareOperator G R C.column t 1 c) := by
  classical
  apply Finsupp.ext
  intro y
  simp only [adjacentSquareOperator, polynomialCoefficientOperator_apply_apply,
    commutationGauge_apply]
  rw [Finsupp.sum_fintype _ _ fun _ => zero_mul _,
    Finsupp.sum_fintype _ _ fun _ => zero_mul _, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [commutationGauge_apply]
  rw [mul_assoc, mul_left_comm (LaurentPolynomial.T (commutationGaugeExponent G C x))
    (c x), coeff_one_mul_commutationGauge G R C t x y]
  ring

omit R [CommRing R] [CharP R 2] in
/-- The forward and reverse gauge exponents add to minus one. -/
theorem commutationGaugeExponent_reverse_add (C : GridDiagram.ColumnCommutationData G)
    (x : GridState n) :
    commutationGaugeExponent (G.swapColumns C.column (finRotate n C.column)) C.reverse x +
      commutationGaugeExponent G C x = -1 := by
  have h := maslov_swapColumns_eq_gauge G C x
  have h' := maslov_swapColumns_eq_gauge
    (G.swapColumns C.column (finRotate n C.column)) C.reverse x
  simp only [GridDiagram.ColumnCommutationData.reverse_column,
    GridDiagram.swapColumns_swapColumns] at h'
  omega

omit [CharP R 2] in
/-- Composing the opposite diagonal gauges multiplies every chain by `T (-1)`. -/
theorem commutationGauge_reverse_comp (C : GridDiagram.ColumnCommutationData G)
    (c : LaurentChain R n) :
    commutationGauge (G.swapColumns C.column (finRotate n C.column)) R C.reverse
      (commutationGauge G R C c) = (LaurentPolynomial.T (-1) : LaurentPolynomial R) • c := by
  apply Finsupp.ext
  intro x
  simp only [commutationGauge_apply, Finsupp.smul_apply, smul_eq_mul, ← mul_assoc,
    ← LaurentPolynomial.T_add, commutationGaugeExponent_reverse_add]

/-- The reverse geometric pentagon count after the gauge is the opposite-turn operator over U. -/
theorem laurentReverseCommutationMap_commutationGauge
    (C : GridDiagram.ColumnCommutationData G) (c : LaurentChain R n) :
    laurentReverseCommutationMap G R C (commutationGauge G R C c) =
      (LaurentPolynomial.T (-1) : LaurentPolynomial R) •
        adjacentSquareOperator G R C.column C.oppositeTurnRow 1 c := by
  rw [laurentReverseCommutationMap, laurentCommutationMap_eq_gauge_operator]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    GridDiagram.ColumnCommutationData.reverse_column,
    GridDiagram.ColumnCommutationData.reverse_turnRow]
  rw [adjacentSquareOperator_one_commutationGauge, commutationGauge_reverse_comp]

/-- Exact operator formula for the geometric opposite-turn pentagon map. -/
theorem laurentReverseCommutationMap_eq_operator_gauge
    (C : GridDiagram.ColumnCommutationData G) :
    laurentReverseCommutationMap G R C = (LaurentPolynomial.T (-1) : LaurentPolynomial R) •
      (adjacentSquareOperator G R C.column C.oppositeTurnRow 1 ∘ₗ
        (commutationGauge G R C).symm.toLinearMap) := by
  apply LinearMap.ext
  intro c
  have h := laurentReverseCommutationMap_commutationGauge G R C ((commutationGauge G R C).symm c)
  simpa using h

end OnLeConjecture.KnotFloer.GridFull
