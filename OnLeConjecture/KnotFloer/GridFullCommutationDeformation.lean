/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullCommutationRectangle
public import OnLeConjecture.KnotFloer.GridWeightedDeformation

/-!
# The pentagon map as a coefficient of the weighted differential

The linear term of the two-square deformation counts exactly the
rectangles corresponding to commutation pentagons. Multiplication by
the explicit diagonal gauge converts their weights to pentagon weights.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Polynomial

variable {n : ℕ} {R : Type*} [CommSemiring R]

/-- A product of the two-square multiplier records the two square memberships separately. -/
theorem prod_twoSquareMultiplier {S : Type*} [CommSemiring S]
    (a b s : Fin n) (hab : a ≠ b) (q : S) (t : Finset (Fin n × Fin n)) :
    ∏ p ∈ t, twoSquareMultiplier a b s q p =
      (if (a, s) ∈ t then q else 1) * (if (b, s) ∈ t then q else 1) := by
  classical
  have heq (p : Fin n × Fin n) : twoSquareMultiplier a b s q p =
      (if p = (a, s) then q else 1) * (if p = (b, s) then q else 1) := by
    by_cases ha : p = (a, s) <;> by_cases hb : p = (b, s) <;>
      simp_all [twoSquareMultiplier, Prod.mk.injEq]
  simp_rw [heq]
  rw [Finset.prod_mul_distrib]
  simp

/-- The deformed rectangle weight has one factor for each adjacent square it contains. -/
theorem squareWeight_adjacentSquareDeformation (G : GridDiagram n)
    (C : GridDiagram.ColumnTurn n) (r : GridRectangle n) :
    squareWeight (adjacentSquareDeformationWeight G R C.column C.turnRow) r =
      Polynomial.C (LaurentPolynomial.T ((G.OColumns r).card : ℤ)) *
        ((if (C.column, C.turnRow) ∈ r.coveredSquares then 1 + X else 1) *
          (if (finRotate n C.column, C.turnRow) ∈ r.coveredSquares then 1 + X else 1)) := by
  simp only [squareWeight, adjacentSquareDeformationWeight, Finset.prod_mul_distrib,
    ← map_prod]
  rw [prod_twoSquareMultiplier _ _ _ C.column_ne_next]
  have hw := squareWeight_oSquareWeight (R := R) G r
  rw [laurentSpecialization_OMonomial] at hw
  exact congrArg (fun z => Polynomial.C z * _) hw

open Classical in
/-- In characteristic two the linear term occurs exactly when one square is contained. -/
theorem coeff_one_squareWeight_adjacentSquareDeformation [CharP R 2]
    (G : GridDiagram n) (C : GridDiagram.ColumnTurn n) {x y : GridState n}
    (r : GridRectangleBetween x y) :
    (squareWeight (adjacentSquareDeformationWeight G R C.column C.turnRow)
      r.toGridRectangle).coeff 1 =
      if crossesOneTurnSquare C r then
        LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) else 0 := by
  rw [squareWeight_adjacentSquareDeformation]
  by_cases ha : (C.column, C.turnRow) ∈ r.toGridRectangle.coveredSquares <;>
    by_cases hb : (finRotate n C.column, C.turnRow) ∈ r.toGridRectangle.coveredSquares <;>
      simp only [crossesOneTurnSquare, Xor, ha, hb, not_true_eq_false,
        not_false_eq_true, and_false, and_true, or_false, false_or,
        if_true, if_false] <;>
      simp [mul_add, add_mul, CharTwo.add_self_eq_zero]

open Classical in
/-- The linear coefficient of the weighted differential is the selected rectangle sum. -/
theorem coeff_one_squareWeightedCoefficient_adjacentSquareDeformation [CharP R 2]
    (G : GridDiagram n) (C : GridDiagram.ColumnTurn n) (x y : GridState n) :
    (squareWeightedCoefficient (adjacentSquareDeformationWeight G R C.column C.turnRow)
      x y).coeff 1 =
      ∑ r ∈ (GridRectangleBetween.emptyRectangles x y).filter (crossesOneTurnSquare C),
        LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) := by
  simp only [squareWeightedCoefficient, finsetSum_coeff,
    coeff_one_squareWeight_adjacentSquareDeformation, Finset.sum_filter]

/-- The geometric pentagon map is the diagonal gauge after the linear deformation operator. -/
theorem laurentCommutationMap_eq_gauge_operator [CharP R 2]
    (G : GridDiagram n) (C : GridDiagram.ColumnCommutationData G) :
    laurentCommutationMap G R C = (commutationGauge G R C).toLinearMap ∘ₗ
      adjacentSquareOperator G R C.column C.turnRow 1 := by
  classical
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, commutationGauge_apply,
    adjacentSquareOperator, polynomialCoefficientOperator_apply_apply,
    laurentCommutationMap_apply_apply,
    coeff_one_squareWeightedCoefficient_adjacentSquareDeformation,
    laurentCommutationCoefficient_eq_rectangle_sum, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro r _
  ring

end OnLeConjecture.KnotFloer.GridFull
