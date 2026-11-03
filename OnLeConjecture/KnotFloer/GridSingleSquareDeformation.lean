/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridWeightedDeformation

/-!
# A polynomial deformation at one grid square

Multiplying the O weight at one square by `1 + X` changes one row and
one column annulus by the same amount. The curvature therefore vanishes
in characteristic two. The linear coefficient counts all empty rectangles
containing that square and commutes with the full Laurent differential.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Polynomial

variable {n : ℕ} {R : Type*} [CommSemiring R]

/-- The O weights deformed at a single square. -/
noncomputable def singleSquareDeformationWeight (G : GridDiagram n) (R : Type*)
    [CommSemiring R] (a s : Fin n) (p : Fin n × Fin n) : Polynomial (LaurentPolynomial R) :=
  C (oSquareWeight G p) * (if p = (a, s) then 1 + X else 1)

theorem singleSquareDeformation_column (G : GridDiagram n) (a s c : Fin n) :
    ∏ r : Fin n, singleSquareDeformationWeight G R a s (c, r) =
      C (LaurentPolynomial.T 1) * (if c = a then 1 + X else 1) := by
  classical
  simp only [singleSquareDeformationWeight, Finset.prod_mul_distrib,
    ← map_prod, oSquareWeight_column]
  by_cases hc : c = a <;> simp [Prod.mk.injEq, hc]

theorem singleSquareDeformation_row (G : GridDiagram n) (a s r : Fin n) :
    ∏ c : Fin n, singleSquareDeformationWeight G R a s (c, r) =
      C (LaurentPolynomial.T 1) * (if r = s then 1 + X else 1) := by
  classical
  simp only [singleSquareDeformationWeight, Finset.prod_mul_distrib,
    ← map_prod, oSquareWeight_row]
  by_cases hr : r = s <;> simp [Prod.mk.injEq, hr]

/-- Row and column contributions cancel for a single-square deformation. -/
theorem singleSquareDeformation_curvature [CharP R 2]
    (G : GridDiagram n) (a s : Fin n) :
    squareWeightCurvature (singleSquareDeformationWeight G R a s) = 0 := by
  classical
  let U : Polynomial (LaurentPolynomial R) := C (LaurentPolynomial.T 1)
  have heq (i j : Fin n) :
      U * (if i = j then 1 + X else 1) = U + (if i = j then U * X else 0) := by
    by_cases h : i = j <;> simp [h, mul_add]
  simp only [squareWeightCurvature, singleSquareDeformation_column,
    singleSquareDeformation_row]
  change (∑ c : Fin n, U * _) + (∑ r : Fin n, U * _) = 0
  simp_rw [heq, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, CharTwo.add_self_eq_zero]

/-- The coefficient operator of the single-square deformation. -/
noncomputable def singleSquareOperator (G : GridDiagram n) (R : Type*)
    [CommSemiring R] (a s : Fin n) (k : ℕ) :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
  polynomialCoefficientOperator (singleSquareDeformationWeight G R a s) k

/-- The constant coefficient is the full Laurent differential. -/
theorem singleSquareOperator_zero (G : GridDiagram n) (a s : Fin n) :
    singleSquareOperator G R a s 0 = laurentDifferential G R := by
  rw [singleSquareOperator, polynomialCoefficientOperator_zero]
  have hw : (fun p => (singleSquareDeformationWeight G R a s p).coeff 0) =
      oSquareWeight (R := R) G := by
    funext p
    simp only [singleSquareDeformationWeight]
    split_ifs <;> simp
  rw [hw, squareWeightedDifferential_oSquareWeight]

/-- The single-square derivative commutes with the full Laurent differential. -/
theorem singleSquareOperator_one_chain [CharP R 2]
    (G : GridDiagram n) (a s : Fin n) :
    laurentDifferential G R ∘ₗ singleSquareOperator G R a s 1 +
      singleSquareOperator G R a s 1 ∘ₗ laurentDifferential G R = 0 := by
  have h := polynomialCoefficientOperator_one_identity (singleSquareDeformationWeight G R a s)
  change singleSquareOperator G R a s 0 ∘ₗ singleSquareOperator G R a s 1 +
    singleSquareOperator G R a s 1 ∘ₗ singleSquareOperator G R a s 0 = _ at h
  simpa only [singleSquareOperator_zero, singleSquareDeformation_curvature,
    Polynomial.coeff_zero, zero_smul] using h

/-- A rectangle has one deformation factor exactly when it contains the chosen square. -/
theorem squareWeight_singleSquareDeformation (G : GridDiagram n)
    (a s : Fin n) (r : GridRectangle n) :
    squareWeight (singleSquareDeformationWeight G R a s) r =
      Polynomial.C (LaurentPolynomial.T ((G.OColumns r).card : ℤ)) *
        (if (a, s) ∈ r.coveredSquares then 1 + X else 1) := by
  classical
  simp only [squareWeight, singleSquareDeformationWeight, Finset.prod_mul_distrib,
    ← map_prod]
  rw [Finset.prod_ite_eq']
  have hw := squareWeight_oSquareWeight (R := R) G r
  rw [laurentSpecialization_OMonomial] at hw
  exact congrArg (fun z => Polynomial.C z * _) hw

open Classical in
/-- The linear coefficient counts all rectangles containing the chosen square. -/
theorem coeff_one_squareWeight_singleSquareDeformation (G : GridDiagram n)
    (a s : Fin n) (r : GridRectangle n) :
    (squareWeight (singleSquareDeformationWeight G R a s) r).coeff 1 =
      if (a, s) ∈ r.coveredSquares then
        LaurentPolynomial.T ((G.OColumns r).card : ℤ) else 0 := by
  rw [squareWeight_singleSquareDeformation]
  split_ifs <;> simp [Polynomial.coeff_one]

open Classical in
/-- The matrix coefficient is the O-weighted sum over empty rectangles containing the square. -/
theorem coeff_one_squareWeightedCoefficient_singleSquareDeformation (G : GridDiagram n)
    (a s : Fin n) (x y : GridState n) :
    (squareWeightedCoefficient (singleSquareDeformationWeight G R a s) x y).coeff 1 =
      ∑ r ∈ (GridRectangleBetween.emptyRectangles x y).filter
        (fun r => (a, s) ∈ r.toGridRectangle.coveredSquares),
        LaurentPolynomial.T ((G.OColumns r.toGridRectangle).card : ℤ) := by
  simp only [squareWeightedCoefficient, finsetSum_coeff,
    coeff_one_squareWeight_singleSquareDeformation, Finset.sum_filter]

end OnLeConjecture.KnotFloer.GridFull
