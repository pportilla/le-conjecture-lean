/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridWeightedCurvature
public import OnLeConjecture.KnotFloer.GridFullLaurent
public import OnLeConjecture.KnotFloer.GridPolynomialOperators
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.CharP.Algebra

/-!
# A polynomial deformation at two adjacent grid squares

The Laurent O weight is multiplied by `1 + X` at two adjacent squares
in one row. Its curvature is exactly `T 1 * X^2` in characteristic two.
Coefficient identities then give an operator commuting with the full
Laurent differential and a homotopy for the square of that operator.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Polynomial

variable {n : ℕ} {R : Type*} [CommSemiring R]

/-- Laurent polynomials retain the characteristic of their coefficient semiring. -/
instance instCharPLaurentPolynomial {p : ℕ} [CharP R p] : CharP (LaurentPolynomial R) p :=
  charP_of_injective_ringHom (f := LaurentPolynomial.C) (by
    intro a b h
    simpa using congrArg (fun f : LaurentPolynomial R => f.coeff 0) h) p

/-- Each O square has Laurent weight `T 1`, and every other square has weight one. -/
noncomputable def oSquareWeight (G : GridDiagram n) (p : Fin n × Fin n) :
    LaurentPolynomial R := if p ∈ G.OSet then LaurentPolynomial.T 1 else 1

theorem oSquareWeight_column (G : GridDiagram n) (c : Fin n) :
    ∏ r : Fin n, oSquareWeight (R := R) G (c, r) = LaurentPolynomial.T 1 := by
  classical
  simp [oSquareWeight, GridDiagram.mem_OSet]

theorem oSquareWeight_row (G : GridDiagram n) (r : Fin n) :
    ∏ c : Fin n, oSquareWeight (R := R) G (c, r) = LaurentPolynomial.T 1 := by
  classical
  have heq (c : Fin n) : G.O c = r ↔ c = G.O.toPerm.symm r :=
    G.O.toPerm.eq_symm_apply.symm
  simp only [oSquareWeight, GridDiagram.mem_OSet]
  simp_rw [heq]
  simp

theorem squareWeight_oSquareWeight (G : GridDiagram n) (r : GridRectangle n) :
    squareWeight (oSquareWeight (R := R) G) r =
      laurentSpecialization R (G.OMonomial R r) := by
  classical
  rw [G.OMonomial_eq_prod_coveredSquares, map_prod]
  simp only [squareWeight, oSquareWeight, apply_ite, laurentSpecialization_X, map_one]

theorem squareWeightedCoefficient_oSquareWeight (G : GridDiagram n) (x y : GridState n) :
    squareWeightedCoefficient (oSquareWeight (R := R) G) x y = laurentCoefficient G R x y := by
  simp only [squareWeightedCoefficient, laurentCoefficient, coefficient,
    squareWeight_oSquareWeight, map_sum]

theorem squareWeightedDifferential_oSquareWeight (G : GridDiagram n) :
    squareWeightedDifferential (oSquareWeight (R := R) G) = laurentDifferential G R := by
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  ext y
  simp [squareWeightedCoefficient_oSquareWeight]

/-- The same multiplier at two distinct columns of a fixed row. -/
noncomputable def twoSquareMultiplier {S : Type*} [CommSemiring S]
    (a b s : Fin n) (q : S) (p : Fin n × Fin n) : S :=
  if p = (a, s) ∨ p = (b, s) then q else 1

theorem twoSquareMultiplier_column {S : Type*} [CommSemiring S]
    (a b s c : Fin n) (q : S) :
    ∏ r : Fin n, twoSquareMultiplier a b s q (c, r) = if c = a ∨ c = b then q else 1 := by
  classical
  by_cases hc : c = a ∨ c = b
  · have heq (r : Fin n) : twoSquareMultiplier a b s q (c, r) = if r = s then q else 1 := by
      by_cases hr : r = s <;> simp [twoSquareMultiplier, Prod.mk.injEq, hc, hr]
    simp_rw [heq]
    simp [hc]
  · have heq (r : Fin n) : twoSquareMultiplier a b s q (c, r) = 1 := by
      simp [twoSquareMultiplier, Prod.mk.injEq, not_or.mp hc]
    simp_rw [heq]
    simp [hc]

theorem twoSquareMultiplier_row {S : Type*} [CommSemiring S]
    (a b s r : Fin n) (hab : a ≠ b) (q : S) :
    ∏ c : Fin n, twoSquareMultiplier a b s q (c, r) = if r = s then q ^ 2 else 1 := by
  classical
  by_cases hr : r = s
  · subst r
    have heq (c : Fin n) : twoSquareMultiplier a b s q (c, s) =
        (if c = a then q else 1) * (if c = b then q else 1) := by
      by_cases hca : c = a <;> by_cases hcb : c = b <;>
        simp_all [twoSquareMultiplier, Prod.mk.injEq]
    simp_rw [heq]
    rw [Finset.prod_mul_distrib]
    simp [pow_two]
  · have heq (c : Fin n) : twoSquareMultiplier a b s q (c, r) = 1 := by
      simp [twoSquareMultiplier, Prod.mk.injEq, hr]
    simp_rw [heq]
    simp [hr]

/-- The O weights deformed at the two squares meeting the selected turn. -/
noncomputable def adjacentSquareDeformationWeight (G : GridDiagram n) (R : Type*)
    [CommSemiring R] (a s : Fin n) (p : Fin n × Fin n) : Polynomial (LaurentPolynomial R) :=
  C (oSquareWeight G p) * twoSquareMultiplier a (finRotate n a) s (1 + X) p

theorem adjacentSquareDeformation_column (G : GridDiagram n) (a s c : Fin n) :
    ∏ r : Fin n, adjacentSquareDeformationWeight G R a s (c, r) =
      C (LaurentPolynomial.T 1) * (if c = a ∨ c = finRotate n a then 1 + X else 1) := by
  simp only [adjacentSquareDeformationWeight, Finset.prod_mul_distrib,
    ← map_prod, oSquareWeight_column, twoSquareMultiplier_column]

theorem adjacentSquareDeformation_row (G : GridDiagram n) (hn : 1 < n) (a s r : Fin n) :
    ∏ c : Fin n, adjacentSquareDeformationWeight G R a s (c, r) =
      C (LaurentPolynomial.T 1) * (if r = s then (1 + X) ^ 2 else 1) := by
  simp only [adjacentSquareDeformationWeight, Finset.prod_mul_distrib,
    ← map_prod, oSquareWeight_row,
    twoSquareMultiplier_row a (finRotate n a) s r (Grid.finRotate_ne_self hn a).symm]

/-- The two-square deformation has exactly one quadratic curvature term. -/
theorem adjacentSquareDeformation_curvature [CharP R 2]
    (G : GridDiagram n) (hn : 1 < n) (a s : Fin n) :
    squareWeightCurvature (adjacentSquareDeformationWeight G R a s) =
      C (LaurentPolynomial.T 1) * X ^ 2 := by
  classical
  let U : Polynomial (LaurentPolynomial R) := C (LaurentPolynomial.T 1)
  have hab : a ≠ finRotate n a := (Grid.finRotate_ne_self hn a).symm
  have hc (c : Fin n) :
      U * (if c = a ∨ c = finRotate n a then 1 + X else 1) =
        U + (if c = a then U * X else 0) +
          (if c = finRotate n a then U * X else 0) := by
    by_cases hca : c = a <;> by_cases hcb : c = finRotate n a <;>
      simp_all [mul_add]
  have hr (r : Fin n) : U * (if r = s then (1 + X) ^ 2 else 1) =
      U + (if r = s then U * X ^ 2 else 0) := by
    by_cases hrs : r = s <;> simp [hrs, CharTwo.add_sq, mul_add]
  simp only [squareWeightCurvature, adjacentSquareDeformation_column,
    adjacentSquareDeformation_row G hn]
  change (∑ c : Fin n, U * _) + (∑ r : Fin n, U * _) = U * X ^ 2
  simp_rw [hc, hr, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [add_assoc (∑ _ : Fin n, U), CharTwo.add_self_eq_zero, add_zero,
    ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- The coefficient operator of the two-square polynomial deformation. -/
noncomputable def adjacentSquareOperator (G : GridDiagram n) (R : Type*)
    [CommSemiring R] (a s : Fin n) (k : ℕ) :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
  polynomialCoefficientOperator (adjacentSquareDeformationWeight G R a s) k

/-- The constant coefficient is the actual full Laurent differential. -/
theorem adjacentSquareOperator_zero (G : GridDiagram n) (a s : Fin n) :
    adjacentSquareOperator G R a s 0 = laurentDifferential G R := by
  rw [adjacentSquareOperator, polynomialCoefficientOperator_zero]
  have hw : (fun p => (adjacentSquareDeformationWeight G R a s p).coeff 0) =
      oSquareWeight (R := R) G := by
    funext p
    simp only [adjacentSquareDeformationWeight, twoSquareMultiplier]
    split_ifs <;> simp
  rw [hw, squareWeightedDifferential_oSquareWeight]

/-- The linear coefficient is a chain map of the full Laurent differential. -/
theorem adjacentSquareOperator_one_chain [CharP R 2]
    (G : GridDiagram n) (hn : 1 < n) (a s : Fin n) :
    laurentDifferential G R ∘ₗ adjacentSquareOperator G R a s 1 +
      adjacentSquareOperator G R a s 1 ∘ₗ laurentDifferential G R = 0 := by
  have h := polynomialCoefficientOperator_one_identity (adjacentSquareDeformationWeight G R a s)
  change adjacentSquareOperator G R a s 0 ∘ₗ adjacentSquareOperator G R a s 1 +
    adjacentSquareOperator G R a s 1 ∘ₗ adjacentSquareOperator G R a s 0 = _ at h
  simpa only [adjacentSquareOperator_zero, adjacentSquareDeformation_curvature G hn,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by decide : ¬1 = 2),
    mul_zero, zero_smul] using h

/-- The quadratic coefficient gives the explicit homotopy between the
square of the linear coefficient and multiplication by the Laurent variable. -/
theorem adjacentSquareOperator_two_homotopy [CharP R 2]
    (G : GridDiagram n) (hn : 1 < n) (a s : Fin n) :
    adjacentSquareOperator G R a s 1 ∘ₗ adjacentSquareOperator G R a s 1 +
      laurentDifferential G R ∘ₗ adjacentSquareOperator G R a s 2 +
      adjacentSquareOperator G R a s 2 ∘ₗ laurentDifferential G R =
      (LaurentPolynomial.T 1 : LaurentPolynomial R) •
        (LinearMap.id : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n) := by
  have h := polynomialCoefficientOperator_two_identity (adjacentSquareDeformationWeight G R a s)
  change adjacentSquareOperator G R a s 1 ∘ₗ adjacentSquareOperator G R a s 1 +
    adjacentSquareOperator G R a s 0 ∘ₗ adjacentSquareOperator G R a s 2 +
    adjacentSquareOperator G R a s 2 ∘ₗ adjacentSquareOperator G R a s 0 = _ at h
  simpa only [adjacentSquareOperator_zero, adjacentSquareDeformation_curvature G hn,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, if_true, mul_one] using h

end OnLeConjecture.KnotFloer.GridFull
