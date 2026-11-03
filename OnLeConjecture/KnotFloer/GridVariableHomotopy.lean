/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridPolynomialOperators
public import OnLeConjecture.KnotFloer.GridFullComplex
public import Mathlib.Algebra.Homology.Homotopy
public import OnLeConjecture.KnotFloer.GridFullBifiltration
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Linear

/-!
# Homotopies between O-variable actions on the full grid complex

A polynomial deformation at one square has linear curvature equal to the
sum of the products along its row and column. For the multivariable O
weights these products are the two O variables on that row and column.
The coefficient identity gives their explicit chain homotopy using all
empty rectangles containing the chosen square, including X crossings.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Polynomial

variable {n : ℕ} {S : Type*} [CommSemiring S]

/-- Multiply the chosen square weight by `1 + X`. -/
noncomputable def deformAtSquare (w : Fin n × Fin n → S) (a s : Fin n)
    (p : Fin n × Fin n) : Polynomial S :=
  C (w p) * (if p = (a, s) then 1 + X else 1)

theorem deformAtSquare_column (w : Fin n × Fin n → S) (a s c : Fin n) :
    ∏ r : Fin n, deformAtSquare w a s (c, r) =
      C (∏ r : Fin n, w (c, r)) * (if c = a then 1 + X else 1) := by
  classical
  simp only [deformAtSquare, Finset.prod_mul_distrib, ← map_prod]
  by_cases hc : c = a <;> simp [Prod.mk.injEq, hc]

theorem deformAtSquare_row (w : Fin n × Fin n → S) (a s r : Fin n) :
    ∏ c : Fin n, deformAtSquare w a s (c, r) =
      C (∏ c : Fin n, w (c, r)) * (if r = s then 1 + X else 1) := by
  classical
  simp only [deformAtSquare, Finset.prod_mul_distrib, ← map_prod]
  by_cases hr : r = s <;> simp [Prod.mk.injEq, hr]

/-- The linear curvature is the sum of the chosen row and column products. -/
theorem coeff_one_curvature_deformAtSquare (w : Fin n × Fin n → S) (a s : Fin n) :
    (squareWeightCurvature (deformAtSquare w a s)).coeff 1 =
      (∏ r : Fin n, w (a, r)) + ∏ c : Fin n, w (c, s) := by
  classical
  have heq (v : S) (i j : Fin n) :
      (C v * (if i = j then 1 + X else 1)).coeff 1 = if i = j then v else 0 := by
    by_cases h : i = j <;> simp [h, Polynomial.coeff_one]
  simp only [squareWeightCurvature, deformAtSquare_column, deformAtSquare_row,
    Polynomial.coeff_add, finsetSum_coeff, heq]
  simp

/-- The linear deformation operator, counting rectangles containing one square. -/
noncomputable def squareDerivative (w : Fin n × Fin n → S) (a s : Fin n) :
    (GridState n →₀ S) →ₗ[S] (GridState n →₀ S) :=
  polynomialCoefficientOperator (deformAtSquare w a s) 1

theorem polynomialCoefficientOperator_zero_deformAtSquare
    (w : Fin n × Fin n → S) (a s : Fin n) :
    polynomialCoefficientOperator (deformAtSquare w a s) 0 = squareWeightedDifferential w := by
  rw [polynomialCoefficientOperator_zero]
  congr 1
  funext p
  simp only [deformAtSquare]
  split_ifs <;> simp

/-- The derivative is a homotopy for the sum of the two annulus actions. -/
theorem squareDerivative_homotopy [CharP S 2] (w : Fin n × Fin n → S) (a s : Fin n) :
    squareWeightedDifferential w ∘ₗ squareDerivative w a s +
      squareDerivative w a s ∘ₗ squareWeightedDifferential w =
      ((∏ r : Fin n, w (a, r)) + ∏ c : Fin n, w (c, s)) •
        (LinearMap.id : (GridState n →₀ S) →ₗ[S] (GridState n →₀ S)) := by
  have h := polynomialCoefficientOperator_one_identity (deformAtSquare w a s)
  simpa only [polynomialCoefficientOperator_zero_deformAtSquare, squareDerivative,
    coeff_one_curvature_deformAtSquare] using h

open Classical in
/-- The derivative matrix entry is the sum over rectangles containing the square. -/
theorem coeff_one_squareWeightedCoefficient_deformAtSquare
    (w : Fin n × Fin n → S) (a s : Fin n) (x y : GridState n) :
    (squareWeightedCoefficient (deformAtSquare w a s) x y).coeff 1 =
      ∑ r ∈ (GridRectangleBetween.emptyRectangles x y).filter
        (fun r => (a, s) ∈ r.toGridRectangle.coveredSquares), squareWeight w r.toGridRectangle := by
  have hr (r : GridRectangle n) :
      (squareWeight (deformAtSquare w a s) r).coeff 1 =
        if (a, s) ∈ r.coveredSquares then squareWeight w r else 0 := by
    simp only [squareWeight, deformAtSquare, Finset.prod_mul_distrib, ← map_prod]
    rw [Finset.prod_ite_eq']
    split_ifs <;> rw [Polynomial.coeff_C_mul] <;> simp [Polynomial.coeff_one]
  simp only [squareWeightedCoefficient, finsetSum_coeff, hr, Finset.sum_filter]

section PolynomialWeights

variable (G : GridDiagram n) (R : Type*) [CommSemiring R]

/-- An O marking in column c carries the separate variable V_c. -/
noncomputable def polynomialOSquareWeight (p : Fin n × Fin n) : MvPolynomial (Fin n) R :=
  if p ∈ G.OSet then MvPolynomial.X p.1 else 1

theorem polynomialOSquareWeight_column (c : Fin n) :
    ∏ r : Fin n, polynomialOSquareWeight G R (c, r) = MvPolynomial.X c := by
  classical
  simp [polynomialOSquareWeight, GridDiagram.mem_OSet]

theorem polynomialOSquareWeight_row (r : Fin n) :
    ∏ c : Fin n, polynomialOSquareWeight G R (c, r) =
      MvPolynomial.X (G.O.toPerm.symm r) := by
  classical
  have heq (c : Fin n) : G.O c = r ↔ c = G.O.toPerm.symm r :=
    G.O.toPerm.eq_symm_apply.symm
  simp only [polynomialOSquareWeight, GridDiagram.mem_OSet]
  simp_rw [heq]
  simp

theorem squareWeight_polynomialOSquareWeight (r : GridRectangle n) :
    squareWeight (polynomialOSquareWeight G R) r = G.OMonomial R r := by
  rw [G.OMonomial_eq_prod_coveredSquares]
  rfl

theorem squareWeightedCoefficient_polynomialOSquareWeight (x y : GridState n) :
    squareWeightedCoefficient (polynomialOSquareWeight G R) x y = coefficient G R x y := by
  simp only [squareWeightedCoefficient, coefficient, squareWeight_polynomialOSquareWeight]

theorem squareWeightedDifferential_polynomialOSquareWeight :
    squareWeightedDifferential (polynomialOSquareWeight G R) = differential G R := by
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  ext y
  simp [squareWeightedCoefficient_polynomialOSquareWeight]

/-- Explicit rectangle homotopy between any two O-variable actions. -/
noncomputable def variableActionHomotopy (a b : Fin n) :
    GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n :=
  squareDerivative (polynomialOSquareWeight G R) a (G.O b)

/-- All O variables induce the same action on total homology of the full complex. -/
theorem differential_variableActionHomotopy [CharP R 2] (a b : Fin n) :
    differential G R ∘ₗ variableActionHomotopy G R a b +
      variableActionHomotopy G R a b ∘ₗ differential G R =
      (MvPolynomial.X a + MvPolynomial.X b : MvPolynomial (Fin n) R) •
        (LinearMap.id : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n) := by
  have h := squareDerivative_homotopy (polynomialOSquareWeight G R) a (G.O b)
  have heq : G.O.toPerm.symm (G.O b) = b := G.O.toPerm.symm_apply_apply b
  simpa only [squareWeightedDifferential_polynomialOSquareWeight, variableActionHomotopy,
    polynomialOSquareWeight_column, polynomialOSquareWeight_row,
    heq] using h

end PolynomialWeights

section NativeHomology

open CategoryTheory HomologicalComplex

variable (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

/-- The rectangle homotopy packaged for the native total complex. -/
noncomputable def variableActionNativeHomotopy (a b : Fin n) :
    Homotopy ((MvPolynomial.X a : MvPolynomial (Fin n) R) • 𝟙 (complex G (R := R)))
      ((MvPolynomial.X b : MvPolynomial (Fin n) R) • 𝟙 (complex G (R := R))) where
  hom i j := ModuleCat.ofHom
    ((chainEquiv G R j).symm.toLinearMap.comp
      ((variableActionHomotopy G R a b).comp (chainEquiv G R i).toLinearMap))
  zero i j h := by
    cases i
    cases j
    exact False.elim (h rfl)
  comm i := by
    cases i
    rw [dNext_eq _ (show (ComplexShape.refl Unit).Rel () () from rfl),
      prevD_eq _ (show (ComplexShape.refl Unit).Rel () () from rfl)]
    ext c : 2
    apply (chainEquiv G R ()).injective
    simp only [HomologicalComplex.smul_f_apply, HomologicalComplex.id_f,
      ModuleCat.hom_smul, ModuleCat.hom_id, ModuleCat.hom_add, ModuleCat.hom_comp,
      ModuleCat.hom_ofHom, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.add_apply,
      LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      map_add, map_smul, chainEquiv_d, LinearEquiv.apply_symm_apply]
    apply Finsupp.ext
    intro y
    have h := congrArg
      (fun L : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n =>
        L (chainEquiv G R () c) y)
      (differential_variableActionHomotopy G R a b)
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.id_apply, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h ⊢
    rw [add_comm (variableActionHomotopy G R a b (differential G R (chainEquiv G R () c)) y),
      h, add_mul, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- The two O-variable chain maps induce identical maps on native total homology. -/
theorem homologyMap_variableAction_eq (a b : Fin n) :
    homologyMap ((MvPolynomial.X a : MvPolynomial (Fin n) R) • 𝟙 (complex G (R := R))) () =
      homologyMap ((MvPolynomial.X b : MvPolynomial (Fin n) R) • 𝟙 (complex G (R := R))) () :=
  (variableActionNativeHomotopy G R a b).homologyMap_eq ()

/-- Polynomial multiplication on the native total complex induces polynomial multiplication
on its native homology module. -/
theorem homologyMap_scalar_identity (p : MvPolynomial (Fin n) R) :
    homologyMap (p • 𝟙 (complex G (R := R))) () =
      p • 𝟙 ((complex G (R := R)).homology ()) := by
  change ShortComplex.homologyMap (p • 𝟙 ((complex G (R := R)).sc ())) = _
  rw [ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

/-- Any two O variables act equally on every native total homology class. -/
theorem variable_smul_homology_eq (a b : Fin n) (ξ : (complex G (R := R)).homology ()) :
    (MvPolynomial.X a : MvPolynomial (Fin n) R) • ξ =
      (MvPolynomial.X b : MvPolynomial (Fin n) R) • ξ := by
  have h := congrArg (fun f => f.hom ξ) (homologyMap_variableAction_eq G R a b)
  rw [homologyMap_scalar_identity, homologyMap_scalar_identity] at h
  simpa only [ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply,
    LinearMap.id_apply] using h

end NativeHomology

end OnLeConjecture.KnotFloer.GridFull
