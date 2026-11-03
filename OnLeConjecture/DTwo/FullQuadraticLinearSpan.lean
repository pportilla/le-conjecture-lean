/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.QuadraticJetAlgebra
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The linear span of three independent binary quadratics

The coefficient presentation shows that three linearly independent binary
quadratics span all binary quadratics. This provides the target-coordinate
step in the rank-three quadratic-jet exclusion.
-/

public section

namespace OnLeConjecture.DTwo

/-- The three ordinary quadratic monomials, in coefficient order. -/
@[expose] noncomputable def quadraticMonomials : Fin 3 → OrbitSourceForm :=
  ![MvPolynomial.X 0 ^ 2, MvPolynomial.X 0 * MvPolynomial.X 1, MvPolynomial.X 1 ^ 2]

theorem homogeneous_quadratic_mem_monomial_span
    (P : OrbitSourceForm) (hP : P.IsHomogeneous 2) :
    P ∈ Submodule.span ℂ (Set.range quadraticMonomials) := by
  let S := Submodule.span ℂ (Set.range quadraticMonomials)
  have hmon (i : Fin 3) : quadraticMonomials i ∈ S :=
    Submodule.subset_span (Set.mem_range_self i)
  rw [eq_binaryQuadraticForm_of_isHomogeneous hP]
  change binaryQuadraticForm _ _ _ ∈ S
  unfold binaryQuadraticForm
  apply S.add_mem
  · apply S.add_mem
    · simpa [quadraticMonomials, Algebra.smul_def,
        MvPolynomial.algebraMap_eq, orbitPolynomialS] using
        S.smul_mem (binaryQuadraticCoefficients P 0) (hmon 0)
    · simpa [quadraticMonomials, Algebra.smul_def, MvPolynomial.algebraMap_eq,
        orbitPolynomialS, orbitPolynomialLambda, mul_assoc] using
        S.smul_mem (binaryQuadraticCoefficients P 1) (hmon 1)
  · simpa [quadraticMonomials, Algebra.smul_def, MvPolynomial.algebraMap_eq,
      orbitPolynomialLambda] using
      S.smul_mem (binaryQuadraticCoefficients P 2) (hmon 2)

/-- Independence of three binary quadratics gives their entire
three-dimensional homogeneous linear span. -/
theorem span_quadratics_eq_monomial_span_of_linearIndependent
    (P : Fin 3 → OrbitSourceForm) (hP : ∀ i, (P i).IsHomogeneous 2)
    (hind : LinearIndependent ℂ P) :
    Submodule.span ℂ (Set.range P) =
      Submodule.span ℂ (Set.range quadraticMonomials) := by
  classical
  let : FiniteDimensional ℂ (Submodule.span ℂ (Set.range quadraticMonomials)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range quadraticMonomials)
  apply Submodule.eq_of_le_of_finrank_le
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact homogeneous_quadratic_mem_monomial_span (P i) (hP i)
  · rw [finrank_span_eq_card hind]
    exact finrank_range_le_card quadraticMonomials

end OnLeConjecture.DTwo
