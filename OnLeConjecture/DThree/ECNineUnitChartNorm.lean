/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ECNineUnitChartSection
public import Mathlib.LinearAlgebra.FreeModule.Norm

/-!
# The determinant norm of the C9 section

Multiplication by the difference section is an endomorphism of the rank nine
unit chart algebra over `ℂ[X]`. Its determinant is the algebra norm of the
section. For a hard form, both the section and its norm are nonzero.

The degree of this norm equals the complex dimension of the quotient of the
unit chart algebra by the section. Proving that the corresponding global
homogeneous norm has degree `9N` requires a separate grading argument.
-/

public section

noncomputable section

namespace OnLeConjecture.DThree

/-- Multiplication by the difference section on the unit chart algebra. -/
@[expose]
def eCNineUnitDifferenceMultiplication (R : Form ℂ) :
    ECNineUnitAlgebra →ₗ[ECNineUnitBase] ECNineUnitAlgebra :=
  (Algebra.lmul ECNineUnitBase ECNineUnitAlgebra)
    (eCNineUnitDifferenceElement R)

theorem eCNineUnitDifferenceMultiplication_apply
    (R : Form ℂ) (z : ECNineUnitAlgebra) :
    eCNineUnitDifferenceMultiplication R z =
      eCNineUnitDifferenceElement R * z := by
  rfl

/-- The determinant norm of the difference section. -/
@[expose]
def eCNineUnitDifferenceNorm (R : Form ℂ) : ECNineUnitBase :=
  Algebra.norm ECNineUnitBase (eCNineUnitDifferenceElement R)

theorem eCNineUnitDifferenceNorm_eq_det (R : Form ℂ) :
    eCNineUnitDifferenceNorm R =
      LinearMap.det (eCNineUnitDifferenceMultiplication R) := by
  rfl

theorem eCNineUnitDifferenceNorm_eq_matrix_det (R : Form ℂ) :
    eCNineUnitDifferenceNorm R =
      (Algebra.leftMulMatrix eCNineUnitBasis
        (eCNineUnitDifferenceElement R)).det := by
  exact Algebra.norm_eq_matrix_det eCNineUnitBasis _

/-- A scalar from the parameter ring has norm equal to its ninth power. -/
theorem eCNineUnit_norm_algebraMap (q : ECNineUnitBase) :
    Algebra.norm ECNineUnitBase
        (algebraMap ECNineUnitBase ECNineUnitAlgebra q) = q ^ 9 := by
  rw [Algebra.norm_algebraMap, eCNineUnitAlgebra_finrank]

/-- Multiplication by a hard difference section is injective. -/
theorem eCNineUnitDifferenceMultiplication_injective
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (R : Form ℂ) (Rzero : ESourceRing ℂ)
    (coefficient : ℂ) (N : ℕ)
    (hR : R = eSourceCubeSubstitutionForm Rzero +
      MvPolynomial.C coefficient * formT ^ N)
    (hcoefficient : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) :
    Function.Injective (eCNineUnitDifferenceMultiplication R) := by
  intro x y hxy
  rw [eCNineUnitDifferenceMultiplication_apply,
    eCNineUnitDifferenceMultiplication_apply] at hxy
  exact mul_left_cancel₀
    (eCNineUnitDifferenceElement_ne_zero homega R Rzero
      coefficient N hR hcoefficient hnotdiv) hxy

/-- The determinant norm of a hard difference section is nonzero. -/
theorem eCNineUnitDifferenceNorm_ne_zero
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (R : Form ℂ) (Rzero : ESourceRing ℂ)
    (coefficient : ℂ) (N : ℕ)
    (hR : R = eSourceCubeSubstitutionForm Rzero +
      MvPolynomial.C coefficient * formT ^ N)
    (hcoefficient : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) :
    eCNineUnitDifferenceNorm R ≠ 0 := by
  exact Algebra.norm_ne_zero_iff.mpr
    (eCNineUnitDifferenceElement_ne_zero homega R Rzero
      coefficient N hR hcoefficient hnotdiv)

/-- The degree of the determinant norm is the complex dimension of the
section quotient on the unit chart. -/
theorem eCNineUnitSectionQuotient_finrank_eq_norm_natDegree
    {R : Form ℂ} (hR : eCNineUnitDifferenceElement R ≠ 0) :
    Module.finrank ℂ
        (ECNineUnitAlgebra ⧸
          Ideal.span ({eCNineUnitDifferenceElement R} :
            Set ECNineUnitAlgebra)) =
      (eCNineUnitDifferenceNorm R).natDegree := by
  exact finrank_quotient_span_eq_natDegree_norm
    eCNineUnitBasis hR

/-- For a hard form, the chart quotient dimension equals the degree of its
nonzero determinant norm. -/
theorem eCNineUnitHardSectionQuotient_finrank_eq_norm_natDegree
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (R : Form ℂ) (Rzero : ESourceRing ℂ)
    (coefficient : ℂ) (N : ℕ)
    (hR : R = eSourceCubeSubstitutionForm Rzero +
      MvPolynomial.C coefficient * formT ^ N)
    (hcoefficient : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) :
    Module.finrank ℂ
        (ECNineUnitAlgebra ⧸
          Ideal.span ({eCNineUnitDifferenceElement R} :
            Set ECNineUnitAlgebra)) =
      (eCNineUnitDifferenceNorm R).natDegree := by
  apply eCNineUnitSectionQuotient_finrank_eq_norm_natDegree
  exact eCNineUnitDifferenceElement_ne_zero homega R Rzero
    coefficient N hR hcoefficient hnotdiv

end OnLeConjecture.DThree
