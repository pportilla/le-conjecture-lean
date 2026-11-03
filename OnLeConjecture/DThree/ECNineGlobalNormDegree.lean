/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ECNineUnitChartDegree
public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.Algebra.Polynomial.Reverse

/-!
# The homogeneous C9 norm form

The determinant norm on the chart `x = 1` has degree at most `9N`.
Homogenizing it to degree `9N` records the part of the norm divisor in the
complementary chart. The resulting binary form is homogeneous of degree
`9N`. For a hard section it is nonzero, so its total degree is exactly
`9N` even when the affine norm has smaller degree.

The complementary chart polynomial is the reflection of the affine norm
at degree `9N`. Its order at the chart origin is exactly the difference
between `9N` and the affine norm degree.
-/

public section

noncomputable section

namespace OnLeConjecture.DThree

open _root_.Polynomial

/-- Homogenization of the unit chart determinant norm to its global degree. -/
@[expose]
def eCNineGlobalDifferenceNormForm (R : Form ℂ) (N : ℕ) : Form ℂ :=
  (eCNineUnitDifferenceNorm R).homogenize (9 * N)

/-- The determinant norm written in the complementary chart `X = 1`. -/
@[expose]
def eCNineCapitalXChartDifferenceNorm (R : Form ℂ) (N : ℕ) : ℂ[X] :=
  (eCNineUnitDifferenceNorm R).reflect (9 * N)

namespace ECNineGlobalNorm

/-- Dehomogenizing a polynomial homogenized to degree `D` in the second
chart gives its reflection at degree `D`. -/
theorem aeval_one_X_homogenize_eq_reflect
    (p : ℂ[X]) (D : ℕ) (hp : p.natDegree ≤ D) :
    MvPolynomial.aeval ![(1 : ℂ[X]), X] (p.homogenize D) =
      p.reflect D := by
  apply Polynomial.induction_with_natDegree_le
    (fun q ↦ MvPolynomial.aeval ![(1 : ℂ[X]), X]
        (q.homogenize D) = q.reflect D) (N := D)
  · simp
  · intro n r hr hn
    rw [Polynomial.homogenize_C_mul,
      Polynomial.homogenize_X_pow hn,
      Polynomial.reflect_C_mul_X_pow,
      Polynomial.revAt_le hn]
    simp
  · intro f g _hdegree _hg hf hg
    rw [Polynomial.homogenize_add, map_add, hf, hg,
      Polynomial.reflect_add]
  · exact hp

/-- For a nonzero polynomial of degree at most `D`, the reflected polynomial
vanishes at the complementary chart origin to order `D - natDegree p`. -/
theorem natTrailingDegree_reflect_of_natDegree_le
    {p : ℂ[X]} {D : ℕ} (hp : p ≠ 0) (hpD : p.natDegree ≤ D) :
    (p.reflect D).natTrailingDegree = D - p.natDegree := by
  apply le_antisymm
  · apply Polynomial.natTrailingDegree_le_of_ne_zero
    rw [Polynomial.coeff_reflect, Polynomial.revAt_le (Nat.sub_le D p.natDegree),
      Nat.sub_sub_self hpD, ← Polynomial.leadingCoeff]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  · apply Polynomial.le_natTrailingDegree
    · exact (Polynomial.reflect_eq_zero_iff.not).mpr hp
    · intro i hi
      rw [Polynomial.coeff_reflect,
        Polynomial.revAt_le (hi.le.trans (Nat.sub_le D p.natDegree))]
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      omega

end ECNineGlobalNorm

/-- The global determinant norm form is homogeneous of degree `9N`. -/
theorem eCNineGlobalDifferenceNormForm_isHomogeneous
    (R : Form ℂ) (N : ℕ) :
    (eCNineGlobalDifferenceNormForm R N).IsHomogeneous (9 * N) := by
  exact Polynomial.isHomogeneous_homogenize _

/-- On `x = 1`, the global norm form is the unit chart determinant norm. -/
theorem eCNineGlobalDifferenceNormForm_dehomogenize
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N) :
    MvPolynomial.aeval ![X, (1 : ℂ[X])]
        (eCNineGlobalDifferenceNormForm R N) =
      eCNineUnitDifferenceNorm R := by
  apply Polynomial.aeval_homogenize_X_one
  exact eCNineUnitDifferenceNorm_natDegree_le hR

/-- On `X = 1`, the global norm form is the reflected affine norm. -/
theorem eCNineGlobalDifferenceNormForm_complementary_dehomogenize
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N) :
    MvPolynomial.aeval ![(1 : ℂ[X]), X]
        (eCNineGlobalDifferenceNormForm R N) =
      eCNineCapitalXChartDifferenceNorm R N := by
  exact ECNineGlobalNorm.aeval_one_X_homogenize_eq_reflect _ _
    (eCNineUnitDifferenceNorm_natDegree_le hR)

/-- The complementary chart origin has order equal to the affine degree
deficit from `9N`. -/
theorem eCNineCapitalXChartDifferenceNorm_natTrailingDegree
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    (hnorm : eCNineUnitDifferenceNorm R ≠ 0) :
    (eCNineCapitalXChartDifferenceNorm R N).natTrailingDegree =
      9 * N - (eCNineUnitDifferenceNorm R).natDegree := by
  exact ECNineGlobalNorm.natTrailingDegree_reflect_of_natDegree_le
    hnorm (eCNineUnitDifferenceNorm_natDegree_le hR)

/-- The unit chart degree and the order at the complementary chart origin
add to `9N`. -/
theorem eCNineNorm_chart_degree_identity
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    (hnorm : eCNineUnitDifferenceNorm R ≠ 0) :
    (eCNineCapitalXChartDifferenceNorm R N).natTrailingDegree +
        (eCNineUnitDifferenceNorm R).natDegree = 9 * N := by
  rw [eCNineCapitalXChartDifferenceNorm_natTrailingDegree hR hnorm]
  exact Nat.sub_add_cancel (eCNineUnitDifferenceNorm_natDegree_le hR)

/-- Finite roots of the unit chart norm, counted with multiplicity, together
with the root at the complementary chart origin have total multiplicity
`9N`. -/
theorem eCNineNorm_projective_root_count
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    (hnorm : eCNineUnitDifferenceNorm R ≠ 0) :
    (eCNineUnitDifferenceNorm R).roots.card +
        (eCNineCapitalXChartDifferenceNorm R N).rootMultiplicity 0 =
      9 * N := by
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree']
  have hsplits : (eCNineUnitDifferenceNorm R).Splits :=
    IsAlgClosed.splits _
  have hroots := hsplits.natDegree_eq_card_roots
  rw [← hroots]
  rw [Nat.add_comm]
  exact eCNineNorm_chart_degree_identity hR hnorm

/-- The global norm has no zero at the complementary chart origin exactly
when the unit chart norm already has degree `9N`. -/
theorem eCNineCapitalXChartDifferenceNorm_natTrailingDegree_eq_zero_iff
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    (hnorm : eCNineUnitDifferenceNorm R ≠ 0) :
    (eCNineCapitalXChartDifferenceNorm R N).natTrailingDegree = 0 ↔
      (eCNineUnitDifferenceNorm R).natDegree = 9 * N := by
  rw [eCNineCapitalXChartDifferenceNorm_natTrailingDegree hR hnorm,
    Nat.sub_eq_zero_iff_le]
  exact (eCNineUnitDifferenceNorm_natDegree_le hR).ge_iff_eq

/-- Reflection preserves nonvanishing of the unit chart norm. -/
theorem eCNineCapitalXChartDifferenceNorm_ne_zero_iff
    (R : Form ℂ) (N : ℕ) :
    eCNineCapitalXChartDifferenceNorm R N ≠ 0 ↔
      eCNineUnitDifferenceNorm R ≠ 0 := by
  exact not_congr Polynomial.reflect_eq_zero_iff

/-- A nonzero unit chart norm gives a nonzero global norm form. -/
theorem eCNineGlobalDifferenceNormForm_ne_zero
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    (hnorm : eCNineUnitDifferenceNorm R ≠ 0) :
    eCNineGlobalDifferenceNormForm R N ≠ 0 := by
  intro hzero
  apply hnorm
  apply Polynomial.eq_zero_of_homogenize_eq_zero
    (eCNineUnitDifferenceNorm_natDegree_le hR)
  exact hzero

/-- The nonzero global norm form has exact total degree `9N`. -/
theorem eCNineGlobalDifferenceNormForm_totalDegree
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    (hnorm : eCNineUnitDifferenceNorm R ≠ 0) :
    (eCNineGlobalDifferenceNormForm R N).totalDegree = 9 * N := by
  exact (eCNineGlobalDifferenceNormForm_isHomogeneous R N).totalDegree
    (eCNineGlobalDifferenceNormForm_ne_zero hR hnorm)

/-- For a hard section, the global determinant norm form has exact total
degree `9N`. -/
theorem eCNineHardGlobalDifferenceNormForm_totalDegree
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (R : Form ℂ) (Rzero : ESourceRing ℂ)
    (coefficient : ℂ) (N : ℕ)
    (hhomogeneous : R.IsHomogeneous N)
    (hR : R = eSourceCubeSubstitutionForm Rzero +
      MvPolynomial.C coefficient * formT ^ N)
    (hcoefficient : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) :
    (eCNineGlobalDifferenceNormForm R N).totalDegree = 9 * N := by
  apply eCNineGlobalDifferenceNormForm_totalDegree hhomogeneous
  exact eCNineUnitDifferenceNorm_ne_zero homega R Rzero coefficient N
    hR hcoefficient hnotdiv

/-- For a hard section, the affine norm degree and the complementary origin
order account for all `9N` zeros of the homogeneous norm form. -/
theorem eCNineHardNorm_chart_degree_identity
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (R : Form ℂ) (Rzero : ESourceRing ℂ)
    (coefficient : ℂ) (N : ℕ)
    (hhomogeneous : R.IsHomogeneous N)
    (hR : R = eSourceCubeSubstitutionForm Rzero +
      MvPolynomial.C coefficient * formT ^ N)
    (hcoefficient : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) :
    (eCNineCapitalXChartDifferenceNorm R N).natTrailingDegree +
        (eCNineUnitDifferenceNorm R).natDegree = 9 * N := by
  apply eCNineNorm_chart_degree_identity hhomogeneous
  exact eCNineUnitDifferenceNorm_ne_zero homega R Rzero coefficient N
    hR hcoefficient hnotdiv

/-- For a hard section, all finite norm roots and the complementary chart
root have total multiplicity `9N`. -/
theorem eCNineHardNorm_projective_root_count
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (R : Form ℂ) (Rzero : ESourceRing ℂ)
    (coefficient : ℂ) (N : ℕ)
    (hhomogeneous : R.IsHomogeneous N)
    (hR : R = eSourceCubeSubstitutionForm Rzero +
      MvPolynomial.C coefficient * formT ^ N)
    (hcoefficient : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) :
    (eCNineUnitDifferenceNorm R).roots.card +
        (eCNineCapitalXChartDifferenceNorm R N).rootMultiplicity 0 =
      9 * N := by
  apply eCNineNorm_projective_root_count hhomogeneous
  exact eCNineUnitDifferenceNorm_ne_zero homega R Rzero coefficient N
    hR hcoefficient hnotdiv

end OnLeConjecture.DThree
