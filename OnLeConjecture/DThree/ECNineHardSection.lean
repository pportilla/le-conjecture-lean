/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ECNineLocalOrder

/-!
# The hard section does not contain C9

For a form of the shape `R₀(x,t³) + c tᴺ`, this file constructs two
points of C9 that differ by a cubic rotation in the first source point.  The
same second source point occurs in both pairs.  If the difference section
vanished at both points, then the pure power term would be invariant under
that rotation.  This contradicts `3 ∤ N`.
-/

public section

namespace OnLeConjecture.DThree

open scoped LinearAlgebra.Projectivization

/-- Evaluation of a descended form is unchanged by a cubic rotation of the
second coordinate. -/
theorem eSourceCubeSubstitutionForm_eval_rotate
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (Rzero : ESourceRing ℂ) (x t : ℂ) :
    MvPolynomial.eval ![x, omega * t]
        (eSourceCubeSubstitutionForm Rzero) =
      MvPolynomial.eval ![x, t] (eSourceCubeSubstitutionForm Rzero) := by
  rw [eSourceCubeSubstitutionForm_pointEval,
    eSourceCubeSubstitutionForm_pointEval]
  congr 1
  rw [mul_pow, homega.pow_eq_one, one_mul]

/-- The difference between a hard form and its cubic rotation is contributed
by its pure power term. -/
theorem e_hard_form_eval_sub_rotate
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (R : Form ℂ) (Rzero : ESourceRing ℂ)
    (coefficient x t : ℂ) (N : ℕ)
    (hR : R = eSourceCubeSubstitutionForm Rzero +
      MvPolynomial.C coefficient * formT ^ N) :
    MvPolynomial.eval ![x, t] R -
        MvPolynomial.eval ![x, omega * t] R =
      coefficient * t ^ N * (1 - omega ^ N) := by
  rw [hR]
  simp only [map_add, map_mul, map_pow, MvPolynomial.eval_C]
  rw [eSourceCubeSubstitutionForm_eval_rotate homega]
  simp [formT, mul_pow]
  ring

/-- A hard form changes under a cubic rotation at every point with nonzero
second coordinate. -/
theorem e_hard_form_eval_ne_rotate
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (R : Form ℂ) (Rzero : ESourceRing ℂ)
    (coefficient x t : ℂ) (N : ℕ)
    (hR : R = eSourceCubeSubstitutionForm Rzero +
      MvPolynomial.C coefficient * formT ^ N)
    (hcoefficient : coefficient ≠ 0) (ht : t ≠ 0)
    (hnotdiv : ¬ 3 ∣ N) :
    MvPolynomial.eval ![x, t] R ≠
      MvPolynomial.eval ![x, omega * t] R := by
  have homegaN : omega ^ N ≠ 1 := by
    intro hpower
    exact hnotdiv (homega.dvd_of_pow_eq_one N hpower)
  intro heq
  have hzero : coefficient * t ^ N * (1 - omega ^ N) = 0 := by
    rw [← e_hard_form_eval_sub_rotate homega R Rzero coefficient x t N hR,
      heq, sub_self]
  exact (mul_ne_zero (mul_ne_zero hcoefficient (pow_ne_zero N ht))
    (sub_ne_zero.mpr homegaN.symm)) hzero

/-- There are two affine representatives on C9 whose first source points
differ by a cubic rotation and whose second source point is the same. -/
theorem eCNine_exists_rotation_comparison_points
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3) :
    ∃ t T : ℂ,
      t ≠ 0 ∧
      T ≠ 0 ∧
      ECNineEquations 0 t 1 T ∧
      ECNineEquations 0 (omega * t) 1 T := by
  obtain ⟨t, htCube⟩ := IsAlgClosed.exists_pow_nat_eq
    ((12 : ℂ)⁻¹) (by norm_num : 0 < 3)
  obtain ⟨T, hTCube⟩ := IsAlgClosed.exists_pow_nat_eq
    ((-4 : ℂ)⁻¹) (by norm_num : 0 < 3)
  have ht : t ≠ 0 := by
    intro htZero
    rw [htZero, zero_pow (by norm_num : 3 ≠ 0)] at htCube
    norm_num at htCube
  have hT : T ≠ 0 := by
    intro hTZero
    rw [hTZero, zero_pow (by norm_num : 3 ≠ 0)] at hTCube
    norm_num at hTCube
  refine ⟨t, T, ht, hT, ?_, ?_⟩
  · rw [ECNineEquations]
    constructor
    · simp only [eCNineFirstValue]
      rw [htCube]
      norm_num
    · simp only [eCNineSecondValue]
      rw [hTCube]
      norm_num
  · have homegaCube : omega ^ 3 = 1 := homega.pow_eq_one
    rw [ECNineEquations]
    constructor
    · simp only [eCNineFirstValue, mul_pow, homegaCube, one_mul]
      rw [htCube]
      norm_num
    · simp only [eCNineSecondValue]
      rw [hTCube]
      norm_num

/-- The difference section of a hard form is nonzero at one of two explicit
affine representatives of C9. -/
theorem eCNine_exists_hard_difference_nonzero
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (R : Form ℂ) (Rzero : ESourceRing ℂ)
    (coefficient : ℂ) (N : ℕ)
    (hR : R = eSourceCubeSubstitutionForm Rzero +
      MvPolynomial.C coefficient * formT ^ N)
    (hcoefficient : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) :
    ∃ x t X T : ℂ,
      ![x, t, X, T] ≠ (0 : ECNineAmbient) ∧
      ECNineEquations x t X T ∧
      eCNineDifferenceValue R x t X T ≠ 0 := by
  obtain ⟨t, T, ht, _hT, hfirst, hsecond⟩ :=
    eCNine_exists_rotation_comparison_points homega
  by_cases hvalue : eCNineDifferenceValue R 0 t 1 T = 0
  · refine ⟨0, omega * t, 1, T, ?_, hsecond, ?_⟩
    · intro hzero
      have hcoordinate := congrFun hzero (2 : Fin 4)
      change (1 : ℂ) = 0 at hcoordinate
      exact one_ne_zero hcoordinate
    intro hrotated
    have hleft : MvPolynomial.eval ![(0 : ℂ), t] R =
        MvPolynomial.eval ![(1 : ℂ), T] R := by
      apply sub_eq_zero.mp
      change MvPolynomial.eval ![(0 : ℂ), t] R -
        MvPolynomial.eval ![(1 : ℂ), T] R = 0 at hvalue
      exact hvalue
    have hright : MvPolynomial.eval ![(0 : ℂ), omega * t] R =
        MvPolynomial.eval ![(1 : ℂ), T] R := by
      apply sub_eq_zero.mp
      change MvPolynomial.eval ![(0 : ℂ), omega * t] R -
        MvPolynomial.eval ![(1 : ℂ), T] R = 0 at hrotated
      exact hrotated
    exact e_hard_form_eval_ne_rotate homega R Rzero coefficient 0 t N
      hR hcoefficient ht hnotdiv (hleft.trans hright.symm)
  · refine ⟨0, t, 1, T, ?_, hfirst, hvalue⟩
    intro hzero
    have hcoordinate := congrFun hzero (2 : Fin 4)
    change (1 : ℂ) = 0 at hcoordinate
    exact one_ne_zero hcoordinate

/-- The projective zero set of a hard difference section does not contain the
projective C9 curve. -/
theorem not_eCNineProjectiveCurve_subset_hard_section
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    {R : Form ℂ} {N : ℕ} (hhomogeneous : R.IsHomogeneous N)
    (Rzero : ESourceRing ℂ) (coefficient : ℂ)
    (hR : R = eSourceCubeSubstitutionForm Rzero +
      MvPolynomial.C coefficient * formT ^ N)
    (hcoefficient : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) :
    ¬ eCNineProjectiveCurve ⊆ eCNineProjectiveSectionZero hhomogeneous := by
  obtain ⟨x, t, X, T, hnonzero, hcurve, hsection⟩ :=
    eCNine_exists_hard_difference_nonzero homega R Rzero coefficient N
      hR hcoefficient hnotdiv
  intro hsubset
  have hprojectiveCurve :
      Projectivization.mk ℂ ![x, t, X, T] hnonzero ∈
        eCNineProjectiveCurve :=
    (eCNineProjectiveCurve_mk_iff x t X T hnonzero).mpr hcurve
  have hprojectiveSection := hsubset hprojectiveCurve
  exact hsection ((eCNineProjectiveSectionZero_mk_iff
    hhomogeneous x t X T hnonzero).mp hprojectiveSection)

end OnLeConjecture.DThree
