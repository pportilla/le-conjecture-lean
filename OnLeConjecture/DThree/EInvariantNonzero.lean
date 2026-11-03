/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EThetaHomogeneous
public import OnLeConjecture.DThree.EThetaZeroDescent

/-!
# Nonvanishing of the invariant E residual factor

If a descended third coordinate does not belong to the base coordinate ring,
then its residual difference factor is nonzero. This removes the component
case from the projective zero supplied by the cocycle argument.
-/

public section

namespace OnLeConjecture.DThree

/-- A canonical source decomposition outside the base coordinate ring has a
nonzero residual difference factor. -/
theorem eThetaPolynomial_ne_zero_of_source_not_mem_range
    {K : Type*} [Field K] [CharZero K]
    (Rzero : ESourceRing K) (c : Fin 4 → EBaseRing K)
    (hdecomposition :
      Rzero = ∑ i : Fin 4,
        eBaseToSource K (c i) * eSourceX K ^ (i : ℕ))
    (hnotbase : Rzero ∉ Set.range (eBaseToSource K)) :
    eThetaPolynomial K c ≠ 0 := by
  intro htheta
  exact hnotbase
    (eSource_mem_range_baseToSource_of_theta_eq_zero
      K Rzero c hdecomposition htheta)

/-- The invariant `E` branch outside the base coordinate ring has a nonzero
homogeneous residual factor and a projective zero away from the diagonal. -/
theorem exists_e_invariant_nonzero_residual_off_diagonal_projective_zero
    {omega : ℂ} (R : Form ℂ) (N : ℕ)
    (homega : IsPrimitiveRoot omega 3)
    (hhomogeneous : R.IsHomogeneous N)
    (hinvariant : R = eRotateForm omega R)
    (hdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian (cubicForm 0 3) R)
    (hnotbase : ∀ Rzero : ESourceRing ℂ,
      eSourceCubeSubstitutionForm Rzero = R →
        Rzero ∉ Set.range (eBaseToSource ℂ)) :
    ∃ Rzero : ESourceRing ℂ, ∃ c : Fin 4 → EBaseRing ℂ,
      eSourceCubeSubstitutionForm Rzero = R ∧
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ) ∧
      EPairIsHomogeneous (eThetaPolynomial ℂ c) (N - 1) ∧
      ePairDiagonal ℂ ^ 2 ∣ eThetaPolynomial ℂ c ∧
      eThetaPolynomial ℂ c ≠ 0 ∧
      ∃ x X : ℂ, (x ≠ 0 ∨ X ≠ 0) ∧
        ePairPointEval ℂ x X (eThetaPolynomial ℂ c) = 0 ∧
        x ≠ X := by
  obtain ⟨Rzero, c, hdescent, hdecomposition, hhomogeneousTheta,
      hdiagonal, x, X, hnonzero, htheta, hne⟩ :=
    exists_e_invariant_residual_off_diagonal_projective_zero
      R N homega hhomogeneous hinvariant hdiv
  have hthetaNe : eThetaPolynomial ℂ c ≠ 0 :=
    eThetaPolynomial_ne_zero_of_source_not_mem_range
      Rzero c hdecomposition (hnotbase Rzero hdescent)
  exact ⟨Rzero, c, hdescent, hdecomposition, hhomogeneousTheta,
    hdiagonal, hthetaNe, x, X, hnonzero, htheta, hne⟩

end OnLeConjecture.DThree
