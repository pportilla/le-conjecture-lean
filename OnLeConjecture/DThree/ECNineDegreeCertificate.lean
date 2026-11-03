/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ECNineHardSection
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Degree and Jacobian certificates for C9

The two defining polynomials of C9 have exact total degree three, so their
degree product is nine.  Their Jacobian minor in the `t` and `T` coordinates
equals `1296 t²T²`.  In particular, the explicit comparison points used for
the hard section include a point where this minor is nonzero.

These calculations provide polynomial and local regularity certificates.
They do not by themselves prove that the projective complete intersection is
pure or reduced.
-/

public section

namespace OnLeConjecture.DThree

/-- The first defining cubic is nonzero. -/
theorem eCNineFirstPolynomial_ne_zero :
    eCNineFirstPolynomial ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval ![(0 : ℂ), 1, 0, 0]) hzero
  rw [eCNineFirstPolynomial_eval] at heval
  norm_num [eCNineFirstValue] at heval

/-- The second defining cubic is nonzero. -/
theorem eCNineSecondPolynomial_ne_zero :
    eCNineSecondPolynomial ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval ![(0 : ℂ), 0, 0, 1]) hzero
  rw [eCNineSecondPolynomial_eval] at heval
  norm_num [eCNineSecondValue] at heval

/-- The first defining polynomial has exact total degree three. -/
theorem eCNineFirstPolynomial_totalDegree :
    eCNineFirstPolynomial.totalDegree = 3 :=
  eCNineFirstPolynomial_isHomogeneous.totalDegree
    eCNineFirstPolynomial_ne_zero

/-- The second defining polynomial has exact total degree three. -/
theorem eCNineSecondPolynomial_totalDegree :
    eCNineSecondPolynomial.totalDegree = 3 :=
  eCNineSecondPolynomial_isHomogeneous.totalDegree
    eCNineSecondPolynomial_ne_zero

/-- The product of the two defining polynomial degrees is nine. -/
theorem eCNine_defining_polynomial_degree_product :
    eCNineFirstPolynomial.totalDegree *
      eCNineSecondPolynomial.totalDegree = 9 := by
  rw [eCNineFirstPolynomial_totalDegree,
    eCNineSecondPolynomial_totalDegree]

/-- The derivative of the first C9 equation with respect to `t`. -/
theorem eCNineFirstPolynomial_pderiv_t_eval
    (x t X T : ℂ) :
    MvPolynomial.eval ![x, t, X, T]
        (MvPolynomial.pderiv (1 : Fin 4) eCNineFirstPolynomial) =
      36 * t ^ 2 := by
  simp [eCNineFirstPolynomial, eCNineX, eCNineT, eCNineCapitalX]
  ring

/-- The first C9 equation is independent of `T`. -/
theorem eCNineFirstPolynomial_pderiv_capitalT_eval
    (x t X T : ℂ) :
    MvPolynomial.eval ![x, t, X, T]
        (MvPolynomial.pderiv (3 : Fin 4) eCNineFirstPolynomial) = 0 := by
  simp [eCNineFirstPolynomial, eCNineX, eCNineT, eCNineCapitalX]

/-- The second C9 equation is independent of `t`. -/
theorem eCNineSecondPolynomial_pderiv_t_eval
    (x t X T : ℂ) :
    MvPolynomial.eval ![x, t, X, T]
        (MvPolynomial.pderiv (1 : Fin 4) eCNineSecondPolynomial) = 0 := by
  simp [eCNineSecondPolynomial, eCNineX, eCNineCapitalX,
    eCNineCapitalT]

/-- The derivative of the second C9 equation with respect to `T`. -/
theorem eCNineSecondPolynomial_pderiv_capitalT_eval
    (x t X T : ℂ) :
    MvPolynomial.eval ![x, t, X, T]
        (MvPolynomial.pderiv (3 : Fin 4) eCNineSecondPolynomial) =
      36 * T ^ 2 := by
  simp [eCNineSecondPolynomial, eCNineX, eCNineCapitalX,
    eCNineCapitalT]
  ring

/-- The `t,T` minor of the Jacobian matrix of the two C9 equations. -/
@[expose]
noncomputable def eCNineJacobianTCapitalTMinor
    (x t X T : ℂ) : ℂ :=
  MvPolynomial.eval ![x, t, X, T]
      (MvPolynomial.pderiv (1 : Fin 4) eCNineFirstPolynomial) *
    MvPolynomial.eval ![x, t, X, T]
      (MvPolynomial.pderiv (3 : Fin 4) eCNineSecondPolynomial) -
  MvPolynomial.eval ![x, t, X, T]
      (MvPolynomial.pderiv (3 : Fin 4) eCNineFirstPolynomial) *
    MvPolynomial.eval ![x, t, X, T]
      (MvPolynomial.pderiv (1 : Fin 4) eCNineSecondPolynomial)

theorem eCNineJacobianTCapitalTMinor_eq
    (x t X T : ℂ) :
    eCNineJacobianTCapitalTMinor x t X T =
      1296 * t ^ 2 * T ^ 2 := by
  rw [eCNineJacobianTCapitalTMinor,
    eCNineFirstPolynomial_pderiv_t_eval,
    eCNineSecondPolynomial_pderiv_capitalT_eval,
    eCNineFirstPolynomial_pderiv_capitalT_eval,
    eCNineSecondPolynomial_pderiv_t_eval]
  ring

/-- The displayed Jacobian minor is nonzero when both cubic root coordinates
are nonzero. -/
theorem eCNineJacobianTCapitalTMinor_ne_zero
    {x t X T : ℂ} (ht : t ≠ 0) (hT : T ≠ 0) :
    eCNineJacobianTCapitalTMinor x t X T ≠ 0 := by
  rw [eCNineJacobianTCapitalTMinor_eq]
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 ht)) (pow_ne_zero 2 hT)

/-- C9 has an explicit point where the `t,T` Jacobian minor is nonzero. -/
theorem eCNine_exists_point_with_jacobian_minor_ne_zero
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3) :
    ∃ t T : ℂ,
      ECNineEquations 0 t 1 T ∧
      eCNineJacobianTCapitalTMinor 0 t 1 T ≠ 0 := by
  obtain ⟨t, T, ht, hT, hcurve, _⟩ :=
    eCNine_exists_rotation_comparison_points homega
  exact ⟨t, T, hcurve,
    eCNineJacobianTCapitalTMinor_ne_zero ht hT⟩

end OnLeConjecture.DThree
