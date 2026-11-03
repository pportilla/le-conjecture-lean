/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Derivations on integral extensions containing rational constants

The positive integer units in the base ring permit normalization of the
derivative of a monic polynomial. Minimality of the minimal polynomial then
shows that every integral element is killed by every base derivation.
-/

public section

namespace OnLeConjecture.Algebra

open Polynomial

theorem derivation_eq_zero_of_isIntegral
    {R A : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [CommRing A] [IsDomain A] [Algebra R A]
    (hnatUnit : ∀ n : ℕ, 0 < n → IsUnit (n : R))
    (D : Derivation R A A) (x : A) (hx : IsIntegral R x) : D x = 0 := by
  by_contra hDx
  have heval : aeval x (derivative (minpoly R x)) = 0 := by
    have h := congrArg D (minpoly.aeval R x)
    rw [D.map_aeval, map_zero, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_right hDx
  have hu : IsUnit (derivative (minpoly R x)).leadingCoeff := by
    rw [leadingCoeff_derivative, (minpoly.monic hx).leadingCoeff, one_mul]
    exact hnatUnit _ (minpoly.natDegree_pos hx)
  have hnormalized :
      aeval x (hu.unit⁻¹ • derivative (minpoly R x)) = 0 := by
    change aeval x ((↑(hu.unit⁻¹) : R) • derivative (minpoly R x)) = 0
    rw [smul_eq_C_mul, map_mul, heval, mul_zero]
  have hmin := minpoly.min R x (monic_of_isUnit_leadingCoeff_inv_smul hu) hnormalized
  exact (not_le_of_gt (degree_derivative_lt (minpoly.ne_zero hx)))
    (hmin.trans (degree_smul_le _ _))

theorem derivation_eq_zero_of_finite
    {R A : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [CommRing A] [IsDomain A] [Algebra R A] [Module.Finite R A]
    (hnatUnit : ∀ n : ℕ, 0 < n → IsUnit (n : R))
    (D : Derivation R A A) : D = 0 := by
  ext x
  exact derivation_eq_zero_of_isIntegral hnatUnit D x
    (Algebra.IsIntegral.isIntegral x)

end OnLeConjecture.Algebra
