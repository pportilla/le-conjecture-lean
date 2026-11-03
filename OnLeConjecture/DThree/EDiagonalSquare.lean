/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EFreeBasis
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Tactic.LinearCombination

/-!
# The double diagonal factor for the `E` pair

This file proves the algebraic symmetry argument used in the invariant branch
of Lemma `dthree-Edouble`.  A symmetric polynomial in two variables which
vanishes on the diagonal is divisible by the square of the diagonal equation.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial
open scoped Polynomial.Bivariate

variable (K : Type*) [Field K] [CharZero K]

/-- The polynomial ring `K[x][X]` used on the residual curve. -/
abbrev EPairRing := Polynomial (Polynomial K)

/-- The first coordinate in `K[x][X]`. -/
@[expose]
noncomputable def ePairFirst : EPairRing K := C X

/-- The second coordinate in `K[x][X]`. -/
@[expose]
noncomputable def ePairSecond : EPairRing K := X

/-- The equation of the diagonal in `K[x][X]`. -/
@[expose]
noncomputable def ePairDiagonal : EPairRing K :=
  ePairSecond K - ePairFirst K

/-- Simultaneous evaluation of both variables at the inner variable. -/
@[expose]
noncomputable def ePairDiagonalEval :
    EPairRing K →ₐ[K] Polynomial K :=
  Polynomial.eval₂AlgHom (AlgHom.id K (Polynomial K)) X
    fun _ ↦ Commute.all _ _

omit [CharZero K] in
theorem ePairDiagonalEval_eq_aevalAeval :
    ePairDiagonalEval K = Polynomial.aevalAeval X X := by
  apply Polynomial.algHom_ext'
  · apply Polynomial.algHom_ext
    simp [ePairDiagonalEval]
  · simp [ePairDiagonalEval]

omit [CharZero K] in
@[simp]
theorem ePairDiagonalEval_first :
    ePairDiagonalEval K (ePairFirst K) = X := by
  simp [ePairDiagonalEval, ePairFirst]

omit [CharZero K] in
@[simp]
theorem ePairDiagonalEval_second :
    ePairDiagonalEval K (ePairSecond K) = X := by
  simp [ePairDiagonalEval, ePairSecond]

omit [CharZero K] in
/-- Evaluation on the diagonal is unchanged after exchanging the two
variables. -/
theorem ePairDiagonalEval_swap (theta : EPairRing K) :
    ePairDiagonalEval K (Polynomial.Bivariate.swap theta) =
      ePairDiagonalEval K theta := by
  rw [ePairDiagonalEval_eq_aevalAeval]
  exact Polynomial.Bivariate.aevalAeval_swap X X theta

omit [CharZero K] in
/-- The exchange of the two variables negates the diagonal equation. -/
theorem ePairDiagonal_swap :
    Polynomial.Bivariate.swap (ePairDiagonal K) = -ePairDiagonal K := by
  simp only [ePairDiagonal, ePairFirst, ePairSecond, map_sub,
    Polynomial.Bivariate.swap_Y, Polynomial.Bivariate.swap_X]
  ring

/-- A symmetric polynomial which vanishes on the diagonal is divisible by
the square of the diagonal equation. -/
theorem ePairDiagonal_sq_dvd_of_swap_eq_self_of_eval_eq_zero
    (theta : EPairRing K)
    (hsymmetric : Polynomial.Bivariate.swap theta = theta)
    (hdiagonal : ePairDiagonalEval K theta = 0) :
    ePairDiagonal K ^ 2 ∣ theta := by
  have hdiagEval : theta.eval X = 0 := by
    have h := hdiagonal
    rw [ePairDiagonalEval, _root_.Polynomial.eval₂AlgHom_apply,
      _root_.Polynomial.eval₂_eq_eval_map] at h
    simpa using h
  have hfirst : ePairDiagonal K ∣ theta := by
    rw [ePairDiagonal]
    exact _root_.Polynomial.dvd_iff_isRoot.mpr hdiagEval
  obtain ⟨quotient, htheta⟩ := hfirst
  have hcomparison :
      ePairDiagonal K * quotient =
        ePairDiagonal K *
          (-Polynomial.Bivariate.swap quotient) := by
    calc
      ePairDiagonal K * quotient = theta := htheta.symm
      _ = Polynomial.Bivariate.swap theta := hsymmetric.symm
      _ = Polynomial.Bivariate.swap
          (ePairDiagonal K * quotient) := by rw [htheta]
      _ = ePairDiagonal K *
          (-Polynomial.Bivariate.swap quotient) := by
        rw [map_mul, ePairDiagonal_swap]
        ring
  have hquotient :
      quotient = -Polynomial.Bivariate.swap quotient :=
    mul_left_cancel₀
      (_root_.Polynomial.X_sub_C_ne_zero X) hcomparison
  have hdiagonalQuotient : ePairDiagonalEval K quotient = 0 := by
    have hneg := congrArg (ePairDiagonalEval K) hquotient
    rw [map_neg, ePairDiagonalEval_swap] at hneg
    have htwice :
        (2 : Polynomial K) * ePairDiagonalEval K quotient = 0 := by
      linear_combination hneg
    exact (mul_eq_zero.mp htwice).resolve_left (by norm_num)
  have hquotientEval : quotient.eval X = 0 := by
    have h := hdiagonalQuotient
    rw [ePairDiagonalEval, _root_.Polynomial.eval₂AlgHom_apply,
      _root_.Polynomial.eval₂_eq_eval_map] at h
    simpa using h
  have hsecond : ePairDiagonal K ∣ quotient := by
    rw [ePairDiagonal]
    exact _root_.Polynomial.dvd_iff_isRoot.mpr hquotientEval
  obtain ⟨secondQuotient, hsecondQuotient⟩ := hsecond
  refine ⟨secondQuotient, ?_⟩
  rw [htheta, hsecondQuotient]
  ring

end OnLeConjecture.DThree
