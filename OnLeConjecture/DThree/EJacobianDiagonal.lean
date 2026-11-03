/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EFreeBasis
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# The diagonal consequence of the `E` Jacobian condition

This file studies the derivation

`D = partial_x - x^2 partial_w`

on `K[x,w]`.  Its value on the image coordinates is `D(P) = 0` and
`D(Q) = 4w`.  Hence it annihilates every coefficient from `K[P,Q]` after
restriction to `w = 0`.  For the canonical basis decomposition of a
polynomial, divisibility of `D(R)` by `w` then gives the coefficient relation
on the diagonal.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial

variable (K : Type*) [Field K] [CharZero K]

/-- Restriction from `K[x,w]` to the line `w = 0`. -/
noncomputable def eSourceAtWZero :
    ESourceRing K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval fun
    | ESourceCoordinate.x => X
    | ESourceCoordinate.w => 0

omit [CharZero K] in
@[simp]
theorem eSourceAtWZero_x :
    eSourceAtWZero K (eSourceX K) = X := by
  rw [eSourceAtWZero, eSourceX, MvPolynomial.aeval_X]

omit [CharZero K] in
@[simp]
theorem eSourceAtWZero_w :
    eSourceAtWZero K (eSourceW K) = 0 := by
  rw [eSourceAtWZero, eSourceW, MvPolynomial.aeval_X]

/-- Evaluation of an image coefficient on `P = x^3` and `Q = x^4`. -/
noncomputable def eBaseAtDiagonal :
    EBaseRing K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval fun
    | EBaseCoordinate.p => X ^ 3
    | EBaseCoordinate.q => X ^ 4

omit [CharZero K] in
@[simp]
theorem eBaseAtDiagonal_p :
    eBaseAtDiagonal K (eBaseP K) = X ^ 3 := by
  rw [eBaseAtDiagonal, eBaseP, MvPolynomial.aeval_X]

omit [CharZero K] in
@[simp]
theorem eBaseAtDiagonal_q :
    eBaseAtDiagonal K (eBaseQ K) = X ^ 4 := by
  rw [eBaseAtDiagonal, eBaseQ, MvPolynomial.aeval_X]

omit [CharZero K] in
/-- Restricting a coefficient after substitution by the `E` pair evaluates
it at `P = x^3` and `Q = x^4`. -/
theorem eSourceAtWZero_comp_baseToSource :
    (eSourceAtWZero K).comp (eBaseToSource K) =
      eBaseAtDiagonal K := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | p =>
      change eSourceAtWZero K
          (eBaseToSource K (eBaseP K)) =
        eBaseAtDiagonal K (eBaseP K)
      rw [eBaseToSource_p, eBaseAtDiagonal_p]
      simp [eSourceP]
  | q =>
      change eSourceAtWZero K
          (eBaseToSource K (eBaseQ K)) =
        eBaseAtDiagonal K (eBaseQ K)
      rw [eBaseToSource_q, eBaseAtDiagonal_q]
      simp [eSourceQ]

/-- The vector field tangent to the fibres of `P` along `w = 0`. -/
noncomputable def eCharacteristicDerivation :
    Derivation K (ESourceRing K) (ESourceRing K) :=
  MvPolynomial.pderiv ESourceCoordinate.x -
    eSourceX K ^ 2 • MvPolynomial.pderiv ESourceCoordinate.w

omit [CharZero K] in
theorem eCharacteristicDerivation_apply (R : ESourceRing K) :
    eCharacteristicDerivation K R =
      MvPolynomial.pderiv ESourceCoordinate.x R -
        eSourceX K ^ 2 * MvPolynomial.pderiv ESourceCoordinate.w R := by
  rfl

omit [CharZero K] in
@[simp]
theorem eCharacteristicDerivation_sourceP :
    eCharacteristicDerivation K (eSourceP K) = 0 := by
  simp only [eSourceP, eSourceX, eSourceW,
    eCharacteristicDerivation_apply, map_add, Derivation.leibniz_pow,
    Nat.add_one_sub_one, MvPolynomial.pderiv_X, Pi.single_eq_same,
    smul_eq_mul, mul_one, nsmul_eq_mul, Nat.cast_ofNat,
    Derivation.leibniz, ne_eq, reduceCtorEq, not_false_eq_true,
    Pi.single_eq_of_ne, mul_zero, MvPolynomial.derivation_C,
    add_zero]
  rw [show MvPolynomial.C (3 : K) = (3 : ESourceRing K) by
    exact map_natCast (MvPolynomial.C : K →+* ESourceRing K) 3]
  ring

omit [CharZero K] in
@[simp]
theorem eCharacteristicDerivation_sourceQ :
    eCharacteristicDerivation K (eSourceQ K) =
      MvPolynomial.C 4 * eSourceW K := by
  simp only [eSourceQ, eSourceX, eSourceW,
    eCharacteristicDerivation_apply, map_add, Derivation.leibniz_pow,
    Nat.add_one_sub_one, MvPolynomial.pderiv_X, Pi.single_eq_same,
    smul_eq_mul, mul_one, nsmul_eq_mul, Nat.cast_ofNat,
    Derivation.leibniz, ne_eq, reduceCtorEq, not_false_eq_true,
    Pi.single_eq_of_ne, mul_zero, MvPolynomial.derivation_C,
    add_zero]
  rw [show MvPolynomial.C (4 : K) = (4 : ESourceRing K) by
    exact map_natCast (MvPolynomial.C : K →+* ESourceRing K) 4]
  ring

omit [CharZero K] in
/-- The explicit product rule for the characteristic derivation. -/
theorem eCharacteristicDerivation_mul
    (A B : ESourceRing K) :
    eCharacteristicDerivation K (A * B) =
      eCharacteristicDerivation K A * B +
        A * eCharacteristicDerivation K B := by
  rw [(eCharacteristicDerivation K).leibniz]
  simp only [smul_eq_mul]
  ring

omit [CharZero K] in
@[simp]
theorem eCharacteristicDerivation_sourceX :
    eCharacteristicDerivation K (eSourceX K) = 1 := by
  simp [eCharacteristicDerivation_apply, eSourceX]

omit [CharZero K] in
/-- The characteristic derivation differentiates powers of `x` in the
usual way. -/
theorem eCharacteristicDerivation_sourceX_pow (n : ℕ) :
    eCharacteristicDerivation K (eSourceX K ^ n) =
      (n : ESourceRing K) * eSourceX K ^ (n - 1) := by
  rw [(eCharacteristicDerivation K).leibniz_pow]
  simp only [eCharacteristicDerivation_sourceX, smul_eq_mul, mul_one,
    nsmul_eq_mul]

omit [CharZero K] in
/-- Every coefficient from `K[P,Q]` is annihilated by the characteristic
derivation after restriction to `w = 0`. -/
theorem eSourceAtWZero_characteristic_baseToSource
    (c : EBaseRing K) :
    eSourceAtWZero K
        (eCharacteristicDerivation K (eBaseToSource K c)) = 0 := by
  induction c using MvPolynomial.induction_on with
  | C a =>
      simp
  | add p q hp hq =>
      simpa using congrArg₂ (fun a b : Polynomial K => a + b) hp hq
  | mul_X p i hp =>
      rw [map_mul, eCharacteristicDerivation_mul, map_add,
        map_mul, map_mul, hp, zero_mul, zero_add]
      cases i with
      | p =>
          suffices h : eSourceAtWZero K
              (eCharacteristicDerivation K
                (eBaseToSource K (eBaseP K))) = 0 by
            rw [show MvPolynomial.X EBaseCoordinate.p = eBaseP K by
              rw [eBaseP]]
            rw [h, mul_zero]
          rw [eBaseToSource_p, eCharacteristicDerivation_sourceP, map_zero]
      | q =>
          suffices h : eSourceAtWZero K
              (eCharacteristicDerivation K
                (eBaseToSource K (eBaseQ K))) = 0 by
            rw [show MvPolynomial.X EBaseCoordinate.q = eBaseQ K by
              rw [eBaseQ]]
            rw [h, mul_zero]
          rw [eBaseToSource_q, eCharacteristicDerivation_sourceQ,
            map_mul, eSourceAtWZero_w, mul_zero]

omit [CharZero K] in
/-- The restriction to `w = 0` of the derivative of one basis summand. -/
theorem eSourceAtWZero_characteristic_basisTerm
    (c : EBaseRing K) (n : ℕ) :
    eSourceAtWZero K
        (eCharacteristicDerivation K
          (eBaseToSource K c * eSourceX K ^ n)) =
      eBaseAtDiagonal K c *
        ((n : Polynomial K) * X ^ (n - 1)) := by
  rw [eCharacteristicDerivation_mul, map_add, map_mul, map_mul,
    eSourceAtWZero_characteristic_baseToSource, zero_mul, zero_add,
    eCharacteristicDerivation_sourceX_pow, map_mul, map_natCast,
    map_pow, eSourceAtWZero_x]
  have hcomp := AlgHom.congr_fun
    (eSourceAtWZero_comp_baseToSource K) c
  simpa only [AlgHom.comp_apply] using congrArg
    (fun z : Polynomial K =>
      z * ((n : Polynomial K) * X ^ (n - 1))) hcomp

/-- Divisibility of the characteristic derivative by `w` gives the
diagonal relation among the four canonical basis coefficients. -/
theorem e_diagonal_coefficient_relation_of_basis_and_w_dvd
    (R : ESourceRing K) (c : Fin 4 → EBaseRing K)
    (hdecomposition :
      R = ∑ i : Fin 4,
        eBaseToSource K (c i) * eSourceX K ^ (i : ℕ))
    (hdiv : eSourceW K ∣ eCharacteristicDerivation K R) :
    eBaseAtDiagonal K (c 1) +
        eBaseAtDiagonal K (c 2) * (2 * X) +
        eBaseAtDiagonal K (c 3) * (3 * X ^ 2) = 0 := by
  have hzero :
      eSourceAtWZero K (eCharacteristicDerivation K R) = 0 := by
    obtain ⟨A, hA⟩ := hdiv
    rw [hA, map_mul, eSourceAtWZero_w, zero_mul]
  have hsum :
      ∑ i : Fin 4,
          eSourceAtWZero K
            (eCharacteristicDerivation K
              (eBaseToSource K (c i) *
                eSourceX K ^ (i : ℕ))) = 0 := by
    calc
      _ = eSourceAtWZero K
          (∑ i : Fin 4,
            eCharacteristicDerivation K
              (eBaseToSource K (c i) *
                eSourceX K ^ (i : ℕ))) := by rw [map_sum]
      _ = eSourceAtWZero K
          (eCharacteristicDerivation K
            (∑ i : Fin 4,
              eBaseToSource K (c i) *
                eSourceX K ^ (i : ℕ))) := by
          apply congrArg (eSourceAtWZero K)
          rw [map_sum]
      _ = eSourceAtWZero K
          (eCharacteristicDerivation K R) := by rw [← hdecomposition]
      _ = 0 := hzero
  simp_rw [eSourceAtWZero_characteristic_basisTerm] at hsum
  rw [Fin.sum_univ_four] at hsum
  norm_num at hsum ⊢
  exact hsum

end OnLeConjecture.DThree
