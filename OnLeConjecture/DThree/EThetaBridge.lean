/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EJacobianDiagonal
public import OnLeConjecture.DThree.EDiagonalSquare
public import OnLeConjecture.DThree.ECocycle
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# The residual difference polynomial for the `E` pair

This file evaluates the canonical basis coefficients on the residual fibre
product.  The resulting polynomial `Theta_R` is symmetric.  Its restriction
to the diagonal is the coefficient relation obtained from the Jacobian
condition, so it is divisible by the square of the diagonal equation.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial
open scoped Polynomial.Bivariate

variable (K : Type*) [Field K] [CharZero K]

/-- The common value of `P` on the residual parametrization. -/
@[expose]
noncomputable def eResidualPairP : EPairRing K :=
  algebraMap K (EPairRing K) (4 : K)⁻¹ *
    ((ePairFirst K + ePairSecond K) *
      (ePairFirst K ^ 2 + ePairSecond K ^ 2))

/-- The common value of `Q` on the residual parametrization. -/
@[expose]
noncomputable def eResidualPairQ : EPairRing K :=
  algebraMap K (EPairRing K) (3 : K)⁻¹ *
    (ePairFirst K * ePairSecond K *
      (ePairFirst K ^ 2 +
        ePairFirst K * ePairSecond K + ePairSecond K ^ 2))

/-- Evaluation of a coefficient in `K[P,Q]` on the residual
parametrization. -/
noncomputable def eResidualBaseToPair :
    EBaseRing K →ₐ[K] EPairRing K :=
  MvPolynomial.aeval fun
    | EBaseCoordinate.p => eResidualPairP K
    | EBaseCoordinate.q => eResidualPairQ K

omit [CharZero K] in
@[simp]
theorem eResidualBaseToPair_p :
    eResidualBaseToPair K (eBaseP K) = eResidualPairP K := by
  rw [eResidualBaseToPair, eBaseP, MvPolynomial.aeval_X]

omit [CharZero K] in
@[simp]
theorem eResidualBaseToPair_q :
    eResidualBaseToPair K (eBaseQ K) = eResidualPairQ K := by
  rw [eResidualBaseToPair, eBaseQ, MvPolynomial.aeval_X]

/-- The residual difference factor attached to the canonical basis
coefficients of `R`. -/
noncomputable def eThetaPolynomial
    (c : Fin 4 → EBaseRing K) : EPairRing K :=
  eResidualBaseToPair K (c 1) +
    eResidualBaseToPair K (c 2) *
      (ePairFirst K + ePairSecond K) +
    eResidualBaseToPair K (c 3) *
      (ePairFirst K ^ 2 +
        ePairFirst K * ePairSecond K + ePairSecond K ^ 2)

/-- The canonical basis expression after residual substitution, evaluated
at one of the two source coordinates. -/
@[expose]
noncomputable def eResidualBasisValue
    (c : Fin 4 → EBaseRing K) (z : EPairRing K) : EPairRing K :=
  eResidualBaseToPair K (c 0) +
    eResidualBaseToPair K (c 1) * z +
    eResidualBaseToPair K (c 2) * z ^ 2 +
    eResidualBaseToPair K (c 3) * z ^ 3

omit [CharZero K] in
/-- The residual difference of the two canonical basis values factors
through `Theta_R`. -/
theorem e_residual_basis_difference_factorization
    (c : Fin 4 → EBaseRing K) :
    eResidualBasisValue K c (ePairFirst K) -
        eResidualBasisValue K c (ePairSecond K) =
      (ePairFirst K - ePairSecond K) * eThetaPolynomial K c := by
  simp only [eResidualBasisValue, eThetaPolynomial]
  ring

/-- On the diagonal, the residual value of `P` is `x^3`. -/
theorem ePairDiagonalEval_residualPairP :
    ePairDiagonalEval K (eResidualPairP K) = X ^ 3 := by
  simp only [ePairDiagonalEval, eResidualPairP, algebraMap_apply,
    algebraMap_eq, ePairFirst, ePairSecond, eval₂AlgHom_apply,
    AlgHom.id_toRingHom, eval₂_mul, eval₂_C,
    RingHomCompTriple.comp_apply, eval₂_add, RingHom.id_apply,
    eval₂_X, eval₂_id, eval_pow, eval_C, eval₂_X_pow]
  have hscalar :
      C ((4 : K)⁻¹) * (4 : Polynomial K) = 1 := by
    change C ((4 : K)⁻¹) * C (4 : K) = 1
    rw [← map_mul]
    norm_num
  calc
    C ((4 : K)⁻¹) * ((X + X) * (X ^ 2 + X ^ 2)) =
        C ((4 : K)⁻¹) * X ^ 3 * 4 := by ring
    C ((4 : K)⁻¹) * X ^ 3 * 4 =
        (C ((4 : K)⁻¹) * 4) * X ^ 3 := by ring
    _ = X ^ 3 := by rw [hscalar, one_mul]

/-- On the diagonal, the residual value of `Q` is `x^4`. -/
theorem ePairDiagonalEval_residualPairQ :
    ePairDiagonalEval K (eResidualPairQ K) = X ^ 4 := by
  simp only [ePairDiagonalEval, eResidualPairQ, algebraMap_apply,
    algebraMap_eq, ePairFirst, ePairSecond, eval₂AlgHom_apply,
    AlgHom.id_toRingHom, eval₂_mul, eval₂_C,
    RingHomCompTriple.comp_apply, RingHom.id_apply, eval₂_X,
    eval₂_add, eval₂_id, eval_pow, eval_C, eval₂_X_pow]
  have hscalar :
      C ((3 : K)⁻¹) * (3 : Polynomial K) = 1 := by
    change C ((3 : K)⁻¹) * C (3 : K) = 1
    rw [← map_mul]
    norm_num
  calc
    C ((3 : K)⁻¹) *
        (X * X * (X ^ 2 + X * X + X ^ 2)) =
      C ((3 : K)⁻¹) * X ^ 4 * 3 := by ring
    C ((3 : K)⁻¹) * X ^ 4 * 3 =
        (C ((3 : K)⁻¹) * 3) * X ^ 4 := by ring
    _ = X ^ 4 := by rw [hscalar, one_mul]

/-- Diagonal evaluation after residual substitution agrees with evaluation
at `P = x^3` and `Q = x^4`. -/
theorem ePairDiagonalEval_comp_residualBaseToPair :
    (ePairDiagonalEval K).comp (eResidualBaseToPair K) =
      eBaseAtDiagonal K := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | p =>
      change ePairDiagonalEval K
          (eResidualBaseToPair K (eBaseP K)) =
        eBaseAtDiagonal K (eBaseP K)
      rw [eResidualBaseToPair_p, ePairDiagonalEval_residualPairP,
        eBaseAtDiagonal_p]
  | q =>
      change ePairDiagonalEval K
          (eResidualBaseToPair K (eBaseQ K)) =
        eBaseAtDiagonal K (eBaseQ K)
      rw [eResidualBaseToPair_q, ePairDiagonalEval_residualPairQ,
        eBaseAtDiagonal_q]

/-- Evaluation of a residual coefficient on the diagonal. -/
theorem ePairDiagonalEval_residualBaseToPair
    (c : EBaseRing K) :
    ePairDiagonalEval K (eResidualBaseToPair K c) =
      eBaseAtDiagonal K c := by
  exact AlgHom.congr_fun
    (ePairDiagonalEval_comp_residualBaseToPair K) c

/-- The diagonal value of `Theta_R` is the coefficient relation supplied
by the characteristic derivative. -/
theorem ePairDiagonalEval_thetaPolynomial
    (c : Fin 4 → EBaseRing K) :
    ePairDiagonalEval K (eThetaPolynomial K c) =
      eBaseAtDiagonal K (c 1) +
        eBaseAtDiagonal K (c 2) * (2 * X) +
        eBaseAtDiagonal K (c 3) * (3 * X ^ 2) := by
  simp only [eThetaPolynomial, map_add, map_mul, map_pow,
    ePairDiagonalEval_residualBaseToPair,
    ePairDiagonalEval_first, ePairDiagonalEval_second]
  ring

omit [CharZero K] in
/-- The residual expression for `P` is fixed by exchanging the two
variables. -/
theorem eResidualPairP_swap :
    Polynomial.Bivariate.swap (eResidualPairP K) =
      eResidualPairP K := by
  simp only [eResidualPairP, ePairFirst, ePairSecond, map_mul,
    map_add, map_pow, Polynomial.Bivariate.swap.commutes,
    Polynomial.Bivariate.swap_Y, Polynomial.Bivariate.swap_X]
  ring

omit [CharZero K] in
/-- The residual expression for `Q` is fixed by exchanging the two
variables. -/
theorem eResidualPairQ_swap :
    Polynomial.Bivariate.swap (eResidualPairQ K) =
      eResidualPairQ K := by
  simp only [eResidualPairQ, ePairFirst, ePairSecond, map_mul,
    map_add, map_pow, Polynomial.Bivariate.swap.commutes,
    Polynomial.Bivariate.swap_Y, Polynomial.Bivariate.swap_X]
  ring

omit [CharZero K] in
/-- Every residually evaluated coefficient is symmetric. -/
theorem eResidualBaseToPair_swap (c : EBaseRing K) :
    Polynomial.Bivariate.swap (eResidualBaseToPair K c) =
      eResidualBaseToPair K c := by
  induction c using MvPolynomial.induction_on with
  | C a =>
      simpa using Polynomial.Bivariate.swap.commutes a
  | add p q hp hq =>
      simp only [map_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, hp]
      cases i with
      | p =>
          rw [show MvPolynomial.X EBaseCoordinate.p = eBaseP K by
            rw [eBaseP]]
          rw [eResidualBaseToPair_p, eResidualPairP_swap]
      | q =>
          rw [show MvPolynomial.X EBaseCoordinate.q = eBaseQ K by
            rw [eBaseQ]]
          rw [eResidualBaseToPair_q, eResidualPairQ_swap]

omit [CharZero K] in
/-- The polynomial `Theta_R` is symmetric in the two residual source
coordinates. -/
theorem eThetaPolynomial_swap (c : Fin 4 → EBaseRing K) :
    Polynomial.Bivariate.swap (eThetaPolynomial K c) =
      eThetaPolynomial K c := by
  simp only [eThetaPolynomial, map_add, map_mul, map_pow,
    eResidualBaseToPair_swap, ePairFirst, ePairSecond,
    Polynomial.Bivariate.swap_Y, Polynomial.Bivariate.swap_X]
  ring

/-- The Jacobian divisibility condition makes `Theta_R` vanish on the
diagonal. -/
theorem eThetaPolynomial_diagonalEval_eq_zero_of_basis_and_w_dvd
    (R : ESourceRing K) (c : Fin 4 → EBaseRing K)
    (hdecomposition :
      R = ∑ i : Fin 4,
        eBaseToSource K (c i) * eSourceX K ^ (i : ℕ))
    (hdiv : eSourceW K ∣ eCharacteristicDerivation K R) :
    ePairDiagonalEval K (eThetaPolynomial K c) = 0 := by
  rw [ePairDiagonalEval_thetaPolynomial]
  exact e_diagonal_coefficient_relation_of_basis_and_w_dvd
    K R c hdecomposition hdiv

/-- The residual difference polynomial associated with the canonical basis
is divisible by the square of the diagonal equation. -/
theorem ePairDiagonal_sq_dvd_thetaPolynomial_of_basis_and_w_dvd
    (R : ESourceRing K) (c : Fin 4 → EBaseRing K)
    (hdecomposition :
      R = ∑ i : Fin 4,
        eBaseToSource K (c i) * eSourceX K ^ (i : ℕ))
    (hdiv : eSourceW K ∣ eCharacteristicDerivation K R) :
    ePairDiagonal K ^ 2 ∣ eThetaPolynomial K c := by
  apply ePairDiagonal_sq_dvd_of_swap_eq_self_of_eval_eq_zero K
  · exact eThetaPolynomial_swap K c
  · exact eThetaPolynomial_diagonalEval_eq_zero_of_basis_and_w_dvd
      K R c hdecomposition hdiv

/-- Evaluation of the two abstract image coordinates at scalar values. -/
noncomputable def eBasePointEval (p q : K) :
    EBaseRing K →ₐ[K] K :=
  MvPolynomial.aeval fun
    | EBaseCoordinate.p => p
    | EBaseCoordinate.q => q

/-- Evaluation of the two residual source coordinates at scalar values. -/
noncomputable def ePairPointEval (x X : K) :
    EPairRing K →ₐ[K] K :=
  Polynomial.aevalAeval x X

omit [CharZero K] in
@[simp]
theorem eBasePointEval_p (p q : K) :
    eBasePointEval K p q (eBaseP K) = p := by
  rw [eBasePointEval, eBaseP, MvPolynomial.aeval_X]

omit [CharZero K] in
@[simp]
theorem eBasePointEval_q (p q : K) :
    eBasePointEval K p q (eBaseQ K) = q := by
  rw [eBasePointEval, eBaseQ, MvPolynomial.aeval_X]

omit [CharZero K] in
@[simp]
theorem ePairPointEval_first (x X : K) :
    ePairPointEval K x X (ePairFirst K) = x := by
  simp [ePairPointEval, ePairFirst]

omit [CharZero K] in
@[simp]
theorem ePairPointEval_second (x X : K) :
    ePairPointEval K x X (ePairSecond K) = X := by
  simp [ePairPointEval, ePairSecond]

omit [CharZero K] in
/-- If the residual image coordinates at `(x,X)` are `(p,q)`, then every
coefficient specializes at the same pair `(p,q)`. -/
theorem ePairPointEval_residualBaseToPair
    (c : EBaseRing K) (x X p q : K)
    (hP : ePairPointEval K x X (eResidualPairP K) = p)
    (hQ : ePairPointEval K x X (eResidualPairQ K) = q) :
    ePairPointEval K x X (eResidualBaseToPair K c) =
      eBasePointEval K p q c := by
  have hcomp :
      (ePairPointEval K x X).comp (eResidualBaseToPair K) =
        eBasePointEval K p q := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | p =>
        change ePairPointEval K x X
            (eResidualBaseToPair K (eBaseP K)) =
          eBasePointEval K p q (eBaseP K)
        rw [eResidualBaseToPair_p, hP, eBasePointEval_p]
    | q =>
        change ePairPointEval K x X
            (eResidualBaseToPair K (eBaseQ K)) =
          eBasePointEval K p q (eBaseQ K)
        rw [eResidualBaseToPair_q, hQ, eBasePointEval_q]
  exact AlgHom.congr_fun hcomp c

omit [CharZero K] in
/-- Scalar evaluation of the residual polynomial agrees with `eTheta` at
the common image point. -/
theorem ePairPointEval_thetaPolynomial
    (c : Fin 4 → EBaseRing K) (x X p q : K)
    (hP : ePairPointEval K x X (eResidualPairP K) = p)
    (hQ : ePairPointEval K x X (eResidualPairQ K) = q) :
    ePairPointEval K x X (eThetaPolynomial K c) =
      eTheta
        (eBasePointEval K p q (c 1))
        (eBasePointEval K p q (c 2))
        (eBasePointEval K p q (c 3)) x X := by
  simp only [eThetaPolynomial, eTheta, map_add, map_mul, map_pow,
    ePairPointEval_residualBaseToPair K _ _ _ _ _ hP hQ,
    ePairPointEval_first, ePairPointEval_second]

omit [CharZero K] in
/-- Scalar evaluation of the residual expression for `P`. -/
theorem ePairPointEval_residualPairP (x X : K) :
    ePairPointEval K x X (eResidualPairP K) =
      (4 : K)⁻¹ * ((x + X) * (x ^ 2 + X ^ 2)) := by
  simp only [eResidualPairP, map_mul, map_add, map_pow,
    (ePairPointEval K x X).commutes,
    Algebra.algebraMap_self_apply,
    ePairPointEval_first, ePairPointEval_second]

omit [CharZero K] in
/-- Scalar evaluation of the residual expression for `Q`. -/
theorem ePairPointEval_residualPairQ (x X : K) :
    ePairPointEval K x X (eResidualPairQ K) =
      (3 : K)⁻¹ *
        (x * X * (x ^ 2 + x * X + X ^ 2)) := by
  simp only [eResidualPairQ, map_mul, map_add, map_pow,
    (ePairPointEval K x X).commutes,
    Algebra.algebraMap_self_apply,
    ePairPointEval_first, ePairPointEval_second]

/-- On each oriented pair in the cocycle triple, the residual image point
is `(1/4,0)`. -/
theorem e_cocycle_triple_residual_values
    (omega : K) (homega : omega ^ 2 + omega + 1 = 0) :
    (ePairPointEval K 1 0 (eResidualPairP K) = (4 : K)⁻¹ ∧
      ePairPointEval K 1 0 (eResidualPairQ K) = 0) ∧
    (ePairPointEval K 0 omega (eResidualPairP K) = (4 : K)⁻¹ ∧
      ePairPointEval K 0 omega (eResidualPairQ K) = 0) ∧
    (ePairPointEval K omega 1 (eResidualPairP K) = (4 : K)⁻¹ ∧
      ePairPointEval K omega 1 (eResidualPairQ K) = 0) := by
  have hcube : omega ^ 3 = 1 := by
    calc
      omega ^ 3 =
          1 + (omega - 1) * (omega ^ 2 + omega + 1) := by ring
      _ = 1 := by rw [homega, mul_zero, add_zero]
  constructor
  · constructor
    · rw [ePairPointEval_residualPairP]
      ring
    · rw [ePairPointEval_residualPairQ]
      ring
  · constructor
    · constructor
      · rw [ePairPointEval_residualPairP]
        calc
          (4 : K)⁻¹ *
              (((0 : K) + omega) * (0 ^ 2 + omega ^ 2)) =
              (4 : K)⁻¹ * omega ^ 3 := by ring
          _ = (4 : K)⁻¹ := by rw [hcube, mul_one]
      · rw [ePairPointEval_residualPairQ]
        ring
    · constructor
      · rw [ePairPointEval_residualPairP]
        have hproduct :
            (omega + 1) * (omega ^ 2 + 1) = 1 := by
          calc
            (omega + 1) * (omega ^ 2 + 1) =
                omega ^ 3 + (omega ^ 2 + omega + 1) := by ring
            _ = 1 := by rw [hcube, homega, add_zero]
        simp only [one_pow]
        rw [hproduct, mul_one]
      · rw [ePairPointEval_residualPairQ]
        simp only [one_pow, mul_one]
        rw [homega, mul_zero, mul_zero]

omit [CharZero K] in
/-- An even power of the chosen diagonal equation evaluates to the same
power of `x-X`. -/
theorem ePairPointEval_diagonal_even_pow
    (x X : K) (k : ℕ) :
    ePairPointEval K x X (ePairDiagonal K ^ (2 * k)) =
      (x - X) ^ (2 * k) := by
  rw [map_pow, ePairDiagonal, map_sub,
    ePairPointEval_second, ePairPointEval_first]
  rw [show X - x = -(x - X) by ring, neg_pow, pow_mul]
  norm_num

/-- A nonzero pure even power of the diagonal cannot equal the residual
polynomial `Theta_R`. -/
theorem eThetaPolynomial_diagonal_power_impossible
    (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0)
    (c : Fin 4 → EBaseRing ℂ)
    (k : ℕ) (hk : 1 ≤ k)
    (coefficient : ℂ) (hcoefficient : coefficient ≠ 0)
    (hpower :
      eThetaPolynomial ℂ c =
        algebraMap ℂ (EPairRing ℂ) coefficient *
          ePairDiagonal ℂ ^ (2 * k)) :
    False := by
  let pzero : ℂ := (4 : ℂ)⁻¹
  let coefficientValue (i : Fin 4) : ℂ :=
    eBasePointEval ℂ pzero 0 (c i)
  obtain ⟨⟨hPoneZero, hQoneZero⟩,
      ⟨⟨hPzeroOmega, hQzeroOmega⟩,
        ⟨hPomegaOne, hQomegaOne⟩⟩⟩ :=
    e_cocycle_triple_residual_values ℂ omega homega
  have htheta (x X : ℂ)
      (hP : ePairPointEval ℂ x X (eResidualPairP ℂ) = pzero)
      (hQ : ePairPointEval ℂ x X (eResidualPairQ ℂ) = 0) :
      eTheta (coefficientValue 1) (coefficientValue 2)
          (coefficientValue 3) x X =
        coefficient * (x - X) ^ (2 * k) := by
    calc
      eTheta (coefficientValue 1) (coefficientValue 2)
          (coefficientValue 3) x X =
          ePairPointEval ℂ x X (eThetaPolynomial ℂ c) := by
            symm
            exact ePairPointEval_thetaPolynomial
              ℂ c x X pzero 0 hP hQ
      _ = ePairPointEval ℂ x X
          (algebraMap ℂ (EPairRing ℂ) coefficient *
            ePairDiagonal ℂ ^ (2 * k)) := by rw [hpower]
      _ = coefficient * (x - X) ^ (2 * k) := by
        rw [map_mul, (ePairPointEval ℂ x X).commutes,
          Algebra.algebraMap_self_apply,
          ePairPointEval_diagonal_even_pow]
  have hdifference (x X : ℂ)
      (hP : ePairPointEval ℂ x X (eResidualPairP ℂ) = pzero)
      (hQ : ePairPointEval ℂ x X (eResidualPairQ ℂ) = 0) :
      eBasisValue (coefficientValue 0) (coefficientValue 1)
          (coefficientValue 2) (coefficientValue 3) x -
        eBasisValue (coefficientValue 0) (coefficientValue 1)
          (coefficientValue 2) (coefficientValue 3) X =
        coefficient * (x - X) ^ (2 * k + 1) := by
    rw [e_basis_difference_factorization,
      htheta x X hP hQ, pow_succ]
    ring
  apply e_odd_power_differences_not_cocycle omega homega k hk
    coefficient
    (eBasisValue (coefficientValue 0) (coefficientValue 1)
      (coefficientValue 2) (coefficientValue 3) 1)
    (eBasisValue (coefficientValue 0) (coefficientValue 1)
      (coefficientValue 2) (coefficientValue 3) 0)
    (eBasisValue (coefficientValue 0) (coefficientValue 1)
      (coefficientValue 2) (coefficientValue 3) omega)
    hcoefficient
  · exact hdifference 1 0 hPoneZero hQoneZero
  · exact hdifference 0 omega hPzeroOmega hQzeroOmega
  · exact hdifference omega 1 hPomegaOne hQomegaOne

end OnLeConjecture.DThree
