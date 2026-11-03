/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HDerivativeRatFunc
public import OnLeConjecture.DThree.RatFuncDerivative

/-!
# Local derivative orders on the rational H conic

The formal derivative in the rational parameter is divided by the derivative
of the conic function `w`. The Jacobian quotient identities identify this
derivative with the Cramer rational function. At either point above `X = 1`,
the function `w` has order one, so exact positive orders decrease by one.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial
open scoped Polynomial WithZero

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- Differentiation of a bivariate polynomial after substitution of two
rational functions. -/
theorem ratFuncDerivative_hFormEval
    (x w : RatFunc K) (F : MvPolynomial (Fin 2) K) :
    ratFuncDerivative (hFormEval x w F) =
      hFormEval x w (MvPolynomial.pderiv 0 F) *
          ratFuncDerivative x +
        hFormEval x w (MvPolynomial.pderiv 1 F) *
          ratFuncDerivative w := by
  induction F using MvPolynomial.induction_on with
  | C c =>
      rw [show hFormEval x w (MvPolynomial.C c) = RatFunc.C c by
        simp [hFormEval], ratFuncDerivative_C]
      simp [hFormEval]
  | add F G hF hG =>
      rw [show hFormEval x w (F + G) =
          hFormEval x w F + hFormEval x w G by
        simp [hFormEval], ratFuncDerivative_add, hF, hG]
      simp [hFormEval]
      ring
  | mul_X F i hF =>
      rw [show hFormEval x w (F * MvPolynomial.X i) =
          hFormEval x w F * (if i = 0 then x else w) by
        simp [hFormEval], ratFuncDerivative_mul, hF]
      fin_cases i
      · simp only [Fin.isValue]
        simp [hFormEval]
        ring
      · simp only [Fin.isValue]
        simp [hFormEval]
        ring

omit [CharZero K] in
/-- The derivative of the cubic coordinate after rational substitution. -/
theorem ratFuncDerivative_hP (x w : RatFunc K) :
    ratFuncDerivative (hP x w) =
      hPPartialX x w * ratFuncDerivative x +
        hPPartialW x * ratFuncDerivative w := by
  have hchain :=
    ratFuncDerivative_hFormEval x w (hPForm (K := K))
  rw [hFormEval_pderiv_hPForm_zero,
    hFormEval_pderiv_hPForm_one] at hchain
  change ratFuncDerivative (x ^ 3 + 3 * x * w) = _
  rw [show x ^ 3 + 3 * x * w = x ^ 3 + 3 * (x * w) by ring]
  simpa [hFormEval, hPForm, hFormX, hFormW, map_ofNat] using hchain

omit [CharZero K] in
/-- The derivative of the quartic coordinate after rational substitution. -/
theorem ratFuncDerivative_hQ (x w : RatFunc K) :
    ratFuncDerivative (hQ x w) =
      hQPartialX x w * ratFuncDerivative x +
        hQPartialW x w * ratFuncDerivative w := by
  have hchain :=
    ratFuncDerivative_hFormEval x w (hQForm (K := K))
  rw [hFormEval_pderiv_hQForm_zero,
    hFormEval_pderiv_hQForm_one] at hchain
  change ratFuncDerivative
    (x ^ 4 + 4 * x ^ 2 * w + 2 * w ^ 2) = _
  rw [show x ^ 4 + 4 * x ^ 2 * w + 2 * w ^ 2 =
      x ^ 4 + 4 * (x ^ 2 * w) + 2 * w ^ 2 by ring]
  simpa [hFormEval, hQForm, hFormX, hFormW, map_ofNat] using hchain

/-- The rational parametrization gives two points in the same fibre of the
cubic and quartic coordinates. -/
theorem h_conic_param_fibre_equations :
    hP 1 (hConicParamW (K := K)) =
        hP hConicParamX hConicParamCapitalW ∧
      hQ 1 (hConicParamW (K := K)) =
        hQ hConicParamX hConicParamCapitalW := by
  have hd : algebraMap K[X] (RatFunc K)
      hConicParamDenominator ≠ 0 :=
    RatFunc.algebraMap_ne_zero h_conic_param_denominator_ne_zero
  have hplus : hConicParamX (K := K) + 1 ≠ 0 := by
    rw [h_conic_param_x_add_one]
    apply div_ne_zero _ hd
    apply RatFunc.algebraMap_ne_zero
    exact mul_ne_zero (by norm_num) h_conic_param_linear_ne_zero
  have htheta :
      hConicParamTheta (K := K) ^ 2 =
        -2 * (hConicParamX ^ 2 + 4 * hConicParamX + 1) :=
    h_conic_equation_eq_zero_iff.mp h_conic_param_equation
  have hfibre := h_conic_parametrizes_fibre hplus htheta
  simpa only [← h_conic_param_w_eq,
    ← h_conic_param_capitalW_eq] using hfibre

/-- After division by `dw/dm`, the derivatives of the parametrized fibre
equations give the tangent vector used in the Cramer identity. -/
theorem h_conic_param_derivative_tangent
    (hdw : ratFuncDerivative (hConicParamW (K := K)) ≠ 0) :
    (3 : RatFunc K) =
        hPPartialX hConicParamX hConicParamCapitalW *
            (ratFuncDerivative hConicParamX /
              ratFuncDerivative hConicParamW) +
          hPPartialW hConicParamX *
            (ratFuncDerivative hConicParamCapitalW /
              ratFuncDerivative hConicParamW) ∧
      (4 : RatFunc K) * (1 + hConicParamW) =
        hQPartialX hConicParamX hConicParamCapitalW *
            (ratFuncDerivative hConicParamX /
              ratFuncDerivative hConicParamW) +
          hQPartialW hConicParamX hConicParamCapitalW *
            (ratFuncDerivative hConicParamCapitalW /
              ratFuncDerivative hConicParamW) := by
  obtain ⟨hPfiber, hQfiber⟩ :=
    h_conic_param_fibre_equations (K := K)
  have hPderivative := congrArg ratFuncDerivative hPfiber
  have hQderivative := congrArg ratFuncDerivative hQfiber
  rw [ratFuncDerivative_hP, ratFuncDerivative_hP] at hPderivative
  rw [ratFuncDerivative_hQ, ratFuncDerivative_hQ] at hQderivative
  have hPclean :
      (3 : RatFunc K) * ratFuncDerivative hConicParamW =
        (3 * hConicParamX ^ 2 +
            3 * hConicParamCapitalW) *
            ratFuncDerivative hConicParamX +
          3 * hConicParamX *
            ratFuncDerivative hConicParamCapitalW := by
    simpa [hPPartialX, hPPartialW] using hPderivative
  have hQclean :
      (4 : RatFunc K) * (1 + hConicParamW) *
          ratFuncDerivative hConicParamW =
        (4 * hConicParamX ^ 3 +
            8 * hConicParamX * hConicParamCapitalW) *
            ratFuncDerivative hConicParamX +
          (4 * hConicParamX ^ 2 +
            4 * hConicParamCapitalW) *
            ratFuncDerivative hConicParamCapitalW := by
    calc
      (4 : RatFunc K) * (1 + hConicParamW) *
          ratFuncDerivative hConicParamW =
        (4 + 4 * hConicParamW) *
          ratFuncDerivative hConicParamW := by ring
      _ = _ := by
        simpa [hQPartialX, hQPartialW] using hQderivative
  constructor
  · simp only [hPPartialX, hPPartialW]
    rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
    exact (eq_div_iff hdw).2 hPclean
  · simp only [hQPartialX, hQPartialW]
    rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
    exact (eq_div_iff hdw).2 hQclean

/-- The derivative with respect to the conic function `w`. -/
@[expose]
noncomputable def hRatFuncDerivativeInW (f : RatFunc K) : RatFunc K :=
  ratFuncDerivative f /
    ratFuncDerivative (hConicParamW (K := K))

/-- Under the two Jacobian quotient identities, the Cramer rational function
is the derivative of the conic difference with respect to `w`. The hypotheses
state the nonvanishing needed for the quotient and for the second Cramer
formula. -/
theorem hDerivativeRatFunc_eq_hRatFuncDerivativeInW
    (R LambdaP LambdaQ : MvPolynomial (Fin 2) K)
    (hLambdaP :
      hFormJacobian hPForm R = hFormW ^ 2 * LambdaP)
    (hLambdaQ :
      hFormJacobian hQForm R = hFormW ^ 2 * LambdaQ)
    (hdw : ratFuncDerivative (hConicParamW (K := K)) ≠ 0)
    (hcapitalW : hConicParamCapitalW (K := K) ≠ 0) :
    hDerivativeRatFunc LambdaP LambdaQ =
      hRatFuncDerivativeInW (hConicDifference R) := by
  have hw : hConicParamW (K := K) ≠ 0 := by
    intro hw
    rw [hw, ratFuncDerivative_zero] at hdw
    exact hdw rfl
  have hdifference :
      hRatFuncDerivativeInW (hConicDifference R) =
        hFormEval 1 hConicParamW (MvPolynomial.pderiv 1 R) -
          (hFormEval hConicParamX hConicParamCapitalW
                (MvPolynomial.pderiv 0 R) *
              (ratFuncDerivative hConicParamX /
                ratFuncDerivative hConicParamW) +
            hFormEval hConicParamX hConicParamCapitalW
                (MvPolynomial.pderiv 1 R) *
              (ratFuncDerivative hConicParamCapitalW /
                ratFuncDerivative hConicParamW)) := by
    simp only [hRatFuncDerivativeInW, hConicDifference,
      hFirstConicPullback, hSecondConicPullback,
      ratFuncDerivative_sub, ratFuncDerivative_hFormEval,
      ratFuncDerivative_one, mul_zero]
    field_simp [hdw]
    ring
  obtain ⟨hPtangent, hQtangent⟩ :=
    h_conic_param_derivative_tangent (K := K) hdw
  have hPfirst := hFormEval_jacobian_quotient_P
    R LambdaP (1 : RatFunc K) hConicParamW hLambdaP hw
  have hPsecond := hFormEval_jacobian_quotient_P
    R LambdaP hConicParamX hConicParamCapitalW hLambdaP hcapitalW
  have hQfirst := hFormEval_jacobian_quotient_Q
    R LambdaQ (1 : RatFunc K) hConicParamW hLambdaQ hw
  have hQsecond := hFormEval_jacobian_quotient_Q
    R LambdaQ hConicParamX hConicParamCapitalW hLambdaQ hcapitalW
  have hcramer := h_cramer_difference_identity
    (K := RatFunc K)
    (w := hConicParamW) (X := hConicParamX)
    (W := hConicParamCapitalW)
    (R_x := hFormEval 1 hConicParamW (MvPolynomial.pderiv 0 R))
    (R_w := hFormEval 1 hConicParamW (MvPolynomial.pderiv 1 R))
    (S_x := hFormEval hConicParamX hConicParamCapitalW
      (MvPolynomial.pderiv 0 R))
    (S_w := hFormEval hConicParamX hConicParamCapitalW
      (MvPolynomial.pderiv 1 R))
    (dX := ratFuncDerivative hConicParamX /
      ratFuncDerivative hConicParamW)
    (dW := ratFuncDerivative hConicParamCapitalW /
      ratFuncDerivative hConicParamW)
    hw hcapitalW hPtangent hQtangent
  rw [← hQfirst, ← hQsecond, ← hPfirst, ← hPsecond] at hcramer
  have hcramer' :
      hFormEval 1 hConicParamW (MvPolynomial.pderiv 1 R) -
          (hFormEval hConicParamX hConicParamCapitalW
                (MvPolynomial.pderiv 0 R) *
              (ratFuncDerivative hConicParamX /
                ratFuncDerivative hConicParamW) +
            hFormEval hConicParamX hConicParamCapitalW
                (MvPolynomial.pderiv 1 R) *
              (ratFuncDerivative hConicParamCapitalW /
                ratFuncDerivative hConicParamW)) =
        hDerivativeRatFunc LambdaP LambdaQ := by
    simpa only [hDerivativeRatFunc, hConicDifference,
      hFirstConicPullback, hSecondConicPullback] using hcramer
  exact hcramer'.symm.trans hdifference.symm

/-- At every parameter value above `X = 1`, the simple zero of `w` supplies
the nonvanishing hypotheses in the derivative identity. -/
theorem hDerivativeRatFunc_eq_hRatFuncDerivativeInW_at_one
    (a : K) (ha : a ^ 2 + 2 * a + 4 = 0)
    (R LambdaP LambdaQ : MvPolynomial (Fin 2) K)
    (hLambdaP :
      hFormJacobian hPForm R = hFormW ^ 2 * LambdaP)
    (hLambdaQ :
      hFormJacobian hQForm R = hFormW ^ 2 * LambdaQ) :
    hDerivativeRatFunc LambdaP LambdaQ =
      hRatFuncDerivativeInW (hConicDifference R) := by
  have hwOrder := h_conic_param_w_order_at_one (K := K) ha
  have hdwOrder := h_finite_order_ratFuncDerivative_of_pos
    a (hConicParamW (K := K)) 1 (by norm_num) hwOrder
  have hdw : ratFuncDerivative (hConicParamW (K := K)) ≠ 0 :=
    h_ratFunc_ne_zero_of_finite_order hdwOrder
  have hcapitalW : hConicParamCapitalW (K := K) ≠ 0 :=
    h_ratFunc_ne_zero_of_finite_order
      (h_conic_param_capitalW_order_at_one (K := K) ha)
  exact hDerivativeRatFunc_eq_hRatFuncDerivativeInW
    R LambdaP LambdaQ hLambdaP hLambdaQ hdw hcapitalW

/-- At every point above `X = 1`, an exact positive order `k` of the conic
difference gives exact order `k - 1` for the Cramer rational function. -/
theorem h_finite_order_hDerivativeRatFunc_at_one
    (a : K) (ha : a ^ 2 + 2 * a + 4 = 0)
    (R LambdaP LambdaQ : MvPolynomial (Fin 2) K)
    (hLambdaP :
      hFormJacobian hPForm R = hFormW ^ 2 * LambdaP)
    (hLambdaQ :
      hFormJacobian hQForm R = hFormW ^ 2 * LambdaQ)
    (k : ℕ) (hk : 0 < k)
    (horder : hFiniteOrderAt a (hConicDifference R) =
      WithZero.exp (k : ℤ)) :
    hFiniteOrderAt a (hDerivativeRatFunc LambdaP LambdaQ) =
      WithZero.exp ((k - 1 : ℕ) : ℤ) := by
  rw [hDerivativeRatFunc_eq_hRatFuncDerivativeInW_at_one
    a ha R LambdaP LambdaQ hLambdaP hLambdaQ,
    hRatFuncDerivativeInW, map_div₀,
    h_finite_order_ratFuncDerivative_of_pos a
      (hConicDifference R) k hk horder,
    h_finite_order_ratFuncDerivative_of_pos a
      (hConicParamW (K := K)) 1 (by norm_num)
        (h_conic_param_w_order_at_one (K := K) ha)]
  exact div_one _

end OnLeConjecture.DThree
