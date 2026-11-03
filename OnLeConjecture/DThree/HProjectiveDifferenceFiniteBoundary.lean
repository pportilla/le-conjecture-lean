/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HProjectiveDifferenceBoundary

/-!
# Finite boundary values of the projective H difference section

At a root of the parametrization denominator, multiplication by its weighted
degree rescales the affine conic pair to a finite projective pair. A root of
the fixed profile numerator then gives equality of the third form at that
pair.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial
open scoped Polynomial WithZero

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem h_ratFunc_eval_algebraMap_id
    (a : K) (p : K[X]) :
    RatFunc.eval (RingHom.id K) a
        (algebraMap K[X] (RatFunc K) p) = p.eval a := by
  simp

omit [CharZero K] in
/-- Evaluation of a weighted homogeneous form commutes with weighted scalar
multiplication. -/
theorem hFormEval_weighted_smul
    {A : Type*} [CommRing A] [Algebra K A]
    (F : MvPolynomial (Fin 2) K) (N : ℕ)
    (hF : F.IsWeightedHomogeneous hFormWeight N)
    (lambda x w : A) :
    hFormEval (lambda * x) (lambda ^ 2 * w) F =
      lambda ^ N * hFormEval x w F := by
  induction hF using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp [hFormEval]
  | add F G hF hG ihF ihG =>
      rw [show hFormEval (lambda * x) (lambda ^ 2 * w) (F + G) =
          hFormEval (lambda * x) (lambda ^ 2 * w) F +
            hFormEval (lambda * x) (lambda ^ 2 * w) G by
        simp [hFormEval], ihF, ihG,
        show hFormEval x w (F + G) =
          hFormEval x w F + hFormEval x w G by
            simp [hFormEval], mul_add]
  | monomial d c hd =>
      have hweight : d 0 + 2 * d 1 = N := by
        rw [h_form_weight_apply] at hd
        exact hd
      rw [hFormEval_monomial, hFormEval_monomial]
      simp only [mul_pow]
      rw [← pow_mul]
      calc
        algebraMap K A c * (lambda ^ d 0 * x ^ d 0) *
              (lambda ^ (2 * d 1) * w ^ d 1) =
            lambda ^ (d 0 + 2 * d 1) *
              (algebraMap K A c * x ^ d 0 * w ^ d 1) := by
          rw [pow_add]
          ring
        _ = lambda ^ N *
            (algebraMap K A c * x ^ d 0 * w ^ d 1) := by
          rw [hweight]

omit [CharZero K] in
/-- The first `H` coordinate has weighted degree three. -/
theorem hP_weighted_smul (lambda x w : K) :
    hP (lambda * x) (lambda ^ 2 * w) =
      lambda ^ 3 * hP x w := by
  simp only [hP, mul_pow]
  ring

omit [CharZero K] in
/-- The second `H` coordinate has weighted degree four. -/
theorem hQ_weighted_smul (lambda x w : K) :
    hQ (lambda * x) (lambda ^ 2 * w) =
      lambda ^ 4 * hQ x w := by
  simp only [hQ, mul_pow]
  ring

theorem h_conic_profile_linear_ne_zero :
    (3 * (Polynomial.X + 1) : K[X]) ≠ 0 := by
  exact mul_ne_zero (by norm_num) h_conic_param_linear_ne_zero

/-- Multiplication by the parametrization denominator clears the denominator
of the conic coordinate `X`. -/
theorem h_conic_param_denominator_mul_x :
    algebraMap K[X] (RatFunc K) hConicParamDenominator *
        hConicParamX =
      algebraMap K[X] (RatFunc K) hConicParamXNumerator := by
  rw [hConicParamX]
  field_simp [RatFunc.algebraMap_ne_zero
    h_conic_param_denominator_ne_zero]

/-- The square of the parametrization denominator leaves only the linear
boundary denominator in the conic function `w`. -/
theorem h_conic_param_denominator_sq_mul_w :
    algebraMap K[X] (RatFunc K) hConicParamDenominator ^ 2 *
        hConicParamW =
      algebraMap K[X] (RatFunc K)
          (-hConicParamOneFactor * hConicParamWFactor) /
        algebraMap K[X] (RatFunc K) (3 * (Polynomial.X + 1)) := by
  simp only [hConicParamW, hConicParamFunctionDenominator,
    map_mul, map_pow]
  field_simp [RatFunc.algebraMap_ne_zero
    h_conic_param_denominator_ne_zero,
    RatFunc.algebraMap_ne_zero
      (h_conic_profile_linear_ne_zero (K := K))]

/-- The square of the parametrization denominator leaves only the linear
boundary denominator in the conic function `W`. -/
theorem h_conic_param_denominator_sq_mul_capitalW :
    algebraMap K[X] (RatFunc K) hConicParamDenominator ^ 2 *
        hConicParamCapitalW =
      algebraMap K[X] (RatFunc K)
          (-hConicParamOneFactor * hConicParamCapitalWFactor) /
        algebraMap K[X] (RatFunc K) (3 * (Polynomial.X + 1)) := by
  simp only [hConicParamCapitalW, hConicParamFunctionDenominator,
    map_mul, map_pow]
  field_simp [RatFunc.algebraMap_ne_zero
    h_conic_param_denominator_ne_zero,
    RatFunc.algebraMap_ne_zero
      (h_conic_profile_linear_ne_zero (K := K))]

/-- Rescaling by the parametrization denominator gives two finite rational
points in one fibre of the `H` pair. -/
theorem h_scaled_infinity_conic_fibre :
    hP (algebraMap K[X] (RatFunc K) hConicParamDenominator)
          (algebraMap K[X] (RatFunc K)
              (-hConicParamOneFactor * hConicParamWFactor) /
            algebraMap K[X] (RatFunc K) (3 * (Polynomial.X + 1))) =
        hP (algebraMap K[X] (RatFunc K) hConicParamXNumerator)
          (algebraMap K[X] (RatFunc K)
              (-hConicParamOneFactor * hConicParamCapitalWFactor) /
            algebraMap K[X] (RatFunc K) (3 * (Polynomial.X + 1))) ∧
      hQ (algebraMap K[X] (RatFunc K) hConicParamDenominator)
          (algebraMap K[X] (RatFunc K)
              (-hConicParamOneFactor * hConicParamWFactor) /
            algebraMap K[X] (RatFunc K) (3 * (Polynomial.X + 1))) =
        hQ (algebraMap K[X] (RatFunc K) hConicParamXNumerator)
          (algebraMap K[X] (RatFunc K)
              (-hConicParamOneFactor * hConicParamCapitalWFactor) /
            algebraMap K[X] (RatFunc K) (3 * (Polynomial.X + 1))) := by
  let d : RatFunc K :=
    algebraMap K[X] (RatFunc K) hConicParamDenominator
  obtain ⟨hPfiber, hQfiber⟩ :=
    h_conic_param_fibre_equations (K := K)
  have hPscaled :
      hP d (d ^ 2 * hConicParamW) =
        hP (d * hConicParamX)
          (d ^ 2 * hConicParamCapitalW) := by
    calc
      hP d (d ^ 2 * hConicParamW) =
          hP (d * 1) (d ^ 2 * hConicParamW) := by rw [mul_one]
      _ = d ^ 3 * hP 1 hConicParamW :=
        hP_weighted_smul d 1 hConicParamW
      _ = d ^ 3 * hP hConicParamX hConicParamCapitalW := by
        rw [hPfiber]
      _ = hP (d * hConicParamX)
          (d ^ 2 * hConicParamCapitalW) :=
        (hP_weighted_smul d hConicParamX
          hConicParamCapitalW).symm
  have hQscaled :
      hQ d (d ^ 2 * hConicParamW) =
        hQ (d * hConicParamX)
          (d ^ 2 * hConicParamCapitalW) := by
    calc
      hQ d (d ^ 2 * hConicParamW) =
          hQ (d * 1) (d ^ 2 * hConicParamW) := by rw [mul_one]
      _ = d ^ 4 * hQ 1 hConicParamW :=
        hQ_weighted_smul d 1 hConicParamW
      _ = d ^ 4 * hQ hConicParamX hConicParamCapitalW := by
        rw [hQfiber]
      _ = hQ (d * hConicParamX)
          (d ^ 2 * hConicParamCapitalW) :=
        (hQ_weighted_smul d hConicParamX
          hConicParamCapitalW).symm
  simpa only [d, h_conic_param_denominator_mul_x,
    h_conic_param_denominator_sq_mul_w,
    h_conic_param_denominator_sq_mul_capitalW] using
      And.intro hPscaled hQscaled

/-- The weighted rescaling of the conic difference is regular at the roots
of the parametrization denominator. -/
theorem h_scaled_infinity_conic_difference
    (F : MvPolynomial (Fin 2) K) (N : ℕ)
    (hF : F.IsWeightedHomogeneous hFormWeight N) :
    algebraMap K[X] (RatFunc K) hConicParamDenominator ^ N *
        hConicDifference F =
      hFormEval
          (algebraMap K[X] (RatFunc K) hConicParamDenominator)
          (algebraMap K[X] (RatFunc K)
              (-hConicParamOneFactor * hConicParamWFactor) /
            algebraMap K[X] (RatFunc K) (3 * (Polynomial.X + 1))) F -
        hFormEval
          (algebraMap K[X] (RatFunc K) hConicParamXNumerator)
          (algebraMap K[X] (RatFunc K)
              (-hConicParamOneFactor * hConicParamCapitalWFactor) /
            algebraMap K[X] (RatFunc K) (3 * (Polynomial.X + 1))) F := by
  let d : RatFunc K :=
    algebraMap K[X] (RatFunc K) hConicParamDenominator
  calc
    d ^ N * hConicDifference F =
        d ^ N * hFormEval 1 hConicParamW F -
          d ^ N * hFormEval hConicParamX hConicParamCapitalW F := by
      simp only [hConicDifference, hFirstConicPullback,
        hSecondConicPullback]
      ring
    _ = hFormEval d (d ^ 2 * hConicParamW) F -
        hFormEval (d * hConicParamX)
          (d ^ 2 * hConicParamCapitalW) F := by
      have hfirst := hFormEval_weighted_smul F N hF
        d 1 hConicParamW
      have hsecond := hFormEval_weighted_smul F N hF
        d hConicParamX hConicParamCapitalW
      rw [mul_one] at hfirst
      rw [← hfirst, ← hsecond]
    _ = _ := by
      rw [h_conic_param_denominator_mul_x,
        h_conic_param_denominator_sq_mul_w,
        h_conic_param_denominator_sq_mul_capitalW]

/-- A root of the fixed profile numerator at a root of `m² + 2` gives a
finite off diagonal projective fibre zero after weighted rescaling. -/
theorem exists_h_projective_difference_zero_at_infinity_boundary
    (N : ℕ) (F : MvPolynomial (Fin 2) K)
    (hF : F.IsWeightedHomogeneous hFormWeight N)
    (p : K[X]) (z : K)
    (hrepresentation :
      hConicDifference F =
        algebraMap K[X] (RatFunc K) p /
          algebraMap K[X] (RatFunc K)
            (hPoleProfileDenominator (N / 2) N))
    (hz : z ^ 2 + 2 = 0)
    (hroot : p.IsRoot z) :
    ∃ w X W : K,
      w ≠ 0 ∧ X ≠ 0 ∧
      hP 0 w = hP X W ∧ hQ 0 w = hQ X W ∧
        hFormEval 0 w F = hFormEval X W F := by
  let linear : K[X] := 3 * (Polynomial.X + 1)
  let firstNumerator : K[X] :=
    -hConicParamOneFactor * hConicParamWFactor
  let secondNumerator : K[X] :=
    -hConicParamOneFactor * hConicParamCapitalWFactor
  let w : K := firstNumerator.eval z / linear.eval z
  let x : K := hConicParamXNumerator.eval z
  let W : K := secondNumerator.eval z / linear.eval z
  have hlinear : linear.eval z ≠ 0 := by
    simp only [linear, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    exact mul_ne_zero (by norm_num)
      (h_conic_param_infinity_root_add_one_ne_zero hz)
  have hfirstNumerator : firstNumerator.eval z ≠ 0 := by
    simpa only [firstNumerator, Polynomial.eval_mul,
      Polynomial.eval_neg, hConicParamOneFactor,
      hConicParamWFactor, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_ofNat] using
        h_conic_param_w_numerator_at_infinity_ne_zero (K := K) hz
  have hx : x ≠ 0 := by
    simpa [x, hConicParamXNumerator] using
      h_conic_param_x_numerator_at_infinity_ne_zero (K := K) hz
  have hw : w ≠ 0 := div_ne_zero hfirstNumerator hlinear
  have hscaledRepresentation :
      algebraMap K[X] (RatFunc K) hConicParamDenominator ^ N *
          hConicDifference F =
        algebraMap K[X] (RatFunc K) p /
          algebraMap K[X] (RatFunc K) (linear ^ (N / 2)) := by
    rw [hrepresentation, hPoleProfileDenominator]
    simp only [linear, map_mul, map_pow]
    field_simp [RatFunc.algebraMap_ne_zero
      h_conic_param_denominator_ne_zero,
      RatFunc.algebraMap_ne_zero
        (h_conic_profile_linear_ne_zero (K := K))]
  have hscaledZero :
      RatFunc.eval (RingHom.id K) z
          (algebraMap K[X] (RatFunc K) hConicParamDenominator ^ N *
            hConicDifference F) = 0 := by
    rw [hscaledRepresentation,
      h_ratFunc_eval_algebraMap_div z p (linear ^ (N / 2))]
    · have hrootEval : p.eval z = 0 := hroot
      rw [hrootEval, zero_div]
    · simpa [Polynomial.eval_pow] using
        pow_ne_zero (N / 2) hlinear
  have hfirstRegular :
      HRatFuncRegularAt z
        (algebraMap K[X] (RatFunc K) firstNumerator /
          algebraMap K[X] (RatFunc K) linear) :=
    hRatFuncRegularAt_of_denom_dvd
      (RatFunc.denom_div_dvd firstNumerator linear) hlinear
  have hsecondRegular :
      HRatFuncRegularAt z
        (algebraMap K[X] (RatFunc K) secondNumerator /
          algebraMap K[X] (RatFunc K) linear) :=
    hRatFuncRegularAt_of_denom_dvd
      (RatFunc.denom_div_dvd secondNumerator linear) hlinear
  have hdenRegular := hRatFuncRegularAt_algebraMap
    (K := K) z hConicParamDenominator
  have hxRegular := hRatFuncRegularAt_algebraMap
    (K := K) z hConicParamXNumerator
  have hthird : hFormEval 0 w F = hFormEval x W F := by
    rw [h_scaled_infinity_conic_difference F N hF] at hscaledZero
    have hfirstFormRegular := hRatFuncRegularAt_hFormEval z
      (algebraMap K[X] (RatFunc K) hConicParamDenominator)
      (algebraMap K[X] (RatFunc K) firstNumerator /
        algebraMap K[X] (RatFunc K) linear) F
      hdenRegular hfirstRegular
    have hsecondFormRegular := hRatFuncRegularAt_hFormEval z
      (algebraMap K[X] (RatFunc K) hConicParamXNumerator)
      (algebraMap K[X] (RatFunc K) secondNumerator /
        algebraMap K[X] (RatFunc K) linear) F
      hxRegular hsecondRegular
    rw [h_ratFunc_eval_sub z _ _ hfirstFormRegular hsecondFormRegular,
      h_ratFunc_eval_hFormEval z _ _ F hdenRegular hfirstRegular,
      h_ratFunc_eval_hFormEval z _ _ F hxRegular hsecondRegular,
      h_ratFunc_eval_algebraMap_div z firstNumerator linear hlinear,
      h_ratFunc_eval_algebraMap_div z secondNumerator linear hlinear,
      h_ratFunc_eval_algebraMap_id] at hscaledZero
    have hscaledZero' := sub_eq_zero.mp hscaledZero
    simpa [w, x, W, hConicParamDenominator, hz] using hscaledZero'
  have hfibre := h_scaled_infinity_conic_fibre (K := K)
  have hPidentity := hfibre.1
  have hQidentity := hfibre.2
  have hPfirstRegular := hRatFuncRegularAt_hFormEval z
    (algebraMap K[X] (RatFunc K) hConicParamDenominator)
    (algebraMap K[X] (RatFunc K) firstNumerator /
      algebraMap K[X] (RatFunc K) linear) hPForm
    hdenRegular hfirstRegular
  have hPsecondRegular := hRatFuncRegularAt_hFormEval z
    (algebraMap K[X] (RatFunc K) hConicParamXNumerator)
    (algebraMap K[X] (RatFunc K) secondNumerator /
      algebraMap K[X] (RatFunc K) linear) hPForm
    hxRegular hsecondRegular
  have hQfirstRegular := hRatFuncRegularAt_hFormEval z
    (algebraMap K[X] (RatFunc K) hConicParamDenominator)
    (algebraMap K[X] (RatFunc K) firstNumerator /
      algebraMap K[X] (RatFunc K) linear) hQForm
    hdenRegular hfirstRegular
  have hQsecondRegular := hRatFuncRegularAt_hFormEval z
    (algebraMap K[X] (RatFunc K) hConicParamXNumerator)
    (algebraMap K[X] (RatFunc K) secondNumerator /
      algebraMap K[X] (RatFunc K) linear) hQForm
    hxRegular hsecondRegular
  have hPeval := congrArg (RatFunc.eval (RingHom.id K) z) hPidentity
  have hQeval := congrArg (RatFunc.eval (RingHom.id K) z) hQidentity
  rw [← hFormEval_hPForm (K := K),
    ← hFormEval_hPForm (K := K),
    h_ratFunc_eval_hFormEval z _ _ hPForm hdenRegular hfirstRegular,
    h_ratFunc_eval_hFormEval z _ _ hPForm hxRegular hsecondRegular,
    h_ratFunc_eval_algebraMap_div z firstNumerator linear hlinear,
    h_ratFunc_eval_algebraMap_div z secondNumerator linear hlinear,
    h_ratFunc_eval_algebraMap_id] at hPeval
  rw [← hFormEval_hQForm (K := K),
    ← hFormEval_hQForm (K := K),
    h_ratFunc_eval_hFormEval z _ _ hQForm hdenRegular hfirstRegular,
    h_ratFunc_eval_hFormEval z _ _ hQForm hxRegular hsecondRegular,
    h_ratFunc_eval_algebraMap_div z firstNumerator linear hlinear,
    h_ratFunc_eval_algebraMap_div z secondNumerator linear hlinear,
    h_ratFunc_eval_algebraMap_id] at hQeval
  refine ⟨w, x, W, hw, hx, ?_, ?_, hthird⟩
  · simpa [w, x, W, hConicParamDenominator, hz,
      hFormEval_hPForm] using hPeval
  · simpa [w, x, W, hConicParamDenominator, hz,
      hFormEval_hQForm] using hQeval

end OnLeConjecture.DThree
