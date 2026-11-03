/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HReciprocalCollision
public import OnLeConjecture.DThree.HProjectiveDifferencePoleBoundary

/-!
# Analytic collisions at the pole of the H profile

The ramified parameter `3(m + 1) = lambda²` removes the simple poles of the
two weighted second coordinates.  The resulting weighted fibre pair is
analytic at `lambda = 0`.
-/

public section

open Filter Set
open scoped Topology Polynomial

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

/-- The ramified profile parameter at the pole. -/
@[expose]
noncomputable def hPoleCollisionParameter (lambda : ℂ) : ℂ :=
  -1 + lambda ^ 2 / 3

/-- The first first coordinate after ramified weighted rescaling. -/
@[expose]
noncomputable def hPoleCollisionFirstX (lambda : ℂ) : ℂ := lambda

/-- The first weighted second coordinate after removing the pole. -/
@[expose]
noncomputable def hPoleCollisionW (lambda : ℂ) : ℂ :=
  (-hConicParamOneFactor * hConicParamWFactor).eval
      (hPoleCollisionParameter lambda) /
    hConicParamDenominator.eval (hPoleCollisionParameter lambda) ^ 2

/-- The second first coordinate after ramified weighted rescaling. -/
@[expose]
noncomputable def hPoleCollisionSecondX (lambda : ℂ) : ℂ :=
  lambda *
    (hConicParamXNumerator.eval (hPoleCollisionParameter lambda) /
      hConicParamDenominator.eval (hPoleCollisionParameter lambda))

/-- The second weighted second coordinate after removing the pole. -/
@[expose]
noncomputable def hPoleCollisionCapitalW (lambda : ℂ) : ℂ :=
  (-hConicParamOneFactor * hConicParamCapitalWFactor).eval
      (hPoleCollisionParameter lambda) /
    hConicParamDenominator.eval (hPoleCollisionParameter lambda) ^ 2

theorem analyticAt_hPoleCollisionParameter :
    AnalyticAt ℂ hPoleCollisionParameter 0 := by
  have hthree : AnalyticAt ℂ (fun _ : ℂ ↦ (3 : ℂ)) 0 :=
    analyticAt_const
  exact analyticAt_const.add
    ((analyticAt_id.pow 2).div hthree (by norm_num))

theorem analyticAt_polynomial_eval_hPoleCollisionParameter
    (p : ℂ[X]) :
    AnalyticAt ℂ
      (fun lambda : ℂ ↦ p.eval (hPoleCollisionParameter lambda)) 0 := by
  have hthree : AnalyticAt ℂ (fun _ : ℂ ↦ (3 : ℂ)) 0 :=
    analyticAt_const
  have hsmall : AnalyticAt ℂ
      (fun lambda : ℂ ↦ lambda ^ 2 / 3) 0 :=
    (analyticAt_id.pow 2).div hthree (by norm_num)
  have houter : AnalyticAt ℂ
      (fun u : ℂ ↦ p.eval ((-1 : ℂ) + u)) 0 :=
    analyticAt_polynomial_eval_add p (-1)
  have houterAt : AnalyticAt ℂ
      (fun u : ℂ ↦ p.eval ((-1 : ℂ) + u))
        ((0 : ℂ) ^ 2 / 3) := by
    simpa using houter
  have hcomposition := AnalyticAt.fun_comp (x := (0 : ℂ))
    houterAt hsmall
  simpa only [hPoleCollisionParameter] using hcomposition

theorem analyticAt_hPoleCollisionFirstX :
    AnalyticAt ℂ hPoleCollisionFirstX 0 := analyticAt_id

theorem analyticAt_hPoleCollisionW :
    AnalyticAt ℂ hPoleCollisionW 0 := by
  let numerator : ℂ[X] :=
    -hConicParamOneFactor * hConicParamWFactor
  have hnum : AnalyticAt ℂ
      (fun lambda : ℂ ↦
        numerator.eval
          (hPoleCollisionParameter lambda)) 0 := by
    exact analyticAt_polynomial_eval_hPoleCollisionParameter numerator
  have hden : AnalyticAt ℂ
      (fun lambda : ℂ ↦
        hConicParamDenominator.eval
          (hPoleCollisionParameter lambda) ^ 2) 0 := by
    have hdenBase :=
      analyticAt_polynomial_eval_hPoleCollisionParameter
        (hConicParamDenominator (K := ℂ))
    exact hdenBase.pow 2
  have hdenZero : hConicParamDenominator.eval
      (hPoleCollisionParameter 0) ^ 2 ≠ 0 := by
    norm_num [hPoleCollisionParameter, hConicParamDenominator]
  exact hnum.div hden hdenZero

theorem analyticAt_hPoleCollisionSecondX :
    AnalyticAt ℂ hPoleCollisionSecondX 0 := by
  have hnum : AnalyticAt ℂ
      (fun lambda : ℂ ↦
        hConicParamXNumerator.eval (hPoleCollisionParameter lambda)) 0 := by
    exact analyticAt_polynomial_eval_hPoleCollisionParameter
      (hConicParamXNumerator (K := ℂ))
  have hden : AnalyticAt ℂ
      (fun lambda : ℂ ↦
        hConicParamDenominator.eval (hPoleCollisionParameter lambda)) 0 := by
    exact analyticAt_polynomial_eval_hPoleCollisionParameter
      (hConicParamDenominator (K := ℂ))
  have hdenZero : hConicParamDenominator.eval
      (hPoleCollisionParameter 0) ≠ 0 := by
    norm_num [hPoleCollisionParameter, hConicParamDenominator]
  exact analyticAt_id.mul (hnum.div hden hdenZero)

theorem analyticAt_hPoleCollisionCapitalW :
    AnalyticAt ℂ hPoleCollisionCapitalW 0 := by
  let numerator : ℂ[X] :=
    -hConicParamOneFactor * hConicParamCapitalWFactor
  have hnum : AnalyticAt ℂ
      (fun lambda : ℂ ↦
        numerator.eval
          (hPoleCollisionParameter lambda)) 0 := by
    exact analyticAt_polynomial_eval_hPoleCollisionParameter numerator
  have hden : AnalyticAt ℂ
      (fun lambda : ℂ ↦
        hConicParamDenominator.eval
          (hPoleCollisionParameter lambda) ^ 2) 0 := by
    have hdenBase :=
      analyticAt_polynomial_eval_hPoleCollisionParameter
        (hConicParamDenominator (K := ℂ))
    exact hdenBase.pow 2
  have hdenZero : hConicParamDenominator.eval
      (hPoleCollisionParameter 0) ^ 2 ≠ 0 := by
    norm_num [hPoleCollisionParameter, hConicParamDenominator]
  exact hnum.div hden hdenZero

/-- The ramified coordinates specialize to the two pole boundary points. -/
theorem h_pole_collision_values_at_zero :
    hPoleCollisionFirstX 0 = 0 ∧
      hPoleCollisionW 0 = -3 ∧
      hPoleCollisionSecondX 0 = 0 ∧
      hPoleCollisionCapitalW 0 = 3 := by
  constructor
  · rfl
  constructor
  · norm_num [hPoleCollisionW, hPoleCollisionParameter,
      hConicParamOneFactor, hConicParamWFactor,
      hConicParamDenominator]
  constructor
  · norm_num [hPoleCollisionSecondX]
  · norm_num [hPoleCollisionCapitalW, hPoleCollisionParameter,
      hConicParamOneFactor, hConicParamCapitalWFactor,
      hConicParamDenominator]

/-- The ramified rescaled coordinates lie in one fibre whenever the conic
denominator is nonzero. -/
theorem h_pole_collision_fibre_at
    (lambda : ℂ)
    (hden : hConicParamDenominator.eval
      (hPoleCollisionParameter lambda) ≠ 0) :
    hP (hPoleCollisionFirstX lambda) (hPoleCollisionW lambda) =
        hP (hPoleCollisionSecondX lambda)
          (hPoleCollisionCapitalW lambda) ∧
      hQ (hPoleCollisionFirstX lambda) (hPoleCollisionW lambda) =
        hQ (hPoleCollisionSecondX lambda)
          (hPoleCollisionCapitalW lambda) := by
  by_cases hlambda : lambda = 0
  · subst lambda
    norm_num [hPoleCollisionFirstX, hPoleCollisionW,
      hPoleCollisionSecondX, hPoleCollisionCapitalW,
      hPoleCollisionParameter, hConicParamOneFactor,
      hConicParamWFactor, hConicParamCapitalWFactor,
      hConicParamXNumerator, hConicParamDenominator, hP, hQ]
  · let m : ℂ := hPoleCollisionParameter lambda
    have hm : m + 1 = lambda ^ 2 / 3 := by
      simp only [m, hPoleCollisionParameter]
      ring
    have hlinear : m + 1 ≠ 0 := by
      rw [hm]
      exact div_ne_zero (pow_ne_zero 2 hlambda) (by norm_num)
    obtain ⟨hxRegular, hwRegular, hcapitalWRegular⟩ :=
      h_conic_param_regular_at m hlinear (by simpa [m] using hden)
    let originalX : ℂ :=
      RatFunc.eval (RingHom.id ℂ) m (hConicParamX (K := ℂ))
    let originalW : ℂ :=
      RatFunc.eval (RingHom.id ℂ) m (hConicParamW (K := ℂ))
    let originalCapitalW : ℂ :=
      RatFunc.eval (RingHom.id ℂ) m
        (hConicParamCapitalW (K := ℂ))
    have hfibre := h_conic_param_eval_fibre m hlinear
      (by simpa [m] using hden)
    have hscaledX :
        lambda * originalX = hPoleCollisionSecondX lambda := by
      simp only [originalX]
      rw [hConicParamX,
        h_ratFunc_eval_algebraMap_div m hConicParamXNumerator
          hConicParamDenominator (by simpa [m] using hden)]
      rfl
    have hellRegular : HRatFuncRegularAt m
        (algebraMap ℂ[X] (RatFunc ℂ)
          (3 * (Polynomial.X + 1))) :=
      hRatFuncRegularAt_algebraMap m (3 * (Polynomial.X + 1))
    have hscaledW :
        lambda ^ 2 * originalW = hPoleCollisionW lambda := by
      have heval := congrArg (RatFunc.eval (RingHom.id ℂ) m)
        (h_conic_profile_linear_mul_w (K := ℂ))
      rw [h_ratFunc_eval_mul_regular m _ _ hellRegular hwRegular,
        h_ratFunc_eval_algebraMap_id,
        h_ratFunc_eval_algebraMap_div m
          (-hConicParamOneFactor * hConicParamWFactor)
          (hConicParamDenominator ^ 2)
          (by simpa [Polynomial.eval_pow, m] using
            pow_ne_zero 2 hden)] at heval
      have hell :
          (3 * (Polynomial.X + 1) : ℂ[X]).eval m = lambda ^ 2 := by
        simp only [Polynomial.eval_mul, Polynomial.eval_ofNat,
          Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
        rw [hm]
        field_simp
      rw [hell] at heval
      simpa only [originalW, hPoleCollisionW, m,
        Polynomial.eval_pow] using heval
    have hscaledCapitalW :
        lambda ^ 2 * originalCapitalW =
          hPoleCollisionCapitalW lambda := by
      have heval := congrArg (RatFunc.eval (RingHom.id ℂ) m)
        (h_conic_profile_linear_mul_capitalW (K := ℂ))
      rw [h_ratFunc_eval_mul_regular m _ _ hellRegular hcapitalWRegular,
        h_ratFunc_eval_algebraMap_id,
        h_ratFunc_eval_algebraMap_div m
          (-hConicParamOneFactor * hConicParamCapitalWFactor)
          (hConicParamDenominator ^ 2)
          (by simpa [Polynomial.eval_pow, m] using
            pow_ne_zero 2 hden)] at heval
      have hell :
          (3 * (Polynomial.X + 1) : ℂ[X]).eval m = lambda ^ 2 := by
        simp only [Polynomial.eval_mul, Polynomial.eval_ofNat,
          Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
        rw [hm]
        field_simp
      rw [hell] at heval
      simpa only [originalCapitalW, hPoleCollisionCapitalW, m,
        Polynomial.eval_pow] using heval
    constructor
    · calc
        hP (hPoleCollisionFirstX lambda) (hPoleCollisionW lambda) =
            hP (lambda * 1) (lambda ^ 2 * originalW) := by
          rw [hPoleCollisionFirstX, mul_one, hscaledW]
        _ = lambda ^ 3 * hP 1 originalW :=
          hP_weighted_smul lambda 1 originalW
        _ = lambda ^ 3 * hP originalX originalCapitalW := by
          rw [hfibre.1]
        _ = hP (lambda * originalX)
            (lambda ^ 2 * originalCapitalW) :=
          (hP_weighted_smul lambda originalX originalCapitalW).symm
        _ = hP (hPoleCollisionSecondX lambda)
            (hPoleCollisionCapitalW lambda) := by
          rw [hscaledX, hscaledCapitalW]
    · calc
        hQ (hPoleCollisionFirstX lambda) (hPoleCollisionW lambda) =
            hQ (lambda * 1) (lambda ^ 2 * originalW) := by
          rw [hPoleCollisionFirstX, mul_one, hscaledW]
        _ = lambda ^ 4 * hQ 1 originalW :=
          hQ_weighted_smul lambda 1 originalW
        _ = lambda ^ 4 * hQ originalX originalCapitalW := by
          rw [hfibre.2]
        _ = hQ (lambda * originalX)
            (lambda ^ 2 * originalCapitalW) :=
          (hQ_weighted_smul lambda originalX originalCapitalW).symm
        _ = hQ (hPoleCollisionSecondX lambda)
            (hPoleCollisionCapitalW lambda) := by
          rw [hscaledX, hscaledCapitalW]

/-- The third difference in the ramified pole chart is the profile numerator
divided by the remaining conic denominator, with the parity factor of the
weight. -/
theorem h_pole_collision_difference_eq_profile_at
    (N : ℕ) (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (p : ℂ[X])
    (hrepresentation :
      hConicDifference R =
        algebraMap ℂ[X] (RatFunc ℂ) p /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (N / 2) N))
    (hroot : p.IsRoot (-1 : ℂ))
    (lambda : ℂ)
    (hden : hConicParamDenominator.eval
      (hPoleCollisionParameter lambda) ≠ 0) :
    hFormEval (hPoleCollisionFirstX lambda)
          (hPoleCollisionW lambda) R -
        hFormEval (hPoleCollisionSecondX lambda)
          (hPoleCollisionCapitalW lambda) R =
      lambda ^ (N % 2) *
        p.eval (hPoleCollisionParameter lambda) /
          hConicParamDenominator.eval
            (hPoleCollisionParameter lambda) ^ N := by
  by_cases hlambda : lambda = 0
  · subst lambda
    have hrootEval : p.eval (-1 : ℂ) = 0 := hroot
    rcases Nat.even_or_odd N with hEven | hOdd
    · obtain ⟨b, rfl⟩ := hEven
      have hR' : R.IsWeightedHomogeneous hFormWeight (2 * b) := by
        simpa [two_mul] using hR
      have hrepresentation' :
          hConicDifference R =
            algebraMap ℂ[X] (RatFunc ℂ) p /
              algebraMap ℂ[X] (RatFunc ℂ)
                (hPoleProfileDenominator b (2 * b)) := by
        simpa [two_mul, show (b + b) / 2 = b by omega] using
          hrepresentation
      have hequal := hFormEval_eq_at_pole_boundary_of_even_weight
        b R hR' p hrepresentation' hroot
      have hzero : hFormEval 0 (-3 : ℂ) R -
          hFormEval 0 3 R = 0 := sub_eq_zero.mpr hequal
      rw [h_pole_collision_values_at_zero.1,
        h_pole_collision_values_at_zero.2.1,
        h_pole_collision_values_at_zero.2.2.1,
        h_pole_collision_values_at_zero.2.2.2,
        show hPoleCollisionParameter 0 = -1 by
          norm_num [hPoleCollisionParameter],
        hrootEval]
      simpa using hzero
    · have hfirst :=
        hFormEval_zero_first_of_odd_weight R N hR hOdd (-3 : ℂ)
      have hsecond :=
        hFormEval_zero_first_of_odd_weight R N hR hOdd 3
      have hzero : hFormEval 0 (-3 : ℂ) R -
          hFormEval 0 3 R = 0 := by rw [hfirst, hsecond, sub_zero]
      rw [h_pole_collision_values_at_zero.1,
        h_pole_collision_values_at_zero.2.1,
        h_pole_collision_values_at_zero.2.2.1,
        h_pole_collision_values_at_zero.2.2.2,
        show hPoleCollisionParameter 0 = -1 by
          norm_num [hPoleCollisionParameter],
        hrootEval]
      simpa using hzero
  · let m : ℂ := hPoleCollisionParameter lambda
    have hm : m + 1 = lambda ^ 2 / 3 := by
      simp only [m, hPoleCollisionParameter]
      ring
    have hlinear : m + 1 ≠ 0 := by
      rw [hm]
      exact div_ne_zero (pow_ne_zero 2 hlambda) (by norm_num)
    have hdenAt : hConicParamDenominator.eval m ≠ 0 := by
      simpa [m] using hden
    obtain ⟨hxRegular, hwRegular, hcapitalWRegular⟩ :=
      h_conic_param_regular_at m hlinear hdenAt
    let originalX : ℂ :=
      RatFunc.eval (RingHom.id ℂ) m (hConicParamX (K := ℂ))
    let originalW : ℂ :=
      RatFunc.eval (RingHom.id ℂ) m (hConicParamW (K := ℂ))
    let originalCapitalW : ℂ :=
      RatFunc.eval (RingHom.id ℂ) m
        (hConicParamCapitalW (K := ℂ))
    have hscaledX :
        lambda * originalX = hPoleCollisionSecondX lambda := by
      simp only [originalX]
      rw [hConicParamX,
        h_ratFunc_eval_algebraMap_div m hConicParamXNumerator
          hConicParamDenominator hdenAt]
      rfl
    have hellRegular : HRatFuncRegularAt m
        (algebraMap ℂ[X] (RatFunc ℂ)
          (3 * (Polynomial.X + 1))) :=
      hRatFuncRegularAt_algebraMap m (3 * (Polynomial.X + 1))
    have hscaledW :
        lambda ^ 2 * originalW = hPoleCollisionW lambda := by
      have heval := congrArg (RatFunc.eval (RingHom.id ℂ) m)
        (h_conic_profile_linear_mul_w (K := ℂ))
      rw [h_ratFunc_eval_mul_regular m _ _ hellRegular hwRegular,
        h_ratFunc_eval_algebraMap_id,
        h_ratFunc_eval_algebraMap_div m
          (-hConicParamOneFactor * hConicParamWFactor)
          (hConicParamDenominator ^ 2)
          (by simpa [Polynomial.eval_pow] using
            pow_ne_zero 2 hdenAt)] at heval
      have hell :
          (3 * (Polynomial.X + 1) : ℂ[X]).eval m = lambda ^ 2 := by
        simp only [Polynomial.eval_mul, Polynomial.eval_ofNat,
          Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
        rw [hm]
        field_simp
      rw [hell] at heval
      simpa only [originalW, hPoleCollisionW, m,
        Polynomial.eval_pow] using heval
    have hscaledCapitalW :
        lambda ^ 2 * originalCapitalW =
          hPoleCollisionCapitalW lambda := by
      have heval := congrArg (RatFunc.eval (RingHom.id ℂ) m)
        (h_conic_profile_linear_mul_capitalW (K := ℂ))
      rw [h_ratFunc_eval_mul_regular m _ _ hellRegular hcapitalWRegular,
        h_ratFunc_eval_algebraMap_id,
        h_ratFunc_eval_algebraMap_div m
          (-hConicParamOneFactor * hConicParamCapitalWFactor)
          (hConicParamDenominator ^ 2)
          (by simpa [Polynomial.eval_pow] using
            pow_ne_zero 2 hdenAt)] at heval
      have hell :
          (3 * (Polynomial.X + 1) : ℂ[X]).eval m = lambda ^ 2 := by
        simp only [Polynomial.eval_mul, Polynomial.eval_ofNat,
          Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
        rw [hm]
        field_simp
      rw [hell] at heval
      simpa only [originalCapitalW, hPoleCollisionCapitalW, m,
        Polynomial.eval_pow] using heval
    have hprofile :
        (hPoleProfileDenominator (K := ℂ) (N / 2) N).eval m ≠ 0 := by
      simp only [hPoleProfileDenominator, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_one, Polynomial.eval_ofNat]
      exact mul_ne_zero
        (pow_ne_zero (N / 2) (mul_ne_zero (by norm_num) hlinear))
          (pow_ne_zero N hdenAt)
    have hrawProfile :
        hFormEval 1 originalW R -
            hFormEval originalX originalCapitalW R =
          p.eval m /
            (hPoleProfileDenominator (N / 2) N).eval m := by
      have heval := congrArg (RatFunc.eval (RingHom.id ℂ) m)
        hrepresentation
      rw [h_ratFunc_eval_hConicDifference_regular R m hlinear hdenAt,
        h_ratFunc_eval_algebraMap_div m p
          (hPoleProfileDenominator (N / 2) N) hprofile] at heval
      exact heval
    have hprofileEval :
        (hPoleProfileDenominator (K := ℂ) (N / 2) N).eval m =
          (lambda ^ 2) ^ (N / 2) *
            hConicParamDenominator.eval m ^ N := by
      simp only [hPoleProfileDenominator, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_one, Polynomial.eval_ofNat]
      have hell : (3 : ℂ) * (m + 1) = lambda ^ 2 := by
        rw [hm]
        field_simp
      rw [hell]
    have hpower :
        lambda ^ N =
          (lambda ^ 2) ^ (N / 2) * lambda ^ (N % 2) := by
      have hdecomposition : N = 2 * (N / 2) + N % 2 := by omega
      calc
        lambda ^ N = lambda ^ (2 * (N / 2) + N % 2) := by
          exact congrArg (fun exponent : ℕ ↦ lambda ^ exponent)
            hdecomposition
        _ = lambda ^ (2 * (N / 2)) * lambda ^ (N % 2) :=
          pow_add lambda _ _
        _ = (lambda ^ 2) ^ (N / 2) * lambda ^ (N % 2) := by
          rw [pow_mul]
    have hsimplify :
        lambda ^ N *
            (p.eval m /
              ((lambda ^ 2) ^ (N / 2) *
                hConicParamDenominator.eval m ^ N)) =
          lambda ^ (N % 2) * p.eval m /
            hConicParamDenominator.eval m ^ N := by
      rw [hpower]
      field_simp [pow_ne_zero (N / 2) (pow_ne_zero 2 hlambda),
        pow_ne_zero N hdenAt]
    have hfirstScaled := hFormEval_weighted_smul R N hR
      lambda 1 originalW
    have hsecondScaled := hFormEval_weighted_smul R N hR
      lambda originalX originalCapitalW
    calc
      hFormEval (hPoleCollisionFirstX lambda)
            (hPoleCollisionW lambda) R -
          hFormEval (hPoleCollisionSecondX lambda)
            (hPoleCollisionCapitalW lambda) R =
        hFormEval (lambda * 1) (lambda ^ 2 * originalW) R -
          hFormEval (lambda * originalX)
            (lambda ^ 2 * originalCapitalW) R := by
          rw [hPoleCollisionFirstX, mul_one, hscaledW,
            hscaledX, hscaledCapitalW]
      _ = lambda ^ N *
          (hFormEval 1 originalW R -
            hFormEval originalX originalCapitalW R) := by
          rw [hfirstScaled, hsecondScaled]
          ring
      _ = lambda ^ N *
          (p.eval m /
            (hPoleProfileDenominator (N / 2) N).eval m) := by
          rw [hrawProfile]
      _ = lambda ^ N *
          (p.eval m /
            ((lambda ^ 2) ^ (N / 2) *
              hConicParamDenominator.eval m ^ N)) := by
          rw [hprofileEval]
      _ = lambda ^ (N % 2) * p.eval m /
          hConicParamDenominator.eval m ^ N := hsimplify
      _ = _ := by rfl

/-- The conic denominator remains nonzero near the ramified pole parameter. -/
theorem eventually_hPoleCollision_denominator :
    ∀ᶠ lambda in nhds (0 : ℂ),
      hConicParamDenominator.eval
        (hPoleCollisionParameter lambda) ≠ 0 := by
  have hzero : hConicParamDenominator (K := ℂ).eval
      (hPoleCollisionParameter 0) ≠ 0 := by
    norm_num [hPoleCollisionParameter, hConicParamDenominator]
  have htendsto : Tendsto
      (fun lambda : ℂ ↦ hConicParamDenominator.eval
        (hPoleCollisionParameter lambda))
      (nhds 0)
      (nhds (hConicParamDenominator.eval
        (hPoleCollisionParameter 0))) := by
    exact (analyticAt_polynomial_eval_hPoleCollisionParameter
      (hConicParamDenominator (K := ℂ))).continuousAt
  exact htendsto.eventually_ne hzero

/-- The ramified pole coordinates lie in one fibre near zero. -/
theorem eventually_hPoleCollision_fibre :
    ∀ᶠ lambda in nhds (0 : ℂ),
      hP (hPoleCollisionFirstX lambda) (hPoleCollisionW lambda) =
          hP (hPoleCollisionSecondX lambda)
            (hPoleCollisionCapitalW lambda) ∧
        hQ (hPoleCollisionFirstX lambda) (hPoleCollisionW lambda) =
          hQ (hPoleCollisionSecondX lambda)
            (hPoleCollisionCapitalW lambda) := by
  filter_upwards [eventually_hPoleCollision_denominator]
    with lambda hden
  exact h_pole_collision_fibre_at lambda hden

/-- A profile numerator root at the pole gives normalized source branch data
with ramified multiplicity `2 * rootMultiplicity + N % 2`. -/
theorem exists_hPoleSourceBranchData_of_profile_root
    (a N : ℕ) (ha : 0 < a)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (p : ℂ[X]) (hp : p ≠ 0)
    (hroot : p.IsRoot (-1 : ℂ))
    (hrepresentation :
      hConicDifference R =
        algebraMap ℂ[X] (RatFunc ℂ) p /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (N / 2) N)) :
    Nonempty (HNormalizedSourceBranchData a N R) := by
  let multiplicity := p.rootMultiplicity (-1 : ℂ)
  let order := 2 * multiplicity + N % 2
  let quotient :=
    p /ₘ (Polynomial.X - Polynomial.C (-1 : ℂ)) ^ multiplicity
  have hmultiplicity : 0 < multiplicity :=
    (Polynomial.rootMultiplicity_pos hp).2 hroot
  have horder : 0 < order := by
    simp only [order]
    omega
  have hpolynomialFactor :
      p = (Polynomial.X - Polynomial.C (-1 : ℂ)) ^ multiplicity *
        quotient :=
    (Polynomial.pow_mul_divByMonic_rootMultiplicity_eq p (-1)).symm
  have hquotient : quotient.eval (-1 : ℂ) ≠ 0 :=
    Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero (-1) hp
  let rawUnit : ℂ → ℂ := fun lambda ↦
    (1 / 3 : ℂ) ^ multiplicity *
      quotient.eval (hPoleCollisionParameter lambda) /
        hConicParamDenominator.eval
          (hPoleCollisionParameter lambda) ^ N
  have hrawUnit : AnalyticAt ℂ rawUnit 0 := by
    have hquotientAnalytic :=
      analyticAt_polynomial_eval_hPoleCollisionParameter quotient
    have hdenAnalytic :=
      (analyticAt_polynomial_eval_hPoleCollisionParameter
        (hConicParamDenominator (K := ℂ))).pow N
    exact (analyticAt_const.mul hquotientAnalytic).div hdenAnalytic
      (by norm_num [hPoleCollisionParameter, hConicParamDenominator])
  have hrawUnit0 : rawUnit 0 ≠ 0 := by
    change (1 / 3 : ℂ) ^ multiplicity *
        quotient.eval (hPoleCollisionParameter 0) /
          hConicParamDenominator.eval
            (hPoleCollisionParameter 0) ^ N ≠ 0
    have hparameter : hPoleCollisionParameter 0 = (-1 : ℂ) := by
      norm_num [hPoleCollisionParameter]
    rw [hparameter]
    exact div_ne_zero
      (mul_ne_zero (pow_ne_zero multiplicity (by norm_num)) hquotient)
      (pow_ne_zero N (by norm_num [hConicParamDenominator]))
  have hrawFactor : ∀ᶠ lambda in nhds 0,
      hFormEval (hPoleCollisionFirstX lambda)
          (hPoleCollisionW lambda) R -
        hFormEval (hPoleCollisionSecondX lambda)
          (hPoleCollisionCapitalW lambda) R =
      lambda ^ order * rawUnit lambda := by
    filter_upwards [eventually_hPoleCollision_denominator]
      with lambda hden
    rw [h_pole_collision_difference_eq_profile_at
      N R hR p hrepresentation hroot lambda hden]
    have hpEval := congrArg
      (fun polynomial : ℂ[X] ↦
        polynomial.eval (hPoleCollisionParameter lambda))
      hpolynomialFactor
    rw [Polynomial.eval_mul, Polynomial.eval_pow] at hpEval
    have hparameter :
        (Polynomial.X - Polynomial.C (-1 : ℂ)).eval
            (hPoleCollisionParameter lambda) = lambda ^ 2 / 3 := by
      simp only [Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, hPoleCollisionParameter]
      ring
    rw [hparameter] at hpEval
    rw [hpEval]
    simp only [rawUnit, order]
    rw [div_pow, ← pow_mul, pow_add, one_div_pow]
    ring
  have hw0 : hPoleCollisionW 0 ≠ 0 := by
    rw [h_pole_collision_values_at_zero.2.1]
    norm_num
  have hcapitalW0 : hPoleCollisionCapitalW 0 ≠ 0 := by
    rw [h_pole_collision_values_at_zero.2.2.2]
    norm_num
  have hdistinct : hPoleCollisionW 0 ≠ hPoleCollisionCapitalW 0 := by
    rw [h_pole_collision_values_at_zero.2.1,
      h_pole_collision_values_at_zero.2.2.2]
    norm_num
  exact exists_hNormalizedSourceBranchData
    a N ha R hR hPoleCollisionFirstX hPoleCollisionW
      hPoleCollisionSecondX hPoleCollisionCapitalW
      analyticAt_hPoleCollisionFirstX analyticAt_hPoleCollisionW
      analyticAt_hPoleCollisionSecondX analyticAt_hPoleCollisionCapitalW
      hw0 hcapitalW0 (Or.inr hdistinct)
      eventually_hPoleCollision_fibre
      order rawUnit horder hrawUnit hrawUnit0 hrawFactor

/-- Weighted order tails exclude an injective representative when the fixed
profile numerator vanishes at the pole. -/
theorem hPoleWeightedOrderTails_not_hasInjectiveRepresentative
    (a N : ℕ) (ha : 0 < a)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (p : ℂ[X]) (hp : p ≠ 0)
    (hroot : p.IsRoot (-1 : ℂ))
    (hrepresentation :
      hConicDifference R =
        algebraMap ℂ[X] (RatFunc ℂ) p /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (N / 2) N))
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (hQuadraticWeightedPolynomialMap a R i) ∈
        Germ.weightedOrderIdeal a
          (hQuadraticWeightedDegrees a N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨data⟩ := exists_hPoleSourceBranchData_of_profile_root
    a N ha R hR p hp hroot hrepresentation
  exact hNormalizedWeightedOrderTails_not_hasInjectiveRepresentative
    a N ha R hR data representative hanalytic hzero htail

end OnLeConjecture.DThree
