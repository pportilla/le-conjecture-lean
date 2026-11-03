/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HExceptionalProfileCollision

/-!
# Source branches at exceptional regular H profile points

The two cubic numerator factors are treated separately.  In each case the
profile is ramified by `lambda ^ (2 * a)`, then normalized by the nonzero
weighted second coordinate.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

theorem analyticAt_hRegularProfileX_ramified
    (a : ℕ) (ha : 0 < a) (z : ℂ)
    (hden : hConicParamDenominator.eval z ≠ 0) :
    AnalyticAt ℂ
      (fun lambda ↦ hRegularProfileX z (lambda ^ (2 * a))) 0 := by
  have hdelta : AnalyticAt ℂ
      (fun lambda : ℂ ↦ lambda ^ (2 * a)) 0 :=
    analyticAt_id.pow (2 * a)
  apply AnalyticAt.fun_comp (x := 0) _ hdelta
  simpa [zero_pow (by omega : 2 * a ≠ 0)] using
    analyticAt_hRegularProfileX z hden

theorem analyticAt_hRegularProfileW_ramified
    (a : ℕ) (ha : 0 < a) (z : ℂ)
    (hfunction : hConicParamFunctionDenominator.eval z ≠ 0) :
    AnalyticAt ℂ
      (fun lambda ↦ hRegularProfileW z (lambda ^ (2 * a))) 0 := by
  have hdelta : AnalyticAt ℂ
      (fun lambda : ℂ ↦ lambda ^ (2 * a)) 0 :=
    analyticAt_id.pow (2 * a)
  apply AnalyticAt.fun_comp (x := 0) _ hdelta
  simpa [zero_pow (by omega : 2 * a ≠ 0)] using
    analyticAt_hRegularProfileW z hfunction

theorem analyticAt_hRegularProfileCapitalW_ramified
    (a : ℕ) (ha : 0 < a) (z : ℂ)
    (hfunction : hConicParamFunctionDenominator.eval z ≠ 0) :
    AnalyticAt ℂ
      (fun lambda ↦
        hRegularProfileCapitalW z (lambda ^ (2 * a))) 0 := by
  have hdelta : AnalyticAt ℂ
      (fun lambda : ℂ ↦ lambda ^ (2 * a)) 0 :=
    analyticAt_id.pow (2 * a)
  apply AnalyticAt.fun_comp (x := 0) _ hdelta
  simpa [zero_pow (by omega : 2 * a ≠ 0)] using
    analyticAt_hRegularProfileCapitalW z hfunction

theorem analyticAt_polynomial_eval_hExceptionalProfileParameter
    (a : ℕ) (z : ℂ) (p : ℂ[X]) :
    AnalyticAt ℂ
      (fun lambda ↦ p.eval (hExceptionalProfileParameter a z lambda)) 0 := by
  simpa [aeval_def] using
    (analyticAt_hExceptionalProfileParameter a z).aeval_polynomial p

theorem analyticAt_hCapitalWZeroUnit
    (a : ℕ) (ha : 0 < a) (z : ℂ)
    (hfunction : hConicParamFunctionDenominator.eval z ≠ 0) :
    AnalyticAt ℂ (hCapitalWZeroUnit a z) 0 := by
  apply ((analyticAt_polynomial_eval_hExceptionalProfileParameter
      a z hConicParamOneFactor).neg.mul
        (analyticAt_hCapitalWTranslatedFactor_reparam a z)).div
    (analyticAt_polynomial_eval_hExceptionalProfileParameter
      a z hConicParamFunctionDenominator)
  simpa [hExceptionalProfileParameter,
    zero_pow (by omega : 2 * a ≠ 0)] using hfunction

theorem analyticAt_hWZeroUnit
    (a : ℕ) (ha : 0 < a) (z : ℂ)
    (hfunction : hConicParamFunctionDenominator.eval z ≠ 0) :
    AnalyticAt ℂ (hWZeroUnit a z) 0 := by
  apply ((analyticAt_polynomial_eval_hExceptionalProfileParameter
      a z hConicParamOneFactor).neg.mul
        (analyticAt_hWTranslatedFactor_reparam a z)).div
    (analyticAt_polynomial_eval_hExceptionalProfileParameter
      a z hConicParamFunctionDenominator)
  simpa [hExceptionalProfileParameter,
    zero_pow (by omega : 2 * a ≠ 0)] using hfunction

theorem h_one_factor_ne_zero_of_regular_W_ne_zero
    (z : ℂ) (hW : hRegularProfileW z 0 ≠ 0) :
    hConicParamOneFactor.eval z ≠ 0 := by
  have hquotient :
      (-hConicParamOneFactor * hConicParamWFactor).eval z /
          hConicParamFunctionDenominator.eval z ≠ 0 := by
    simpa [hRegularProfileW, hRegularProfileParameter] using hW
  have hnumerator := (div_ne_zero_iff.mp hquotient).1
  rw [Polynomial.eval_mul, Polynomial.eval_neg] at hnumerator
  exact neg_ne_zero.mp (mul_ne_zero_iff.mp hnumerator).1

theorem h_one_factor_ne_zero_of_regular_capitalW_ne_zero
    (z : ℂ) (hCapitalW : hRegularProfileCapitalW z 0 ≠ 0) :
    hConicParamOneFactor.eval z ≠ 0 := by
  have hquotient :
      (-hConicParamOneFactor * hConicParamCapitalWFactor).eval z /
          hConicParamFunctionDenominator.eval z ≠ 0 := by
    simpa [hRegularProfileCapitalW, hRegularProfileParameter] using hCapitalW
  have hnumerator := (div_ne_zero_iff.mp hquotient).1
  rw [Polynomial.eval_mul, Polynomial.eval_neg] at hnumerator
  exact neg_ne_zero.mp (mul_ne_zero_iff.mp hnumerator).1

theorem h_capitalW_factor_root_of_regular_value_zero
    (z : ℂ)
    (hfunction : hConicParamFunctionDenominator.eval z ≠ 0)
    (hone : hConicParamOneFactor.eval z ≠ 0)
    (hzero : hRegularProfileCapitalW z 0 = 0) :
    hConicParamCapitalWFactor.eval z = 0 := by
  have hquotient :
      (-hConicParamOneFactor * hConicParamCapitalWFactor).eval z /
          hConicParamFunctionDenominator.eval z = 0 := by
    simpa [hRegularProfileCapitalW, hRegularProfileParameter] using hzero
  have hnumerator :=
    (div_eq_zero_iff.mp hquotient).resolve_right hfunction
  rw [Polynomial.eval_mul, Polynomial.eval_neg] at hnumerator
  exact (mul_eq_zero.mp hnumerator).resolve_left (neg_ne_zero.mpr hone)

theorem h_W_factor_root_of_regular_value_zero
    (z : ℂ)
    (hfunction : hConicParamFunctionDenominator.eval z ≠ 0)
    (hone : hConicParamOneFactor.eval z ≠ 0)
    (hzero : hRegularProfileW z 0 = 0) :
    hConicParamWFactor.eval z = 0 := by
  have hquotient :
      (-hConicParamOneFactor * hConicParamWFactor).eval z /
          hConicParamFunctionDenominator.eval z = 0 := by
    simpa [hRegularProfileW, hRegularProfileParameter] using hzero
  have hnumerator :=
    (div_eq_zero_iff.mp hquotient).resolve_right hfunction
  rw [Polynomial.eval_mul, Polynomial.eval_neg] at hnumerator
  exact (mul_eq_zero.mp hnumerator).resolve_left (neg_ne_zero.mpr hone)

theorem hCapitalWZeroUnit_zero_ne_zero
    (a : ℕ) (ha : 0 < a) (z : ℂ)
    (hfunction : hConicParamFunctionDenominator.eval z ≠ 0)
    (hone : hConicParamOneFactor.eval z ≠ 0)
    (hfactor : hConicParamCapitalWFactor.eval z = 0) :
    hCapitalWZeroUnit a z 0 ≠ 0 := by
  change (-(hConicParamOneFactor.eval (z + 0 ^ (2 * a))) *
      hCapitalWTranslatedFactor z (0 ^ (2 * a))) /
        hConicParamFunctionDenominator.eval (z + 0 ^ (2 * a)) ≠ 0
  rw [zero_pow (by omega : 2 * a ≠ 0), add_zero]
  exact div_ne_zero
    (mul_ne_zero (neg_ne_zero.mpr hone)
      (hCapitalWTranslatedFactor_zero_ne_zero z hfactor))
    hfunction

theorem hWZeroUnit_zero_ne_zero
    (a : ℕ) (ha : 0 < a) (z : ℂ)
    (hfunction : hConicParamFunctionDenominator.eval z ≠ 0)
    (hone : hConicParamOneFactor.eval z ≠ 0)
    (hfactor : hConicParamWFactor.eval z = 0) :
    hWZeroUnit a z 0 ≠ 0 := by
  change (-(hConicParamOneFactor.eval (z + 0 ^ (2 * a))) *
      hWTranslatedFactor z (0 ^ (2 * a))) /
        hConicParamFunctionDenominator.eval (z + 0 ^ (2 * a)) ≠ 0
  rw [zero_pow (by omega : 2 * a ≠ 0), add_zero]
  exact div_ne_zero
    (mul_ne_zero (neg_ne_zero.mpr hone)
      (hWTranslatedFactor_zero_ne_zero z hfactor))
    hfunction

/-- A regular profile root where the second point has zero weighted second
coordinate gives source branch data in the zero coordinate chart. -/
theorem exists_hZeroSecondSourceBranchData_of_capitalW_profile_root
    (a N : ℕ) (ha : 0 < a)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (p : ℂ[X]) (hp : p ≠ 0) (z : ℂ) (hz : p.IsRoot z)
    (hlinear : z + 1 ≠ 0)
    (hden : hConicParamDenominator.eval z ≠ 0)
    (hW : hRegularProfileW z 0 ≠ 0)
    (hCapitalW : hRegularProfileCapitalW z 0 = 0)
    (hrepresentation :
      hConicDifference R =
        algebraMap ℂ[X] (RatFunc ℂ) p /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (N / 2) N)) :
    Nonempty (HZeroSecondSourceBranchData a N R) := by
  have hfunction := h_regular_function_denominator_ne_zero hlinear hden
  have hone := h_one_factor_ne_zero_of_regular_W_ne_zero z hW
  have hcapitalFactor := h_capitalW_factor_root_of_regular_value_zero
    z hfunction hone hCapitalW
  have hprofile :
      (hPoleProfileDenominator (K := ℂ) (N / 2) N).eval z ≠ 0 := by
    simp only [hPoleProfileDenominator, Polynomial.eval_mul,
      Polynomial.eval_pow]
    have hlinearScaled : (3 : ℂ) * (z + 1) ≠ 0 :=
      mul_ne_zero (by norm_num) hlinear
    exact mul_ne_zero
      (pow_ne_zero (N / 2) (by simpa using hlinearScaled))
      (pow_ne_zero N hden)
  let order := p.rootMultiplicity z
  let quotient := p /ₘ (Polynomial.X - Polynomial.C z) ^ order
  have horder : 0 < order := (Polynomial.rootMultiplicity_pos hp).2 hz
  have hpolynomialFactor :
      p = (Polynomial.X - Polynomial.C z) ^ order * quotient :=
    (Polynomial.pow_mul_divByMonic_rootMultiplicity_eq p z).symm
  have hquotient : quotient.eval z ≠ 0 :=
    Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero z hp
  let rawUnit : ℂ → ℂ := fun lambda ↦
    quotient.eval (hExceptionalProfileParameter a z lambda) /
      (hPoleProfileDenominator (N / 2) N).eval
        (hExceptionalProfileParameter a z lambda)
  have hrawUnit : AnalyticAt ℂ rawUnit 0 := by
    apply (analyticAt_polynomial_eval_hExceptionalProfileParameter
      a z quotient).div
        (analyticAt_polynomial_eval_hExceptionalProfileParameter
          a z (hPoleProfileDenominator (N / 2) N))
    simpa [hExceptionalProfileParameter,
      zero_pow (by omega : 2 * a ≠ 0)] using hprofile
  have hrawUnit0 : rawUnit 0 ≠ 0 := by
    simpa [rawUnit, hExceptionalProfileParameter,
      zero_pow (by omega : 2 * a ≠ 0)] using
      div_ne_zero hquotient hprofile
  have hdelta : Tendsto (fun lambda : ℂ ↦ lambda ^ (2 * a))
      (nhds 0) (nhds 0) := by
    have hdeltaAnalytic : AnalyticAt ℂ
        (fun lambda : ℂ ↦ lambda ^ (2 * a)) 0 :=
      analyticAt_id.pow (2 * a)
    have ht := hdeltaAnalytic.continuousAt
    change Tendsto (fun lambda : ℂ ↦ lambda ^ (2 * a))
      (nhds 0) (nhds (0 ^ (2 * a))) at ht
    simpa [zero_pow (by omega : 2 * a ≠ 0)] using ht
  have hfibreReparam := hdelta.eventually
    (eventually_hRegularProfile_fibre z hlinear hden)
  have hprofileReparam := hdelta.eventually
    (eventually_hRegularProfile_difference_eq_profile
      R p (N / 2) N z hlinear hden hprofile hrepresentation)
  have hfibre : ∀ᶠ lambda in nhds 0,
      hP 1 (hRegularProfileW z (lambda ^ (2 * a))) =
          hP (hRegularProfileX z (lambda ^ (2 * a)))
            (lambda ^ (2 * a) * hCapitalWZeroUnit a z lambda) ∧
        hQ 1 (hRegularProfileW z (lambda ^ (2 * a))) =
          hQ (hRegularProfileX z (lambda ^ (2 * a)))
            (lambda ^ (2 * a) * hCapitalWZeroUnit a z lambda) := by
    filter_upwards [hfibreReparam] with lambda hfibreAt
    rw [← h_regular_profile_capitalW_ramified_factor
      a z lambda hcapitalFactor]
    exact hfibreAt
  have hrawFactor : ∀ᶠ lambda in nhds 0,
      hFormEval 1 (hRegularProfileW z (lambda ^ (2 * a))) R -
          hFormEval (hRegularProfileX z (lambda ^ (2 * a)))
            (lambda ^ (2 * a) * hCapitalWZeroUnit a z lambda) R =
        lambda ^ ((2 * a) * order) * rawUnit lambda := by
    filter_upwards [hprofileReparam] with lambda hprofileAt
    rw [← h_regular_profile_capitalW_ramified_factor
      a z lambda hcapitalFactor]
    have hpEval := congrArg (fun polynomial : ℂ[X] ↦
      polynomial.eval
        (hExceptionalProfileParameter a z lambda)) hpolynomialFactor
    rw [Polynomial.eval_mul, Polynomial.eval_pow] at hpEval
    have hlinearEval :
        (Polynomial.X - Polynomial.C z).eval
            (hExceptionalProfileParameter a z lambda) =
          lambda ^ (2 * a) := by
      simp [hExceptionalProfileParameter]
    rw [hlinearEval] at hpEval
    rw [hprofileAt]
    change p.eval (hExceptionalProfileParameter a z lambda) /
        (hPoleProfileDenominator (N / 2) N).eval
          (hExceptionalProfileParameter a z lambda) = _
    rw [hpEval]
    simp only [rawUnit, hExceptionalProfileParameter]
    have hpow : (lambda ^ (2 * a)) ^ order =
        lambda ^ ((2 * a) * order) := by
      exact (pow_mul lambda (2 * a) order).symm
    rw [hpow]
    ring
  apply exists_hZeroSecondSourceBranchData
    a N ha R hR
      (fun _ ↦ 1)
      (fun lambda ↦ hRegularProfileW z (lambda ^ (2 * a)))
      (fun lambda ↦ hRegularProfileX z (lambda ^ (2 * a)))
      (hCapitalWZeroUnit a z)
      (m := (2 * a) * order) (rawUnit := rawUnit)
  · exact analyticAt_const
  · exact analyticAt_hRegularProfileW_ramified a ha z hfunction
  · exact analyticAt_hRegularProfileX_ramified a ha z hden
  · exact analyticAt_hCapitalWZeroUnit a ha z hfunction
  · simpa [zero_pow (by omega : 2 * a ≠ 0)] using hW
  · exact hCapitalWZeroUnit_zero_ne_zero
      a ha z hfunction hone hcapitalFactor
  · exact hfibre
  · exact Nat.mul_pos (by omega) horder
  · exact hrawUnit
  · exact hrawUnit0
  · exact hrawFactor

/-- A regular profile root where the first point has zero weighted second
coordinate gives source branch data after interchanging the two points. -/
theorem exists_hZeroSecondSourceBranchData_of_W_profile_root
    (a N : ℕ) (ha : 0 < a)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (p : ℂ[X]) (hp : p ≠ 0) (z : ℂ) (hz : p.IsRoot z)
    (hlinear : z + 1 ≠ 0)
    (hden : hConicParamDenominator.eval z ≠ 0)
    (hW : hRegularProfileW z 0 = 0)
    (hCapitalW : hRegularProfileCapitalW z 0 ≠ 0)
    (hrepresentation :
      hConicDifference R =
        algebraMap ℂ[X] (RatFunc ℂ) p /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (N / 2) N)) :
    Nonempty (HZeroSecondSourceBranchData a N R) := by
  have hfunction := h_regular_function_denominator_ne_zero hlinear hden
  have hone := h_one_factor_ne_zero_of_regular_capitalW_ne_zero
    z hCapitalW
  have hWFactor := h_W_factor_root_of_regular_value_zero
    z hfunction hone hW
  have hprofile :
      (hPoleProfileDenominator (K := ℂ) (N / 2) N).eval z ≠ 0 := by
    simp only [hPoleProfileDenominator, Polynomial.eval_mul,
      Polynomial.eval_pow]
    have hlinearScaled : (3 : ℂ) * (z + 1) ≠ 0 :=
      mul_ne_zero (by norm_num) hlinear
    exact mul_ne_zero
      (pow_ne_zero (N / 2) (by simpa using hlinearScaled))
      (pow_ne_zero N hden)
  let order := p.rootMultiplicity z
  let quotient := p /ₘ (Polynomial.X - Polynomial.C z) ^ order
  have horder : 0 < order := (Polynomial.rootMultiplicity_pos hp).2 hz
  have hpolynomialFactor :
      p = (Polynomial.X - Polynomial.C z) ^ order * quotient :=
    (Polynomial.pow_mul_divByMonic_rootMultiplicity_eq p z).symm
  have hquotient : quotient.eval z ≠ 0 :=
    Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero z hp
  let rawUnit : ℂ → ℂ := fun lambda ↦
    -(quotient.eval (hExceptionalProfileParameter a z lambda) /
      (hPoleProfileDenominator (N / 2) N).eval
        (hExceptionalProfileParameter a z lambda))
  have hrawUnit : AnalyticAt ℂ rawUnit 0 := by
    apply AnalyticAt.neg
    apply (analyticAt_polynomial_eval_hExceptionalProfileParameter
      a z quotient).div
        (analyticAt_polynomial_eval_hExceptionalProfileParameter
          a z (hPoleProfileDenominator (N / 2) N))
    simpa [hExceptionalProfileParameter,
      zero_pow (by omega : 2 * a ≠ 0)] using hprofile
  have hrawUnit0 : rawUnit 0 ≠ 0 := by
    have hdivision := div_ne_zero hquotient hprofile
    simpa [rawUnit, hExceptionalProfileParameter,
      zero_pow (by omega : 2 * a ≠ 0)] using neg_ne_zero.mpr hdivision
  have hdelta : Tendsto (fun lambda : ℂ ↦ lambda ^ (2 * a))
      (nhds 0) (nhds 0) := by
    have hdeltaAnalytic : AnalyticAt ℂ
        (fun lambda : ℂ ↦ lambda ^ (2 * a)) 0 :=
      analyticAt_id.pow (2 * a)
    have ht := hdeltaAnalytic.continuousAt
    change Tendsto (fun lambda : ℂ ↦ lambda ^ (2 * a))
      (nhds 0) (nhds (0 ^ (2 * a))) at ht
    simpa [zero_pow (by omega : 2 * a ≠ 0)] using ht
  have hfibreReparam := hdelta.eventually
    (eventually_hRegularProfile_fibre z hlinear hden)
  have hprofileReparam := hdelta.eventually
    (eventually_hRegularProfile_difference_eq_profile
      R p (N / 2) N z hlinear hden hprofile hrepresentation)
  have hfibre : ∀ᶠ lambda in nhds 0,
      hP (hRegularProfileX z (lambda ^ (2 * a)))
          (hRegularProfileCapitalW z (lambda ^ (2 * a))) =
        hP 1 (lambda ^ (2 * a) * hWZeroUnit a z lambda) ∧
      hQ (hRegularProfileX z (lambda ^ (2 * a)))
          (hRegularProfileCapitalW z (lambda ^ (2 * a))) =
        hQ 1 (lambda ^ (2 * a) * hWZeroUnit a z lambda) := by
    filter_upwards [hfibreReparam] with lambda hfibreAt
    rw [← h_regular_profile_W_ramified_factor
      a z lambda hWFactor]
    exact ⟨hfibreAt.1.symm, hfibreAt.2.symm⟩
  have hrawFactor : ∀ᶠ lambda in nhds 0,
      hFormEval (hRegularProfileX z (lambda ^ (2 * a)))
          (hRegularProfileCapitalW z (lambda ^ (2 * a))) R -
        hFormEval 1
          (lambda ^ (2 * a) * hWZeroUnit a z lambda) R =
        lambda ^ ((2 * a) * order) * rawUnit lambda := by
    filter_upwards [hprofileReparam] with lambda hprofileAt
    rw [← h_regular_profile_W_ramified_factor
      a z lambda hWFactor]
    have hpEval := congrArg (fun polynomial : ℂ[X] ↦
      polynomial.eval
        (hExceptionalProfileParameter a z lambda)) hpolynomialFactor
    rw [Polynomial.eval_mul, Polynomial.eval_pow] at hpEval
    have hlinearEval :
        (Polynomial.X - Polynomial.C z).eval
            (hExceptionalProfileParameter a z lambda) =
          lambda ^ (2 * a) := by
      simp [hExceptionalProfileParameter]
    rw [hlinearEval] at hpEval
    have hpow : (lambda ^ (2 * a)) ^ order =
        lambda ^ ((2 * a) * order) :=
      (pow_mul lambda (2 * a) order).symm
    calc
      hFormEval (hRegularProfileX z (lambda ^ (2 * a)))
            (hRegularProfileCapitalW z (lambda ^ (2 * a))) R -
          hFormEval 1 (hRegularProfileW z (lambda ^ (2 * a))) R =
          -(p.eval (z + lambda ^ (2 * a)) /
            (hPoleProfileDenominator (N / 2) N).eval
              (z + lambda ^ (2 * a))) := by
        rw [← hprofileAt]
        ring
      _ = lambda ^ ((2 * a) * order) * rawUnit lambda := by
        change -(p.eval (hExceptionalProfileParameter a z lambda) /
            (hPoleProfileDenominator (N / 2) N).eval
              (hExceptionalProfileParameter a z lambda)) = _
        rw [hpEval, hpow]
        simp only [rawUnit]
        ring
  apply exists_hZeroSecondSourceBranchData
    a N ha R hR
      (fun lambda ↦ hRegularProfileX z (lambda ^ (2 * a)))
      (fun lambda ↦
        hRegularProfileCapitalW z (lambda ^ (2 * a)))
      (fun _ ↦ 1)
      (hWZeroUnit a z)
      (m := (2 * a) * order) (rawUnit := rawUnit)
  · exact analyticAt_hRegularProfileX_ramified a ha z hden
  · exact analyticAt_hRegularProfileCapitalW_ramified a ha z hfunction
  · exact analyticAt_const
  · exact analyticAt_hWZeroUnit a ha z hfunction
  · simpa [zero_pow (by omega : 2 * a ≠ 0)] using hCapitalW
  · exact hWZeroUnit_zero_ne_zero a ha z hfunction hone hWFactor
  · exact hfibre
  · exact Nat.mul_pos (by omega) horder
  · exact hrawUnit
  · exact hrawUnit0
  · exact hrawFactor

end OnLeConjecture.DThree
