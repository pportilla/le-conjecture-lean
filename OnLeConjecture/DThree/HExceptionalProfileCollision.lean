/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HZeroSecondSourceBranch

/-!
# Exceptional regular profile collisions in the H case

At a regular profile parameter, either weighted second coordinate can
vanish.  Its cubic numerator has a simple root.  Ramification by the power
`2 * a` therefore gives the source coordinate required by the zero second
coordinate chart.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

@[expose]
noncomputable def hExceptionalProfileParameter
    (a : ℕ) (z lambda : ℂ) : ℂ :=
  z + lambda ^ (2 * a)

@[expose]
noncomputable def hWTranslatedFactor (z delta : ℂ) : ℂ :=
  (z + delta) ^ 2 + (z + delta) * z + z ^ 2 + 6

@[expose]
noncomputable def hCapitalWTranslatedFactor (z delta : ℂ) : ℂ :=
  (z + delta) ^ 2 + (z + delta) * z + z ^ 2 +
    6 * ((z + delta) + z) + 18

theorem h_conic_param_W_factor_translate
    (z delta : ℂ)
    (hz : hConicParamWFactor.eval z = 0) :
    hConicParamWFactor.eval (z + delta) =
      delta * hWTranslatedFactor z delta := by
  simp only [hConicParamWFactor, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul,
    Polynomial.eval_ofNat] at hz ⊢
  simp only [hWTranslatedFactor]
  linear_combination hz

theorem h_conic_param_capitalW_factor_translate
    (z delta : ℂ)
    (hz : hConicParamCapitalWFactor.eval z = 0) :
    hConicParamCapitalWFactor.eval (z + delta) =
      delta * hCapitalWTranslatedFactor z delta := by
  simp only [hConicParamCapitalWFactor, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul,
    Polynomial.eval_ofNat] at hz ⊢
  simp only [hCapitalWTranslatedFactor]
  linear_combination hz

theorem hWTranslatedFactor_zero_ne_zero
    (z : ℂ) (hz : hConicParamWFactor.eval z = 0) :
    hWTranslatedFactor z 0 ≠ 0 := by
  have hz' : z ^ 3 + 6 * z + 16 = 0 := by
    simpa [hConicParamWFactor] using hz
  have hvalue : hWTranslatedFactor z 0 = 3 * z ^ 2 + 6 := by
    simp [hWTranslatedFactor]
    ring
  rw [hvalue]
  intro hderivative
  have hfalse : (1 : ℂ) = 0 := by
    linear_combination
      (1 / 18 - z / 72) * hz' +
        (z ^ 2 / 216 - z / 54 + 1 / 54) * hderivative
  norm_num at hfalse

theorem hCapitalWTranslatedFactor_zero_ne_zero
    (z : ℂ) (hz : hConicParamCapitalWFactor.eval z = 0) :
    hCapitalWTranslatedFactor z 0 ≠ 0 := by
  have hz' : z ^ 3 + 6 * z ^ 2 + 18 * z + 4 = 0 := by
    simpa [hConicParamCapitalWFactor] using hz
  have hvalue : hCapitalWTranslatedFactor z 0 =
      3 * z ^ 2 + 12 * z + 18 := by
    simp [hCapitalWTranslatedFactor]
    ring
  rw [hvalue]
  intro hderivative
  have hfalse : (1 : ℂ) = 0 := by
    linear_combination
      (-z / 72 - 1 / 12) * hz' +
        (z ^ 2 / 216 + z / 27 + 2 / 27) * hderivative
  norm_num at hfalse

theorem h_conic_param_second_factors_not_both_zero (z : ℂ) :
    hConicParamWFactor.eval z ≠ 0 ∨
      hConicParamCapitalWFactor.eval z ≠ 0 := by
  by_contra hboth
  push Not at hboth
  have hW : z ^ 3 + 6 * z + 16 = 0 := by
    simpa [hConicParamWFactor] using hboth.1
  have hCapitalW : z ^ 3 + 6 * z ^ 2 + 18 * z + 4 = 0 := by
    simpa [hConicParamCapitalWFactor] using hboth.2
  have hfalse : (1 : ℂ) = 0 := by
    linear_combination
      (z ^ 2 / 216 + 5 * z / 216 + 2 / 27) * hW +
        (-z ^ 2 / 216 + z / 216 - 5 / 108) * hCapitalW
  norm_num at hfalse

theorem analyticAt_hExceptionalProfileParameter
    (a : ℕ) (z : ℂ) :
    AnalyticAt ℂ (hExceptionalProfileParameter a z) 0 := by
  exact analyticAt_const.add (analyticAt_id.pow (2 * a))

theorem analyticAt_hWTranslatedFactor_reparam
    (a : ℕ) (z : ℂ) :
    AnalyticAt ℂ
      (fun lambda ↦ hWTranslatedFactor z (lambda ^ (2 * a))) 0 := by
  have hdelta : AnalyticAt ℂ (fun lambda : ℂ ↦ lambda ^ (2 * a)) 0 :=
    analyticAt_id.pow (2 * a)
  exact ((((analyticAt_const.add hdelta).pow 2).add
    ((analyticAt_const.add hdelta).mul analyticAt_const)).add
      (analyticAt_const.pow 2)).add analyticAt_const

theorem analyticAt_hCapitalWTranslatedFactor_reparam
    (a : ℕ) (z : ℂ) :
    AnalyticAt ℂ
      (fun lambda ↦
        hCapitalWTranslatedFactor z (lambda ^ (2 * a))) 0 := by
  have hdelta : AnalyticAt ℂ (fun lambda : ℂ ↦ lambda ^ (2 * a)) 0 :=
    analyticAt_id.pow (2 * a)
  exact (((((analyticAt_const.add hdelta).pow 2).add
    ((analyticAt_const.add hdelta).mul analyticAt_const)).add
      (analyticAt_const.pow 2)).add
        (analyticAt_const.mul
          ((analyticAt_const.add hdelta).add analyticAt_const))).add
            analyticAt_const

/-- The unit left after removing the ramified zero of the second weighted
coordinate. -/
@[expose]
noncomputable def hCapitalWZeroUnit
    (a : ℕ) (z lambda : ℂ) : ℂ :=
  (-(hConicParamOneFactor.eval
        (hExceptionalProfileParameter a z lambda)) *
      hCapitalWTranslatedFactor z (lambda ^ (2 * a))) /
    hConicParamFunctionDenominator.eval
      (hExceptionalProfileParameter a z lambda)

@[expose]
noncomputable def hWZeroUnit
    (a : ℕ) (z lambda : ℂ) : ℂ :=
  (-(hConicParamOneFactor.eval
        (hExceptionalProfileParameter a z lambda)) *
      hWTranslatedFactor z (lambda ^ (2 * a))) /
    hConicParamFunctionDenominator.eval
      (hExceptionalProfileParameter a z lambda)

theorem h_regular_profile_capitalW_ramified_factor
    (a : ℕ) (z lambda : ℂ)
    (hz : hConicParamCapitalWFactor.eval z = 0) :
    hRegularProfileCapitalW z (lambda ^ (2 * a)) =
      lambda ^ (2 * a) * hCapitalWZeroUnit a z lambda := by
  rw [hRegularProfileCapitalW]
  change
    (-hConicParamOneFactor * hConicParamCapitalWFactor).eval
          (z + lambda ^ (2 * a)) /
        hConicParamFunctionDenominator.eval
          (z + lambda ^ (2 * a)) = _
  rw [Polynomial.eval_mul, Polynomial.eval_neg,
    h_conic_param_capitalW_factor_translate z (lambda ^ (2 * a)) hz]
  simp only [hCapitalWZeroUnit,
    hExceptionalProfileParameter]
  ring

theorem h_regular_profile_W_ramified_factor
    (a : ℕ) (z lambda : ℂ)
    (hz : hConicParamWFactor.eval z = 0) :
    hRegularProfileW z (lambda ^ (2 * a)) =
      lambda ^ (2 * a) * hWZeroUnit a z lambda := by
  rw [hRegularProfileW]
  change
    (-hConicParamOneFactor * hConicParamWFactor).eval
          (z + lambda ^ (2 * a)) /
        hConicParamFunctionDenominator.eval
          (z + lambda ^ (2 * a)) = _
  rw [Polynomial.eval_mul, Polynomial.eval_neg,
    h_conic_param_W_factor_translate z (lambda ^ (2 * a)) hz]
  simp only [hWZeroUnit,
    hExceptionalProfileParameter]
  ring

end OnLeConjecture.DThree
