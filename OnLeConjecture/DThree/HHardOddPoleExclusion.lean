/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HHardOddInfinity
public import OnLeConjecture.DThree.HProjectiveDifferencePoleBoundary

/-!
# Exclusion of the pole boundary for the odd H norm

At `m = -1`, multiplication by `3(m + 1)` removes the simple poles of the
two conic functions. An odd weighted form has pole order at most `N / 2`.
Consequently its squared difference contributes zero to the leading scaled
norm. The remaining pure odd term has a nonzero leading value.
-/

public section

noncomputable section

namespace OnLeConjecture.DThree

open _root_.Polynomial

/-- Multiplication by the pole factor to the profile exponent makes a
profiled rational function regular at `m = -1`. -/
theorem hRatFuncRegularAt_pole_scaled_of_hasHPoleProfile
    (a b : ℕ) (f : RatFunc ℂ) (hf : HasHPoleProfile a b f) :
    HRatFuncRegularAt (-1 : ℂ)
      (algebraMap ℂ[X] (RatFunc ℂ)
          (3 * (Polynomial.X + 1)) ^ a * f) := by
  obtain ⟨p, _hpDegree, hrepresentation⟩ := hf
  rw [hrepresentation]
  have hell : algebraMap ℂ[X] (RatFunc ℂ)
      (3 * (Polynomial.X + 1)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero
      (h_conic_profile_linear_ne_zero (K := ℂ))
  have hden : algebraMap ℂ[X] (RatFunc ℂ)
      (hConicParamDenominator (K := ℂ)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero h_conic_param_denominator_ne_zero
  have hidentity :
      algebraMap ℂ[X] (RatFunc ℂ)
            (3 * (Polynomial.X + 1)) ^ a *
          (algebraMap ℂ[X] (RatFunc ℂ) p /
            algebraMap ℂ[X] (RatFunc ℂ)
              (hPoleProfileDenominator a b)) =
        algebraMap ℂ[X] (RatFunc ℂ) p /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hConicParamDenominator ^ b) := by
    simp only [hPoleProfileDenominator, map_mul, map_pow]
    field_simp [hell, hden]
    simpa [mul_assoc] using
      (mul_div_cancel_left₀
        (algebraMap ℂ[X] (RatFunc ℂ) p)
        (pow_ne_zero a hell))
  rw [hidentity]
  apply hRatFuncRegularAt_of_denom_dvd
    (RatFunc.denom_div_dvd p (hConicParamDenominator ^ b))
  norm_num [Polynomial.eval_pow, hConicParamDenominator]

/-- The scaled square of the descended difference is regular and vanishes
at the pole when the weight is odd. -/
theorem hHardOdd_scaled_difference_square_regular_and_zero_at_pole
    (Rzero : MvPolynomial (Fin 2) ℂ) (N : ℕ)
    (hNodd : Odd N)
    (hRzero : Rzero.IsWeightedHomogeneous hFormWeight N) :
    let ell : RatFunc ℂ :=
      algebraMap ℂ[X] (RatFunc ℂ) (3 * (Polynomial.X + 1))
    HRatFuncRegularAt (-1 : ℂ)
        (ell ^ N * hConicDifference Rzero ^ 2) ∧
      RatFunc.eval (RingHom.id ℂ) (-1)
          (ell ^ N * hConicDifference Rzero ^ 2) = 0 := by
  obtain ⟨j, rfl⟩ := hNodd
  let ell : RatFunc ℂ :=
    algebraMap ℂ[X] (RatFunc ℂ) (3 * (Polynomial.X + 1))
  let scaledA : RatFunc ℂ :=
    ell ^ j * hConicDifference Rzero
  have hellRegular : HRatFuncRegularAt (-1 : ℂ) ell := by
    exact hRatFuncRegularAt_algebraMap (-1) (3 * (Polynomial.X + 1))
  have hellZero : RatFunc.eval (RingHom.id ℂ) (-1) ell = 0 := by
    dsimp only [ell]
    rw [h_ratFunc_eval_algebraMap_id]
    norm_num
  have hscaledA : HRatFuncRegularAt (-1 : ℂ) scaledA := by
    simpa [scaledA, ell, show (2 * j + 1) / 2 = j by omega] using
      (hRatFuncRegularAt_pole_scaled_of_hasHPoleProfile
        ((2 * j + 1) / 2) (2 * j + 1) (hConicDifference Rzero)
          (hasHPoleProfile_hConicDifference (2 * j + 1) Rzero hRzero))
  have hidentity :
      ell ^ (2 * j + 1) * hConicDifference Rzero ^ 2 =
        ell * scaledA ^ 2 := by
    dsimp only [scaledA]
    rw [pow_add]
    norm_num
    ring
  change HRatFuncRegularAt (-1 : ℂ)
      (ell ^ (2 * j + 1) * hConicDifference Rzero ^ 2) ∧
    RatFunc.eval (RingHom.id ℂ) (-1)
      (ell ^ (2 * j + 1) * hConicDifference Rzero ^ 2) = 0
  rw [hidentity]
  have hregular := hRatFuncRegularAt_mul hellRegular
    (hRatFuncRegularAt_pow hscaledA 2)
  refine ⟨hregular, ?_⟩
  rw [h_ratFunc_eval_mul_regular (-1) _ _ hellRegular
      (hRatFuncRegularAt_pow hscaledA 2),
    hellZero, zero_mul]

/-- Scaling the hard norm by its pole factor rewrites it in terms of the
scaled descended square and the two scaled conic functions. -/
theorem hHardOdd_pole_scaled_norm_identity
    (Rzero : MvPolynomial (Fin 2) ℂ) (coefficient : ℂ) (N : ℕ) :
    let ell : RatFunc ℂ :=
      algebraMap ℂ[X] (RatFunc ℂ) (3 * (Polynomial.X + 1))
    let B := ell ^ N * hConicDifference Rzero ^ 2
    ell ^ (2 * N) * hHardOddNorm Rzero coefficient N =
      (B + algebraMap ℂ (RatFunc ℂ) (coefficient ^ 2) *
          ((ell * hConicParamW) ^ N -
            (ell * hConicParamCapitalW) ^ N)) ^ 2 -
        algebraMap ℂ (RatFunc ℂ) (4 * coefficient ^ 2) *
          B * (ell * hConicParamW) ^ N := by
  simp only [hHardOddNorm]
  ring

/-- The leading value of the scaled odd hard norm at the pole is nonzero. -/
theorem hHardOdd_pole_scaled_norm_eval_ne_zero
    (Rzero : MvPolynomial (Fin 2) ℂ) (coefficient : ℂ) (N : ℕ)
    (hNodd : Odd N) (hcoefficient : coefficient ≠ 0)
    (hRzero : Rzero.IsWeightedHomogeneous hFormWeight N) :
    let ell : RatFunc ℂ :=
      algebraMap ℂ[X] (RatFunc ℂ) (3 * (Polynomial.X + 1))
    HRatFuncRegularAt (-1 : ℂ)
        (ell ^ (2 * N) * hHardOddNorm Rzero coefficient N) ∧
      RatFunc.eval (RingHom.id ℂ) (-1)
          (ell ^ (2 * N) * hHardOddNorm Rzero coefficient N) ≠ 0 := by
  let ell : RatFunc ℂ :=
    algebraMap ℂ[X] (RatFunc ℂ) (3 * (Polynomial.X + 1))
  let B : RatFunc ℂ := ell ^ N * hConicDifference Rzero ^ 2
  have hB := hHardOdd_scaled_difference_square_regular_and_zero_at_pole
    Rzero N hNodd hRzero
  have hellW : HRatFuncRegularAt (-1 : ℂ)
      (ell * hConicParamW) := by
    dsimp only [ell]
    rw [h_conic_profile_linear_mul_w]
    apply hRatFuncRegularAt_of_denom_dvd
      (RatFunc.denom_div_dvd
        (-hConicParamOneFactor * hConicParamWFactor)
        (hConicParamDenominator ^ 2))
    norm_num [Polynomial.eval_pow, hConicParamDenominator]
  have hellCapitalW : HRatFuncRegularAt (-1 : ℂ)
      (ell * hConicParamCapitalW) := by
    dsimp only [ell]
    rw [h_conic_profile_linear_mul_capitalW]
    apply hRatFuncRegularAt_of_denom_dvd
      (RatFunc.denom_div_dvd
        (-hConicParamOneFactor * hConicParamCapitalWFactor)
        (hConicParamDenominator ^ 2))
    norm_num [Polynomial.eval_pow, hConicParamDenominator]
  let cTwo : RatFunc ℂ := algebraMap ℂ (RatFunc ℂ) (coefficient ^ 2)
  let cFour : RatFunc ℂ :=
    algebraMap ℂ (RatFunc ℂ) (4 * coefficient ^ 2)
  have hcTwo : HRatFuncRegularAt (-1 : ℂ) cTwo := by
    change HRatFuncRegularAt (-1 : ℂ) (RatFunc.C (coefficient ^ 2))
    exact hRatFuncRegularAt_C (-1) _
  have hcFour : HRatFuncRegularAt (-1 : ℂ) cFour := by
    change HRatFuncRegularAt (-1 : ℂ)
      (RatFunc.C (4 * coefficient ^ 2))
    exact hRatFuncRegularAt_C (-1) _
  have hwpow := hRatFuncRegularAt_pow hellW N
  have hWpow := hRatFuncRegularAt_pow hellCapitalW N
  have hpowers := hRatFuncRegularAt_sub hwpow hWpow
  have hmiddle := hRatFuncRegularAt_add hB.1
    (hRatFuncRegularAt_mul hcTwo hpowers)
  have hleft := hRatFuncRegularAt_pow hmiddle 2
  have hright := hRatFuncRegularAt_mul
    (hRatFuncRegularAt_mul hcFour hB.1) hwpow
  have hidentity := hHardOdd_pole_scaled_norm_identity
    Rzero coefficient N
  change HRatFuncRegularAt (-1 : ℂ)
      (ell ^ (2 * N) * hHardOddNorm Rzero coefficient N) ∧ _
  rw [hidentity]
  refine ⟨hRatFuncRegularAt_sub hleft hright, ?_⟩
  have hcTwoEval :
      RatFunc.eval (RingHom.id ℂ) (-1)
          (algebraMap ℂ (RatFunc ℂ) (coefficient ^ 2)) =
        coefficient ^ 2 := by
    change RatFunc.eval (RingHom.id ℂ) (-1)
      (RatFunc.C (coefficient ^ 2)) = coefficient ^ 2
    rw [RatFunc.eval_C]
    rfl
  have hcFourEval :
      RatFunc.eval (RingHom.id ℂ) (-1)
          (algebraMap ℂ (RatFunc ℂ) (4 * coefficient ^ 2)) =
        4 * coefficient ^ 2 := by
    change RatFunc.eval (RingHom.id ℂ) (-1)
      (RatFunc.C (4 * coefficient ^ 2)) = 4 * coefficient ^ 2
    rw [RatFunc.eval_C]
    rfl
  rw [h_ratFunc_eval_sub (-1) _ _ hleft hright,
    h_ratFunc_eval_pow (-1) _ hmiddle,
    h_ratFunc_eval_add_regular (-1) _ _ hB.1
      (hRatFuncRegularAt_mul hcTwo hpowers),
    hB.2,
    h_ratFunc_eval_mul_regular (-1) _ _ hcTwo hpowers,
    h_ratFunc_eval_sub (-1) _ _ hwpow hWpow,
    h_ratFunc_eval_pow (-1) _ hellW,
    h_ratFunc_eval_pow (-1) _ hellCapitalW,
    h_ratFunc_eval_mul_regular (-1) _ _
      (hRatFuncRegularAt_mul hcFour hB.1) hwpow,
    h_ratFunc_eval_mul_regular (-1) _ _ hcFour hB.1,
    hB.2,
    hcTwoEval, hcFourEval,
    h_conic_profile_linear_scaled_values_at_pole.1,
    h_conic_profile_linear_scaled_values_at_pole.2]
  have hoddPowers : (-3 : ℂ) ^ N - 3 ^ N ≠ 0 := by
    rw [hNodd.neg_pow]
    intro hzero
    have hthreePower : (3 : ℂ) ^ N = 0 := by
      linear_combination (-1 / 2) * hzero
    exact (pow_ne_zero N (by norm_num : (3 : ℂ) ≠ 0)) hthreePower
  simpa only [zero_add, mul_zero, zero_mul, sub_zero] using
    pow_ne_zero 2
      (mul_ne_zero (pow_ne_zero 2 hcoefficient) hoddPowers)

/-- A represented hard norm numerator cannot vanish at `m = -1`. -/
theorem not_hHardOddNorm_numerator_isRoot_pole
    (Rzero : MvPolynomial (Fin 2) ℂ) (coefficient : ℂ) (N : ℕ)
    (hNodd : Odd N) (hcoefficient : coefficient ≠ 0)
    (hRzero : Rzero.IsWeightedHomogeneous hFormWeight N)
    (numerator : ℂ[X])
    (hrepresentation :
      hHardOddNorm Rzero coefficient N =
        algebraMap ℂ[X] (RatFunc ℂ) numerator /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (2 * N) (4 * N))) :
    ¬ numerator.IsRoot (-1 : ℂ) := by
  intro hroot
  let ell : RatFunc ℂ :=
    algebraMap ℂ[X] (RatFunc ℂ) (3 * (Polynomial.X + 1))
  have hscaled := hHardOdd_pole_scaled_norm_eval_ne_zero
    Rzero coefficient N hNodd hcoefficient hRzero
  have hdenEval :
      (hConicParamDenominator (K := ℂ) ^ (4 * N)).eval (-1) ≠ 0 := by
    norm_num [Polynomial.eval_pow, hConicParamDenominator]
  have hscaledRepresentation :
      ell ^ (2 * N) * hHardOddNorm Rzero coefficient N =
        algebraMap ℂ[X] (RatFunc ℂ) numerator /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hConicParamDenominator ^ (4 * N)) := by
    rw [hrepresentation, hPoleProfileDenominator]
    dsimp only [ell]
    simp only [map_mul, map_pow]
    have hell : algebraMap ℂ[X] (RatFunc ℂ)
        (3 * (Polynomial.X + 1)) ≠ 0 :=
      RatFunc.algebraMap_ne_zero
        (h_conic_profile_linear_ne_zero (K := ℂ))
    have hden : algebraMap ℂ[X] (RatFunc ℂ)
        (hConicParamDenominator (K := ℂ)) ≠ 0 :=
      RatFunc.algebraMap_ne_zero h_conic_param_denominator_ne_zero
    field_simp [hell, hden]
    simpa [mul_assoc] using
      (mul_div_cancel_left₀
        (algebraMap ℂ[X] (RatFunc ℂ) numerator)
        (pow_ne_zero (2 * N) hell))
  have heval := congrArg (RatFunc.eval (RingHom.id ℂ) (-1))
    hscaledRepresentation
  rw [h_ratFunc_eval_algebraMap_div (-1) numerator
      (hConicParamDenominator ^ (4 * N)) hdenEval] at heval
  have hnumerator : numerator.eval (-1 : ℂ) = 0 := hroot
  rw [hnumerator, zero_div] at heval
  exact hscaled.2 heval

end OnLeConjecture.DThree
