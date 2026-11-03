/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HHardOddRootCount
public import OnLeConjecture.DThree.HReciprocalCollision

/-!
# The parameter infinity alternative for the odd H norm

A degree drop in the fixed norm profile gives a zero in the reciprocal
chart. The reciprocal conic point is regular. Factoring the norm into its
four sign conjugates therefore gives an affine collision for the odd hard
form.
-/

public section

noncomputable section

namespace OnLeConjecture.DThree

open _root_.Polynomial
open scoped WithZero

/-- A zero of the scalar norm formula gives square roots for which one sign
difference vanishes. -/
theorem exists_signs_hard_difference_zero_of_formula_zero
    (coefficient A w W : ℂ) (N : ℕ) (hNodd : Odd N)
    (hzero :
      (A ^ 2 + coefficient ^ 2 * (w ^ N - W ^ N)) ^ 2 -
          (4 * coefficient ^ 2) * A ^ 2 * w ^ N = 0) :
    ∃ t T : ℂ,
      t ^ 2 = w ∧
      T ^ 2 = W ∧
      A + coefficient * (t ^ N - T ^ N) = 0 := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq
    w (by norm_num : 0 < 2)
  obtain ⟨T, hT⟩ := IsAlgClosed.exists_pow_nat_eq
    W (by norm_num : 0 < 2)
  have hproduct := hHardOddNorm_eq_sign_product
    coefficient t T N A w W ht hT
  rw [hzero] at hproduct
  rcases mul_eq_zero.mp hproduct with hleft | hfourth
  · rcases mul_eq_zero.mp hleft with hleft | hthird
    · rcases mul_eq_zero.mp hleft with hfirst | hsecond
      · exact ⟨t, T, ht, hT, hfirst⟩
      · exact ⟨t, -T, ht, by simpa using hT,
          by simpa only [hNodd.neg_pow, sub_neg_eq_add] using hsecond⟩
    · exact ⟨-t, T, by simpa using ht, hT,
        by simpa only [hNodd.neg_pow] using hthird⟩
  · exact ⟨-t, -T, by simpa using ht, by simpa using hT,
      by simpa only [hNodd.neg_pow, sub_neg_eq_add] using hfourth⟩

/-- Reciprocal substitution preserves the displayed hard norm formula. -/
theorem h_reciprocalRatFuncRingHom_hHardOddNorm
    (Rzero : MvPolynomial (Fin 2) ℂ) (coefficient : ℂ) (N : ℕ) :
    hReciprocalRatFuncRingHom (hHardOddNorm Rzero coefficient N) =
      let A := hReciprocalRatFuncRingHom (hConicDifference Rzero)
      (A ^ 2 + algebraMap ℂ (RatFunc ℂ) (coefficient ^ 2) *
          (hMinusParamW ^ N - hMinusParamCapitalW ^ N)) ^ 2 -
        algebraMap ℂ (RatFunc ℂ) (4 * coefficient ^ 2) *
          A ^ 2 * hMinusParamW ^ N := by
  simp only [hHardOddNorm, map_sub, map_add, map_mul, map_pow,
    h_reciprocalRatFuncRingHom_algebraMap_scalar,
    h_reciprocalRatFuncRingHom_hConicParamW,
    h_reciprocalRatFuncRingHom_hConicParamCapitalW]

/-- Evaluation of the reciprocal descended difference at zero is the
difference at the affine conic point represented by parameter infinity. -/
theorem h_reciprocal_hConicDifference_eval_zero
    (Rzero : MvPolynomial (Fin 2) ℂ) :
    RatFunc.eval (RingHom.id ℂ) 0
        (hReciprocalRatFuncRingHom (hConicDifference Rzero)) =
      hFormEval 1 (-(1 / 3) : ℂ) Rzero -
        hFormEval (-1) (-(1 / 3) : ℂ) Rzero := by
  rw [h_reciprocalRatFuncRingHom_hConicDifference]
  have hfirstRegular := hRatFuncRegularAt_hFormEval
    0 1 (hMinusParamW (K := ℂ)) Rzero
      (by simpa using hRatFuncRegularAt_algebraMap (K := ℂ) 0 1)
      h_minus_param_regular_at_zero.2.1
  have hsecondRegular := hRatFuncRegularAt_hFormEval
    0 (hMinusParamX (K := ℂ)) hMinusParamCapitalW Rzero
      h_minus_param_regular_at_zero.1
      h_minus_param_regular_at_zero.2.2
  rw [h_ratFunc_eval_sub 0 _ _ hfirstRegular hsecondRegular,
    h_ratFunc_eval_hFormEval 0 1 hMinusParamW Rzero
      (by simpa using hRatFuncRegularAt_algebraMap (K := ℂ) 0 1)
      h_minus_param_regular_at_zero.2.1,
    h_ratFunc_eval_hFormEval 0 hMinusParamX hMinusParamCapitalW Rzero
      h_minus_param_regular_at_zero.1
      h_minus_param_regular_at_zero.2.2,
    h_minus_param_values_at_zero.1,
    h_minus_param_values_at_zero.2.1,
    h_minus_param_values_at_zero.2.2,
    RatFunc.eval_one]

/-- Evaluation of the reciprocal hard norm at zero is its scalar norm
formula at the reciprocal conic point. -/
theorem h_reciprocal_hHardOddNorm_eval_zero
    (Rzero : MvPolynomial (Fin 2) ℂ) (coefficient : ℂ) (N : ℕ) :
    RatFunc.eval (RingHom.id ℂ) 0
        (hReciprocalRatFuncRingHom
          (hHardOddNorm Rzero coefficient N)) =
      let A := RatFunc.eval (RingHom.id ℂ) 0
        (hReciprocalRatFuncRingHom (hConicDifference Rzero))
      let w := (-(1 / 3) : ℂ)
      (A ^ 2 + coefficient ^ 2 * (w ^ N - w ^ N)) ^ 2 -
        (4 * coefficient ^ 2) * A ^ 2 * w ^ N := by
  rw [h_reciprocalRatFuncRingHom_hHardOddNorm]
  let A := hReciprocalRatFuncRingHom (hConicDifference Rzero)
  have hA : HRatFuncRegularAt 0 A := by
    dsimp only [A]
    rw [h_reciprocalRatFuncRingHom_hConicDifference]
    exact hRatFuncRegularAt_sub
      (hRatFuncRegularAt_hFormEval 0 1 hMinusParamW Rzero
        (by simpa using hRatFuncRegularAt_algebraMap (K := ℂ) 0 1)
        h_minus_param_regular_at_zero.2.1)
      (hRatFuncRegularAt_hFormEval 0 hMinusParamX
        hMinusParamCapitalW Rzero h_minus_param_regular_at_zero.1
          h_minus_param_regular_at_zero.2.2)
  let cTwo : RatFunc ℂ := algebraMap ℂ (RatFunc ℂ) (coefficient ^ 2)
  let cFour : RatFunc ℂ :=
    algebraMap ℂ (RatFunc ℂ) (4 * coefficient ^ 2)
  have hcTwo : HRatFuncRegularAt 0 cTwo := by
    change HRatFuncRegularAt 0 (RatFunc.C (coefficient ^ 2))
    exact hRatFuncRegularAt_C 0 _
  have hcFour : HRatFuncRegularAt 0 cFour := by
    change HRatFuncRegularAt 0 (RatFunc.C (4 * coefficient ^ 2))
    exact hRatFuncRegularAt_C 0 _
  have hcTwoEval :
      RatFunc.eval (RingHom.id ℂ) 0
        (algebraMap ℂ (RatFunc ℂ) (coefficient ^ 2)) =
          coefficient ^ 2 := by
    change RatFunc.eval (RingHom.id ℂ) 0
      (RatFunc.C (coefficient ^ 2)) = coefficient ^ 2
    rw [RatFunc.eval_C]
    rfl
  have hcFourEval :
      RatFunc.eval (RingHom.id ℂ) 0
        (algebraMap ℂ (RatFunc ℂ) (4 * coefficient ^ 2)) =
        4 * coefficient ^ 2 := by
    change RatFunc.eval (RingHom.id ℂ) 0
      (RatFunc.C (4 * coefficient ^ 2)) = 4 * coefficient ^ 2
    rw [RatFunc.eval_C]
    rfl
  have hwRegular :
      HRatFuncRegularAt (0 : ℂ) (hMinusParamW (K := ℂ)) :=
    h_minus_param_regular_at_zero.2.1
  have hWRegular :
      HRatFuncRegularAt (0 : ℂ) (hMinusParamCapitalW (K := ℂ)) :=
    h_minus_param_regular_at_zero.2.2
  have hASquare := hRatFuncRegularAt_pow hA 2
  have hwPower := hRatFuncRegularAt_pow hwRegular N
  have hWPower := hRatFuncRegularAt_pow hWRegular N
  have hpowers := hRatFuncRegularAt_sub hwPower hWPower
  have hscaled := hRatFuncRegularAt_mul hcTwo hpowers
  have hmiddle := hRatFuncRegularAt_add hASquare hscaled
  have hleft := hRatFuncRegularAt_pow hmiddle 2
  have hright := hRatFuncRegularAt_mul
    (hRatFuncRegularAt_mul hcFour hASquare) hwPower
  rw [h_ratFunc_eval_sub 0 _ _ hleft hright,
    h_ratFunc_eval_pow 0 _ hmiddle,
    h_ratFunc_eval_add_regular 0 _ _ hASquare hscaled,
    h_ratFunc_eval_pow 0 A hA,
    h_ratFunc_eval_mul_regular 0 _ _ hcTwo hpowers,
    h_ratFunc_eval_sub 0 _ _ hwPower hWPower,
    h_ratFunc_eval_pow 0 _ hwRegular,
    h_ratFunc_eval_pow 0 _ hWRegular,
    h_ratFunc_eval_mul_regular 0 _ _
      (hRatFuncRegularAt_mul hcFour hASquare) hwPower,
    h_ratFunc_eval_mul_regular 0 _ _ hcFour hASquare,
    h_ratFunc_eval_pow 0 A hA,
    h_ratFunc_eval_pow 0 _ hwRegular,
    hcTwoEval, hcFourEval,
    h_minus_param_values_at_zero.2.1,
    h_minus_param_values_at_zero.2.2]

/-- A degree drop in the hard norm profile gives an explicit affine off
diagonal fibre pair. -/
theorem exists_hard_odd_affine_fibre_of_norm_degree_drop
    (Rzero : MvPolynomial (Fin 2) ℂ) (coefficient : ℂ) (N : ℕ)
    (hNodd : Odd N) (numerator : ℂ[X]) (hnumerator : numerator ≠ 0)
    (hdegree : numerator.natDegree < 10 * N)
    (hrepresentation :
      hHardOddNorm Rzero coefficient N =
        algebraMap ℂ[X] (RatFunc ℂ) numerator /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (2 * N) (4 * N))) :
    ∃ t T : ℂ,
      (1 : ℂ) ≠ -1 ∧
      hP 1 (t ^ 2) = hP (-1) (T ^ 2) ∧
      hQ 1 (t ^ 2) = hQ (-1) (T ^ 2) ∧
      hFormEval 1 (t ^ 2) Rzero + coefficient * t ^ N =
        hFormEval (-1) (T ^ 2) Rzero + coefficient * T ^ N := by
  have hdegreeProfile :
      numerator.natDegree < 2 * N + 2 * (4 * N) := by
    omega
  obtain ⟨k, hk, horderInfinity⟩ :=
    h_order_at_infinity_positive_of_pole_profile_degree_drop
      (2 * N) (4 * N) hnumerator hdegreeProfile hrepresentation
  have horderZero :
      hFiniteOrderAt (0 : ℂ)
          (hReciprocalRatFuncRingHom
            (hHardOddNorm Rzero coefficient N)) =
        WithZero.exp (k : ℤ) := by
    rw [h_finite_order_reciprocalRatFuncRingHom]
    exact horderInfinity
  have hnormZero := h_ratFunc_eval_eq_zero_of_finite_order_pos
    0 (hReciprocalRatFuncRingHom
      (hHardOddNorm Rzero coefficient N)) k hk horderZero
  rw [h_reciprocal_hHardOddNorm_eval_zero] at hnormZero
  let A := RatFunc.eval (RingHom.id ℂ) 0
    (hReciprocalRatFuncRingHom (hConicDifference Rzero))
  let w : ℂ := -(1 / 3)
  obtain ⟨t, T, ht, hT, hsection⟩ :=
    exists_signs_hard_difference_zero_of_formula_zero
      coefficient A w w N hNodd (by simpa [A, w] using hnormZero)
  have hPfiber :=
    (h_parameter_infinity_off_diagonal_fibre (K := ℂ)).2.1
  have hQfiber :=
    (h_parameter_infinity_off_diagonal_fibre (K := ℂ)).2.2
  have hPfiber' : hP 1 (t ^ 2) = hP (-1) (T ^ 2) := by
    rw [ht, hT]
    simpa only [w] using hPfiber
  have hQfiber' : hQ 1 (t ^ 2) = hQ (-1) (T ^ 2) := by
    rw [ht, hT]
    simpa only [w] using hQfiber
  have hthird :
      hFormEval 1 (t ^ 2) Rzero + coefficient * t ^ N =
        hFormEval (-1) (T ^ 2) Rzero + coefficient * T ^ N := by
    dsimp only [A] at hsection
    rw [h_reciprocal_hConicDifference_eval_zero Rzero] at hsection
    rw [ht, hT]
    linear_combination hsection
  exact ⟨t, T,
    (h_parameter_infinity_off_diagonal_fibre (K := ℂ)).1,
    hPfiber', hQfiber', hthird⟩

end OnLeConjecture.DThree
