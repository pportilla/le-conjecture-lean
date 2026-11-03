/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HProjectiveDifferenceFiniteBoundary

/-!
# The pole boundary of the projective H difference section

The pole at `m = -1` is removed by multiplying a form of weight `2a` by
the `a`th power of `3(m + 1)`. Its boundary value is obtained by setting the
first variable to zero and retaining the rescaled second variable.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial
open scoped Polynomial WithZero

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem h_ratFunc_eval_mul_regular
    (a : K) (f g : RatFunc K)
    (hf : HRatFuncRegularAt a f) (hg : HRatFuncRegularAt a g) :
    RatFunc.eval (RingHom.id K) a (f * g) =
      RatFunc.eval (RingHom.id K) a f *
        RatFunc.eval (RingHom.id K) a g := by
  let P : MvPolynomial (Fin 2) K :=
    MvPolynomial.X 0 * MvPolynomial.X 1
  have hsource : hFormEval f g P = f * g := by
    simp only [P, hFormEval, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_X]
    simp
  have htarget :
      hFormEval (RatFunc.eval (RingHom.id K) a f)
          (RatFunc.eval (RingHom.id K) a g) P =
        RatFunc.eval (RingHom.id K) a f *
          RatFunc.eval (RingHom.id K) a g := by
    simp only [P, hFormEval]
    simp
  have h := h_ratFunc_eval_hFormEval a f g P hf hg
  rw [hsource, htarget] at h
  exact h

omit [CharZero K] in
theorem h_ratFunc_eval_add_regular
    (a : K) (f g : RatFunc K)
    (hf : HRatFuncRegularAt a f) (hg : HRatFuncRegularAt a g) :
    RatFunc.eval (RingHom.id K) a (f + g) =
      RatFunc.eval (RingHom.id K) a f +
        RatFunc.eval (RingHom.id K) a g := by
  let P : MvPolynomial (Fin 2) K :=
    MvPolynomial.X 0 + MvPolynomial.X 1
  have hsource : hFormEval f g P = f + g := by
    simp only [P, hFormEval, MvPolynomial.eval₂_add,
      MvPolynomial.eval₂_X]
    simp
  have htarget :
      hFormEval (RatFunc.eval (RingHom.id K) a f)
          (RatFunc.eval (RingHom.id K) a g) P =
        RatFunc.eval (RingHom.id K) a f +
          RatFunc.eval (RingHom.id K) a g := by
    simp only [P, hFormEval]
    simp
  have h := h_ratFunc_eval_hFormEval a f g P hf hg
  rw [hsource, htarget] at h
  exact h

omit [CharZero K] in
theorem hRatFuncRegularAt_pow
    {a : K} {f : RatFunc K}
    (hf : HRatFuncRegularAt a f) (n : ℕ) :
    HRatFuncRegularAt a (f ^ n) := by
  induction n with
  | zero =>
      simpa using hRatFuncRegularAt_algebraMap (K := K) a 1
  | succ n ih =>
      rw [pow_succ]
      exact hRatFuncRegularAt_mul ih hf

omit [CharZero K] in
theorem h_ratFunc_eval_pow
    (a : K) (f : RatFunc K)
    (hf : HRatFuncRegularAt a f) (n : ℕ) :
    RatFunc.eval (RingHom.id K) a (f ^ n) =
      RatFunc.eval (RingHom.id K) a f ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ,
        h_ratFunc_eval_mul_regular a (f ^ n) f
          (hRatFuncRegularAt_pow hf n) hf, ih]

omit [CharZero K] in
theorem hRatFuncRegularAt_C (a : K) (c : K) :
    HRatFuncRegularAt a (RatFunc.C c) := by
  change HRatFuncRegularAt a
    (algebraMap K[X] (RatFunc K) (Polynomial.C c))
  exact hRatFuncRegularAt_algebraMap a (Polynomial.C c)

omit [CharZero K] in
/-- The scaled value of an even weight form at a zero of the scaling
function is its value on the boundary `x = 0`. -/
theorem h_pole_scaled_form_regular_and_eval
    (point : K) (ell x w : RatFunc K) (a : ℕ)
    (F : MvPolynomial (Fin 2) K)
    (hF : F.IsWeightedHomogeneous hFormWeight (2 * a))
    (hell : HRatFuncRegularAt point ell)
    (hx : HRatFuncRegularAt point x)
    (hscaledW : HRatFuncRegularAt point (ell * w))
    (hellZero : RatFunc.eval (RingHom.id K) point ell = 0) :
    HRatFuncRegularAt point (ell ^ a * hFormEval x w F) ∧
      RatFunc.eval (RingHom.id K) point
          (ell ^ a * hFormEval x w F) =
        hFormEval 0
          (RatFunc.eval (RingHom.id K) point (ell * w)) F := by
  induction hF using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
      constructor
      · simpa [hFormEval] using
          hRatFuncRegularAt_algebraMap (K := K) point 0
      · simp [hFormEval]
  | add F G hF hG ihF ihG =>
      have hidentity :
          ell ^ a * hFormEval x w (F + G) =
            ell ^ a * hFormEval x w F +
              ell ^ a * hFormEval x w G := by
        simp [hFormEval, mul_add]
      rw [hidentity]
      constructor
      · exact hRatFuncRegularAt_add ihF.1 ihG.1
      · rw [h_ratFunc_eval_add_regular point _ _ ihF.1 ihG.1,
          ihF.2, ihG.2]
        simp [hFormEval]
  | monomial d c hd =>
      have hweight : d 0 + 2 * d 1 = 2 * a := by
        rw [h_form_weight_apply] at hd
        exact hd
      have hj : d 1 ≤ a := by omega
      have hidentity :
          ell ^ a * hFormEval x w (MvPolynomial.monomial d c) =
            RatFunc.C c * ell ^ (a - d 1) * x ^ d 0 *
              (ell * w) ^ d 1 := by
        have hpowers :
            ell ^ (a - d 1) * ell ^ d 1 = ell ^ a := by
          rw [← pow_add, Nat.sub_add_cancel hj]
        rw [hFormEval_monomial, mul_pow]
        calc
          ell ^ a * (RatFunc.C c * x ^ d 0 * w ^ d 1) =
              RatFunc.C c * ell ^ a * x ^ d 0 * w ^ d 1 := by
            ring
          _ = RatFunc.C c *
              (ell ^ (a - d 1) * ell ^ d 1) *
                x ^ d 0 * w ^ d 1 := by rw [hpowers]
          _ = RatFunc.C c * ell ^ (a - d 1) * x ^ d 0 *
              (ell ^ d 1 * w ^ d 1) := by ring
      have hcRegular := hRatFuncRegularAt_C point c
      have hellPower := hRatFuncRegularAt_pow hell (a - d 1)
      have hxPower := hRatFuncRegularAt_pow hx (d 0)
      have hwPower := hRatFuncRegularAt_pow hscaledW (d 1)
      have hfirstRegular := hRatFuncRegularAt_mul hcRegular hellPower
      have hsecondRegular := hRatFuncRegularAt_mul hfirstRegular hxPower
      rw [hidentity]
      constructor
      · exact hRatFuncRegularAt_mul hsecondRegular hwPower
      · rw [h_ratFunc_eval_mul_regular point _ _
            hsecondRegular hwPower,
          h_ratFunc_eval_mul_regular point _ _
            hfirstRegular hxPower,
          h_ratFunc_eval_mul_regular point _ _
            hcRegular hellPower,
          h_ratFunc_eval_pow point ell hell,
          h_ratFunc_eval_pow point x hx,
          h_ratFunc_eval_pow point (ell * w) hscaledW,
          RatFunc.eval_C, hellZero,
          hFormEval_monomial]
        by_cases hi : d 0 = 0
        · have hjEqual : d 1 = a := by omega
          simp [hi, hjEqual]
        · have hdifference : a - d 1 ≠ 0 := by omega
          simp [hi, hdifference]

omit [CharZero K] in
/-- An odd weight form vanishes when its first variable is zero. -/
theorem hFormEval_zero_first_of_odd_weight
    (F : MvPolynomial (Fin 2) K) (N : ℕ)
    (hF : F.IsWeightedHomogeneous hFormWeight N)
    (hN : Odd N) (w : K) :
    hFormEval 0 w F = 0 := by
  induction hF using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp [hFormEval]
  | add F G hF hG ihF ihG =>
      rw [show hFormEval 0 w (F + G) =
          hFormEval 0 w F + hFormEval 0 w G by
        simp [hFormEval], ihF, ihG, add_zero]
  | monomial d c hd =>
      have hweight : d 0 + 2 * d 1 = N := by
        rw [h_form_weight_apply] at hd
        exact hd
      obtain ⟨k, hk⟩ := hN
      have hi : d 0 ≠ 0 := by
        intro hi
        rw [hi, zero_add] at hweight
        omega
      rw [hFormEval_monomial]
      simp [hi]

/-- Multiplication by `3(m + 1)` removes the simple pole of `w`. -/
theorem h_conic_profile_linear_mul_w :
    algebraMap K[X] (RatFunc K) (3 * (Polynomial.X + 1)) *
        hConicParamW =
      algebraMap K[X] (RatFunc K)
          (-hConicParamOneFactor * hConicParamWFactor) /
        algebraMap K[X] (RatFunc K) (hConicParamDenominator ^ 2) := by
  have honeAddX :
      algebraMap K[X] (RatFunc K) (1 + Polynomial.X) ≠ 0 := by
    apply RatFunc.algebraMap_ne_zero
    simpa [add_comm] using
      Polynomial.X_add_C_ne_zero (1 : K)
  have hthree :
      algebraMap K[X] (RatFunc K) (3 : K[X]) ≠ 0 := by
    apply RatFunc.algebraMap_ne_zero
    norm_num
  have hcancel (r : RatFunc K) :
      algebraMap K[X] (RatFunc K) (1 + Polynomial.X) * r *
          (algebraMap K[X] (RatFunc K)
            (1 + Polynomial.X))⁻¹ = r := by
    calc
      algebraMap K[X] (RatFunc K) (1 + Polynomial.X) * r *
            (algebraMap K[X] (RatFunc K)
              (1 + Polynomial.X))⁻¹ =
          (algebraMap K[X] (RatFunc K) (1 + Polynomial.X) *
              (algebraMap K[X] (RatFunc K)
                (1 + Polynomial.X))⁻¹) * r := by
            ring
      _ = r := by rw [mul_inv_cancel₀ honeAddX, one_mul]
  simp only [hConicParamW, hConicParamFunctionDenominator,
    map_mul, map_pow]
  field_simp [RatFunc.algebraMap_ne_zero
    h_conic_param_denominator_ne_zero,
    RatFunc.algebraMap_ne_zero
      (h_conic_profile_linear_ne_zero (K := K)),
    RatFunc.algebraMap_ne_zero
      (Polynomial.X_add_C_ne_zero (1 : K)), honeAddX, hthree]
  simpa [div_eq_mul_inv, add_comm, mul_assoc] using hcancel
    (algebraMap K[X] (RatFunc K) (-hConicParamOneFactor) *
      algebraMap K[X] (RatFunc K) hConicParamWFactor)

/-- Multiplication by `3(m + 1)` removes the simple pole of `W`. -/
theorem h_conic_profile_linear_mul_capitalW :
    algebraMap K[X] (RatFunc K) (3 * (Polynomial.X + 1)) *
        hConicParamCapitalW =
      algebraMap K[X] (RatFunc K)
          (-hConicParamOneFactor * hConicParamCapitalWFactor) /
        algebraMap K[X] (RatFunc K) (hConicParamDenominator ^ 2) := by
  have honeAddX :
      algebraMap K[X] (RatFunc K) (1 + Polynomial.X) ≠ 0 := by
    apply RatFunc.algebraMap_ne_zero
    simpa [add_comm] using
      Polynomial.X_add_C_ne_zero (1 : K)
  have hthree :
      algebraMap K[X] (RatFunc K) (3 : K[X]) ≠ 0 := by
    apply RatFunc.algebraMap_ne_zero
    norm_num
  have hcancel (r : RatFunc K) :
      algebraMap K[X] (RatFunc K) (1 + Polynomial.X) * r *
          (algebraMap K[X] (RatFunc K)
            (1 + Polynomial.X))⁻¹ = r := by
    calc
      algebraMap K[X] (RatFunc K) (1 + Polynomial.X) * r *
            (algebraMap K[X] (RatFunc K)
              (1 + Polynomial.X))⁻¹ =
          (algebraMap K[X] (RatFunc K) (1 + Polynomial.X) *
              (algebraMap K[X] (RatFunc K)
                (1 + Polynomial.X))⁻¹) * r := by
            ring
      _ = r := by rw [mul_inv_cancel₀ honeAddX, one_mul]
  simp only [hConicParamCapitalW, hConicParamFunctionDenominator,
    map_mul, map_pow]
  field_simp [RatFunc.algebraMap_ne_zero
    h_conic_param_denominator_ne_zero,
    RatFunc.algebraMap_ne_zero
      (h_conic_profile_linear_ne_zero (K := K)),
    RatFunc.algebraMap_ne_zero
      (Polynomial.X_add_C_ne_zero (1 : K)), honeAddX, hthree]
  simpa [div_eq_mul_inv, add_comm, mul_assoc] using hcancel
    (algebraMap K[X] (RatFunc K) (-hConicParamOneFactor) *
      algebraMap K[X] (RatFunc K) hConicParamCapitalWFactor)

/-- The two conic functions have boundary values `-3` and `3` after their
simple poles at `m = -1` are removed. -/
theorem h_conic_profile_linear_scaled_values_at_pole :
    RatFunc.eval (RingHom.id K) (-1)
        (algebraMap K[X] (RatFunc K) (3 * (Polynomial.X + 1)) *
          hConicParamW) = -3 ∧
      RatFunc.eval (RingHom.id K) (-1)
        (algebraMap K[X] (RatFunc K) (3 * (Polynomial.X + 1)) *
          hConicParamCapitalW) = 3 := by
  rw [h_conic_profile_linear_mul_w,
    h_conic_profile_linear_mul_capitalW,
    h_ratFunc_eval_algebraMap_div,
    h_ratFunc_eval_algebraMap_div]
  · norm_num [hConicParamOneFactor, hConicParamWFactor,
      hConicParamCapitalWFactor, hConicParamDenominator]
  · norm_num [hConicParamDenominator]
  · norm_num [hConicParamDenominator]

/-- A numerator root at `m = -1` forces equality of an even weight form at
the two pole boundary points. -/
theorem hFormEval_eq_at_pole_boundary_of_even_weight
    (a : ℕ) (F : MvPolynomial (Fin 2) K)
    (hF : F.IsWeightedHomogeneous hFormWeight (2 * a))
    (p : K[X])
    (hrepresentation :
      hConicDifference F =
        algebraMap K[X] (RatFunc K) p /
          algebraMap K[X] (RatFunc K)
            (hPoleProfileDenominator a (2 * a)))
    (hroot : p.IsRoot (-1 : K)) :
    hFormEval 0 (-3 : K) F = hFormEval 0 3 F := by
  let ell : RatFunc K :=
    algebraMap K[X] (RatFunc K) (3 * (Polynomial.X + 1))
  have hellRegular : HRatFuncRegularAt (-1 : K) ell :=
    hRatFuncRegularAt_algebraMap (-1) (3 * (Polynomial.X + 1))
  have hellZero :
      RatFunc.eval (RingHom.id K) (-1) ell = 0 := by
    change RatFunc.eval (RingHom.id K) (-1)
      (algebraMap K[X] (RatFunc K)
        (3 * (Polynomial.X + 1))) = 0
    rw [h_ratFunc_eval_algebraMap_id]
    norm_num
  have honeRegular : HRatFuncRegularAt (-1 : K) (1 : RatFunc K) := by
    simpa using hRatFuncRegularAt_algebraMap (K := K) (-1) 1
  have hxRegular :
      HRatFuncRegularAt (-1 : K) (hConicParamX (K := K)) := by
    apply hRatFuncRegularAt_of_denom_dvd
      (RatFunc.denom_div_dvd hConicParamXNumerator
        hConicParamDenominator)
    norm_num [hConicParamDenominator]
  have hwScaledRegular :
      HRatFuncRegularAt (-1 : K) (ell * hConicParamW) := by
    change HRatFuncRegularAt (-1 : K)
      (algebraMap K[X] (RatFunc K) (3 * (Polynomial.X + 1)) *
        hConicParamW)
    rw [h_conic_profile_linear_mul_w]
    apply hRatFuncRegularAt_of_denom_dvd
      (RatFunc.denom_div_dvd
        (-hConicParamOneFactor * hConicParamWFactor)
        (hConicParamDenominator ^ 2))
    norm_num [hConicParamDenominator]
  have hWScaledRegular :
      HRatFuncRegularAt (-1 : K) (ell * hConicParamCapitalW) := by
    change HRatFuncRegularAt (-1 : K)
      (algebraMap K[X] (RatFunc K) (3 * (Polynomial.X + 1)) *
        hConicParamCapitalW)
    rw [h_conic_profile_linear_mul_capitalW]
    apply hRatFuncRegularAt_of_denom_dvd
      (RatFunc.denom_div_dvd
        (-hConicParamOneFactor * hConicParamCapitalWFactor)
        (hConicParamDenominator ^ 2))
    norm_num [hConicParamDenominator]
  have hfirst := h_pole_scaled_form_regular_and_eval
    (-1 : K) ell 1 hConicParamW a F hF hellRegular
      honeRegular hwScaledRegular hellZero
  have hsecond := h_pole_scaled_form_regular_and_eval
    (-1 : K) ell hConicParamX hConicParamCapitalW a F hF
      hellRegular hxRegular hWScaledRegular hellZero
  have hscaledRepresentation :
      ell ^ a * hConicDifference F =
        algebraMap K[X] (RatFunc K) p /
          algebraMap K[X] (RatFunc K)
            (hConicParamDenominator ^ (2 * a)) := by
    rw [hrepresentation, hPoleProfileDenominator]
    simp only [ell, map_mul, map_pow]
    have hlinearPower :
        algebraMap K[X] (RatFunc K)
            (3 * (Polynomial.X + 1)) ^ a ≠ 0 :=
      pow_ne_zero a (RatFunc.algebraMap_ne_zero
        (h_conic_profile_linear_ne_zero (K := K)))
    have honeAddX :
        algebraMap K[X] (RatFunc K) (1 + Polynomial.X) ≠ 0 := by
      apply RatFunc.algebraMap_ne_zero
      simpa [add_comm] using
        Polynomial.X_add_C_ne_zero (1 : K)
    have hthree :
        algebraMap K[X] (RatFunc K) (3 : K[X]) ≠ 0 := by
      apply RatFunc.algebraMap_ne_zero
      norm_num
    have hcancelPowers (r : RatFunc K) :
        algebraMap K[X] (RatFunc K) (3 : K[X]) ^ a *
            algebraMap K[X] (RatFunc K) (1 + Polynomial.X) ^ a *
            r *
            (algebraMap K[X] (RatFunc K) (3 : K[X]))⁻¹ ^ a *
            (algebraMap K[X] (RatFunc K)
              (1 + Polynomial.X))⁻¹ ^ a = r := by
      calc
        algebraMap K[X] (RatFunc K) (3 : K[X]) ^ a *
              algebraMap K[X] (RatFunc K)
                (1 + Polynomial.X) ^ a * r *
              (algebraMap K[X] (RatFunc K) (3 : K[X]))⁻¹ ^ a *
              (algebraMap K[X] (RatFunc K)
                (1 + Polynomial.X))⁻¹ ^ a =
            (algebraMap K[X] (RatFunc K) (3 : K[X]) *
                (algebraMap K[X] (RatFunc K) (3 : K[X]))⁻¹) ^ a *
              (algebraMap K[X] (RatFunc K)
                  (1 + Polynomial.X) *
                (algebraMap K[X] (RatFunc K)
                  (1 + Polynomial.X))⁻¹) ^ a * r := by
            rw [mul_pow, mul_pow]
            ring
        _ = r := by
          rw [mul_inv_cancel₀ hthree, mul_inv_cancel₀ honeAddX]
          simp
    field_simp [RatFunc.algebraMap_ne_zero
      h_conic_param_denominator_ne_zero, hlinearPower,
      honeAddX, hthree]
    simpa [div_eq_mul_inv, mul_pow, inv_pow, add_comm,
      mul_comm, mul_left_comm, mul_assoc] using
        hcancelPowers (algebraMap K[X] (RatFunc K) p)
  have hzero :
      RatFunc.eval (RingHom.id K) (-1)
          (ell ^ a * hConicDifference F) = 0 := by
    rw [hscaledRepresentation,
      h_ratFunc_eval_algebraMap_div]
    · have hpole : p.eval (-1 : K) = 0 := hroot
      rw [hpole, zero_div]
    · norm_num [hConicParamDenominator]
  have hscaledDifference :
      ell ^ a * hConicDifference F =
        ell ^ a * hFormEval 1 hConicParamW F -
          ell ^ a * hFormEval hConicParamX
            hConicParamCapitalW F := by
    simp only [hConicDifference, hFirstConicPullback,
      hSecondConicPullback]
    ring
  rw [hscaledDifference,
    h_ratFunc_eval_sub (-1) _ _ hfirst.1 hsecond.1,
    hfirst.2, hsecond.2,
    h_conic_profile_linear_scaled_values_at_pole.1,
    h_conic_profile_linear_scaled_values_at_pole.2] at hzero
  exact sub_eq_zero.mp hzero

/-- The two pole boundary points form a nontrivial fibre pair. -/
theorem h_pole_boundary_fibre :
    (-3 : K) ≠ 3 ∧
      hP 0 (-3 : K) = hP 0 3 ∧
      hQ 0 (-3 : K) = hQ 0 3 := by
  constructor
  · norm_num
  constructor
  · norm_num [hP, hQ]
  · norm_num [hP, hQ]

/-- A profile numerator root at `m = -1` gives a projective fibre zero for
every weighted homogeneous form. -/
theorem exists_h_projective_difference_zero_at_pole_boundary
    (N : ℕ) (F : MvPolynomial (Fin 2) K)
    (hF : F.IsWeightedHomogeneous hFormWeight N)
    (p : K[X])
    (hrepresentation :
      hConicDifference F =
        algebraMap K[X] (RatFunc K) p /
          algebraMap K[X] (RatFunc K)
            (hPoleProfileDenominator (N / 2) N))
    (hroot : p.IsRoot (-1 : K)) :
    ∃ w W : K,
      w ≠ W ∧ hP 0 w = hP 0 W ∧ hQ 0 w = hQ 0 W ∧
        hFormEval 0 w F = hFormEval 0 W F := by
  refine ⟨-3, 3, h_pole_boundary_fibre.1,
    h_pole_boundary_fibre.2.1,
    h_pole_boundary_fibre.2.2, ?_⟩
  rcases Nat.even_or_odd N with hEven | hOdd
  · obtain ⟨a, rfl⟩ := hEven
    have hF' :
        F.IsWeightedHomogeneous hFormWeight (2 * a) := by
      simpa [two_mul] using hF
    have hrepresentation' :
        hConicDifference F =
          algebraMap K[X] (RatFunc K) p /
            algebraMap K[X] (RatFunc K)
              (hPoleProfileDenominator a (2 * a)) := by
      simpa [two_mul, show (a + a) / 2 = a by omega] using
        hrepresentation
    exact hFormEval_eq_at_pole_boundary_of_even_weight
      a F hF' p hrepresentation' hroot
  · rw [hFormEval_zero_first_of_odd_weight F N hF hOdd (-3),
      hFormEval_zero_first_of_odd_weight F N hF hOdd 3]

end OnLeConjecture.DThree
