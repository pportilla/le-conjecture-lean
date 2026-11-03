/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HProfileInfinity
public import OnLeConjecture.DThree.HDerivativeLocalOrder
public import Mathlib.Algebra.Polynomial.Reverse

/-!
# Boundary values of the projective H difference section

Reciprocal substitution identifies order at parameter infinity with order at
zero in the reciprocal chart. A degree drop in the fixed pole profile then
forces the homogeneous difference to vanish at the regular conic point
represented by parameter infinity.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial
open scoped Polynomial WithZero

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- Reciprocal polynomial substitution is a reversed polynomial divided by
the corresponding power of the parameter. -/
theorem h_reciprocalPolynomialRingHom_eq_reverse_div
    (p : K[X]) :
    hReciprocalPolynomialRingHom p =
      algebraMap K[X] (RatFunc K) p.reverse /
        RatFunc.X ^ p.natDegree := by
  let _ : Invertible (RatFunc.X : RatFunc K) :=
    invertibleOfNonzero RatFunc.X_ne_zero
  apply (eq_div_iff (pow_ne_zero _ RatFunc.X_ne_zero)).2
  have hreverse := Polynomial.eval₂_reflect_mul_pow
    (algebraMap K (RatFunc K)) (RatFunc.X : RatFunc K)
    p.natDegree p.reverse p.reverse_natDegree_le
  change Polynomial.eval₂ (algebraMap K (RatFunc K))
      (1 / RatFunc.X) p * RatFunc.X ^ p.natDegree =
    algebraMap K[X] (RatFunc K) p.reverse
  simpa only [Polynomial.reverse, Polynomial.reflect_reflect,
    invOf_eq_inv, one_div, ← Polynomial.aeval_def,
    RatFunc.aeval_X_left_eq_algebraMap] using hreverse

omit [CharZero K] in
/-- Reciprocal substitution turns polynomial degree into order at zero. -/
theorem h_finite_order_reciprocalPolynomialRingHom
    (p : K[X]) (hp : p ≠ 0) :
    hFiniteOrderAt (0 : K) (hReciprocalPolynomialRingHom p) =
      WithZero.exp (-(p.natDegree : ℤ)) := by
  have hreverseEval : p.reverse.eval (0 : K) ≠ 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.coeff_zero_reverse]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  have hparameter :
      hFiniteOrderAt (0 : K) (RatFunc.X : RatFunc K) =
        WithZero.exp (1 : ℤ) := by
    simpa using h_finite_order_parameter (K := K) 0
  rw [h_reciprocalPolynomialRingHom_eq_reverse_div, map_div₀,
    map_pow, h_finite_order_polynomial_of_eval_ne_zero
      0 p.reverse hreverseEval,
    hparameter]
  simp [← WithZero.exp_neg]

omit [CharZero K] in
/-- Reciprocal substitution transports the order at infinity to the finite
order at zero. -/
theorem h_finite_order_reciprocalRatFuncRingHom
    (f : RatFunc K) :
    hFiniteOrderAt (0 : K) (hReciprocalRatFuncRingHom f) =
      hOrderAtInfinity f := by
  by_cases hf : f = 0
  · simp [hf]
  have hmap :
      hReciprocalRatFuncRingHom f =
        hReciprocalPolynomialRingHom f.num /
          hReciprocalPolynomialRingHom f.denom := by
    conv_lhs =>
      rw [← RatFunc.num_div_denom f]
    rw [map_div₀, h_reciprocalRatFuncRingHom_algebraMap,
      h_reciprocalRatFuncRingHom_algebraMap]
    rfl
  rw [hmap, map_div₀,
    h_finite_order_reciprocalPolynomialRingHom f.num
      (RatFunc.num_ne_zero hf),
    h_finite_order_reciprocalPolynomialRingHom f.denom
      f.denom_ne_zero,
    h_order_at_infinity_eq_natDegree_sub f hf]
  calc
    WithZero.exp (-(f.num.natDegree : ℤ)) /
          WithZero.exp (-(f.denom.natDegree : ℤ)) =
        WithZero.exp (-(f.num.natDegree : ℤ) -
          -(f.denom.natDegree : ℤ)) :=
      (WithZero.exp_sub _ _).symm
    _ = WithZero.exp ((f.denom.natDegree : ℤ) -
        f.num.natDegree) := by
      congr 1
      ring

omit [CharZero K] in
/-- A rational function is regular at a finite parameter value when its
reduced denominator does not vanish there. -/
@[expose]
def HRatFuncRegularAt (a : K) (f : RatFunc K) : Prop :=
  f.denom.eval a ≠ 0

omit [CharZero K] in
theorem hRatFuncRegularAt_of_denom_dvd
    {a : K} {f : RatFunc K} {q : K[X]}
    (hdiv : f.denom ∣ q) (hq : q.eval a ≠ 0) :
    HRatFuncRegularAt a f := by
  rcases hdiv with ⟨c, rfl⟩
  intro hden
  rw [Polynomial.eval_mul, hden, zero_mul] at hq
  exact hq rfl

omit [CharZero K] in
theorem hRatFuncRegularAt_algebraMap (a : K) (p : K[X]) :
    HRatFuncRegularAt a (algebraMap K[X] (RatFunc K) p) := by
  simp [HRatFuncRegularAt]

omit [CharZero K] in
theorem hRatFuncRegularAt_add
    {a : K} {f g : RatFunc K}
    (hf : HRatFuncRegularAt a f) (hg : HRatFuncRegularAt a g) :
    HRatFuncRegularAt a (f + g) := by
  apply hRatFuncRegularAt_of_denom_dvd
    (RatFunc.denom_add_dvd f g)
  simpa [Polynomial.eval_mul] using mul_ne_zero hf hg

omit [CharZero K] in
theorem hRatFuncRegularAt_mul
    {a : K} {f g : RatFunc K}
    (hf : HRatFuncRegularAt a f) (hg : HRatFuncRegularAt a g) :
    HRatFuncRegularAt a (f * g) := by
  apply hRatFuncRegularAt_of_denom_dvd
    (RatFunc.denom_mul_dvd f g)
  simpa [Polynomial.eval_mul] using mul_ne_zero hf hg

omit [CharZero K] in
theorem hRatFuncRegularAt_sub
    {a : K} {f g : RatFunc K}
    (hf : HRatFuncRegularAt a f) (hg : HRatFuncRegularAt a g) :
    HRatFuncRegularAt a (f - g) := by
  have hq : f.denom * g.denom ≠ 0 :=
    mul_ne_zero f.denom_ne_zero g.denom_ne_zero
  have hrepresentation :
      f - g =
        algebraMap K[X] (RatFunc K)
            (f.num * g.denom - f.denom * g.num) /
          algebraMap K[X] (RatFunc K) (f.denom * g.denom) := by
    conv_lhs =>
      rw [← RatFunc.num_div_denom f,
        ← RatFunc.num_div_denom g]
    rw [map_sub, map_mul, map_mul, map_mul,
      div_sub_div]
    · exact RatFunc.algebraMap_ne_zero f.denom_ne_zero
    · exact RatFunc.algebraMap_ne_zero g.denom_ne_zero
  have hdiv : (f - g).denom ∣ f.denom * g.denom :=
    (RatFunc.denom_dvd hq).2 ⟨_, hrepresentation⟩
  apply hRatFuncRegularAt_of_denom_dvd hdiv
  simpa [Polynomial.eval_mul] using mul_ne_zero hf hg

omit [CharZero K] in
/-- Evaluation of a regular explicit polynomial fraction has the expected
value. -/
theorem h_ratFunc_eval_algebraMap_div
    (a : K) (p q : K[X]) (hq : q.eval a ≠ 0) :
    RatFunc.eval (RingHom.id K) a
        (algebraMap K[X] (RatFunc K) p /
          algebraMap K[X] (RatFunc K) q) =
      p.eval a / q.eval a := by
  let f : RatFunc K :=
    algebraMap K[X] (RatFunc K) p /
      algebraMap K[X] (RatFunc K) q
  have hqpoly : q ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.eval_zero] at hq
    exact hq rfl
  have hf : HRatFuncRegularAt a f :=
    hRatFuncRegularAt_of_denom_dvd
      (RatFunc.denom_div_dvd p q) hq
  have hqregular := hRatFuncRegularAt_algebraMap a q
  have hproduct := RatFunc.eval_mul
    (f := RingHom.id K) (a := a) hf hqregular
  have hidentity :
      f * algebraMap K[X] (RatFunc K) q =
        algebraMap K[X] (RatFunc K) p := by
    simp only [f]
    field_simp [RatFunc.algebraMap_ne_zero hqpoly]
  rw [hidentity, RatFunc.eval_algebraMap,
    RatFunc.eval_algebraMap] at hproduct
  have hproduct' :
      RatFunc.eval (RingHom.id K) a f * q.eval a = p.eval a := by
    simpa using hproduct.symm
  exact (eq_div_iff hq).2 hproduct'

omit [CharZero K] in
/-- Evaluation preserves subtraction at a point where both rational
functions are regular. -/
theorem h_ratFunc_eval_sub
    (a : K) (f g : RatFunc K)
    (hf : HRatFuncRegularAt a f) (hg : HRatFuncRegularAt a g) :
    RatFunc.eval (RingHom.id K) a (f - g) =
      RatFunc.eval (RingHom.id K) a f -
        RatFunc.eval (RingHom.id K) a g := by
  have hsub := hRatFuncRegularAt_sub hf hg
  have hadd := RatFunc.eval_add
    (f := RingHom.id K) (a := a) hsub hg
  rw [sub_add_cancel] at hadd
  exact eq_sub_of_add_eq hadd.symm

omit [CharZero K] in
/-- Substitution of regular rational functions in a bivariate polynomial is
regular. -/
theorem hRatFuncRegularAt_hFormEval
    (a : K) (x w : RatFunc K) (F : MvPolynomial (Fin 2) K)
    (hx : HRatFuncRegularAt a x) (hw : HRatFuncRegularAt a w) :
    HRatFuncRegularAt a (hFormEval x w F) := by
  induction F using MvPolynomial.induction_on with
  | C c =>
      simpa [hFormEval] using
        hRatFuncRegularAt_algebraMap a (Polynomial.C c)
  | add F G hF hG =>
      rw [show hFormEval x w (F + G) =
          hFormEval x w F + hFormEval x w G by
        simp [hFormEval]]
      exact hRatFuncRegularAt_add hF hG
  | mul_X F i hF =>
      rw [show hFormEval x w (F * MvPolynomial.X i) =
          hFormEval x w F * (if i = 0 then x else w) by
        simp [hFormEval]]
      fin_cases i
      · exact hRatFuncRegularAt_mul hF hx
      · exact hRatFuncRegularAt_mul hF hw

omit [CharZero K] in
/-- Evaluation at a regular point commutes with substitution in a bivariate
polynomial. -/
theorem h_ratFunc_eval_hFormEval
    (a : K) (x w : RatFunc K) (F : MvPolynomial (Fin 2) K)
    (hx : HRatFuncRegularAt a x) (hw : HRatFuncRegularAt a w) :
    RatFunc.eval (RingHom.id K) a (hFormEval x w F) =
      hFormEval (RatFunc.eval (RingHom.id K) a x)
        (RatFunc.eval (RingHom.id K) a w) F := by
  induction F using MvPolynomial.induction_on with
  | C c =>
      simp [hFormEval]
  | add F G hF hG =>
      rw [show hFormEval x w (F + G) =
          hFormEval x w F + hFormEval x w G by
        simp [hFormEval]]
      rw [RatFunc.eval_add (RingHom.id K) a
        (hRatFuncRegularAt_hFormEval a x w F hx hw)
        (hRatFuncRegularAt_hFormEval a x w G hx hw), hF, hG]
      simp [hFormEval]
  | mul_X F i hF =>
      rw [show hFormEval x w (F * MvPolynomial.X i) =
          hFormEval x w F * (if i = 0 then x else w) by
        simp [hFormEval]]
      rw [RatFunc.eval_mul (RingHom.id K) a
        (hRatFuncRegularAt_hFormEval a x w F hx hw)]
      · rw [hF]
        fin_cases i
        · simp [hFormEval]
        · simp [hFormEval]
      · fin_cases i
        · exact hx
        · exact hw

omit [CharZero K] in
/-- Positive finite order forces the value of a rational function to be zero
at that parameter. -/
theorem h_ratFunc_eval_eq_zero_of_finite_order_pos
    (a : K) (f : RatFunc K) (k : ℕ) (hk : 0 < k)
    (horder : hFiniteOrderAt a f = WithZero.exp (k : ℤ)) :
    RatFunc.eval (RingHom.id K) a f = 0 := by
  have hf : f ≠ 0 := h_ratFunc_ne_zero_of_finite_order horder
  have hcoeff := h_divisor_coefficients_of_finite_order hf a k horder
  rw [h_finite_zero_divisor_apply] at hcoeff
  have hroot : f.num.IsRoot a :=
    (Polynomial.rootMultiplicity_pos (RatFunc.num_ne_zero hf)).1 (by
      rw [hcoeff.1]
      exact hk)
  rw [RatFunc.eval, show Polynomial.eval₂ (RingHom.id K) a f.num = 0 by
    simpa [Polynomial.IsRoot] using hroot, zero_div]

/-- The reciprocal conic coordinates are regular at parameter zero. -/
theorem h_minus_param_regular_at_zero :
    HRatFuncRegularAt (0 : K) (hMinusParamX (K := K)) ∧
      HRatFuncRegularAt (0 : K) hMinusParamW ∧
      HRatFuncRegularAt (0 : K) hMinusParamCapitalW := by
  refine ⟨?_, ?_, ?_⟩
  · apply hRatFuncRegularAt_of_denom_dvd
      (RatFunc.denom_div_dvd hMinusParamXNumerator
        hMinusParamDenominator)
    norm_num [hMinusParamDenominator]
  · apply hRatFuncRegularAt_of_denom_dvd
      (RatFunc.denom_div_dvd hMinusParamWNumerator
        hMinusParamFunctionDenominator)
    norm_num [hMinusParamFunctionDenominator, hMinusParamDenominator]
  · apply hRatFuncRegularAt_of_denom_dvd
      (RatFunc.denom_div_dvd hMinusParamCapitalWNumerator
        hMinusParamFunctionDenominator)
    norm_num [hMinusParamFunctionDenominator, hMinusParamDenominator]

/-- The reciprocal conic coordinates at parameter zero represent the regular
point corresponding to parameter infinity in the original chart. -/
theorem h_minus_param_values_at_zero :
    RatFunc.eval (RingHom.id K) 0 (hMinusParamX (K := K)) = -1 ∧
      RatFunc.eval (RingHom.id K) 0 hMinusParamW = -(1 / 3) ∧
      RatFunc.eval (RingHom.id K) 0 hMinusParamCapitalW = -(1 / 3) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hMinusParamX,
      h_ratFunc_eval_algebraMap_div]
    · norm_num [hMinusParamXNumerator, hMinusParamDenominator]
    · norm_num [hMinusParamDenominator]
  · rw [hMinusParamW,
      h_ratFunc_eval_algebraMap_div]
    · norm_num [hMinusParamWNumerator,
        hMinusParamFunctionDenominator, hMinusParamDenominator]
    · norm_num [hMinusParamFunctionDenominator,
        hMinusParamDenominator]
  · rw [hMinusParamCapitalW,
      h_ratFunc_eval_algebraMap_div]
    · norm_num [hMinusParamCapitalWNumerator,
        hMinusParamFunctionDenominator, hMinusParamDenominator]
    · norm_num [hMinusParamFunctionDenominator,
        hMinusParamDenominator]

/-- A degree drop in a pole profile for the conic difference gives equality
of the homogeneous form at the two points represented by parameter
infinity. -/
theorem hFormEval_eq_at_parameter_infinity_of_profile_degree_drop
    (a b : ℕ) (F : MvPolynomial (Fin 2) K) (p : K[X])
    (hp : p ≠ 0) (hdegree : p.natDegree < a + 2 * b)
    (hrepresentation :
      hConicDifference F =
        algebraMap K[X] (RatFunc K) p /
          algebraMap K[X] (RatFunc K)
            (hPoleProfileDenominator a b)) :
    hFormEval 1 (-(1 / 3) : K) F =
      hFormEval (-1) (-(1 / 3) : K) F := by
  obtain ⟨k, hk, horderInfinity⟩ :=
    h_order_at_infinity_positive_of_pole_profile_degree_drop
      a b hp hdegree hrepresentation
  have horderZero :
      hFiniteOrderAt (0 : K)
          (hReciprocalRatFuncRingHom (hConicDifference F)) =
        WithZero.exp (k : ℤ) := by
    rw [h_finite_order_reciprocalRatFuncRingHom]
    exact horderInfinity
  have hzero := h_ratFunc_eval_eq_zero_of_finite_order_pos
    0 (hReciprocalRatFuncRingHom (hConicDifference F)) k
      (by omega) horderZero
  rw [h_reciprocalRatFuncRingHom_hConicDifference] at hzero
  have hfirstRegular := hRatFuncRegularAt_hFormEval
    0 1 (hMinusParamW (K := K)) F
      (by simpa using hRatFuncRegularAt_algebraMap (K := K) 0 1)
      h_minus_param_regular_at_zero.2.1
  have hsecondRegular := hRatFuncRegularAt_hFormEval
    0 (hMinusParamX (K := K)) hMinusParamCapitalW F
      h_minus_param_regular_at_zero.1
      h_minus_param_regular_at_zero.2.2
  rw [h_ratFunc_eval_sub 0 _ _ hfirstRegular hsecondRegular,
    h_ratFunc_eval_hFormEval 0 1 hMinusParamW F
      (by simpa using hRatFuncRegularAt_algebraMap (K := K) 0 1)
      h_minus_param_regular_at_zero.2.1,
    h_ratFunc_eval_hFormEval 0 hMinusParamX hMinusParamCapitalW F
      h_minus_param_regular_at_zero.1
      h_minus_param_regular_at_zero.2.2,
    h_minus_param_values_at_zero.1,
    h_minus_param_values_at_zero.2.1,
    h_minus_param_values_at_zero.2.2,
    RatFunc.eval_one] at hzero
  exact sub_eq_zero.mp hzero

/-- The two points represented by parameter infinity are distinct and lie in
one fibre of the `H` pair. -/
theorem h_parameter_infinity_off_diagonal_fibre :
    (1 : K) ≠ -1 ∧
      hP 1 (-(1 / 3) : K) = hP (-1) (-(1 / 3) : K) ∧
      hQ 1 (-(1 / 3) : K) = hQ (-1) (-(1 / 3) : K) := by
  constructor
  · norm_num
  constructor
  · norm_num [hP, hQ]
  · norm_num [hP, hQ]

/-- A pole profile degree drop gives an explicit off diagonal fibre point at
which the weighted homogeneous difference vanishes. -/
theorem exists_h_projective_difference_zero_of_profile_degree_drop
    (a b : ℕ) (F : MvPolynomial (Fin 2) K) (p : K[X])
    (hp : p ≠ 0) (hdegree : p.natDegree < a + 2 * b)
    (hrepresentation :
      hConicDifference F =
        algebraMap K[X] (RatFunc K) p /
          algebraMap K[X] (RatFunc K)
            (hPoleProfileDenominator a b)) :
    ∃ x w X W : K,
      x ≠ X ∧ hP x w = hP X W ∧ hQ x w = hQ X W ∧
        hFormEval x w F = hFormEval X W F := by
  refine ⟨1, -(1 / 3), -1, -(1 / 3),
    h_parameter_infinity_off_diagonal_fibre.1,
    h_parameter_infinity_off_diagonal_fibre.2.1,
    h_parameter_infinity_off_diagonal_fibre.2.2, ?_⟩
  exact hFormEval_eq_at_parameter_infinity_of_profile_degree_drop
    a b F p hp hdegree hrepresentation

omit [CharZero K] in
/-- Two distinct roots of the quadratic above `X = 1` exhaust its roots. -/
theorem h_conic_one_roots_exhaust
    {a b z : K}
    (ha : a ^ 2 + 2 * a + 4 = 0)
    (hb : b ^ 2 + 2 * b + 4 = 0)
    (hab : a ≠ b)
    (hz : z ^ 2 + 2 * z + 4 = 0) :
    z = a ∨ z = b := by
  have hsumProduct : (a - b) * (a + b + 2) = 0 := by
    calc
      (a - b) * (a + b + 2) =
          (a ^ 2 + 2 * a + 4) -
            (b ^ 2 + 2 * b + 4) := by ring
      _ = 0 := by rw [ha, hb, sub_zero]
  have hsum : a + b = -2 := by
    have hsecond : a + b + 2 = 0 :=
      (mul_eq_zero.mp hsumProduct).resolve_left
        (sub_ne_zero.mpr hab)
    linear_combination hsecond
  have hbFormula : b = -2 - a := by
    linear_combination hsum
  have hproduct : a * b = 4 := by
    rw [hbFormula]
    linear_combination -ha
  have hfactor : (z - a) * (z - b) = 0 := by
    calc
      (z - a) * (z - b) =
          z ^ 2 - (a + b) * z + a * b := by ring
      _ = z ^ 2 + 2 * z + 4 := by
        rw [hsum, hproduct]
        ring
      _ = 0 := hz
  rcases mul_eq_zero.mp hfactor with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

/-- Nonvanishing of a positive pole profile denominator excludes both finite
boundary factors. -/
theorem h_pole_profile_factors_ne_zero
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (z : K)
    (hprofile :
      (hPoleProfileDenominator (K := K) a b).eval z ≠ 0) :
    z + 1 ≠ 0 ∧ hConicParamDenominator.eval z ≠ 0 := by
  have hproduct :
      (3 * (z + 1)) ^ a *
          (hConicParamDenominator (K := K).eval z) ^ b ≠ 0 := by
    simpa [hPoleProfileDenominator] using hprofile
  obtain ⟨hlinearPower, hdenPower⟩ := mul_ne_zero_iff.mp hproduct
  have hlinear : (3 : K) * (z + 1) ≠ 0 :=
    (pow_ne_zero_iff (Nat.ne_of_gt ha)).mp hlinearPower
  exact ⟨(mul_ne_zero_iff.mp hlinear).2,
    (pow_ne_zero_iff (Nat.ne_of_gt hb)).mp hdenPower⟩

/-- The original conic coordinates are regular away from the two finite
profile boundary factors. -/
theorem h_conic_param_regular_at
    (z : K)
    (hlinear : z + 1 ≠ 0)
    (hden : hConicParamDenominator (K := K).eval z ≠ 0) :
    HRatFuncRegularAt z (hConicParamX (K := K)) ∧
      HRatFuncRegularAt z hConicParamW ∧
      HRatFuncRegularAt z hConicParamCapitalW := by
  have hfunctionDen :
      hConicParamFunctionDenominator (K := K).eval z ≠ 0 := by
    simp only [hConicParamFunctionDenominator, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_one, Polynomial.eval_ofNat]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hlinear)
      (pow_ne_zero 2 hden)
  refine ⟨?_, ?_, ?_⟩
  · apply hRatFuncRegularAt_of_denom_dvd
      (RatFunc.denom_div_dvd hConicParamXNumerator
        hConicParamDenominator)
    exact hden
  · apply hRatFuncRegularAt_of_denom_dvd
      (RatFunc.denom_div_dvd
        (-hConicParamOneFactor * hConicParamWFactor)
        hConicParamFunctionDenominator)
    exact hfunctionDen
  · apply hRatFuncRegularAt_of_denom_dvd
      (RatFunc.denom_div_dvd
        (-hConicParamOneFactor * hConicParamCapitalWFactor)
        hConicParamFunctionDenominator)
    exact hfunctionDen

omit [CharZero K] in
/-- Evaluation of the polynomial forms `hPForm` and `hQForm` recovers the two
coordinates of the `H` pair. -/
theorem hFormEval_hPForm_hQForm
    {A : Type*} [Field A] [Algebra K A] (x w : A) :
    hFormEval x w (hPForm (K := K)) = hP x w ∧
      hFormEval x w (hQForm (K := K)) = hQ x w := by
  constructor
  · simp [hFormEval, hPForm, hFormX, hFormW, hP, map_ofNat]
    ring
  · simp [hFormEval, hQForm, hFormX, hFormW, hQ, map_ofNat]
    ring

omit [CharZero K] in
theorem hFormEval_hPForm
    {A : Type*} [Field A] [Algebra K A] (x w : A) :
    hFormEval x w (hPForm (K := K)) = hP x w :=
  (hFormEval_hPForm_hQForm x w).1

omit [CharZero K] in
theorem hFormEval_hQForm
    {A : Type*} [Field A] [Algebra K A] (x w : A) :
    hFormEval x w (hQForm (K := K)) = hQ x w :=
  (hFormEval_hPForm_hQForm x w).2

/-- Evaluation of the rational parametrization away from its finite boundary
gives two points in one fibre of the `H` pair. -/
theorem h_conic_param_eval_fibre
    (z : K)
    (hlinear : z + 1 ≠ 0)
    (hden : hConicParamDenominator (K := K).eval z ≠ 0) :
    hP 1 (RatFunc.eval (RingHom.id K) z hConicParamW) =
        hP (RatFunc.eval (RingHom.id K) z hConicParamX)
          (RatFunc.eval (RingHom.id K) z hConicParamCapitalW) ∧
      hQ 1 (RatFunc.eval (RingHom.id K) z hConicParamW) =
        hQ (RatFunc.eval (RingHom.id K) z hConicParamX)
          (RatFunc.eval (RingHom.id K) z hConicParamCapitalW) := by
  obtain ⟨hPfiber, hQfiber⟩ :=
    h_conic_param_fibre_equations (K := K)
  obtain ⟨hxRegular, hwRegular, hWRegular⟩ :=
    h_conic_param_regular_at z hlinear hden
  have honeRegular : HRatFuncRegularAt z (1 : RatFunc K) := by
    simpa using hRatFuncRegularAt_algebraMap (K := K) z 1
  have hPeval := congrArg (RatFunc.eval (RingHom.id K) z) hPfiber
  have hQeval := congrArg (RatFunc.eval (RingHom.id K) z) hQfiber
  rw [← hFormEval_hPForm (K := K) 1 hConicParamW,
    ← hFormEval_hPForm (K := K)
      hConicParamX hConicParamCapitalW] at hPeval
  rw [← hFormEval_hQForm (K := K) 1 hConicParamW,
    ← hFormEval_hQForm (K := K)
      hConicParamX hConicParamCapitalW] at hQeval
  rw [h_ratFunc_eval_hFormEval z 1 hConicParamW hPForm
      honeRegular hwRegular,
    h_ratFunc_eval_hFormEval z hConicParamX hConicParamCapitalW hPForm
      hxRegular hWRegular,
    hFormEval_hPForm,
    hFormEval_hPForm,
    RatFunc.eval_one] at hPeval
  rw [
    h_ratFunc_eval_hFormEval z 1 hConicParamW hQForm
      honeRegular hwRegular,
    h_ratFunc_eval_hFormEval z hConicParamX hConicParamCapitalW hQForm
      hxRegular hWRegular,
    hFormEval_hQForm,
    hFormEval_hQForm,
    RatFunc.eval_one] at hQeval
  exact ⟨hPeval, hQeval⟩

/-- Away from the profile boundary, a root of the fixed numerator is an
affine zero of the conic difference. -/
theorem hFormEval_eq_of_profile_numerator_root
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (F : MvPolynomial (Fin 2) K) (p : K[X]) (z : K)
    (hrepresentation :
      hConicDifference F =
        algebraMap K[X] (RatFunc K) p /
          algebraMap K[X] (RatFunc K)
            (hPoleProfileDenominator a b))
    (hroot : p.IsRoot z)
    (hprofile :
      (hPoleProfileDenominator (K := K) a b).eval z ≠ 0) :
    hFormEval 1 (RatFunc.eval (RingHom.id K) z hConicParamW) F =
      hFormEval (RatFunc.eval (RingHom.id K) z hConicParamX)
        (RatFunc.eval (RingHom.id K) z hConicParamCapitalW) F := by
  obtain ⟨hlinear, hden⟩ :=
    h_pole_profile_factors_ne_zero a b ha hb z hprofile
  obtain ⟨hxRegular, hwRegular, hWRegular⟩ :=
    h_conic_param_regular_at z hlinear hden
  have honeRegular : HRatFuncRegularAt z (1 : RatFunc K) := by
    simpa using hRatFuncRegularAt_algebraMap (K := K) z 1
  have hfirstRegular := hRatFuncRegularAt_hFormEval
    z 1 hConicParamW F honeRegular hwRegular
  have hsecondRegular := hRatFuncRegularAt_hFormEval
    z hConicParamX hConicParamCapitalW F hxRegular hWRegular
  have hzero :
      RatFunc.eval (RingHom.id K) z (hConicDifference F) = 0 := by
    rw [hrepresentation,
      h_ratFunc_eval_algebraMap_div z p
        (hPoleProfileDenominator a b) hprofile]
    have hrootEval : p.eval z = 0 := hroot
    rw [hrootEval, zero_div]
  rw [hConicDifference, hFirstConicPullback,
    hSecondConicPullback,
    h_ratFunc_eval_sub z _ _ hfirstRegular hsecondRegular,
    h_ratFunc_eval_hFormEval z 1 hConicParamW F
      honeRegular hwRegular,
    h_ratFunc_eval_hFormEval z hConicParamX hConicParamCapitalW F
      hxRegular hWRegular,
    RatFunc.eval_one] at hzero
  exact sub_eq_zero.mp hzero

/-- An affine parameter away from the two points above `X = 1` gives an off
diagonal pair. -/
theorem h_conic_param_eval_x_ne_one
    {a b z : K}
    (ha : a ^ 2 + 2 * a + 4 = 0)
    (hb : b ^ 2 + 2 * b + 4 = 0)
    (hab : a ≠ b) (hza : z ≠ a) (hzb : z ≠ b)
    (hden : hConicParamDenominator (K := K).eval z ≠ 0) :
    RatFunc.eval (RingHom.id K) z (hConicParamX (K := K)) ≠ 1 := by
  have hxvalue :
      RatFunc.eval (RingHom.id K) z (hConicParamX (K := K)) =
        hConicParamXNumerator.eval z /
          hConicParamDenominator.eval z := by
    exact h_ratFunc_eval_algebraMap_div z
      hConicParamXNumerator hConicParamDenominator hden
  intro hxOne
  rw [hxvalue] at hxOne
  have hnumerator :
      hConicParamXNumerator (K := K).eval z =
        hConicParamDenominator.eval z :=
    (div_eq_one_iff_eq hden).mp hxOne
  have hz : z ^ 2 + 2 * z + 4 = 0 := by
    simp only [hConicParamXNumerator, hConicParamDenominator,
      Polynomial.eval_neg, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_ofNat] at hnumerator
    linear_combination (-1 / 2) * hnumerator
  rcases h_conic_one_roots_exhaust ha hb hab hz with h | h
  · exact hza h
  · exact hzb h

/-- A numerator root away from the profile boundary and from the two points
above `X = 1` gives an off diagonal fibre zero. -/
theorem exists_h_projective_difference_zero_of_profile_numerator_root
    (aProfile bProfile : ℕ)
    (haProfile : 0 < aProfile) (hbProfile : 0 < bProfile)
    (F : MvPolynomial (Fin 2) K) (p : K[X])
    {a b z : K}
    (ha : a ^ 2 + 2 * a + 4 = 0)
    (hb : b ^ 2 + 2 * b + 4 = 0)
    (hab : a ≠ b) (hza : z ≠ a) (hzb : z ≠ b)
    (hrepresentation :
      hConicDifference F =
        algebraMap K[X] (RatFunc K) p /
          algebraMap K[X] (RatFunc K)
            (hPoleProfileDenominator aProfile bProfile))
    (hroot : p.IsRoot z)
    (hprofile :
      (hPoleProfileDenominator (K := K)
        aProfile bProfile).eval z ≠ 0) :
    ∃ x w X W : K,
      x ≠ X ∧ hP x w = hP X W ∧ hQ x w = hQ X W ∧
        hFormEval x w F = hFormEval X W F := by
  obtain ⟨hlinear, hden⟩ := h_pole_profile_factors_ne_zero
    aProfile bProfile haProfile hbProfile z hprofile
  refine ⟨1,
    RatFunc.eval (RingHom.id K) z hConicParamW,
    RatFunc.eval (RingHom.id K) z hConicParamX,
    RatFunc.eval (RingHom.id K) z hConicParamCapitalW,
    ?_, ?_, ?_, ?_⟩
  · exact Ne.symm (h_conic_param_eval_x_ne_one
      ha hb hab hza hzb hden)
  · exact (h_conic_param_eval_fibre z hlinear hden).1
  · exact (h_conic_param_eval_fibre z hlinear hden).2
  · exact hFormEval_eq_of_profile_numerator_root
      aProfile bProfile haProfile hbProfile F p z
        hrepresentation hroot hprofile

/-- A zero of a positive pole profile denominator lies at `m = -1` or at a
root of the parametrization denominator. -/
theorem h_pole_profile_denominator_root_classification
    (a b : ℕ) (z : K)
    (hzero :
      (hPoleProfileDenominator (K := K) a b).eval z = 0) :
    z = -1 ∨ hConicParamDenominator.eval z = 0 := by
  have hproduct :
      (3 * (z + 1)) ^ a *
          (hConicParamDenominator (K := K).eval z) ^ b = 0 := by
    simpa [hPoleProfileDenominator] using hzero
  rcases mul_eq_zero.mp hproduct with hlinearPower | hdenPower
  · have hlinear : (3 : K) * (z + 1) = 0 := by
      by_contra hne
      exact (pow_ne_zero a hne) hlinearPower
    have hz : z + 1 = 0 :=
      (mul_eq_zero.mp hlinear).resolve_left (by norm_num)
    left
    linear_combination hz
  · right
    by_contra hne
    exact (pow_ne_zero b hne) hdenPower

/-- The projective zero alternative gives an off diagonal affine collision
unless its finite numerator root lies on one of the two boundary factors. -/
theorem h_projective_difference_zero_or_boundary_of_profile_alternative
    (aProfile bProfile : ℕ)
    (haProfile : 0 < aProfile) (hbProfile : 0 < bProfile)
    (F : MvPolynomial (Fin 2) K) (p : K[X])
    (hp : p ≠ 0)
    (hrepresentation :
      hConicDifference F =
        algebraMap K[X] (RatFunc K) p /
          algebraMap K[X] (RatFunc K)
            (hPoleProfileDenominator aProfile bProfile))
    {a b : K}
    (ha : a ^ 2 + 2 * a + 4 = 0)
    (hb : b ^ 2 + 2 * b + 4 = 0)
    (hab : a ≠ b)
    (halternative :
      p.natDegree < aProfile + 2 * bProfile ∨
        ∃ z : K, z ≠ a ∧ z ≠ b ∧ p.IsRoot z) :
    (∃ x w X W : K,
      x ≠ X ∧ hP x w = hP X W ∧ hQ x w = hQ X W ∧
        hFormEval x w F = hFormEval X W F) ∨
      p.IsRoot (-1) ∨
        ∃ z : K,
          hConicParamDenominator.IsRoot z ∧ p.IsRoot z := by
  rcases halternative with hdegree | ⟨z, hza, hzb, hroot⟩
  · exact Or.inl
      (exists_h_projective_difference_zero_of_profile_degree_drop
        aProfile bProfile F p hp hdegree hrepresentation)
  · by_cases hprofile :
        (hPoleProfileDenominator (K := K)
          aProfile bProfile).eval z = 0
    · rcases h_pole_profile_denominator_root_classification
          aProfile bProfile z hprofile with hz | hden
      · right
        left
        simpa [hz] using hroot
      · right
        right
        exact ⟨z, by simpa [Polynomial.IsRoot] using hden, hroot⟩
    · left
      exact exists_h_projective_difference_zero_of_profile_numerator_root
        aProfile bProfile haProfile hbProfile F p ha hb hab hza hzb
          hrepresentation hroot hprofile

/-- The local derivative identity removes the derivative order assumptions
from the projective zero count. The two remaining alternatives are exactly
the boundary points `m = -1` and the roots of `m² + 2`. -/
theorem exists_hConicDifference_collision_or_boundary
    [IsAlgClosed K]
    (N kOne kTwo : ℕ) (hN : 5 ≤ N)
    (hkOne : 1 ≤ kOne) (hkTwo : 1 ≤ kTwo)
    (R LambdaP LambdaQ : MvPolynomial (Fin 2) K)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hLambdaP :
      hFormJacobian hPForm R = hFormW ^ 2 * LambdaP)
    (hLambdaQ :
      hFormJacobian hQForm R = hFormW ^ 2 * LambdaQ)
    {a b : K}
    (ha : a ^ 2 + 2 * a + 4 = 0)
    (hb : b ^ 2 + 2 * b + 4 = 0)
    (hab : a ≠ b)
    (hdifferenceA :
      hFiniteOrderAt a (hConicDifference R) =
        WithZero.exp (kOne : ℤ))
    (hdifferenceB :
      hFiniteOrderAt b (hConicDifference R) =
        WithZero.exp (kTwo : ℤ)) :
    (∃ x w X W : K,
      x ≠ X ∧ hP x w = hP X W ∧ hQ x w = hQ X W ∧
        hFormEval x w R = hFormEval X W R) ∨
      ∃ p : K[X],
        p ≠ 0 ∧
        p.natDegree ≤ N / 2 + 2 * N ∧
        hConicDifference R =
          algebraMap K[X] (RatFunc K) p /
            algebraMap K[X] (RatFunc K)
              (hPoleProfileDenominator (N / 2) N) ∧
        (p.IsRoot (-1) ∨
          ∃ z : K,
            hConicParamDenominator.IsRoot z ∧ p.IsRoot z) := by
  have hderivativeA := h_finite_order_hDerivativeRatFunc_at_one
    a ha R LambdaP LambdaQ hLambdaP hLambdaQ kOne
      (by omega) hdifferenceA
  have hderivativeB := h_finite_order_hDerivativeRatFunc_at_one
    b hb R LambdaP LambdaQ hLambdaP hLambdaQ kTwo
      (by omega) hdifferenceB
  obtain ⟨p, hp, hpDegree, hrepresentation, halternative⟩ :=
    exists_hConicDifference_numerator_zero_away_or_degree_drop
      N kOne kTwo hN hkOne hkTwo R LambdaP LambdaQ hR
        hLambdaP hLambdaQ ha hb hab hdifferenceA hdifferenceB
        hderivativeA hderivativeB
  rcases h_projective_difference_zero_or_boundary_of_profile_alternative
      (N / 2) N (by omega) (by omega) R p hp hrepresentation
        ha hb hab halternative with hcollision | hboundary
  · exact Or.inl hcollision
  · exact Or.inr ⟨p, hp, hpDegree, hrepresentation, hboundary⟩

end OnLeConjecture.DThree
