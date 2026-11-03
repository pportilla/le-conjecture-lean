/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HJacobianDescent

/-!
# Positive local orders of the homogeneous H difference

At either point of the residual conic above `X = 1`, both ordered source
points specialize to `(1,0)`. The homogeneous difference therefore vanishes
there. If the difference is a nonzero rational function, its fixed pole
profile has a numerator with positive root multiplicity at each of these
points. This supplies the exact positive local orders required by the
projective difference theorem.

The final theorems combine these orders with the Jacobian quotient identities
obtained from literal divisibility by `t ^ 5` after the substitution
`w = t ^ 2`.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial
open scoped WithZero

variable {K : Type*} [Field K] [CharZero K]

/-- The two parametrized source points both specialize to `(1,0)` at a point
of the residual conic above `X = 1`. -/
theorem h_conic_param_values_at_one
    {a : K} (ha : a ^ 2 + 2 * a + 4 = 0) :
    RatFunc.eval (RingHom.id K) a (hConicParamX (K := K)) = 1 ∧
      RatFunc.eval (RingHom.id K) a hConicParamW = 0 ∧
      RatFunc.eval (RingHom.id K) a hConicParamCapitalW = 0 := by
  have hden : hConicParamDenominator (K := K).eval a ≠ 0 := by
    simpa [hConicParamDenominator] using
      h_conic_param_denominator_at_one_root_ne_zero ha
  have hfunctionDen :
      hConicParamFunctionDenominator (K := K).eval a ≠ 0 := by
    simp only [hConicParamFunctionDenominator, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_one, Polynomial.eval_ofNat]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num)
        (h_conic_param_one_root_add_one_ne_zero ha))
      (pow_ne_zero 2 hden)
  constructor
  · rw [hConicParamX,
      h_ratFunc_eval_algebraMap_div a
        hConicParamXNumerator hConicParamDenominator hden]
    apply (div_eq_one_iff_eq hden).2
    simp only [hConicParamXNumerator, hConicParamDenominator,
      Polynomial.eval_neg, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    linear_combination -2 * ha
  constructor
  · rw [hConicParamW,
      h_ratFunc_eval_algebraMap_div a
        (-hConicParamOneFactor * hConicParamWFactor)
        hConicParamFunctionDenominator hfunctionDen]
    rw [div_eq_zero_iff]
    left
    have hone : hConicParamOneFactor (K := K).eval a = 0 := by
      simp only [hConicParamOneFactor, Polynomial.eval_add,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat,
        Polynomial.eval_mul]
      exact ha
    simp only [Polynomial.eval_mul, Polynomial.eval_neg, hone,
      neg_zero, zero_mul]
  · rw [hConicParamCapitalW,
      h_ratFunc_eval_algebraMap_div a
        (-hConicParamOneFactor * hConicParamCapitalWFactor)
        hConicParamFunctionDenominator hfunctionDen]
    rw [div_eq_zero_iff]
    left
    have hone : hConicParamOneFactor (K := K).eval a = 0 := by
      simp only [hConicParamOneFactor, Polynomial.eval_add,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat,
        Polynomial.eval_mul]
      exact ha
    simp only [Polynomial.eval_mul, Polynomial.eval_neg, hone,
      neg_zero, zero_mul]

/-- The conic difference of every polynomial vanishes at either point above
`X = 1`. -/
theorem h_ratFunc_eval_hConicDifference_at_one
    {a : K} (ha : a ^ 2 + 2 * a + 4 = 0)
    (R : MvPolynomial (Fin 2) K) :
    RatFunc.eval (RingHom.id K) a (hConicDifference R) = 0 := by
  have hden : hConicParamDenominator (K := K).eval a ≠ 0 := by
    simpa [hConicParamDenominator] using
      h_conic_param_denominator_at_one_root_ne_zero ha
  obtain ⟨hxRegular, hwRegular, hWRegular⟩ :=
    h_conic_param_regular_at a
      (h_conic_param_one_root_add_one_ne_zero ha) hden
  have honeRegular : HRatFuncRegularAt a (1 : RatFunc K) := by
    simpa using hRatFuncRegularAt_algebraMap (K := K) a 1
  have hvalues := h_conic_param_values_at_one ha
  rw [hConicDifference, hFirstConicPullback,
    hSecondConicPullback,
    h_ratFunc_eval_sub a _ _
      (hRatFuncRegularAt_hFormEval a 1 hConicParamW R
        honeRegular hwRegular)
      (hRatFuncRegularAt_hFormEval a hConicParamX
        hConicParamCapitalW R hxRegular hWRegular),
    h_ratFunc_eval_hFormEval a 1 hConicParamW R
      honeRegular hwRegular,
    h_ratFunc_eval_hFormEval a hConicParamX
      hConicParamCapitalW R hxRegular hWRegular,
    RatFunc.eval_one, hvalues.1, hvalues.2.1, hvalues.2.2,
    sub_self]

/-- A nonzero homogeneous conic difference has an exact positive local order
at either point above `X = 1`. -/
theorem exists_h_positive_local_order_at_one
    {N : ℕ} {a : K} (ha : a ^ 2 + 2 * a + 4 = 0)
    (R : MvPolynomial (Fin 2) K)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hdifference : hConicDifference R ≠ 0) :
    ∃ k : ℕ, 1 ≤ k ∧
      hFiniteOrderAt a (hConicDifference R) =
        WithZero.exp (k : ℤ) := by
  obtain ⟨p, hpDegree, hrepresentation⟩ :=
    hasHPoleProfile_hConicDifference N R hR
  let q := hPoleProfileDenominator (K := K) (N / 2) N
  have hqEval : q.eval a ≠ 0 := by
    exact h_pole_profile_denominator_eval_ne_zero_at_one_root
      (N / 2) N ha
  have hp : p ≠ 0 := by
    intro hpZero
    apply hdifference
    rw [hrepresentation, hpZero]
    simp
  have hpEval : p.eval a = 0 := by
    have hzero := h_ratFunc_eval_hConicDifference_at_one ha R
    rw [hrepresentation,
      h_ratFunc_eval_algebraMap_div a p q hqEval] at hzero
    exact (div_eq_zero_iff.mp hzero).resolve_right hqEval
  have hk : 0 < p.rootMultiplicity a :=
    (Polynomial.rootMultiplicity_pos hp).2 hpEval
  refine ⟨p.rootMultiplicity a, hk, ?_⟩
  rw [hrepresentation, map_div₀,
    h_finite_order_polynomial_eq_rootMultiplicity a p hp,
    h_finite_order_polynomial_of_eval_ne_zero a q hqEval,
    div_one]

/-- Literal Jacobian divisibility and a nonzero conic difference imply an
off diagonal homogeneous fibre pair. -/
theorem exists_h_homogeneous_fibre_difference_zero_of_literal_divisibilities
    [IsAlgClosed K]
    (N : ℕ) (hN : 5 ≤ N)
    (R : MvPolynomial (Fin 2) K)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hdifference : hConicDifference R ≠ 0)
    (hPdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (cubicForm 3 0) (hQuadraticSubstitutionForm R))
    (hQdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (quarticForm 1 0 4 0 2) (hQuadraticSubstitutionForm R))
    {a b : K}
    (ha : a ^ 2 + 2 * a + 4 = 0)
    (hb : b ^ 2 + 2 * b + 4 = 0)
    (hab : a ≠ b) :
    ∃ x t X T : K,
      (x ≠ 0 ∨ t ≠ 0 ∨ X ≠ 0 ∨ T ≠ 0) ∧
      (x ≠ X ∨ t ≠ T) ∧
      hP x (t ^ 2) = hP X (T ^ 2) ∧
      hQ x (t ^ 2) = hQ X (T ^ 2) ∧
      hFormEval x (t ^ 2) R = hFormEval X (T ^ 2) R := by
  obtain ⟨LambdaP, LambdaQ, hLambdaP, hLambdaQ⟩ :=
    exists_h_jacobian_quotients_of_literal_divisibilities R hPdiv hQdiv
  obtain ⟨kOne, hkOne, horderOne⟩ :=
    exists_h_positive_local_order_at_one ha R hR hdifference
  obtain ⟨kTwo, hkTwo, horderTwo⟩ :=
    exists_h_positive_local_order_at_one hb R hR hdifference
  exact exists_h_homogeneous_fibre_difference_zero
    N kOne kTwo hN hkOne hkTwo R LambdaP LambdaQ hR
      hLambdaP hLambdaQ ha hb hab horderOne horderTwo

/-- The literal divisibility endpoint over the complex numbers. -/
theorem exists_complex_h_homogeneous_fibre_difference_zero_of_literal_divisibilities
    (N : ℕ) (hN : 5 ≤ N)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hdifference : hConicDifference R ≠ 0)
    (hPdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (cubicForm 3 0) (hQuadraticSubstitutionForm R))
    (hQdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (quarticForm 1 0 4 0 2) (hQuadraticSubstitutionForm R)) :
    ∃ x t X T : ℂ,
      (x ≠ 0 ∨ t ≠ 0 ∨ X ≠ 0 ∨ T ≠ 0) ∧
      (x ≠ X ∨ t ≠ T) ∧
      hP x (t ^ 2) = hP X (T ^ 2) ∧
      hQ x (t ^ 2) = hQ X (T ^ 2) ∧
      hFormEval x (t ^ 2) R = hFormEval X (T ^ 2) R := by
  exact
    exists_h_homogeneous_fibre_difference_zero_of_literal_divisibilities
      N hN R hR hdifference hPdiv hQdiv
        h_conic_one_roots_equations.1
        h_conic_one_roots_equations.2 h_conic_one_roots_ne

end OnLeConjecture.DThree
