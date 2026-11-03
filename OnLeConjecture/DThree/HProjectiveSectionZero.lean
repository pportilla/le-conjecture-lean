/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HDerivativeRatFunc
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# A projective zero count for the `H` conic

A pole profile writes a rational function with a fixed polynomial
denominator. The numerator represents the corresponding projective section.
If its orders at two finite points do not exhaust the degree of that
denominator, the section vanishes either at another finite point or at the
point at infinity.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial
open scoped WithZero

variable {K : Type*} [Field K]

/-- The first parameter value above `X = 1` on the complex conic. -/
@[expose]
noncomputable def hConicOneRootPlus : ℂ :=
  -1 + Complex.I * Real.sqrt 3

/-- The second parameter value above `X = 1` on the complex conic. -/
@[expose]
noncomputable def hConicOneRootMinus : ℂ :=
  -1 - Complex.I * Real.sqrt 3

private theorem h_complex_sqrt_three_square :
    ((Complex.I * (Real.sqrt 3 : ℂ)) ^ 2) = -3 := by
  have hsqrt : ((Real.sqrt 3 : ℂ) ^ 2) = 3 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  rw [mul_pow, Complex.I_sq, hsqrt]
  norm_num

/-- Both specified parameter values lie above `X = 1`. -/
theorem h_conic_one_roots_equations :
    hConicOneRootPlus ^ 2 + 2 * hConicOneRootPlus + 4 = 0 ∧
      hConicOneRootMinus ^ 2 + 2 * hConicOneRootMinus + 4 = 0 := by
  constructor
  · simp only [hConicOneRootPlus]
    linear_combination h_complex_sqrt_three_square
  · simp only [hConicOneRootMinus]
    linear_combination h_complex_sqrt_three_square

/-- The two parameter values above `X = 1` are distinct. -/
theorem h_conic_one_roots_ne : hConicOneRootPlus ≠ hConicOneRootMinus := by
  have hsqrt : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3)
  have himaginary : Complex.I * (Real.sqrt 3 : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero hsqrt
  intro hequal
  apply himaginary
  simp only [hConicOneRootPlus, hConicOneRootMinus] at hequal
  linear_combination (1 / 2) * hequal

/-- A profile numerator has a projective zero away from two prescribed
finite points when their orders do not exhaust the profile degree. A strict
degree drop records a zero at infinity. -/
theorem HasHPoleProfile.exists_numerator_zero_away_or_degree_drop
    [IsAlgClosed K]
    {profileFinite profileInfinity : ℕ} {f : RatFunc K}
    (hprofile : HasHPoleProfile profileFinite profileInfinity f)
    (hf : f ≠ 0) {a b : K} (hab : a ≠ b)
    {kOne kTwo : ℕ}
    (hdenA :
      (hPoleProfileDenominator profileFinite profileInfinity).eval a ≠ 0)
    (hdenB :
      (hPoleProfileDenominator profileFinite profileInfinity).eval b ≠ 0)
    (horderA : hFiniteOrderAt a f = WithZero.exp (kOne : ℤ))
    (horderB : hFiniteOrderAt b f = WithZero.exp (kTwo : ℤ))
    (hstrict : kOne + kTwo < profileFinite + 2 * profileInfinity) :
    ∃ numerator : K[X],
      numerator ≠ 0 ∧
      numerator.natDegree ≤ profileFinite + 2 * profileInfinity ∧
      f = algebraMap K[X] (RatFunc K) numerator /
        algebraMap K[X] (RatFunc K)
          (hPoleProfileDenominator profileFinite profileInfinity) ∧
      (numerator.natDegree < profileFinite + 2 * profileInfinity ∨
        ∃ z : K, z ≠ a ∧ z ≠ b ∧ numerator.IsRoot z) := by
  classical
  rcases hprofile with ⟨numerator, hdegree, hrepresentation⟩
  have hnumerator : numerator ≠ 0 := by
    intro hzero
    apply hf
    rw [hrepresentation, hzero]
    simp
  let denominator :=
    hPoleProfileDenominator (K := K) profileFinite profileInfinity
  have hdenOrderA :
      hFiniteOrderAt a
          (algebraMap K[X] (RatFunc K) denominator) = 1 := by
    exact h_finite_order_polynomial_of_eval_ne_zero a denominator hdenA
  have hdenOrderB :
      hFiniteOrderAt b
          (algebraMap K[X] (RatFunc K) denominator) = 1 := by
    exact h_finite_order_polynomial_of_eval_ne_zero b denominator hdenB
  have hnumOrderA :
      hFiniteOrderAt a
          (algebraMap K[X] (RatFunc K) numerator) =
        WithZero.exp (kOne : ℤ) := by
    rw [hrepresentation, map_div₀, hdenOrderA, div_one] at horderA
    exact horderA
  have hnumOrderB :
      hFiniteOrderAt b
          (algebraMap K[X] (RatFunc K) numerator) =
        WithZero.exp (kTwo : ℤ) := by
    rw [hrepresentation, map_div₀, hdenOrderB, div_one] at horderB
    exact horderB
  have hmultiplicityA : numerator.rootMultiplicity a = kOne := by
    have hformula :=
      h_finite_order_polynomial_eq_rootMultiplicity a numerator hnumerator
    have hexponent :
        (numerator.rootMultiplicity a : ℤ) = (kOne : ℤ) :=
      WithZero.exp_injective (hformula.symm.trans hnumOrderA)
    exact_mod_cast hexponent
  have hmultiplicityB : numerator.rootMultiplicity b = kTwo := by
    have hformula :=
      h_finite_order_polynomial_eq_rootMultiplicity b numerator hnumerator
    have hexponent :
        (numerator.rootMultiplicity b : ℤ) = (kTwo : ℤ) :=
      WithZero.exp_injective (hformula.symm.trans hnumOrderB)
    exact_mod_cast hexponent
  refine ⟨numerator, hnumerator, hdegree, hrepresentation, ?_⟩
  by_cases hdrop :
      numerator.natDegree < profileFinite + 2 * profileInfinity
  · exact Or.inl hdrop
  · right
    by_contra haway
    have hsupport :
        ∀ z ∈ numerator.roots, z ∈ ({a, b} : Finset K) := by
      intro z hz
      by_cases hza : z = a
      · simp [hza]
      · by_cases hzb : z = b
        · simp [hzb]
        · exfalso
          apply haway
          exact ⟨z, hza, hzb, (Polynomial.mem_roots hnumerator).mp hz⟩
    have hcount :
        ∑ z ∈ ({a, b} : Finset K), numerator.roots.count z =
          numerator.roots.card := by
      apply Multiset.sum_count_eq_card
      exact hsupport
    have hcard : numerator.roots.card = numerator.natDegree :=
      IsAlgClosed.card_roots_eq_natDegree
    have hsum : kOne + kTwo = numerator.natDegree := by
      rw [Finset.sum_pair hab, Polynomial.count_roots,
        Polynomial.count_roots, hmultiplicityA, hmultiplicityB,
        hcard] at hcount
      exact hcount
    have hfull :
        numerator.natDegree = profileFinite + 2 * profileInfinity :=
      Nat.le_antisymm hdegree (Nat.le_of_not_gt hdrop)
    omega

/-- The profile denominator is nonzero at either parameter value above
`X = 1` on the conic. -/
theorem h_pole_profile_denominator_eval_ne_zero_at_one_root
    [CharZero K]
    (profileFinite profileInfinity : ℕ) {a : K}
    (ha : a ^ 2 + 2 * a + 4 = 0) :
    (hPoleProfileDenominator (K := K) profileFinite profileInfinity).eval a ≠
      0 := by
  rw [hPoleProfileDenominator, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_pow]
  apply mul_ne_zero
  · apply pow_ne_zero
    rw [Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    exact mul_ne_zero (by norm_num)
      (h_conic_param_one_root_add_one_ne_zero ha)
  · apply pow_ne_zero
    simpa [hConicParamDenominator] using
      h_conic_param_denominator_at_one_root_ne_zero ha

/-- The branch order bound is strictly smaller than the degree of the
projective section associated with the pole profile `(N / 2, N)`. -/
theorem h_branch_order_sum_bound_lt_profile_degree
    (N : ℕ) (hN : 5 ≤ N) :
    hBranchOrderSumBound N < N / 2 + 2 * N := by
  simp only [hBranchOrderSumBound]
  omega

/-- The Jacobian quotient estimate and exact local orders force a projective
zero of the `H` residual section away from the two points above `X = 1`.
The degree drop alternative represents the point at infinity. -/
theorem exists_hConicDifference_numerator_zero_away_or_degree_drop
    [CharZero K] [IsAlgClosed K]
    (N kOne kTwo : ℕ) (hN : 5 ≤ N)
    (hkOne : 1 ≤ kOne) (hkTwo : 1 ≤ kTwo)
    (R LambdaP LambdaQ : MvPolynomial (Fin 2) K)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hLambdaP :
      hFormJacobian hPForm R = hFormW ^ 2 * LambdaP)
    (hLambdaQ :
      hFormJacobian hQForm R = hFormW ^ 2 * LambdaQ)
    {a b : K}
    (haRoot : a ^ 2 + 2 * a + 4 = 0)
    (hbRoot : b ^ 2 + 2 * b + 4 = 0)
    (hab : a ≠ b)
    (hdifferenceA :
      hFiniteOrderAt a (hConicDifference R) =
        WithZero.exp (kOne : ℤ))
    (hdifferenceB :
      hFiniteOrderAt b (hConicDifference R) =
        WithZero.exp (kTwo : ℤ))
    (hderivativeA :
      hFiniteOrderAt a (hDerivativeRatFunc LambdaP LambdaQ) =
        WithZero.exp ((kOne - 1 : ℕ) : ℤ))
    (hderivativeB :
      hFiniteOrderAt b (hDerivativeRatFunc LambdaP LambdaQ) =
        WithZero.exp ((kTwo - 1 : ℕ) : ℤ)) :
    ∃ numerator : K[X],
      numerator ≠ 0 ∧
      numerator.natDegree ≤ N / 2 + 2 * N ∧
      hConicDifference R =
        algebraMap K[X] (RatFunc K) numerator /
          algebraMap K[X] (RatFunc K)
            (hPoleProfileDenominator (N / 2) N) ∧
      (numerator.natDegree < N / 2 + 2 * N ∨
        ∃ z : K, z ≠ a ∧ z ≠ b ∧ numerator.IsRoot z) := by
  have hderivative : hDerivativeRatFunc LambdaP LambdaQ ≠ 0 :=
    h_ratFunc_ne_zero_of_finite_order hderivativeA
  have hpole :
      hProjectivePoleDivisorDegree
          (hDerivativeRatFunc LambdaP LambdaQ) ≤
        hDerivativePoleDegreeBound N :=
    hDerivativeRatFunc_projectivePoleDegree_le N R LambdaP LambdaQ
      (by omega) hR hLambdaP hLambdaQ
  have hbranch : kOne + kTwo ≤ hBranchOrderSumBound N :=
    h_branch_order_sum_le_of_ratFunc N kOne kTwo (by omega)
      hkOne hkTwo hderivative hab hderivativeA hderivativeB hpole
  have hstrict : kOne + kTwo < N / 2 + 2 * N :=
    hbranch.trans_lt (h_branch_order_sum_bound_lt_profile_degree N hN)
  apply HasHPoleProfile.exists_numerator_zero_away_or_degree_drop
    (hasHPoleProfile_hConicDifference N R hR)
    (h_ratFunc_ne_zero_of_finite_order hdifferenceA) hab
    (h_pole_profile_denominator_eval_ne_zero_at_one_root
      (N / 2) N haRoot)
    (h_pole_profile_denominator_eval_ne_zero_at_one_root
      (N / 2) N hbRoot)
    hdifferenceA hdifferenceB hstrict

/-- The preceding zero count at the two explicit complex parameter values
above `X = 1`. -/
theorem exists_hConicDifference_numerator_zero_away_from_one_fibre
    (N kOne kTwo : ℕ) (hN : 5 ≤ N)
    (hkOne : 1 ≤ kOne) (hkTwo : 1 ≤ kTwo)
    (R LambdaP LambdaQ : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hLambdaP :
      hFormJacobian hPForm R = hFormW ^ 2 * LambdaP)
    (hLambdaQ :
      hFormJacobian hQForm R = hFormW ^ 2 * LambdaQ)
    (hdifferencePlus :
      hFiniteOrderAt hConicOneRootPlus (hConicDifference R) =
        WithZero.exp (kOne : ℤ))
    (hdifferenceMinus :
      hFiniteOrderAt hConicOneRootMinus (hConicDifference R) =
        WithZero.exp (kTwo : ℤ))
    (hderivativePlus :
      hFiniteOrderAt hConicOneRootPlus
          (hDerivativeRatFunc LambdaP LambdaQ) =
        WithZero.exp ((kOne - 1 : ℕ) : ℤ))
    (hderivativeMinus :
      hFiniteOrderAt hConicOneRootMinus
          (hDerivativeRatFunc LambdaP LambdaQ) =
        WithZero.exp ((kTwo - 1 : ℕ) : ℤ)) :
    ∃ numerator : ℂ[X],
      numerator ≠ 0 ∧
      numerator.natDegree ≤ N / 2 + 2 * N ∧
      hConicDifference R =
        algebraMap ℂ[X] (RatFunc ℂ) numerator /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (N / 2) N) ∧
      (numerator.natDegree < N / 2 + 2 * N ∨
        ∃ z : ℂ,
          z ≠ hConicOneRootPlus ∧ z ≠ hConicOneRootMinus ∧
            numerator.IsRoot z) := by
  exact exists_hConicDifference_numerator_zero_away_or_degree_drop
    N kOne kTwo hN hkOne hkTwo R LambdaP LambdaQ hR hLambdaP hLambdaQ
      h_conic_one_roots_equations.1 h_conic_one_roots_equations.2
      h_conic_one_roots_ne hdifferencePlus hdifferenceMinus
      hderivativePlus hderivativeMinus

end OnLeConjecture.DThree
