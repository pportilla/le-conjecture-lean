/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Polynomial.RatFuncConstants
public import OnLeConjecture.DFour.QuarticClassification
import Mathlib.Tactic.LinearCombination

/-!
# Power identities from a vanishing weighted derivative

For nonzero polynomials over a field of characteristic zero, the identity
`k * P' * R - d * P * R' = 0` forces `R ^ d` to be a nonzero scalar
multiple of `P ^ k`. The natural exponents may be zero.

This is the polynomial argument used after the equality `ell = k * alpha`
in the weighted initial pair lemma. The final theorem connects its quartic
specialization to the existing classification of depressed quartics.
-/

public section

namespace OnLeConjecture.Polynomial

open _root_.Polynomial
open OnLeConjecture.DThree

variable {K : Type*} [Field K]

/-- Multiplying the derivative of a power by its base removes the truncated
subtraction in the power rule, including when the exponent is zero. -/
theorem mul_derivative_pow_eq (P : K[X]) (k : ℕ) :
    P * (P ^ k).derivative = C (k : K) * P ^ k * P.derivative := by
  cases k with
  | zero => simp
  | succ k =>
      rw [_root_.Polynomial.derivative_pow]
      simp only [Nat.add_one_sub_one, pow_succ]
      ring

/-- The weighted derivative identity makes the numerator in the quotient
rule for `R ^ d / P ^ k` vanish. -/
theorem power_ratio_derivative_numerator_eq_zero
    (P R : K[X]) (d k : ℕ)
    (hP : P ≠ 0) (hR : R ≠ 0)
    (hweighted : C (k : K) * P.derivative * R -
      C (d : K) * P * R.derivative = 0) :
    (R ^ d).derivative * P ^ k - R ^ d * (P ^ k).derivative = 0 := by
  have hRpower := mul_derivative_pow_eq R d
  have hPpower := mul_derivative_pow_eq P k
  have hproduct : (P * R) *
      ((R ^ d).derivative * P ^ k - R ^ d * (P ^ k).derivative) = 0 := by
    linear_combination
      (P * P ^ k) * hRpower - (R * R ^ d) * hPpower -
        (P ^ k * R ^ d) * hweighted
  exact (mul_eq_zero.mp hproduct).resolve_left (mul_ne_zero hP hR)

/-- Vanishing of the weighted derivative gives the power identity, with no
positivity assumption on the natural exponents. -/
theorem exists_power_identity_of_weighted_derivative_eq_zero
    [CharZero K] (P R : K[X]) (d k : ℕ)
    (hP : P ≠ 0) (hR : R ≠ 0)
    (hweighted : C (k : K) * P.derivative * R -
      C (d : K) * P * R.derivative = 0) :
    ∃ c : K, c ≠ 0 ∧ R ^ d = C c * P ^ k := by
  let f : RatFunc K :=
    algebraMap K[X] (RatFunc K) (R ^ d) /
      algebraMap K[X] (RatFunc K) (P ^ k)
  have hdenominator : P ^ k ≠ 0 := pow_ne_zero k hP
  have hdenominatorMap :
      algebraMap K[X] (RatFunc K) (P ^ k) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hdenominator
  have hnumerator :=
    power_ratio_derivative_numerator_eq_zero P R d k hP hR hweighted
  have hnumeratorMap :
      algebraMap K[X] (RatFunc K) (R ^ d).derivative *
          algebraMap K[X] (RatFunc K) (P ^ k) -
        algebraMap K[X] (RatFunc K) (R ^ d) *
          algebraMap K[X] (RatFunc K) (P ^ k).derivative = 0 := by
    simpa only [map_sub, map_mul, map_zero] using
      congrArg (algebraMap K[X] (RatFunc K)) hnumerator
  have hderivative : ratFuncDerivative f = 0 := by
    change ratFuncDerivative
      (algebraMap K[X] (RatFunc K) (R ^ d) /
        algebraMap K[X] (RatFunc K) (P ^ k)) = 0
    rw [ratFuncDerivative_div, hnumeratorMap, zero_div]
  obtain ⟨c, hc⟩ := (ratFuncDerivative_eq_zero_iff_constant f).mp hderivative
  change algebraMap K[X] (RatFunc K) (R ^ d) /
      algebraMap K[X] (RatFunc K) (P ^ k) = RatFunc.C c at hc
  have hmap : algebraMap K[X] (RatFunc K) (R ^ d) =
      algebraMap K[X] (RatFunc K) (C c * P ^ k) := by
    rw [map_mul, RatFunc.algebraMap_C]
    exact (div_eq_iff hdenominatorMap).mp hc
  have hpolynomial : R ^ d = C c * P ^ k :=
    RatFunc.algebraMap_injective K hmap
  refine ⟨c, ?_, hpolynomial⟩
  intro hcZero
  have hpower : R ^ d = 0 := by simpa [hcZero] using hpolynomial
  exact pow_ne_zero d hR hpower

/-- The nonzero scalar weight cancels once `ell = k * alpha` has been
established, giving the power identity of the weighted initial pair. -/
theorem exists_power_identity_of_weighted_initial_pair
    [CharZero K] (P R : K[X]) (d k : ℕ) (ell alpha : K)
    (hP : P ≠ 0) (hR : R ≠ 0) (halpha : alpha ≠ 0)
    (hell : ell = (k : K) * alpha)
    (hweighted : C ell * P.derivative * R -
      C ((d : K) * alpha) * P * R.derivative = 0) :
    ∃ c : K, c ≠ 0 ∧ R ^ d = C c * P ^ k := by
  apply exists_power_identity_of_weighted_derivative_eq_zero P R d k hP hR
  have hproduct : C alpha *
      (C (k : K) * P.derivative * R - C (d : K) * P * R.derivative) = 0 := by
    rw [hell, map_mul, map_mul] at hweighted
    linear_combination hweighted
  exact (mul_eq_zero.mp hproduct).resolve_left (C_ne_zero.mpr halpha)

end OnLeConjecture.Polynomial

namespace OnLeConjecture.DFour

open _root_.Polynomial

/-- A vanishing weighted derivative for a normalized depressed quartic
gives its square factorization. The positive exponent hypothesis is
required here by the quartic classification. -/
theorem quartic_classification_of_weighted_initial_pair
    (P R : ℂ[X]) (k : ℕ) (ell alpha : ℂ)
    (hPmonic : P.Monic)
    (hPdegree : P.natDegree = 4)
    (hPdepressed : P.coeff 3 = 0)
    (hPnotFourth : ∀ Q : ℂ[X], P ≠ Q ^ 4)
    (hR : R ≠ 0)
    (hk : 0 < k)
    (halpha : alpha ≠ 0)
    (hell : ell = (k : ℂ) * alpha)
    (hweighted : C ell * P.derivative * R -
      C (4 * alpha) * P * R.derivative = 0)
    (hRnormalized : ∀ (s : ℕ) (γ : ℂ),
      0 < s → γ ≠ 0 → R ≠ C γ * P ^ s) :
    ∃ (e : ℕ) (η μ : ℂ),
      k % 4 = 2 ∧ k = 2 * e ∧ Odd e ∧ η * μ ≠ 0 ∧
        P = (X ^ 2 + C η) ^ 2 ∧
        R = C μ * (X ^ 2 + C η) ^ e := by
  obtain ⟨c, hc, hpower⟩ :=
    OnLeConjecture.Polynomial.exists_power_identity_of_weighted_initial_pair
      P R 4 k ell alpha hPmonic.ne_zero hR halpha hell hweighted
  exact quartic_power_identity_classification hPmonic hPdegree hPdepressed
    hPnotFourth hk hc hpower hRnormalized

end OnLeConjecture.DFour
