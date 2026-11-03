/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Polynomial.WeightedPowerIdentity
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# Polynomial degree constraints for a weighted initial pair

For a monic polynomial `P` of degree `m`, the coefficient at index
`m - 1 + R.natDegree` in the weighted derivative determines the relation
`ell = alpha * R.natDegree` whenever its degree is at most `m - 2`.
Subtracting the leading multiple of `P` then excludes `R.natDegree = m`
unless `R` was that scalar multiple of `P`.

The lower bound `m ≤ R.natDegree` in the combined degree theorem is an
explicit input. In the manuscript it follows from the ordinary order of
the analytic function and the pure first-coordinate monomial in its initial
form. The coefficient calculation and the subtraction argument are proved
here for arbitrary polynomials and every `m ≥ 2`, including `m = 3, 4`.
-/

public section

namespace OnLeConjecture.Polynomial

open _root_.Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- The one-variable polynomial obtained from the weighted initial Jacobian.
-/
@[expose]
noncomputable def weightedPairOmega
    (m : ℕ) (ell alpha : K) (P R : K[X]) : K[X] :=
  C ell * P.derivative * R - C ((m : K) * alpha) * P * R.derivative

/-- The highest potentially nonzero coefficient of the weighted derivative.
The formula includes constant nonzero `R` and also the zero polynomial. -/
theorem weightedPairOmega_coeff_top
    (m : ℕ) (ell alpha : K) (P R : K[X])
    (hm : 0 < m) (hPmonic : P.Monic) (hPdegree : P.natDegree = m) :
    (weightedPairOmega m ell alpha P R).coeff (m - 1 + R.natDegree) =
      (m : K) * (ell - alpha * (R.natDegree : K)) * R.leadingCoeff := by
  have hPderiv : P.derivative.natDegree = m - 1 := by
    rw [natDegree_derivative, hPdegree]
  have hfirst : (P.derivative * R).coeff (m - 1 + R.natDegree) =
      (m : K) * R.leadingCoeff := by
    rw [← hPderiv, coeff_mul_degree_add_degree, leadingCoeff_derivative,
      hPmonic.leadingCoeff, hPdegree, one_mul]
  have hsecond : (P * R.derivative).coeff (m - 1 + R.natDegree) =
      (R.natDegree : K) * R.leadingCoeff := by
    by_cases hRdegree : R.natDegree = 0
    · have hRderiv : R.derivative = 0 := derivative_eq_zero.mpr hRdegree
      simp [hRderiv, hRdegree]
    · have hindex : m - 1 + R.natDegree = m + (R.natDegree - 1) := by omega
      rw [hindex, ← hPdegree, ← natDegree_derivative R,
        coeff_mul_degree_add_degree, hPmonic.leadingCoeff,
        leadingCoeff_derivative, one_mul]
      ring
  simp only [weightedPairOmega, coeff_sub, mul_assoc, coeff_C_mul]
  rw [hfirst, hsecond]
  ring

/-- A sufficiently low degree of the weighted derivative forces the weight
of `R` to equal its degree times `alpha`. -/
theorem ell_eq_alpha_mul_natDegree_of_weightedPairOmega_degree
    (m : ℕ) (ell alpha : K) (P R : K[X])
    (hm : 2 ≤ m) (hPmonic : P.Monic) (hPdegree : P.natDegree = m)
    (hR : R ≠ 0)
    (hdegree : (weightedPairOmega m ell alpha P R).natDegree ≤ m - 2) :
    ell = alpha * (R.natDegree : K) := by
  have hindex : (weightedPairOmega m ell alpha P R).natDegree <
      m - 1 + R.natDegree := by omega
  have hcoefficient := coeff_eq_zero_of_natDegree_lt hindex
  rw [weightedPairOmega_coeff_top m ell alpha P R (by omega)
    hPmonic hPdegree] at hcoefficient
  have hmCast : (m : K) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hscalar : ell - alpha * (R.natDegree : K) = 0 :=
    (mul_eq_zero.mp
      ((mul_eq_zero.mp hcoefficient).resolve_right
        (leadingCoeff_ne_zero.mpr hR))).resolve_left hmCast
  exact sub_eq_zero.mp hscalar

omit [CharZero K] in
/-- Subtracting a scalar multiple of `P` preserves the weighted derivative
when the weight is `m * alpha`. -/
theorem weightedPairOmega_sub_C_mul
    (m : ℕ) (alpha c : K) (P R : K[X]) :
    weightedPairOmega m ((m : K) * alpha) alpha P (R - C c * P) =
      weightedPairOmega m ((m : K) * alpha) alpha P R := by
  simp only [weightedPairOmega, derivative_sub, derivative_mul,
    derivative_C, zero_mul, zero_add]
  ring

omit [CharZero K] in
/-- The leading multiple of a monic polynomial cancels the top coefficient
of another polynomial of the same positive degree. -/
theorem natDegree_sub_le_pred_of_monic_same_degree
    (m : ℕ) (P R : K[X])
    (hm : 0 < m) (hPmonic : P.Monic)
    (hPdegree : P.natDegree = m) (hRdegree : R.natDegree = m) :
    (R - C R.leadingCoeff * P).natDegree ≤ m - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_sub, coeff_C_mul]
  by_cases hnm : n = m
  · subst n
    have hRcoeff : R.coeff m = R.leadingCoeff := by
      simpa [hRdegree] using R.coeff_natDegree
    have hPcoeff : P.coeff m = 1 := by
      simpa [hPdegree] using hPmonic.coeff_natDegree
    rw [hRcoeff, hPcoeff, mul_one, sub_self]
  · have hmn : m < n := by omega
    rw [coeff_eq_zero_of_natDegree_lt (by omega : R.natDegree < n),
      coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < n),
      mul_zero, sub_zero]

/-- A polynomial of degree exactly `m` with low weighted derivative must
be its leading coefficient times the monic polynomial `P`. -/
theorem eq_leadingCoeff_mul_of_weightedPairOmega_degree
    (m : ℕ) (ell alpha : K) (P R : K[X])
    (hm : 2 ≤ m) (halpha : alpha ≠ 0)
    (hPmonic : P.Monic) (hPdegree : P.natDegree = m)
    (hRdegree : R.natDegree = m)
    (hdegree : (weightedPairOmega m ell alpha P R).natDegree ≤ m - 2) :
    R = C R.leadingCoeff * P := by
  have hR : R ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hRdegree
    omega
  have hell := ell_eq_alpha_mul_natDegree_of_weightedPairOmega_degree
    m ell alpha P R hm hPmonic hPdegree hR hdegree
  have hellm : ell = (m : K) * alpha := by
    rw [hRdegree] at hell
    simpa [mul_comm] using hell
  let Q : K[X] := R - C R.leadingCoeff * P
  have hQdegree : Q.natDegree ≤ m - 1 :=
    natDegree_sub_le_pred_of_monic_same_degree m P R (by omega)
      hPmonic hPdegree hRdegree
  have hQzero : Q = 0 := by
    by_contra hQ
    have hQomega : weightedPairOmega m ell alpha P Q =
        weightedPairOmega m ell alpha P R := by
      rw [hellm]
      exact weightedPairOmega_sub_C_mul m alpha R.leadingCoeff P R
    have hQomegaDegree : (weightedPairOmega m ell alpha P Q).natDegree ≤ m - 2 := by
      rw [hQomega]
      exact hdegree
    have hellQ := ell_eq_alpha_mul_natDegree_of_weightedPairOmega_degree
      m ell alpha P Q hm hPmonic hPdegree hQ hQomegaDegree
    have hcast : (m : K) = (Q.natDegree : K) := by
      apply mul_left_cancel₀ halpha
      rw [← hellQ, hellm, mul_comm]
    have hequal : m = Q.natDegree := by exact_mod_cast hcast
    omega
  exact sub_eq_zero.mp hQzero

/-- The polynomial coefficient and subtraction arguments used in the
nonzero weighted-Jacobian case, with the analytic lower degree bound stated
explicitly. -/
theorem weighted_initial_pair_degree_constraints
    (m : ℕ) (ell alpha : K) (P R : K[X])
    (hm : 2 ≤ m) (halpha : alpha ≠ 0)
    (hPmonic : P.Monic) (hPdegree : P.natDegree = m)
    (hRdegree : m ≤ R.natDegree)
    (hdegree : (weightedPairOmega m ell alpha P R).natDegree ≤ m - 2)
    (hnormalized : ∀ c : K, R ≠ C c * P) :
    ell = alpha * (R.natDegree : K) ∧ m + 1 ≤ R.natDegree := by
  have hR : R ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hRdegree
    omega
  refine ⟨ell_eq_alpha_mul_natDegree_of_weightedPairOmega_degree
    m ell alpha P R hm hPmonic hPdegree hR hdegree, ?_⟩
  by_contra hnot
  have hequal : R.natDegree = m := by omega
  exact hnormalized R.leadingCoeff
    (eq_leadingCoeff_mul_of_weightedPairOmega_degree
      m ell alpha P R hm halpha hPmonic hPdegree hequal hdegree)

/-- When the weighted derivative vanishes, its coefficient formula supplies
the degree relation needed by the general power-identity theorem. -/
theorem exists_power_identity_of_weightedPairOmega_eq_zero
    (m : ℕ) (ell alpha : K) (P R : K[X])
    (hm : 2 ≤ m) (halpha : alpha ≠ 0)
    (hPmonic : P.Monic) (hPdegree : P.natDegree = m)
    (hR : R ≠ 0) (homega : weightedPairOmega m ell alpha P R = 0) :
    ∃ c : K, c ≠ 0 ∧ R ^ m = C c * P ^ R.natDegree := by
  have hdegree : (weightedPairOmega m ell alpha P R).natDegree ≤ m - 2 := by
    rw [homega, natDegree_zero]
    omega
  have hell := ell_eq_alpha_mul_natDegree_of_weightedPairOmega_degree
    m ell alpha P R hm hPmonic hPdegree hR hdegree
  exact exists_power_identity_of_weighted_initial_pair P R m R.natDegree
    ell alpha hPmonic.ne_zero hR halpha (by simpa [mul_comm] using hell) homega

end OnLeConjecture.Polynomial
