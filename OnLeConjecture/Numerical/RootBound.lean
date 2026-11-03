/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order

/-!
# The numerical root bound

This file formalizes the last arithmetic step in the reduction theorem from
the article *On Lê's conjecture*.  All variables are integers so that the
subtractions in the polar estimate have their usual meaning.
-/

public section

namespace OnLeConjecture.Numerical

/-- The integer form of the arithmetic argument in the reduction theorem. -/
theorem root_bound_int
    (d M S m n b : ℤ)
    (hd : 2 ≤ d)
    (hM : 0 ≤ M)
    (hS : d ≤ S)
    (hb : 1 ≤ b)
    (hMS : M ≤ d * S)
    (hm : 2 ≤ m)
    (hestimate : M + S ≤ 3 * m)
    (hn : d ≤ n)
    (hpolar : n * (m - 1) ≤ 2 * M - S - b) :
    d ≤ 4 := by
  have hd0 : 0 ≤ d := by omega
  have hm1 : 0 ≤ m - 1 := by omega
  have hdn : d * (m - 1) ≤ n * (m - 1) := by
    exact mul_le_mul_of_nonneg_right hn hm1
  have harithmetic :
      (d - 6) * M + (d + 3) * S + 3 * b - 3 * d ≤ 0 := by
    nlinarith
  by_contra hnot
  have hd5 : 5 ≤ d := by omega
  by_cases hd6 : 6 ≤ d
  · have hcoef : 0 ≤ d - 6 := by omega
    have hfirst : 0 ≤ (d - 6) * M :=
      mul_nonneg hcoef hM
    have hpositive : 0 < (d + 3) * S + 3 * b - 3 * d := by
      nlinarith
    linarith
  · have deq : d = 5 := by omega
    subst d
    have hlower : 8 * S + 3 * b - 15 ≤ M := by
      linarith
    nlinarith

/-- The numerical data used in the proof that the order of the pulled back
maximal ideal is at most four. -/
structure ReductionCertificate where
  d : ℕ
  M : ℕ
  S : ℕ
  m : ℕ
  n : ℕ
  b : ℕ
  two_le_d : 2 ≤ d
  d_le_S : d ≤ S
  b_positive : 1 ≤ b
  M_le_dS : M ≤ d * S
  m_at_least_two : 2 ≤ m
  global_estimate : M + S ≤ 3 * m
  d_le_n : d ≤ n
  polar_estimate : n * (m - 1) + S + b ≤ 2 * M

namespace ReductionCertificate

/-- Every reduction certificate has order at most four. -/
theorem d_le_four (c : ReductionCertificate) : c.d ≤ 4 := by
  have hd : (2 : ℤ) ≤ c.d := by exact_mod_cast c.two_le_d
  have hM : (0 : ℤ) ≤ c.M := Int.natCast_nonneg c.M
  have hS : (c.d : ℤ) ≤ c.S := by exact_mod_cast c.d_le_S
  have hb : (1 : ℤ) ≤ c.b := by exact_mod_cast c.b_positive
  have hMS : (c.M : ℤ) ≤ c.d * c.S := by exact_mod_cast c.M_le_dS
  have hm : (2 : ℤ) ≤ c.m := by exact_mod_cast c.m_at_least_two
  have hestimate : (c.M : ℤ) + c.S ≤ 3 * c.m := by
    exact_mod_cast c.global_estimate
  have hn : (c.d : ℤ) ≤ c.n := by exact_mod_cast c.d_le_n
  have hm_one : 1 ≤ c.m := by omega
  have hpolar_cast :
      ((c.n * (c.m - 1) + c.S + c.b : ℕ) : ℤ) ≤ ((2 * c.M : ℕ) : ℤ) := by
    exact_mod_cast c.polar_estimate
  push_cast [Nat.cast_sub hm_one] at hpolar_cast
  have hpolar :
      (c.n : ℤ) * ((c.m : ℤ) - 1) ≤ 2 * c.M - c.S - c.b := by
    linarith
  have hresult := root_bound_int
    (c.d : ℤ) (c.M : ℤ) (c.S : ℤ) (c.m : ℤ) (c.n : ℤ) (c.b : ℤ)
    hd hM hS hb hMS hm hestimate hn hpolar
  exact_mod_cast hresult

/-- The only possible values of the order in a reduction certificate are two,
three, and four. -/
theorem d_eq_two_or_three_or_four (c : ReductionCertificate) :
    c.d = 2 ∨ c.d = 3 ∨ c.d = 4 := by
  have hlower := c.two_le_d
  have hupper := c.d_le_four
  omega

end ReductionCertificate

end OnLeConjecture.Numerical
