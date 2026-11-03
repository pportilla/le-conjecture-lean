/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicMixedPowerObstruction
public import Mathlib.Algebra.Polynomial.Expand

/-!
# Coefficients and orders of a reduced cyclic norm

The noninvariant binomial term has coefficients that cannot be cancelled
by a polynomial in `Yᵏ`. Two such coefficients control the degree and the
root multiplicity at zero.
-/

public section

namespace OnLeConjecture.DTwo

open _root_.Polynomial

theorem coeff_one_sub_X_pow_pow_ne_zero
    (N q m : ℕ) (hN : 0 < N) (hm : m ≤ q) :
    (((1 : Polynomial ℂ) - X ^ N) ^ q).coeff (m * N) ≠ 0 := by
  have hpolynomial : ((1 : Polynomial ℂ) - X ^ N) ^ q =
      C ((-1 : ℂ) ^ q) * expand ℂ N ((X + C (-1)) ^ q) := by
    simp only [map_pow, map_add, expand_X, expand_C]
    rw [← mul_pow]
    congr 1
    simp [sub_eq_add_neg]
  rw [hpolynomial, coeff_C_mul, coeff_expand_mul hN, coeff_X_add_C_pow]
  apply mul_ne_zero (pow_ne_zero _ (by norm_num))
  exact mul_ne_zero (pow_ne_zero _ (by norm_num))
    (Nat.cast_ne_zero.mpr (Nat.choose_pos hm).ne')

/-- The two coefficients outside the `k`-divisible support are nonzero. -/
theorem cyclicNorm_distinguished_coefficients
    (k N q : ℕ) (hk : 0 < k) (hN : 0 < N) (hq : 1 ≤ q)
    (hnot : ¬ k ∣ N) (hdiv : k ∣ q * N)
    (F : Polynomial ℂ) (a : ℂ) (ha : a ≠ 0) :
    let P := expand ℂ k F + C a * (1 - X ^ N) ^ q
    P.coeff N ≠ 0 ∧ P.coeff ((q - 1) * N) ≠ 0 := by
  have hnotHigh : ¬ k ∣ (q - 1) * N := by
    intro h
    apply hnot
    have hsub := Nat.dvd_sub hdiv h
    have hsum : q * N = (q - 1) * N + N := by
      have hqsum := Nat.sub_one_add_one (by omega : q ≠ 0)
      nlinarith
    simpa only [hsum, Nat.add_sub_cancel_left] using hsub
  dsimp
  constructor
  · rw [coeff_add, coeff_expand hk, if_neg hnot, zero_add, coeff_C_mul]
    apply mul_ne_zero ha
    simpa only [one_mul] using coeff_one_sub_X_pow_pow_ne_zero N q 1 hN hq
  · rw [coeff_add, coeff_expand hk, if_neg hnotHigh, zero_add, coeff_C_mul]
    exact mul_ne_zero ha (coeff_one_sub_X_pow_pow_ne_zero N q (q - 1) hN (by omega))

/-- The norm has degree at least `(q-1)N`, and order at zero at most `N`. -/
theorem cyclicNorm_degree_and_zero_order
    (k N q : ℕ) (hk : 0 < k) (hN : 0 < N) (hq : 1 ≤ q)
    (hnot : ¬ k ∣ N) (hdiv : k ∣ q * N)
    (F : Polynomial ℂ) (a : ℂ) (ha : a ≠ 0) :
    let P := expand ℂ k F + C a * (1 - X ^ N) ^ q
    P ≠ 0 ∧ (q - 1) * N ≤ P.natDegree ∧ P.rootMultiplicity 0 ≤ N := by
  obtain ⟨hlow, hhigh⟩ := cyclicNorm_distinguished_coefficients k N q hk hN hq hnot hdiv F a ha
  dsimp at hlow hhigh ⊢
  refine ⟨?_, le_natDegree_of_ne_zero hhigh, ?_⟩
  · intro h
    exact hlow (by simp [h])
  · rw [rootMultiplicity_eq_natTrailingDegree']
    exact natTrailingDegree_le_of_ne_zero hlow

/-- Root multiplicities satisfy the minimum rule when unequal. -/
theorem rootMultiplicity_add_eq_min_of_ne
    (P Q : Polynomial ℂ) (hP : P ≠ 0) (hQ : Q ≠ 0) (z : ℂ)
    (hne : P.rootMultiplicity z ≠ Q.rootMultiplicity z) :
    (P + Q).rootMultiplicity z = min (P.rootMultiplicity z) (Q.rootMultiplicity z) := by
  have hsum : P + Q ≠ 0 := by
    intro h
    have heq : P = -Q := eq_neg_of_add_eq_zero_left h
    apply hne
    rw [heq]
    simp [rootMultiplicity_eq_multiplicity, hQ, multiplicity_neg]
  simp only [rootMultiplicity_eq_multiplicity, if_neg hP, if_neg hQ, if_neg hsum] at hne ⊢
  exact multiplicity_add_eq_min (finiteMultiplicity_X_sub_C z hP)
    (finiteMultiplicity_X_sub_C z hQ) hne

/-- At a common simple zero, a reduced power sum has order at most `q`.
The coprime-power obstruction is the elementary condition `q ∤ r`. -/
theorem rootMultiplicity_reduced_power_sum_le
    (G A T : Polynomial ℂ) (q r : ℕ) (hq : 0 < q) (hnot : ¬ q ∣ r)
    (a z : ℂ) (ha : a ≠ 0) (hGzero : G ≠ 0)
    (hG : G.rootMultiplicity z = 1) (hTzero : T ≠ 0)
    (hT : T.rootMultiplicity z = 1) :
    (G ^ r * A ^ q + C a * T ^ q).rootMultiplicity z ≤ q := by
  have hright : C a * T ^ q ≠ 0 := mul_ne_zero (C_ne_zero.mpr ha) (pow_ne_zero _ hTzero)
  have hrightOrder : (C a * T ^ q).rootMultiplicity z = q := by
    rw [rootMultiplicity_mul hright, rootMultiplicity_C,
      OnLeConjecture.Polynomial.rootMultiplicity_pow_eq_mul T hTzero,
      hT, mul_one, zero_add]
  by_cases hA : A = 0
  · simp only [hA, zero_pow hq.ne', mul_zero, zero_add, hrightOrder]
    exact le_rfl
  have hleft : G ^ r * A ^ q ≠ 0 := mul_ne_zero (pow_ne_zero _ hGzero) (pow_ne_zero _ hA)
  have hleftOrder : (G ^ r * A ^ q).rootMultiplicity z = r + q * A.rootMultiplicity z := by
    rw [rootMultiplicity_mul hleft,
      OnLeConjecture.Polynomial.rootMultiplicity_pow_eq_mul G hGzero,
      OnLeConjecture.Polynomial.rootMultiplicity_pow_eq_mul A hA, hG, mul_one]
  have hne : (G ^ r * A ^ q).rootMultiplicity z ≠ (C a * T ^ q).rootMultiplicity z := by
    rw [hleftOrder, hrightOrder]
    intro h
    apply hnot
    have hdiv : q ∣ r + q * A.rootMultiplicity z := by rw [h]
    simpa only [Nat.add_sub_cancel_right] using
      Nat.dvd_sub hdiv (dvd_mul_right q (A.rootMultiplicity z))
  rw [rootMultiplicity_add_eq_min_of_ne _ _ hleft hright z hne, hrightOrder]
  exact min_le_right _ _

end OnLeConjecture.DTwo
