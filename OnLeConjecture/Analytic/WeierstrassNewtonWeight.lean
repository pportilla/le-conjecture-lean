/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OneVariableOrder
public import OnLeConjecture.Analytic.WeierstrassPreparation
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Integer Newton weights selected from analytic coefficients

The minimum of the finitely many nonzero lower-coefficient slopes is
constructed after clearing denominators with `m!`. Zero coefficients
have infinite order and impose no additional restriction. No Newton
slope, rational minimizer, or Puiseux expansion is assumed as input.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- Every possible lower-coefficient denominator divides `m!`. -/
theorem lower_coefficient_denominator_dvd_factorial (m i : ℕ) (hi : i < m) :
    m - i ∣ m.factorial :=
  Nat.dvd_factorial (by omega) (Nat.sub_le m i)

private theorem clear_factorial_denominator (m i v : ℕ) (hi : i < m) :
    (m.factorial / (m - i) * v) * (m - i) = m.factorial * v := by
  calc
    (m.factorial / (m - i) * v) * (m - i) =
        (m.factorial / (m - i) * (m - i)) * v := by ring
    _ = m.factorial * v := by
      rw [Nat.div_mul_cancel (lower_coefficient_denominator_dvd_factorial m i hi)]

/-- Positive integer weights realize the least lower-coefficient slope.
The denominator can be chosen to be `m!`, and a nonzero coefficient
attains the bound. Monicity is not needed for this selection theorem. -/
theorem exists_integer_newton_weight
    (m A : ℕ) (_hm : 0 < m) (hA : 0 < A) (P : Polynomial (Germ 1))
    (hcoeff : ∀ i < m, P.coeff i ∈ maximalIdeal 1 ^ (A * (m - i)))
    (hnonzero : ∃ i < m, P.coeff i ≠ 0) :
    ∃ s r : ℕ, s = m.factorial ∧ 0 < s ∧ 0 < r ∧ s * A ≤ r ∧
      (∀ i < m, ((r * (m - i) : ℕ) : ℕ∞) ≤ s • vanishingOrder (P.coeff i)) ∧
      ∃ i < m, P.coeff i ≠ 0 ∧
        ((r * (m - i) : ℕ) : ℕ∞) = s • vanishingOrder (P.coeff i) := by
  classical
  let candidates := (Finset.range m).filter fun i ↦ P.coeff i ≠ 0
  have hnonempty : candidates.Nonempty := by
    obtain ⟨i, hi, hPi⟩ := hnonzero
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hPi⟩⟩
  let scaledOrder (i : ℕ) :=
    m.factorial / (m - i) * (vanishingOrder (P.coeff i)).toNat
  obtain ⟨j, hj, hminimal⟩ := candidates.exists_min_image scaledOrder hnonempty
  have hjlt : j < m := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have hjne : P.coeff j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hfinite (i : ℕ) (hi : P.coeff i ≠ 0) :
      ((vanishingOrder (P.coeff i)).toNat : ℕ∞) = vanishingOrder (P.coeff i) :=
    ENat.natCast_toNat (vanishingOrder_eq_top_iff.not.mpr hi)
  have horder (i : ℕ) (hi : i < m) (hPi : P.coeff i ≠ 0) :
      A * (m - i) ≤ (vanishingOrder (P.coeff i)).toNat := by
    have h := mem_maximalIdeal_one_pow_iff.mp (hcoeff i hi)
    rw [← hfinite i hPi] at h
    exact_mod_cast h
  have hlower : m.factorial * A ≤ scaledOrder j := by
    have h := Nat.mul_le_mul_left (m.factorial / (m - j)) (horder j hjlt hjne)
    have heq : m.factorial / (m - j) * (A * (m - j)) = m.factorial * A := by
      rw [← mul_assoc, clear_factorial_denominator m j A hjlt]
    rwa [heq] at h
  have hpositive : 0 < scaledOrder j :=
    (Nat.mul_pos (Nat.factorial_pos m) hA).trans_le hlower
  refine ⟨m.factorial, scaledOrder j, rfl, Nat.factorial_pos m,
    hpositive, hlower, ?_, j, hjlt, hjne, ?_⟩
  · intro i hi
    by_cases hPi : P.coeff i = 0
    · rw [hPi, vanishingOrder_zero, nsmul_eq_mul,
        ENat.mul_top (by exact_mod_cast (Nat.factorial_pos m).ne')]
      exact le_top
    · have himem : i ∈ candidates :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hPi⟩
      have hbound := Nat.mul_le_mul_right (m - i) (hminimal i himem)
      change scaledOrder j * (m - i) ≤
        (m.factorial / (m - i) * (vanishingOrder (P.coeff i)).toNat) * (m - i) at hbound
      rw [clear_factorial_denominator m i _ hi] at hbound
      rw [← hfinite i hPi, nsmul_eq_mul]
      exact_mod_cast hbound
  · rw [← hfinite j hjne, nsmul_eq_mul]
    have heq := clear_factorial_denominator m j (vanishingOrder (P.coeff j)).toNat hjlt
    change scaledOrder j * (m - j) = m.factorial * (vanishingOrder (P.coeff j)).toNat at heq
    exact_mod_cast heq

/-- For a depressed polynomial, any nonzero lower coefficient attaining
the Newton bound has index at most `m-2`. -/
theorem attaining_index_le_sub_two_of_depressed
    (m : ℕ) (P : Polynomial (Germ 1)) (hdepressed : P.coeff (m - 1) = 0)
    (i : ℕ) (hi : i < m) (hPi : P.coeff i ≠ 0) : i ≤ m - 2 := by
  have hne : i ≠ m - 1 := by
    intro heq
    exact hPi (heq ▸ hdepressed)
  omega

/-- A monic polynomial with all its lower coefficients zero is the pure
power of the polynomial variable. -/
theorem monic_eq_X_pow_of_lower_coefficients_zero
    (m : ℕ) (P : Polynomial (Germ 1)) (hmonic : P.Monic) (hdegree : P.natDegree = m)
    (hzero : ∀ i < m, P.coeff i = 0) : P = X ^ m := by
  ext i
  by_cases hi : i < m
  · rw [hzero i hi, Polynomial.coeff_X_pow, if_neg (by omega)]
  · by_cases hieq : i = m
    · subst i
      rw [← hdegree, Polynomial.coeff_natDegree, hmonic, Polynomial.coeff_X_pow,
        if_pos rfl]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
        Polynomial.coeff_X_pow, if_neg (by omega)]

/-- A squarefree analytic germ prepared by a monic polynomial of degree
at least two must have a nonzero lower coefficient. In particular this
supplies the nonempty set needed for Newton weight selection. The
factor multiplying the polynomial need not be assumed a unit here. -/
theorem exists_nonzero_lower_coefficient_of_squarefree_preparation
    (m : ℕ) (hm : 2 ≤ m) (P : Polynomial (Germ 1))
    (hmonic : P.Monic) (hdegree : P.natDegree = m) (u : Germ 2)
    (hsquarefree : Squarefree (u * firstCoordinatePolynomialEvaluation P)) :
    ∃ i < m, P.coeff i ≠ 0 := by
  by_contra h
  push Not at h
  have hpure := monic_eq_X_pow_of_lower_coefficients_zero m P hmonic hdegree h
  have hsf := hsquarefree.of_mul_right
  rw [hpure, firstCoordinatePolynomialEvaluation, Polynomial.eval₂_pow,
    Polynomial.eval₂_X] at hsf
  have hnonunit : ¬ IsUnit (coordinate (0 : Fin 2)) := by
    rw [isUnit_iff_valueRingHom_ne_zero, valueRingHom_coordinate]
    simp
  have hcases := hsf.eq_zero_or_one_of_pow_of_not_isUnit hnonunit
  omega

end OnLeConjecture.Analytic.Germ
