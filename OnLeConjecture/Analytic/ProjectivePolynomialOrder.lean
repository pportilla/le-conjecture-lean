/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OneVariablePolynomialRootOrder
import Mathlib.Tactic

/-!
# The polynomial contribution at the complementary exceptional point

Reversing a degree-bounded coefficient list exchanges the two projective
charts of a homogeneous plane polynomial. The degree in the finite chart
plus the vanishing order at the complementary point is bounded by the
homogeneous degree. The proof uses the nonzero leading coefficient and
the corresponding nonzero coefficient of the reversed polynomial.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- A nonzero coefficient bounds the analytic order of a polynomial germ. -/
theorem polynomialEvaluation_order_le_of_coeff_ne_zero
    (P : ℂ[X]) (n : ℕ) (hn : P.coeff n ≠ 0) :
    (vanishingOrder (oneVariablePolynomialEvaluation P)).toNat ≤ n := by
  have hnot : oneVariablePolynomialEvaluation P ∉ maximalIdeal 1 ^ (n + 1) := by
    intro hmem
    rw [maximalIdeal_one_pow_eq_span_coordinate_pow, Ideal.mem_span_singleton] at hmem
    have hdiv := map_dvd oneVariableTaylorRingHom hmem
    rw [map_pow, oneVariableTaylorRingHom_apply,
      oneVariableTaylorSeries_coordinate_eq_X, oneVariableTaylor_polynomialEvaluation] at hdiv
    have hcoeff := (PowerSeries.X_pow_dvd_iff.mp hdiv) n (by omega)
    exact hn (by simpa only [Polynomial.coeff_coe] using hcoeff)
  have hlt : vanishingOrder (oneVariablePolynomialEvaluation P) < ((n + 1 : ℕ) : ℕ∞) :=
    lt_of_not_ge (fun h => hnot (mem_maximalIdeal_one_pow_iff.mpr h))
  have hle : vanishingOrder (oneVariablePolynomialEvaluation P) ≤ (n : ℕ∞) :=
    ENat.lt_natCast_add_one_iff.mp (by simpa only [Nat.cast_add, Nat.cast_one] using hlt)
  simpa only [ENat.toNat_natCast] using ENat.toNat_le_toNat hle (ENat.natCast_ne_top n)

/-- Coefficients of a finite coefficient list, including the endpoints. -/
theorem coefficient_sum_C_mul_X_pow
    (m : ℕ) (a : Fin (m + 1) → ℂ) (k : Fin (m + 1)) :
    (∑ j : Fin (m + 1), C (a j) * (X : ℂ[X]) ^ j.val).coeff k.val = a k := by
  classical
  rw [finsetSum_coeff, Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    have hne : j.val ≠ k.val := fun h => hj (Fin.ext h)
    simp [coeff_C_mul, coeff_X_pow, Ne.symm hne]
  · simp

/-- Reversal of the bounded coefficient list sends index `k` to `m-k`. -/
theorem coefficient_sum_C_mul_X_pow_reverse
    (m : ℕ) (a : Fin (m + 1) → ℂ) (k : Fin (m + 1)) :
    (∑ j : Fin (m + 1), C (a j) * (X : ℂ[X]) ^ (m - j.val)).coeff
      (m - k.val) = a k := by
  classical
  rw [finsetSum_coeff, Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    have hne : m - j.val ≠ m - k.val := by
      intro h
      apply hj
      apply Fin.ext
      have hjlt := j.isLt
      have hklt := k.isLt
      omega
    simp [coeff_C_mul, coeff_X_pow, Ne.symm hne]
  · simp

/-- The finite chart degree and the complementary analytic order fit
within the original homogeneous degree. -/
theorem polynomial_reverse_order_budget
    (m : ℕ) (a : Fin (m + 1) → ℂ)
    (hne : (∑ k : Fin (m + 1), C (a k) * (X : ℂ[X]) ^ k.val) ≠ 0) :
    (∑ k : Fin (m + 1), C (a k) * (X : ℂ[X]) ^ k.val).natDegree +
      (vanishingOrder (oneVariablePolynomialEvaluation
        (∑ k : Fin (m + 1), C (a k) * (X : ℂ[X]) ^ (m - k.val)))).toNat ≤ m := by
  classical
  let P : ℂ[X] := ∑ k : Fin (m + 1), C (a k) * X ^ k.val
  have hdegree : P.natDegree ≤ m := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k _
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      (by simpa only [natDegree_X_pow] using (show k.val ≤ m by omega))
  let k : Fin (m + 1) := ⟨P.natDegree, by omega⟩
  have hak : a k ≠ 0 := by
    have heq := coefficient_sum_C_mul_X_pow m a k
    change P.coeff P.natDegree = a k at heq
    rw [coeff_natDegree] at heq
    rw [← heq]
    exact leadingCoeff_ne_zero.mpr hne
  have hcoeff :
      (∑ j : Fin (m + 1), C (a j) * (X : ℂ[X]) ^ (m - j.val)).coeff
        (m - P.natDegree) ≠ 0 := by
    change (∑ j : Fin (m + 1), C (a j) * (X : ℂ[X]) ^ (m - j.val)).coeff
      (m - k.val) ≠ 0
    rw [coefficient_sum_C_mul_X_pow_reverse]
    exact hak
  have horder := polynomialEvaluation_order_le_of_coeff_ne_zero _ _ hcoeff
  change P.natDegree + _ ≤ m
  omega

end OnLeConjecture.Analytic.Germ
