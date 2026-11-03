/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.PlaneCurve.Morse
public import OnLeConjecture.PlaneCurve.BranchCountInvariance
public import OnLeConjecture.Analytic.PlaneWeierstrassPrimes
public import OnLeConjecture.Analytic.PlaneElimination
public import Mathlib.Algebra.Polynomial.Monic

/-!
# Irreducibility of the odd quadratic curve

If a monic quadratic over the one-variable analytic ring factors, its
constant term is the product of two roots whose sum is zero. Its order
is therefore even. Convergent Weierstrass division transports the prime
polynomial to the actual plane analytic germ.
-/

public section

namespace OnLeConjecture.PlaneCurve

open Analytic Analytic.Germ _root_.Polynomial

private theorem vanishingOrder_neg_eq (a : Germ 1) : vanishingOrder (-a) = vanishingOrder a := by
  have heq : -a = (-1 : Germ 1) * a := by ring
  rw [heq, vanishingOrder_mul,
    vanishingOrder_eq_zero_iff_isUnit.mpr isUnit_neg_one, zero_add]

/-- The odd-exponent quadratic is irreducible already over the analytic
coefficient ring. -/
theorem odd_morse_polynomial_irreducible (k : ℕ) (hodd : Odd k) :
    Irreducible ((X : Polynomial (Germ 1)) ^ 2 + C (coordinate (0 : Fin 1) ^ k)) := by
  let P : Polynomial (Germ 1) := X ^ 2 + C (coordinate (0 : Fin 1) ^ k)
  have hmonic : P.Monic := monic_X_pow_add_C _ (by omega)
  have hdegree : P.natDegree = 2 := natDegree_X_pow_add_C
  by_contra hn
  obtain ⟨a, b, hab, hsum⟩ :=
    (hmonic.not_irreducible_iff_exists_add_mul_eq_coeff hdegree).mp hn
  have hc0 : P.coeff 0 = coordinate (0 : Fin 1) ^ k := by
    norm_num only [P, coeff_add, coeff_X_pow, coeff_C, zero_add, ite_true, ite_false]
  have hc1 : P.coeff 1 = 0 := by
    norm_num only [P, coeff_add, coeff_X_pow, coeff_C, zero_add, ite_true, ite_false]
  have hab' : coordinate (0 : Fin 1) ^ k = a * b := by
    simpa only [hc0] using hab
  have hsum' : a + b = 0 := by
    simpa only [hc1] using hsum.symm
  have hb : b = -a := eq_neg_of_add_eq_zero_right hsum'
  have ha : a ≠ 0 := by
    intro hz
    have hzero : coordinate (0 : Fin 1) ^ k = 0 := by rw [hab', hz, zero_mul]
    exact pow_ne_zero k (coordinate_ne_zero (0 : Fin 1)) hzero
  have horder := congrArg vanishingOrder hab'
  rw [vanishingOrder_coordinate_pow, vanishingOrder_mul, hb, vanishingOrder_neg_eq] at horder
  have hfinite : vanishingOrder a ≠ ⊤ := vanishingOrder_eq_top_iff.not.mpr ha
  have hnat : k = (vanishingOrder a).toNat + (vanishingOrder a).toNat := by
    have h := congrArg ENat.toNat horder
    simpa only [ENat.toNat_natCast, ENat.toNat_add hfinite hfinite] using h
  obtain ⟨n, hn⟩ := hodd
  omega

/-- For a positive odd exponent, the equation `x²+y^k` has one
irreducible analytic branch. -/
theorem morseCurve_irreducible_of_odd (k : ℕ) (hk : 0 < k) (hodd : Odd k) :
    Irreducible (morseCurve k) := by
  let P : Polynomial (Germ 1) := X ^ 2 + C (coordinate (0 : Fin 1) ^ k)
  have hprime : Prime P := UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (odd_morse_polynomial_irreducible k hodd)
  have hcoeff : ∀ j, j < 1 + 1 → P.coeff j ∈ maximalIdeal 1 := by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 := by omega
    rcases hjcases with rfl | rfl
    · have hc : P.coeff 0 = coordinate (0 : Fin 1) ^ k := by
        norm_num only [P, coeff_add, coeff_X_pow, coeff_C, zero_add, ite_true, ite_false]
      rw [hc]
      exact (maximalIdeal 1).pow_mem_of_mem (coordinate_mem_maximalIdeal 0) k hk
    · have hc : P.coeff 1 = 0 := by
        norm_num only [P, coeff_add, coeff_X_pow, coeff_C, zero_add, ite_true, ite_false]
      rw [hc]
      exact Ideal.zero_mem _
  have h := prime_firstCoordinatePolynomialEvaluation_of_distinguished (d := 1)
    hprime (monic_X_pow_add_C _ (by omega)) (show P.natDegree = 1 + 1 from
      natDegree_X_pow_add_C) hcoeff
  have heval : firstCoordinatePolynomialEvaluation P = morseCurve k := by
    simp only [P, firstCoordinatePolynomialEvaluation, eval₂_add, eval₂_pow,
      eval₂_X, eval₂_C, map_pow, hyperplaneExtension_coordinate_plane, morseCurve]
  rw [heval] at h
  exact h.irreducible

theorem irreducibleBranchCount_morseCurve_of_odd (k : ℕ) (hk : 0 < k) (hodd : Odd k) :
    irreducibleBranchCount (morseCurve k) = 1 :=
  irreducibleBranchCount_eq_one_of_irreducible _ (morseCurve_irreducible_of_odd k hk hodd)

end OnLeConjecture.PlaneCurve
