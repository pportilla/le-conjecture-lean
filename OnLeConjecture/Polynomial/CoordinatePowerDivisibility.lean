/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic.FinCases

/-!
# Descent of polynomial coordinate divisibility through ramification

The substitution `(X,Y) ↦ (X,Yᵇ)` is injective for positive `b` and
multiplies the second exponent of each coefficient by exactly `b`.
-/

public section

namespace OnLeConjecture.Polynomial

open MvPolynomial

/-- Coordinate divisibility is detected by the coefficients below the
corresponding coordinate exponent. -/
theorem variable_pow_dvd_iff_coeff_eq_zero (i : Fin 2) (N : ℕ)
    (P : MvPolynomial (Fin 2) ℂ) :
    X i ^ N ∣ P ↔ ∀ d : Fin 2 →₀ ℕ, d i < N → coeff d P = 0 := by
  classical
  rw [X_pow_eq_monomial, monomial_one_dvd_iff_modMonomial_eq_zero]
  constructor
  · intro h d hd
    have hnot : ¬ Finsupp.single i N ≤ d := by simpa using Nat.not_le.mpr hd
    have hc := congrArg (coeff d) h
    simpa only [coeff_modMonomial_of_not_le P hnot, coeff_zero] using hc
  · intro h
    apply MvPolynomial.ext
    intro d
    rw [coeff_zero]
    by_cases hle : Finsupp.single i N ≤ d
    · exact coeff_modMonomial_of_le P hle
    · rw [coeff_modMonomial_of_not_le P hle]
      exact h d (by simpa using Nat.lt_of_not_ge (by simpa using hle))

private noncomputable def secondExponentScale (b : ℕ) (d : Fin 2 →₀ ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (d 0) + Finsupp.single 1 (b * d 1)

private theorem secondExponentScale_injective (b : ℕ) (hb : 0 < b) :
    Function.Injective (secondExponentScale b) := by
  intro d e heq
  have hzero := congrArg (fun v : Fin 2 →₀ ℕ => v 0) heq
  have hone := congrArg (fun v : Fin 2 →₀ ℕ => v 1) heq
  simp only [secondExponentScale, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide),
    Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide), zero_add, add_zero] at hzero hone
  ext i
  fin_cases i
  · exact hzero
  · exact Nat.eq_of_mul_eq_mul_left hb hone

private theorem second_power_substitution_monomial (b : ℕ) (d : Fin 2 →₀ ℕ) (c : ℂ) :
    MvPolynomial.aeval (![X 0, X 1 ^ b] : Fin 2 → MvPolynomial (Fin 2) ℂ) (monomial d c) =
      monomial (secondExponentScale b d) c := by
  simp [MvPolynomial.monomial_fin_two, secondExponentScale, ← pow_mul]

/-- Every original coefficient occurs at its ramified exponent. -/
theorem coeff_second_power_substitution (b : ℕ) (hb : 0 < b)
    (P : MvPolynomial (Fin 2) ℂ) (d : Fin 2 →₀ ℕ) :
    coeff (Finsupp.single 0 (d 0) + Finsupp.single 1 (b * d 1))
      (MvPolynomial.aeval (![X 0, X 1 ^ b] : Fin 2 → MvPolynomial (Fin 2) ℂ) P) =
        coeff d P := by
  classical
  change coeff (secondExponentScale b d) _ = _
  induction P using MvPolynomial.induction_on' with
  | monomial e c =>
      rw [second_power_substitution_monomial]
      simp only [coeff_monomial,
        (secondExponentScale_injective b hb).eq_iff]
  | add P Q hP hQ => simp only [map_add, coeff_add, hP, hQ]

/-- A coordinate-power factor of the ramified polynomial descends to the
corresponding factor of the original polynomial. -/
theorem second_variable_pow_dvd_of_ramified_dvd (b N : ℕ) (hb : 0 < b)
    (P : MvPolynomial (Fin 2) ℂ)
    (hdiv : X (1 : Fin 2) ^ (b * N) ∣
      MvPolynomial.aeval (![X 0, X 1 ^ b] : Fin 2 → MvPolynomial (Fin 2) ℂ) P) :
    X (1 : Fin 2) ^ N ∣ P := by
  rw [variable_pow_dvd_iff_coeff_eq_zero] at hdiv ⊢
  intro d hd
  rw [← coeff_second_power_substitution b hb P d]
  apply hdiv
  simpa using Nat.mul_lt_mul_of_pos_left hd hb

end OnLeConjecture.Polynomial
