/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.QuinticTwoForms
public import OnLeConjecture.DThree.RationalCubicInitialPair
public import OnLeConjecture.Analytic.RationalInitialCoefficientOrder
import Mathlib.Tactic

/-!
# Integrality in the quintic alternative

The constant cubic-quintic equation forces both lower cubic coefficients
to occur. Their exact orders in the original analytic polynomial show
that the ramification denominator divides both twice and three times the
weight numerator, hence divides the numerator itself.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial

theorem lower_coefficients_ne_zero_of_weighted_quintic_omega
    (p q : ℂ[X]) (hp : p.Monic) (hdegree : p.natDegree = 3)
    (hdepressed : p.coeff 2 = 0) (hq : q.natDegree ≤ 5) (r : ℂ) (hr : r ≠ 0)
    (hne : OnLeConjecture.Polynomial.weightedPairOmega 3 (5 * r) r p q ≠ 0)
    (hconstant : (OnLeConjecture.Polynomial.weightedPairOmega 3 (5 * r) r p q).natDegree = 0) :
    p.coeff 1 ≠ 0 ∧ p.coeff 0 ≠ 0 ∧ (p.coeff 1) ^ 3 = 9 * (p.coeff 0) ^ 2 := by
  let Ω := OnLeConjecture.Polynomial.weightedPairOmega 3 (5 * r) r p q
  have hΩ : Ω = C (Ω.coeff 0) := eq_C_of_natDegree_eq_zero hconstant
  have hc : Ω.coeff 0 ≠ 0 := by
    intro hzero
    have hzeroΩ : Ω = 0 := hΩ.trans (by rw [hzero, map_zero])
    exact hne hzeroΩ
  have hscale : C r * (5 * p.derivative * q - 3 * p * q.derivative) = Ω := by
    simp only [Ω, OnLeConjecture.Polynomial.weightedPairOmega, map_mul,
      C_ofNat, Nat.cast_ofNat]
    ring
  have hODE : 5 * p.derivative * q - 3 * p * q.derivative = C (Ω.coeff 0 / r) := by
    apply mul_left_cancel₀ (C_ne_zero.mpr hr)
    calc
      C r * (5 * p.derivative * q - 3 * p * q.derivative) = Ω := hscale
      _ = C (Ω.coeff 0) := hΩ
      _ = C r * C (Ω.coeff 0 / r) := by
        rw [← map_mul]
        congr 1
        field_simp
  have hpForm := eq_cubic_of_monic_degree_three p hp hdegree hdepressed
  have h := lower_coefficients_ne_zero_of_cubic_quintic_constant_ode
    (p.coeff 1) (p.coeff 0) q hq (Ω.coeff 0 / r) (div_ne_zero hc hr)
      (by simpa only [← hpForm] using hODE)
  exact h

end OnLeConjecture.DThree

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- The quintic alternative makes the actual rational Newton weight an
integer. Both original lower cubic coefficient orders are attained. -/
theorem RationalPreparedWeightedPair.quintic_weight_integral
    {s r t : ℕ} {hs : 0 < s} {P : Polynomial (Germ 1)} {U u : Germ 2}
    {hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u}
    (data : RationalPreparedWeightedPair s r 3 t hs P U u hfinite)
    (hr : 0 < r) (hP : P.Monic) (hPm : P.natDegree = 3) (hU : IsUnit U)
    (horder : ∀ i, i < 3 →
      ((r * (3 - i) : ℕ) : ℕ∞) ≤ s • vanishingOrder (P.coeff i))
    (hdepressed : P.coeff 2 = 0)
    (hquintic : (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial).natDegree = 5)
    (hne : OnLeConjecture.Polynomial.weightedPairOmega 3 (data.degree : ℂ) (r : ℂ)
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.firstInitial)
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial) ≠ 0)
    (hconstant : (OnLeConjecture.Polynomial.weightedPairOmega 3 (data.degree : ℂ) (r : ℂ)
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.firstInitial)
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial)).natDegree = 0) :
    let p := MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.firstInitial
    p.coeff 1 ≠ 0 ∧ p.coeff 0 ≠ 0 ∧ (p.coeff 1) ^ 3 = 9 * (p.coeff 0) ^ 2 ∧
      s • vanishingOrder (P.coeff 1) = ((2 * r : ℕ) : ℕ∞) ∧
      s • vanishingOrder (P.coeff 0) = ((3 * r : ℕ) : ℕ∞) ∧ s ∣ r := by
  dsimp only
  have hweight := (data.nonzero_omega hne).2.2.1
  rw [hquintic] at hweight
  have hweightComplex : (data.degree : ℂ) = 5 * (r : ℂ) := by
    rw [hweight, Nat.cast_mul, Nat.cast_ofNat, mul_comm]
  have hcoeff := DThree.lower_coefficients_ne_zero_of_weighted_quintic_omega
    _ _ data.first_chart_monic data.first_chart_degree (data.first_zero_coefficient 2 hdepressed)
      hquintic.le r (by exact_mod_cast Nat.ne_zero_of_lt hr)
        (by rwa [← hweightComplex]) (by rwa [← hweightComplex])
  obtain ⟨h1, hd1⟩ := data.coefficient_order_of_chart_ne_zero hr hP hPm hU horder 1 hcoeff.1
  obtain ⟨h0, hd0⟩ := data.coefficient_order_of_chart_ne_zero hr hP hPm hU horder 0 hcoeff.2.1
  have hd2 : s ∣ 2 * r := by simpa only [Nat.reduceSub, Nat.mul_comm] using hd1
  have hd3 : s ∣ 3 * r := by simpa only [Nat.sub_zero, Nat.mul_comm] using hd0
  have hdr : s ∣ r := by
    have h := Nat.dvd_sub hd3 hd2
    have heq : 3 * r - 2 * r = r := by omega
    rwa [heq] at h
  exact ⟨hcoeff.1, hcoeff.2.1, hcoeff.2.2,
    by simpa only [Nat.reduceSub, Nat.mul_comm] using h1,
    by simpa only [Nat.sub_zero, Nat.mul_comm] using h0, hdr⟩

end OnLeConjecture.Analytic.Germ
