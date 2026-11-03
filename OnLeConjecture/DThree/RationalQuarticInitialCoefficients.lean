/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.CubicQuinticPointBasisExclusion
public import OnLeConjecture.Analytic.RationalInitialCoefficientStrictOrder
import Mathlib.Tactic

/-!
# Coefficient orders in the cubic-quartic alternatives

The constant weighted Jacobian equation gives the E/H alternatives for
the first chart. The nonzero coefficient has its exact original order,
and the other coefficient has strictly larger order than its Newton
bound. No original analytic coefficient is assumed to vanish.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial

theorem eq_quartic_of_natDegree_le_four (q : ℂ[X]) (hq : q.natDegree ≤ 4) :
    q = quartic (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0) := by
  ext j
  by_cases hj : j < 5
  · interval_cases j <;> simp [quartic, coeff_mul_X_pow']
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    simp [quartic, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C,
      show j ≠ 0 by omega, show 1 ≠ j by omega,
      show j ≠ 2 by omega, show j ≠ 3 by omega, show j ≠ 4 by omega]

theorem lower_coefficients_of_weighted_quartic_omega
    (p q : ℂ[X]) (hp : p.Monic) (hdegree : p.natDegree = 3)
    (hdepressed : p.coeff 2 = 0) (hq : q.natDegree ≤ 4) (r : ℂ) (hr : r ≠ 0)
    (hne : OnLeConjecture.Polynomial.weightedPairOmega 3 (4 * r) r p q ≠ 0)
    (hconstant : (OnLeConjecture.Polynomial.weightedPairOmega 3 (4 * r) r p q).natDegree = 0) :
    (p.coeff 1 = 0 ∧ p.coeff 0 ≠ 0) ∨ (p.coeff 0 = 0 ∧ p.coeff 1 ≠ 0) := by
  let Ω := OnLeConjecture.Polynomial.weightedPairOmega 3 (4 * r) r p q
  have hΩ : Ω = C (Ω.coeff 0) := eq_C_of_natDegree_eq_zero hconstant
  have hc : Ω.coeff 0 ≠ 0 := by
    intro hzero
    exact hne (hΩ.trans (by rw [hzero, map_zero]))
  have hscale : C r * (4 * p.derivative * q - 3 * p * q.derivative) = Ω := by
    simp only [Ω, OnLeConjecture.Polynomial.weightedPairOmega, map_mul,
      C_ofNat, Nat.cast_ofNat]
    ring
  have hODE : 4 * p.derivative * q - 3 * p * q.derivative = C (Ω.coeff 0 / r) := by
    apply mul_left_cancel₀ (C_ne_zero.mpr hr)
    calc
      C r * (4 * p.derivative * q - 3 * p * q.derivative) = Ω := hscale
      _ = C (Ω.coeff 0) := hΩ
      _ = C r * C (Ω.coeff 0 / r) := by
        rw [← map_mul]
        congr 1
        field_simp
  have hpForm := eq_cubic_of_monic_degree_three p hp hdegree hdepressed
  have hqForm := eq_quartic_of_natDegree_le_four q hq
  have h := (classify_two_forms_of_ode (p.coeff 1) (p.coeff 0)
    (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
      (Ω.coeff 0 / r) (div_ne_zero hc hr)
        (by simpa only [← hpForm, ← hqForm] using hODE)).2
  rcases h with h | h
  · exact Or.inl ⟨h.1, h.2.1⟩
  · exact Or.inr ⟨h.1, h.2.1⟩

end OnLeConjecture.DThree

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

theorem RationalPreparedWeightedPair.quartic_coefficient_order_alternatives
    {s r t : ℕ} {hs : 0 < s} {P : Polynomial (Germ 1)} {U u : Germ 2}
    {hfinite : PlaneCurve.HasFiniteIntersection (U * firstCoordinatePolynomialEvaluation P) u}
    (data : RationalPreparedWeightedPair s r 3 t hs P U u hfinite)
    (hr : 0 < r) (hP : P.Monic) (hPm : P.natDegree = 3) (hU : IsUnit U)
    (horder : ∀ j, j < 3 →
      ((r * (3 - j) : ℕ) : ℕ∞) ≤ s • vanishingOrder (P.coeff j))
    (hdepressed : P.coeff 2 = 0)
    (hquartic : (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial).natDegree = 4)
    (hne : OnLeConjecture.Polynomial.weightedPairOmega 3 (data.degree : ℂ) (r : ℂ)
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.firstInitial)
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial) ≠ 0)
    (hconstant : (OnLeConjecture.Polynomial.weightedPairOmega 3 (data.degree : ℂ) (r : ℂ)
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.firstInitial)
      (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) data.secondInitial)).natDegree = 0) :
    (s • vanishingOrder (P.coeff 0) = ((3 * r : ℕ) : ℕ∞) ∧
      ((2 * r : ℕ) : ℕ∞) < s • vanishingOrder (P.coeff 1) ∧ s ∣ 3 * r) ∨
    (s • vanishingOrder (P.coeff 1) = ((2 * r : ℕ) : ℕ∞) ∧
      ((3 * r : ℕ) : ℕ∞) < s • vanishingOrder (P.coeff 0) ∧ s ∣ 2 * r) := by
  have hweight := (data.nonzero_omega hne).2.2.1
  rw [hquartic] at hweight
  have hweightC : (data.degree : ℂ) = 4 * (r : ℂ) := by
    rw [hweight, Nat.cast_mul, Nat.cast_ofNat, mul_comm]
  have h := DThree.lower_coefficients_of_weighted_quartic_omega _ _
    data.first_chart_monic data.first_chart_degree (data.first_zero_coefficient 2 hdepressed)
      hquartic.le r (by exact_mod_cast Nat.ne_zero_of_lt hr)
        (by rwa [← hweightC]) (by rwa [← hweightC])
  rcases h with ⟨hzero, hneCoeff⟩ | ⟨hzero, hneCoeff⟩
  · left
    obtain ⟨hexact, hdiv⟩ := data.coefficient_order_of_chart_ne_zero hr hP hPm hU horder 0 hneCoeff
    have hstrict := data.coefficient_order_gt_of_chart_zero hr hP hPm hU horder 1 hzero
    simpa only [Nat.sub_zero, Nat.reduceSub, Nat.mul_comm] using ⟨hexact, hstrict, hdiv⟩
  · right
    obtain ⟨hexact, hdiv⟩ := data.coefficient_order_of_chart_ne_zero hr hP hPm hU horder 1 hneCoeff
    have hstrict := data.coefficient_order_gt_of_chart_zero hr hP hPm hU horder 0 hzero
    simpa only [Nat.sub_zero, Nat.reduceSub, Nat.mul_comm] using ⟨hexact, hstrict, hdiv⟩

end OnLeConjecture.Analytic.Germ
