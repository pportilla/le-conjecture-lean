/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DFour.QuarticResolutionCoverage
import Mathlib.Tactic

/-!
# Coefficient expressions throughout the quartic free chart chain

The two values of `ε` describe the integral and half-integral Newton
slopes. The expressions below are obtained by division of the original
coefficients and exact chart substitution. In particular their use does
not posit expressions for the germs recorded in a resolution.
-/

public section

namespace OnLeConjecture.DFour

open Analytic Analytic.Germ _root_.Polynomial

/-- The coefficient information obtained from a square ramified initial
chart, with the ramification and ordinary coefficients retained. -/
structure SquareQuarticNewtonData (P : Polynomial (Germ 1)) (η : ℂ) where
  s : ℕ
  r : ℕ
  s_pos : 0 < s
  r_pos : 0 < r
  monic : P.Monic
  degree : P.natDegree = 4
  depressed : P.coeff 3 = 0
  parameter_ne_zero : η ≠ 0
  order : ∀ i < 4, ((r * (4 - i) : ℕ) : ℕ∞) ≤ s • vanishingOrder (P.coeff i)
  initial : MvPolynomial (Fin 2) ℂ
  homogeneous : initial.IsWeightedHomogeneous ![r, 1] (r * 4)
  tail : firstCoordinatePolynomialEvaluation
      (P.map (oneVariablePowerMapGerm s s_pos).pullbackRingHom) -
    coordinatePolynomialAlgHom 2 initial ∈ weightedOrderIdeal r (r * 4 + 1)
  chart : MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) initial = (X ^ 2 + C η) ^ 2

/-- Divided analytic coefficients. The existence theorem below derives
these identities from the square initial chart. -/
structure QuarticCoefficientExpansion (A ε : ℕ) (P : Polynomial (Germ 1)) (η : ℂ) where
  a₂ : Germ 1
  a₁ : Germ 1
  a₀ : Germ 1
  coeff_two : P.coeff 2 = coordinate (0 : Fin 1) ^ (2 * A + ε) *
    (constRingHom 1 (2 * η) + coordinate (0 : Fin 1) * a₂)
  coeff_one : P.coeff 1 = coordinate (0 : Fin 1) ^ (3 * A + ε + 1) * a₁
  coeff_zero : P.coeff 0 = coordinate (0 : Fin 1) ^ (4 * A + 2 * ε) *
    (constRingHom 1 (η ^ 2) + coordinate (0 : Fin 1) * a₀)

theorem SquareQuarticNewtonData.exists_coefficientExpansion
    {P : Polynomial (Germ 1)} {η : ℂ} (d : SquareQuarticNewtonData P η)
    (A ε : ℕ) (_hε : ε ≤ 1) (hslope : 2 * d.r = d.s * (2 * A + ε)) :
    Nonempty (QuarticCoefficientExpansion A ε P η) := by
  obtain ⟨q₂, q₁, q₀, hf₂, hv₂, hf₁, hv₁, hf₀, hv₀⟩ :=
    exists_coefficients_of_quartic_square_initial d.s d.r d.s_pos d.r_pos P
      d.monic d.degree d.order d.initial d.homogeneous d.tail η d.chart
  have he₀ : d.s * (4 * A + 2 * ε) = 4 * d.r := by nlinarith [hslope]
  obtain ⟨a₂, ha₂⟩ := exists_coefficient_expansion_of_ramified_factor d.s (2 * A + ε)
    d.s_pos (P.coeff 2) q₂ (2 * η) (mul_ne_zero (by norm_num) d.parameter_ne_zero)
    (by simpa only [← hslope] using hf₂) hv₂
  obtain ⟨a₀, ha₀⟩ := exists_coefficient_expansion_of_ramified_factor d.s (4 * A + 2 * ε)
    d.s_pos (P.coeff 0) q₀ (η ^ 2) (pow_ne_zero 2 d.parameter_ne_zero)
    (by simpa only [he₀] using hf₀) hv₀
  have hstrict := ramified_order_gt_of_divided_value_zero d.s (3 * d.r) d.s_pos
    (P.coeff 1) q₁ hf₁ hv₁
  have he₁ : d.s * (3 * A + ε) ≤ 3 * d.r := by nlinarith [hslope]
  have hmem := mem_pow_succ_of_strict_ramified_order d.s (3 * A + ε) d.s_pos
    (P.coeff 1) (lt_of_le_of_lt (by exact_mod_cast he₁) hstrict)
  rw [maximalIdeal_one_pow_eq_span_coordinate_pow, Ideal.mem_span_singleton] at hmem
  obtain ⟨a₁, ha₁⟩ := hmem
  exact ⟨⟨a₂, a₁, a₀, ha₂, ha₁, ha₀⟩⟩

/-- The divided polynomial after `A-δ` charts, written at the exceptional
coordinate `ζ`. The coefficient germs depend only on the second variable. -/
@[expose] noncomputable def quarticCoefficientModel
    (δ ε : ℕ) (η ζ : ℂ) (a₂ a₁ a₀ : Germ 1) : Germ 2 :=
  (coordinate (0 : Fin 2) + constRingHom 2 ζ) ^ 4 +
  coordinate (1 : Fin 2) ^ (2 * δ + ε) *
    (constRingHom 2 (2 * η) + coordinate (1 : Fin 2) * hyperplaneExtension 1 a₂) *
      (coordinate (0 : Fin 2) + constRingHom 2 ζ) ^ 2 +
  coordinate (1 : Fin 2) ^ (3 * δ + ε + 1) * hyperplaneExtension 1 a₁ *
    (coordinate (0 : Fin 2) + constRingHom 2 ζ) +
  coordinate (1 : Fin 2) ^ (4 * δ + 2 * ε) *
    (constRingHom 2 (η ^ 2) + coordinate (1 : Fin 2) * hyperplaneExtension 1 a₀)

theorem quarticCoefficientModel_value_of_pos
    (δ ε : ℕ) (hδ : 0 < δ) (η ζ : ℂ) (a₂ a₁ a₀ : Germ 1) :
    valueRingHom 2 (quarticCoefficientModel δ ε η ζ a₂ a₁ a₀) = ζ ^ 4 := by
  have h₂ : 2 * δ + ε ≠ 0 := by omega
  have h₁ : 3 * δ + ε + 1 ≠ 0 := by omega
  have h₀ : 4 * δ + 2 * ε ≠ 0 := by omega
  simp only [quarticCoefficientModel, map_add, map_mul, map_pow,
    valueRingHom_coordinate, valueRingHom_const, zero_pow h₂, zero_pow h₁,
    zero_pow h₀, zero_add, zero_mul, add_zero]

theorem quarticCoefficientModel_first_axis
    (δ ε : ℕ) (hδ : 0 < δ) (η : ℂ) (a₂ a₁ a₀ : Germ 1) :
    pointBlowupExceptionalLine.pullbackRingHom (quarticCoefficientModel δ ε η 0 a₂ a₁ a₀) =
      coordinate (0 : Fin 1) ^ 4 := by
  have h₂ : 2 * δ + ε ≠ 0 := by omega
  have h₁ : 3 * δ + ε + 1 ≠ 0 := by omega
  have h₀ : 4 * δ + 2 * ε ≠ 0 := by omega
  simp only [quarticCoefficientModel, map_add, map_mul, map_pow, map_zero,
    pointBlowupExceptionalLine_pullback_zero, pointBlowupExceptionalLine_pullback_one,
    zero_pow h₂, zero_pow h₁, zero_pow h₀, zero_mul, add_zero]

theorem quarticCoefficientModel_integral (η ζ : ℂ) (a₂ a₁ a₀ : Germ 1) :
    quarticCoefficientModel 0 0 η ζ a₂ a₁ a₀ = integralQuarticTransform η ζ
      (hyperplaneExtension 1 a₂) (hyperplaneExtension 1 a₁) (hyperplaneExtension 1 a₀) := by
  simp only [quarticCoefficientModel, integralQuarticTransform, Nat.mul_zero,
    zero_add, pow_zero, pow_one, one_mul, map_mul, map_ofNat, map_pow]
  ring

theorem quarticCoefficientModel_half_integral (η : ℂ) (a₂ a₁ a₀ : Germ 1) :
    quarticCoefficientModel 0 1 η 0 a₂ a₁ a₀ = halfIntegralQuarticTransform η
      (hyperplaneExtension 1 a₂) (hyperplaneExtension 1 a₁) (hyperplaneExtension 1 a₀) := by
  simp only [quarticCoefficientModel, halfIntegralQuarticTransform, Nat.mul_zero,
    Nat.zero_add, Nat.reduceMul, Nat.reduceAdd, pow_one, map_zero, add_zero,
    map_mul, map_ofNat, map_pow]
  ring

theorem quarticCoefficientModel_terminal_value
    (ε : ℕ) (hε : ε ≤ 1) (η ζ : ℂ) (a₂ a₁ a₀ : Germ 1) :
    valueRingHom 2 (quarticCoefficientModel 0 ε η ζ a₂ a₁ a₀) =
      if ε = 0 then (ζ ^ 2 + η) ^ 2 else ζ ^ 4 := by
  interval_cases ε <;> simp [quarticCoefficientModel]
  ring

private theorem hyperplaneExtension_const (γ : ℂ) :
    hyperplaneExtension 1 (constRingHom 1 γ) = constRingHom 2 γ :=
  PointedMapGerm.pullback_constRingHom (hyperplaneTailGerm 1) γ

private theorem quartic_scaling_identity {R : Type*} [CommRing R]
    (j δ ε : ℕ) (x y η a₂ a₁ a₀ : R) :
    (y ^ j * x) ^ 4 + y ^ (2 * (j + δ) + ε) * (2 * η + y * a₂) * (y ^ j * x) ^ 2 +
      y ^ (3 * (j + δ) + ε + 1) * a₁ * (y ^ j * x) +
      y ^ (4 * (j + δ) + 2 * ε) * (η ^ 2 + y * a₀) =
    y ^ (4 * j) * (x ^ 4 + y ^ (2 * δ + ε) * (2 * η + y * a₂) * x ^ 2 +
      y ^ (3 * δ + ε + 1) * a₁ * x + y ^ (4 * δ + 2 * ε) * (η ^ 2 + y * a₀)) := by
  simp only [Nat.mul_add, pow_add, pow_mul]
  ring

theorem QuarticCoefficientExpansion.pullback_factor
    {A ε : ℕ} {P : Polynomial (Germ 1)} {η : ℂ}
    (e : QuarticCoefficientExpansion A ε P η)
    (hmonic : P.Monic) (hdegree : P.natDegree = 4) (hdepressed : P.coeff 3 = 0)
    (j : ℕ) (hj : j ≤ A) (ζ : ℂ) (B : PointedMapGerm 2 2)
    (hx : B.pullbackRingHom (coordinate (0 : Fin 2)) =
      coordinate (1 : Fin 2) ^ j * (coordinate (0 : Fin 2) + constRingHom 2 ζ))
    (hb : ∀ a : Germ 1, B.pullbackRingHom (hyperplaneExtension 1 a) = hyperplaneExtension 1 a) :
    B.pullbackRingHom (firstCoordinatePolynomialEvaluation P) =
      coordinate (1 : Fin 2) ^ (4 * j) *
        quarticCoefficientModel (A - j) ε η ζ e.a₂ e.a₁ e.a₀ := by
  rw [polynomialEvaluation_depressed_quartic P hmonic hdegree hdepressed]
  simp only [map_add, map_mul, map_pow, hx, hb]
  rw [e.coeff_two, e.coeff_one, e.coeff_zero]
  simp only [map_add, map_mul, map_pow, hyperplaneExtension_coordinate_plane,
    hyperplaneExtension_const, map_ofNat, quarticCoefficientModel]
  have hA : A = j + (A - j) := by omega
  simpa only [← hA] using quartic_scaling_identity j (A - j) ε (coordinate 0 + constRingHom 2 ζ)
    (coordinate 1) (constRingHom 2 η) (hyperplaneExtension 1 e.a₂)
    (hyperplaneExtension 1 e.a₁) (hyperplaneExtension 1 e.a₀)

end OnLeConjecture.DFour
