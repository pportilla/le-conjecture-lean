/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.RationalQuarticInitialCoefficients
public import OnLeConjecture.Analytic.DividedCoefficientOrders
import Mathlib.Tactic

/-!
# The coefficient alternatives after the top-order free chain

Exact coordinate division at the original chain length expresses the
nonintegral excess through an integer coefficient order. The remaining
coefficient bounds distinguish a smooth germ, a two-three cusp, a node,
or a germ still of order at least three.
-/

public section

namespace OnLeConjecture.Analytic.Germ

theorem ne_zero_of_finite_ramified_order
    (s D : ℕ) (hs : 0 < s) (b : Germ 1)
    (horder : s • vanishingOrder b = (D : ℕ∞)) : b ≠ 0 := by
  intro hb
  have hsne : (s : ℕ∞) ≠ 0 := by exact_mod_cast hs.ne'
  rw [hb, vanishingOrder_zero, nsmul_eq_mul, ENat.mul_top hsne] at horder
  exact ENat.natCast_ne_top D horder.symm

/-- In the E alternative, the constant coefficient of the divided
cubic has order `n`, with `3r=s(3A+n)`. -/
theorem cubic_E_divided_coefficient_orders
    (s r A : ℕ) (hs : 0 < s) (hA : s * A ≤ r)
    (b₁ b₀ q₁ q₀ : Germ 1)
    (hfactor₁ : b₁ = coordinate (0 : Fin 1) ^ (2 * A) * q₁)
    (hfactor₀ : b₀ = coordinate (0 : Fin 1) ^ (3 * A) * q₀)
    (hexact : s • vanishingOrder b₀ = ((3 * r : ℕ) : ℕ∞))
    (hstrict : ((2 * r : ℕ) : ℕ∞) < s • vanishingOrder b₁) :
    ∃ n : ℕ, ∃ B : Germ 1, IsUnit B ∧ q₀ = coordinate (0 : Fin 1) ^ n * B ∧
      3 * r = s * (3 * A + n) ∧
      q₁ ∈ maximalIdeal 1 ∧ (2 ≤ n → q₁ ∈ maximalIdeal 1 ^ 2) := by
  have hq₀ : q₀ ≠ 0 := by
    intro hzero
    apply ne_zero_of_finite_ramified_order s (3 * r) hs b₀ hexact
    rw [hfactor₀, hzero, mul_zero]
  obtain ⟨n, B, hB, hq₀⟩ := exists_eq_coordinate_pow_mul_unit hq₀
  have hqOrder := vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hB hq₀
  have heq : 3 * r = s * (3 * A + n) := by
    rw [hfactor₀, vanishingOrder_mul, vanishingOrder_coordinate_pow,
      hqOrder, nsmul_eq_mul, ← Nat.cast_add, ← Nat.cast_mul] at hexact
    exact (ENat.natCast_inj.mp hexact).symm
  refine ⟨n, B, hB, hq₀, heq, ?_, ?_⟩
  · have hle : s * (2 * A + 0) ≤ 2 * r := by nlinarith
    have h := divided_mem_pow_succ_of_ramified_order_gt s (2 * A) 0 hs b₁ q₁ hfactor₁
      (lt_of_le_of_lt (by exact_mod_cast hle) hstrict)
    simpa only [Nat.zero_add, pow_one] using h
  · intro hn
    have hle : s * (2 * A + 1) ≤ 2 * r := by nlinarith
    exact divided_mem_pow_succ_of_ramified_order_gt s (2 * A) 1 hs b₁ q₁ hfactor₁
      (lt_of_le_of_lt (by exact_mod_cast hle) hstrict)

/-- In the H alternative, the linear coefficient of the divided
cubic has order `n`, with `2r=s(2A+n)`. -/
theorem cubic_H_divided_coefficient_orders
    (s r A : ℕ) (hs : 0 < s)
    (b₁ b₀ q₁ q₀ : Germ 1)
    (hfactor₁ : b₁ = coordinate (0 : Fin 1) ^ (2 * A) * q₁)
    (hfactor₀ : b₀ = coordinate (0 : Fin 1) ^ (3 * A) * q₀)
    (hexact : s • vanishingOrder b₁ = ((2 * r : ℕ) : ℕ∞))
    (hstrict : ((3 * r : ℕ) : ℕ∞) < s • vanishingOrder b₀) :
    ∃ n : ℕ, ∃ B : Germ 1, IsUnit B ∧ q₁ = coordinate (0 : Fin 1) ^ n * B ∧
      2 * r = s * (2 * A + n) ∧
      (1 ≤ n → q₀ ∈ maximalIdeal 1 ^ 2) ∧ (2 ≤ n → q₀ ∈ maximalIdeal 1 ^ 3) := by
  have hq₁ : q₁ ≠ 0 := by
    intro hzero
    apply ne_zero_of_finite_ramified_order s (2 * r) hs b₁ hexact
    rw [hfactor₁, hzero, mul_zero]
  obtain ⟨n, B, hB, hq₁⟩ := exists_eq_coordinate_pow_mul_unit hq₁
  have hqOrder := vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hB hq₁
  have heq : 2 * r = s * (2 * A + n) := by
    rw [hfactor₁, vanishingOrder_mul, vanishingOrder_coordinate_pow,
      hqOrder, nsmul_eq_mul, ← Nat.cast_add, ← Nat.cast_mul] at hexact
    exact (ENat.natCast_inj.mp hexact).symm
  refine ⟨n, B, hB, hq₁, heq, ?_, ?_⟩
  · intro hn
    have hle : s * (3 * A + 1) ≤ 3 * r := by nlinarith
    exact divided_mem_pow_succ_of_ramified_order_gt s (3 * A) 1 hs b₀ q₀ hfactor₀
      (lt_of_le_of_lt (by exact_mod_cast hle) hstrict)
  · intro hn
    have hle : s * (3 * A + 2) ≤ 3 * r := by nlinarith
    exact divided_mem_pow_succ_of_ramified_order_gt s (3 * A) 2 hs b₀ q₀ hfactor₀
      (lt_of_le_of_lt (by exact_mod_cast hle) hstrict)

end OnLeConjecture.Analytic.Germ
