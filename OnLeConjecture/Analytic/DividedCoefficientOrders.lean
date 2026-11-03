/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedPolynomialScaling
import Mathlib.Tactic

/-!
# Orders after division by a coordinate power

The statements use exact analytic factor identities. Finite ramification
orders and strict ramification inequalities are transported to the
original divided coefficients.
-/

public section

namespace OnLeConjecture.Analytic.Germ

theorem coordinate_pow_mul_mem_pow_add_iff (d k : ℕ) (q : Germ 1) :
    coordinate (0 : Fin 1) ^ d * q ∈ maximalIdeal 1 ^ (d + k) ↔
      q ∈ maximalIdeal 1 ^ k := by
  rw [maximalIdeal_one_pow_eq_span_coordinate_pow,
    maximalIdeal_one_pow_eq_span_coordinate_pow, Ideal.mem_span_singleton,
    Ideal.mem_span_singleton, pow_add,
    mul_dvd_mul_iff_left (pow_ne_zero d coordinate_zero_ne_zero)]

theorem exists_unit_factor_of_order_eq_nat
    (q : Germ 1) (k : ℕ) (horder : vanishingOrder q = (k : ℕ∞)) :
    ∃ u : Germ 1, IsUnit u ∧ q = coordinate (0 : Fin 1) ^ k * u := by
  have hq : q ≠ 0 := by
    intro hz
    rw [hz, vanishingOrder_zero] at horder
    exact ENat.natCast_ne_top k horder.symm
  obtain ⟨d, u, hu, hfactor⟩ := exists_eq_coordinate_pow_mul_unit hq
  have hd : d = k := by
    have h := vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hu hfactor
    rw [horder] at h
    exact (ENat.natCast_inj.mp h).symm
  exact ⟨u, hu, by simpa only [hd] using hfactor⟩

theorem not_mem_pow_succ_of_order_eq_nat
    (q : Germ 1) (k : ℕ) (horder : vanishingOrder q = (k : ℕ∞)) :
    q ∉ maximalIdeal 1 ^ (k + 1) := by
  intro hmem
  have hbound := mem_maximalIdeal_one_pow_iff.mp hmem
  rw [horder] at hbound
  have hbad : k + 1 ≤ k := by exact_mod_cast hbound
  omega

theorem order_eq_of_ramified_order_eq
    (s k : ℕ) (hs : 0 < s) (q : Germ 1)
    (horder : s • vanishingOrder q = ((s * k : ℕ) : ℕ∞)) :
    vanishingOrder q = (k : ℕ∞) := by
  have hsne : (s : ℕ∞) ≠ 0 := by exact_mod_cast hs.ne'
  rw [nsmul_eq_mul, Nat.cast_mul] at horder
  apply le_antisymm
  · exact (ENat.mul_le_mul_left_iff hsne (ENat.natCast_ne_top s)).mp horder.le
  · exact (ENat.mul_le_mul_left_iff hsne (ENat.natCast_ne_top s)).mp horder.ge

theorem divided_order_eq_of_ramified_order_eq
    (s d k : ℕ) (hs : 0 < s) (b q : Germ 1)
    (hfactor : b = coordinate (0 : Fin 1) ^ d * q)
    (horder : s • vanishingOrder b = ((s * (d + k) : ℕ) : ℕ∞)) :
    vanishingOrder q = (k : ℕ∞) := by
  have h := order_eq_of_ramified_order_eq s (d + k) hs b horder
  rw [hfactor, vanishingOrder_mul, vanishingOrder_coordinate_pow, Nat.cast_add] at h
  exact (ENat.add_right_injective_of_ne_top (ENat.natCast_ne_top d)) h

theorem mem_pow_succ_of_ramified_order_gt
    (s k : ℕ) (_hs : 0 < s) (b : Germ 1)
    (horder : ((s * k : ℕ) : ℕ∞) < s • vanishingOrder b) :
    b ∈ maximalIdeal 1 ^ (k + 1) := by
  by_cases hb : b = 0
  · simp [hb]
  have hfinite := ENat.natCast_toNat (vanishingOrder_eq_top_iff.not.mpr hb)
  rw [← hfinite, nsmul_eq_mul] at horder
  have hnat : s * k < s * (vanishingOrder b).toNat := by exact_mod_cast horder
  have hbound : k + 1 ≤ (vanishingOrder b).toNat := by nlinarith
  rw [mem_maximalIdeal_one_pow_iff, ← hfinite]
  exact_mod_cast hbound

theorem divided_mem_pow_succ_of_ramified_order_gt
    (s d k : ℕ) (hs : 0 < s) (b q : Germ 1)
    (hfactor : b = coordinate (0 : Fin 1) ^ d * q)
    (horder : ((s * (d + k) : ℕ) : ℕ∞) < s • vanishingOrder b) :
    q ∈ maximalIdeal 1 ^ (k + 1) := by
  have h := mem_pow_succ_of_ramified_order_gt s (d + k) hs b horder
  rw [hfactor, Nat.add_assoc] at h
  exact (coordinate_pow_mul_mem_pow_add_iff d (k + 1) q).mp h

end OnLeConjecture.Analytic.Germ
