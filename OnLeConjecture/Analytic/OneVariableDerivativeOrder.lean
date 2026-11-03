/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OneVariableOrder
public import OnLeConjecture.Analytic.JacobianPullback

/-!
# Vanishing order of a one-variable derivative

For a nonzero analytic germ vanishing at the origin, differentiation
decreases its vanishing order by exactly one. The coefficient left after
removing that coordinate power is proved to be an analytic unit.
-/

public section

namespace OnLeConjecture.Analytic.Germ

theorem exists_derivative_order_factorization (f : Germ 1)
    (hf : f ∈ maximalIdeal 1) (hne : f ≠ 0) :
    ∃ k : ℕ, 0 < k ∧ vanishingOrder f = k ∧
      ∃ u : Germ 1, IsUnit u ∧
        partialDerivative (0 : Fin 1) f = coordinate (0 : Fin 1) ^ (k - 1) * u := by
  obtain ⟨k, v, hv, hfactor⟩ := exists_eq_coordinate_pow_mul_unit hne
  have hk : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero, one_mul] at hfactor
    have hf0 := mem_maximalIdeal_iff.mp hf
    rw [hfactor] at hf0
    exact (isUnit_iff_valueRingHom_ne_zero.mp hv) hf0
  let u : Germ 1 := k • v + coordinate (0 : Fin 1) * partialDerivative (0 : Fin 1) v
  have hu : IsUnit u := by
    apply isUnit_iff_valueRingHom_ne_zero.mpr
    change valueRingHom 1 (k • v + coordinate (0 : Fin 1) *
      partialDerivative (0 : Fin 1) v) ≠ 0
    rw [map_add, map_nsmul, map_mul, valueRingHom_coordinate, zero_mul, add_zero, nsmul_eq_mul]
    exact mul_ne_zero (by exact_mod_cast Nat.ne_zero_of_lt hk)
      (isUnit_iff_valueRingHom_ne_zero.mp hv)
  refine ⟨k, hk, vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hv hfactor, u, hu, ?_⟩
  rw [hfactor, partialDerivative_mul, partialDerivative_pow, partialDerivative_coordinate_same]
  have hpower : coordinate (0 : Fin 1) ^ k =
      coordinate (0 : Fin 1) ^ (k - 1) * coordinate (0 : Fin 1) := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  rw [hpower]
  simp only [u, nsmul_eq_mul, smul_eq_mul, mul_one]
  ring

/-- The derivative is nonzero and its finite order is exactly one less
than the order of a nonzero germ vanishing at the origin. -/
theorem derivative_ne_zero_and_order_add_one (f : Germ 1)
    (hf : f ∈ maximalIdeal 1) (hne : f ≠ 0) :
    partialDerivative (0 : Fin 1) f ≠ 0 ∧
      (vanishingOrder (partialDerivative (0 : Fin 1) f)).toNat + 1 =
        (vanishingOrder f).toNat := by
  obtain ⟨k, hk, horder, u, hu, hfactor⟩ := exists_derivative_order_factorization f hf hne
  have hderivOrder := vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hu hfactor
  refine ⟨?_, ?_⟩
  · rw [hfactor]
    exact mul_ne_zero (pow_ne_zero _ coordinate_zero_ne_zero) hu.ne_zero
  · rw [hderivOrder, horder, ENat.toNat_natCast, ENat.toNat_natCast, Nat.sub_add_cancel hk]

end OnLeConjecture.Analytic.Germ
