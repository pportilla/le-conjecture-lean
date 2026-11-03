/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OneVariableOrder

/-!
# Comparing two analytic radial orders

An equality between a coordinate-power multiple of an analytic germ and
a coordinate-power multiple of a unit determines the allowable order and
the special-fiber coefficient.
-/

public section

namespace OnLeConjecture.Analytic.Germ

theorem coordinate_pow_comparison_with_unit
    (d e : ℕ) (f u : Germ 1) (hu : IsUnit u)
    (heq : coordinate (0 : Fin 1) ^ d * f = coordinate (0 : Fin 1) ^ e * u) :
    d ≤ e ∧ f = coordinate (0 : Fin 1) ^ (e - d) * u := by
  have hdvd : coordinate (0 : Fin 1) ^ d ∣ coordinate (0 : Fin 1) ^ e * u :=
    ⟨f, heq.symm⟩
  have horder := vanishingOrder_le_iff_dvd.mpr hdvd
  rw [vanishingOrder_coordinate_pow, vanishingOrder_mul,
    vanishingOrder_coordinate_pow, vanishingOrder_eq_zero_iff_isUnit.mpr hu,
    add_zero] at horder
  have hde : d ≤ e := by exact_mod_cast horder
  refine ⟨hde, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero d coordinate_zero_irreducible.ne_zero)
  rw [heq, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hde]

theorem value_eq_zero_of_strict_coordinate_pow_comparison
    (d e : ℕ) (hde : d < e) (f u : Germ 1) (hu : IsUnit u)
    (heq : coordinate (0 : Fin 1) ^ d * f = coordinate (0 : Fin 1) ^ e * u) :
    valueRingHom 1 f = 0 := by
  have hfactor := (coordinate_pow_comparison_with_unit d e f u hu heq).2
  rw [hfactor, map_mul, map_pow, valueRingHom_coordinate,
    zero_pow (by omega : e - d ≠ 0), zero_mul]

theorem value_eq_of_equal_coordinate_pow_comparison
    (d : ℕ) (f u : Germ 1)
    (heq : coordinate (0 : Fin 1) ^ d * f = coordinate (0 : Fin 1) ^ d * u) :
    valueRingHom 1 f = valueRingHom 1 u := by
  exact congrArg (valueRingHom 1)
    (mul_left_cancel₀ (pow_ne_zero d coordinate_zero_irreducible.ne_zero) heq)

end OnLeConjecture.Analytic.Germ
