/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicAxisDecomposition

/-!
# The analytic theta decomposition at the extreme transverse order

The coefficient recurrence with cutoff `2k` leaves only coefficients zero
and `k` below that cutoff, and relates them by `b₀=2vbₖ`. Analytic
coordinate-power division then constructs the convergent remainder.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

local instance : CharZero (Germ 1) := (valueRingHom 1).charZero

/-- The quadratic-cubic expression in the extreme order-two case. -/
@[expose] noncomputable def extremeTheta (k : ℕ) : Germ 2 :=
  coordinate (0 : Fin 2) *
    (2 * (coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ k) + coordinate 1 ^ k)

theorem extremeTheta_eq (k : ℕ) : extremeTheta k =
    2 * coordinate (0 : Fin 2) ^ 3 + 3 * coordinate 0 * coordinate (1 : Fin 2) ^ k := by
  dsimp only [extremeTheta]
  ring

private theorem extreme_odd_coefficient_relation
    (k : ℕ) (hk : 1 ≤ k) (A B : Germ 2)
    (hdiv : coordinate (1 : Fin 2) ^ (2 * k - 1) ∣
      jacobian (coordinate (0 : Fin 2) ^ 2 + coordinate 1 ^ k)
        (Germ.quadraticBaseSubstitutionAlgHom k hk A + coordinate 0 *
          Germ.quadraticBaseSubstitutionAlgHom k hk B)) :
    Germ.secondCoordinateTaylorCoefficient 0 B =
      2 * coordinate (0 : Fin 1) * Germ.secondCoordinateTaylorCoefficient k B := by
  have hrec := Germ.satisfiesCoefficientRecurrenceOver_of_jacobian_dvd hk A B hdiv
  have h := hrec k hk (by omega)
  rw [if_pos (le_refl k), Nat.sub_self, show 2 * k - k = k by omega] at h
  have hkne : (k : Germ 1) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  apply (mul_left_cancel₀ hkne)
  push_cast at h
  linear_combination -h

private theorem extreme_odd_coefficient_remainder_dvd
    (k : ℕ) (hk : 1 ≤ k) (A B : Germ 2)
    (hdiv : coordinate (1 : Fin 2) ^ (2 * k - 1) ∣
      jacobian (coordinate (0 : Fin 2) ^ 2 + coordinate 1 ^ k)
        (Germ.quadraticBaseSubstitutionAlgHom k hk A + coordinate 0 *
          Germ.quadraticBaseSubstitutionAlgHom k hk B)) :
    coordinate (1 : Fin 2) ^ (2 * k) ∣ B -
      (Germ.secondCoordinateConstantExtension (Germ.secondCoordinateTaylorCoefficient 0 B) +
        coordinate 1 ^ k * Germ.secondCoordinateConstantExtension
          (Germ.secondCoordinateTaylorCoefficient k B)) := by
  apply Germ.secondCoordinateFormalRingHom_X_pow_dvd_iff.mp
  rw [map_sub, map_add, map_mul, map_pow,
    Germ.secondCoordinateFormalRingHom_coordinate_one,
    Germ.secondCoordinateFormalRingHom_constantExtension,
    Germ.secondCoordinateFormalRingHom_constantExtension, PowerSeries.X_pow_dvd_iff]
  have hrec := Germ.satisfiesCoefficientRecurrenceOver_of_jacobian_dvd hk A B hdiv
  intro j hj
  rw [map_sub, map_add, Germ.secondCoordinateFormalRingHom_coeff,
    PowerSeries.coeff_C, PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow]
  by_cases hj0 : j = 0
  · subst j
    simp [show (0 : ℕ) ≠ k by omega]
  by_cases hjk : j = k
  · subst j
    simp [show k ≠ 0 by omega]
  have hjndvd : ¬ k ∣ j := by
    intro hkdvd
    obtain ⟨r, hr⟩ := hkdvd
    have hr2 : r < 2 := by nlinarith
    have hr0 : r ≠ 0 := by intro hz; rw [hz, mul_zero] at hr; exact hj0 hr
    have hr1 : r = 1 := by omega
    apply hjk
    simpa only [hr1, mul_one] using hr
  have hzero := coefficient_eq_zero_of_not_dvd_over hk coordinate_zero_ne_zero hrec hj hjndvd
  simp only [hzero, if_neg hj0, if_neg hjk, zero_mul, add_zero, sub_self]

/-- The extreme minor divisibility constructs both one-variable
coefficients and a convergent `y^(2k)` remainder. -/
theorem exists_extreme_theta_decomposition
    (k : ℕ) (hk : 1 ≤ k) (H : Germ 2)
    (hdiv : coordinate (1 : Fin 2) ^ (2 * k - 1) ∣
      jacobian (coordinate (0 : Fin 2) ^ 2 + coordinate 1 ^ k) H) :
    ∃ A B : Germ 1, ∃ C : Germ 2,
      H = (cyclicScalarMap k hk).pullbackRingHom A +
        extremeTheta k * (cyclicScalarMap k hk).pullbackRingHom B + coordinate 1 ^ (2 * k) * C := by
  obtain ⟨⟨A, B⟩, hH, _⟩ := Germ.existsUnique_quadraticBase_decomposition k hk H
  have hdiv' := hdiv
  rw [hH] at hdiv'
  have hAdvd := Germ.secondCoordinate_sub_constantExtension_dvd_of_partialDerivative_dvd
    (by omega : 1 ≤ 2 * k)
    (Germ.coefficient_divisibilities_of_jacobian k (2 * k) hk A B hdiv').1
  obtain ⟨C, hC⟩ := hAdvd
  obtain ⟨D, hD⟩ := extreme_odd_coefficient_remainder_dvd k hk A B hdiv'
  have hbeta := extreme_odd_coefficient_relation k hk A B hdiv'
  have hAeq : A = Germ.secondCoordinateConstantExtension
      (Germ.secondCoordinateTaylorCoefficient 0 A) + coordinate 1 ^ (2 * k) * C := by
    linear_combination hC
  have hBeq : B = Germ.secondCoordinateConstantExtension
      (Germ.secondCoordinateTaylorCoefficient 0 B) + coordinate 1 ^ k *
        Germ.secondCoordinateConstantExtension (Germ.secondCoordinateTaylorCoefficient k B) +
          coordinate 1 ^ (2 * k) * D := by
    linear_combination hD
  refine ⟨Germ.secondCoordinateTaylorCoefficient 0 A,
    Germ.secondCoordinateTaylorCoefficient k B,
    Germ.quadraticBaseSubstitutionAlgHom k hk C +
      coordinate 0 * Germ.quadraticBaseSubstitutionAlgHom k hk D, ?_⟩
  conv_lhs => rw [hH, hAeq, hBeq]
  simp only [map_add, map_mul, map_pow,
    Germ.quadraticBaseSubstitutionAlgHom_coordinate_one,
    quadraticBase_constantExtension_eq_cyclicScalar_pullback]
  rw [hbeta, map_mul, map_mul, map_ofNat, PointedMapGerm.pullback_coordinate,
    cyclicScalarMap_component]
  dsimp only [extremeTheta]
  ring

end OnLeConjecture.DTwo
