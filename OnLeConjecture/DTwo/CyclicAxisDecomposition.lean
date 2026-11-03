/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.AnalyticCoefficientSpecialization
public import OnLeConjecture.Analytic.SecondCoordinateAnalyticSubtraction

/-!
# Restriction to the smooth critical axis

For `P=x²+y^k`, the divisibility `y^(k-1) ∣ J(P,H)` forces an analytic
decomposition `H=A(P)+x B(P)+y^k C`. Both one-variable coefficients are
constructed from the convergent quadratic decomposition.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

/-- The scalar map defined by `x²+y^k`. -/
@[expose] noncomputable def cyclicScalarMap (k : ℕ) (hk : 1 ≤ k) :
    PointedMapGerm 2 1 :=
  PointedMapGerm.firstCoordinateProjection.comp (Germ.quadraticBaseMapGerm k hk)

@[simp] theorem cyclicScalarMap_component (k : ℕ) (hk : 1 ≤ k) (i : Fin 1) :
    (cyclicScalarMap k hk).1.component i = coordinate (0 : Fin 2) ^ 2 + coordinate 1 ^ k := by
  rw [cyclicScalarMap, PointedMapGerm.component_comp_eq_pullback,
    PointedMapGerm.firstCoordinateProjection_component, PointedMapGerm.pullback_coordinate]
  exact Germ.quadraticBaseMapGerm_component_zero k hk

theorem secondCoordinateConstantExtension_eq_firstCoordinateProjection_pullback
    (q : Germ 1) :
    Germ.secondCoordinateConstantExtension q =
      PointedMapGerm.firstCoordinateProjection.pullbackRingHom q := by
  have hmap : (Germ.hyperplaneTailGerm 1).comp
      planeCoordinateSwapEquiv.forward = PointedMapGerm.firstCoordinateProjection := by
    apply PointedMapGerm.ext_components
    intro i
    fin_cases i
    apply Subtype.ext
    rfl
  change (planeCoordinateSwapEquiv.forward.pullbackRingHom.comp
    (Germ.hyperplaneTailGerm 1).pullbackRingHom) q = _
  rw [← PointedMapGerm.pullbackRingHom_comp, hmap]

theorem quadraticBase_constantExtension_eq_cyclicScalar_pullback
    (k : ℕ) (hk : 1 ≤ k) (q : Germ 1) :
    Germ.quadraticBaseSubstitutionAlgHom k hk (Germ.secondCoordinateConstantExtension q) =
      (cyclicScalarMap k hk).pullbackRingHom q := by
  rw [secondCoordinateConstantExtension_eq_firstCoordinateProjection_pullback,
    Germ.quadraticBaseSubstitutionAlgHom_apply]
  rw [cyclicScalarMap, PointedMapGerm.pullbackRingHom_comp]
  rfl

/-- Below degree `k`, the odd coefficient recurrence has zero right side. -/
theorem secondCoordinate_pow_dvd_oddCoefficient_sub_constant
    (k : ℕ) (hk : 1 ≤ k) (A B : Germ 2)
    (hdiv : coordinate (1 : Fin 2) ^ (k - 1) ∣
      jacobian (coordinate (0 : Fin 2) ^ 2 + coordinate 1 ^ k)
        (Germ.quadraticBaseSubstitutionAlgHom k hk A + coordinate 0 *
          Germ.quadraticBaseSubstitutionAlgHom k hk B)) :
    coordinate (1 : Fin 2) ^ k ∣ B - Germ.secondCoordinateConstantExtension
      (Germ.secondCoordinateTaylorCoefficient 0 B) := by
  apply Germ.secondCoordinateFormalRingHom_X_pow_dvd_iff.mp
  rw [map_sub, Germ.secondCoordinateFormalRingHom_constantExtension, PowerSeries.X_pow_dvd_iff]
  have hrec := Germ.satisfiesCoefficientRecurrenceOver_of_jacobian_dvd hk A B hdiv
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    rw [map_sub, Germ.secondCoordinateFormalRingHom_coeff, PowerSeries.coeff_C]
    simp
  · have heq := hrec j (by omega) hj
    rw [if_neg (by omega)] at heq
    have hn : ((2 * j : ℕ) : Germ 1) ≠ 0 := by
      intro h
      have hv := congrArg (valueRingHom 1) h
      simp only [map_natCast, map_zero] at hv
      exact (by omega : 2 * j ≠ 0) (Nat.cast_eq_zero.mp hv)
    have hcoeff := (mul_eq_zero.mp heq).resolve_left
      (mul_ne_zero hn Germ.coordinate_zero_ne_zero)
    simp only [map_sub, Germ.secondCoordinateFormalRingHom_coeff,
      PowerSeries.coeff_C_of_ne_zero hj0, hcoeff, sub_zero]

/-- Analytic axis coefficients and an analytic multiple of `y^k` are
deduced from the common Jacobian factor. -/
theorem exists_cyclic_axis_decomposition
    (k : ℕ) (hk : 1 ≤ k) (H : Germ 2)
    (hdiv : coordinate (1 : Fin 2) ^ (k - 1) ∣
      jacobian (coordinate (0 : Fin 2) ^ 2 + coordinate 1 ^ k) H) :
    ∃ A B : Germ 1, ∃ C : Germ 2,
      H = (cyclicScalarMap k hk).pullbackRingHom A +
        coordinate 0 * (cyclicScalarMap k hk).pullbackRingHom B + coordinate 1 ^ k * C := by
  obtain ⟨⟨A, B⟩, hH, _⟩ := Germ.existsUnique_quadraticBase_decomposition k hk H
  have hdiv' := hdiv
  rw [hH] at hdiv'
  have hAdvd := Germ.secondCoordinate_sub_constantExtension_dvd_of_partialDerivative_dvd hk
    (Germ.coefficient_divisibilities_of_jacobian k k hk A B hdiv').1
  have hBdvd := secondCoordinate_pow_dvd_oddCoefficient_sub_constant k hk A B hdiv'
  obtain ⟨C, hC⟩ := hAdvd
  obtain ⟨D, hD⟩ := hBdvd
  refine ⟨Germ.secondCoordinateTaylorCoefficient 0 A,
    Germ.secondCoordinateTaylorCoefficient 0 B,
    Germ.quadraticBaseSubstitutionAlgHom k hk C + coordinate 0 *
      Germ.quadraticBaseSubstitutionAlgHom k hk D, ?_⟩
  have hAeq : A = Germ.secondCoordinateConstantExtension
      (Germ.secondCoordinateTaylorCoefficient 0 A) + coordinate 1 ^ k * C := by
    linear_combination hC
  have hBeq : B = Germ.secondCoordinateConstantExtension
      (Germ.secondCoordinateTaylorCoefficient 0 B) + coordinate 1 ^ k * D := by
    linear_combination hD
  conv_lhs => rw [hH, hAeq, hBeq]
  rw [map_add, map_add, map_mul, map_mul,
    map_pow, Germ.quadraticBaseSubstitutionAlgHom_coordinate_one,
    quadraticBase_constantExtension_eq_cyclicScalar_pullback,
    quadraticBase_constantExtension_eq_cyclicScalar_pullback]
  ring

/-- The even axis coefficient has the value of the original component. -/
theorem value_even_coefficient_of_cyclic_axis_decomposition
    (k : ℕ) (hk : 1 ≤ k) (H : Germ 2) (A B : Germ 1) (C : Germ 2)
    (hH : H = (cyclicScalarMap k hk).pullbackRingHom A +
      coordinate 0 * (cyclicScalarMap k hk).pullbackRingHom B + coordinate 1 ^ k * C) :
    valueRingHom 1 A = valueRingHom 2 H := by
  rw [hH, map_add, map_add, map_mul, map_mul, map_pow,
    PointedMapGerm.valueRingHom_pullback, valueRingHom_coordinate,
    valueRingHom_coordinate, zero_pow (by omega : k ≠ 0)]
  ring

/-- The odd axis coefficient has the first partial derivative value of
the original component. -/
theorem value_odd_coefficient_of_cyclic_axis_decomposition
    (k : ℕ) (hk : 1 ≤ k) (H : Germ 2) (A B : Germ 1) (C : Germ 2)
    (hH : H = (cyclicScalarMap k hk).pullbackRingHom A +
      coordinate 0 * (cyclicScalarMap k hk).pullbackRingHom B + coordinate 1 ^ k * C) :
    valueRingHom 1 B = valueRingHom 2 (partialDerivative 0 H) := by
  rw [hH, partialDerivative_add, partialDerivative_add,
    partialDerivative_mul, partialDerivative_mul,
    partialDerivative_oneVariable_pullback, partialDerivative_oneVariable_pullback,
    cyclicScalarMap_component]
  simp only [partialDerivative_add, partialDerivative_pow, smul_eq_mul,
    partialDerivative_coordinate_same,
    partialDerivative_coordinate_ne (by decide : (0 : Fin 2) ≠ 1),
    mul_zero, nsmul_zero, add_zero, map_add, map_mul, map_pow, map_nsmul,
    valueRingHom_coordinate, one_mul, mul_one,
    PointedMapGerm.valueRingHom_pullback, Nat.reduceSub, pow_one,
    zero_mul, mul_zero, nsmul_zero, zero_add,
    zero_pow (by omega : k ≠ 0), add_zero]

end OnLeConjecture.DTwo
