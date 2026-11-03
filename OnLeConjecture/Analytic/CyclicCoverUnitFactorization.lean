/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CyclicCoverAnalyticDivision
public import OnLeConjecture.Analytic.CoordinateAxesFactorization
public import OnLeConjecture.Analytic.PolynomialJets
import Mathlib.Tactic

/-!
# Unit factorization on the cyclic-cover hypersurface

The actual cyclic-cover pullback detects equality modulo `U * Xi - lambda^r`.
A coordinate-power factorization of that pullback descends to an analytic
unit factorization on the hypersurface, without a separate descent
assumption for the inverse unit.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.Analytic.CyclicCover

/-- The cyclic cover is fixed by every element of its cyclic action. -/
theorem cover_comp_action (r : ℕ) (hr : 0 < r) (ζ : ℂ) (hζ : ζ ^ r = 1) :
    (coverGerm r hr).comp (actionGerm ζ) = coverGerm r hr := by
  have hζ0 : ζ ≠ 0 := by
    intro hz
    simp [hz, zero_pow hr.ne'] at hζ
  simp only [coverGerm, actionGerm, PointedMapGerm.comp_ofFunction]
  apply Subtype.ext
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  apply Filter.Eventually.of_forall
  intro z
  funext i
  fin_cases i
  · simp [coverFunction, actionFunction, actionScalar, mul_pow, hζ]
  · simp [coverFunction, actionFunction, actionScalar, mul_pow, inv_pow, hζ]
  · simp [coverFunction, actionFunction, actionScalar]
    field_simp

/-- Every analytic function pulled back from the hypersurface is
invariant under the cyclic action. -/
theorem actionAlgHom_cover_pullback (r : ℕ) (hr : 0 < r) (ζ : ℂ)
    (hζ : ζ ^ r = 1) (D : Germ 3) :
    actionAlgHom ζ ((coverGerm r hr).pullbackRingHom D) =
      (coverGerm r hr).pullbackRingHom D := by
  change ((actionGerm ζ).pullbackRingHom.comp
    (coverGerm r hr).pullbackRingHom) D = _
  rw [← PointedMapGerm.pullbackRingHom_comp, cover_comp_action r hr ζ hζ]

/-- An analytic unit remaining after removal of a power of the first
cover coordinate descends to a unit modulo the hypersurface equation. -/
theorem exists_unit_factor_mod_relation_of_cover_factorization
    (r N : ℕ) (hr : 0 < r) (D : Germ 3) (u : Germ 2) (hu : IsUnit u)
    (hfactor : (coverGerm r hr).pullbackRingHom D =
      Germ.coordinate (0 : Fin 2) ^ (r * N) * u) :
    ∃ ε : Germ 3, IsUnit ε ∧
      D - Germ.coordinate (0 : Fin 3) ^ N * ε ∈ Ideal.span {relationGerm r} := by
  let ζ := Complex.exp (2 * ↑Real.pi * Complex.I / r)
  have hζ : IsPrimitiveRoot ζ r := Complex.isPrimitiveRoot_exp r hr.ne'
  have hmonomial : actionAlgHom ζ (Germ.coordinate (0 : Fin 2) ^ (r * N)) =
      Germ.coordinate (0 : Fin 2) ^ (r * N) := by
    rw [map_pow, actionAlgHom_coordinate, mul_pow]
    simp only [actionScalar, Matrix.cons_val_zero, ← map_pow, pow_mul, hζ.pow_eq_one,
      one_pow, map_one, one_mul]
  have hinvariant : (actionGerm ζ).pullbackRingHom u = u := by
    have h := actionAlgHom_cover_pullback r hr ζ hζ.pow_eq_one D
    rw [hfactor, map_mul, hmonomial] at h
    exact mul_left_cancel₀ (pow_ne_zero _ (Germ.coordinate_ne_zero _)) h
  obtain ⟨ε, hε⟩ := exists_analytic_descent r hr ζ hζ u hinvariant
  have hunit : IsUnit ε := by
    apply Germ.isUnit_of_valueRingHom_ne_zero
    have hvalue := Germ.valueRingHom_ne_zero_of_isUnit hu
    rwa [hε, PointedMapGerm.valueRingHom_pullback] at hvalue
  refine ⟨ε, hunit, (cover_pullback_eq_iff_sub_mem_span r hr D _).mp ?_⟩
  rw [map_mul, map_pow, coverGerm_pullback_first, ← pow_mul, ← hε]
  exact hfactor

end OnLeConjecture.Analytic.CyclicCover

namespace OnLeConjecture.Analytic.Germ

/-- A nonzero restriction to the first coordinate axis excludes the
second coordinate factor and determines the exponent of the first. -/
theorem exists_first_coordinate_power_mul_unit_of_axes_support
    (F : Source 2 → ℂ) (hF : AnalyticAt ℂ F 0) (n : ℕ) (c : ℂ) (hc : c ≠ 0)
    (hsupport : ∀ᶠ z in 𝓝 (0 : Source 2), F z = 0 → z 0 = 0 ∨ z 1 = 0)
    (haxis : lineRestriction (![1, 0] : Source 2) (ofFunction F hF) =
      constRingHom 1 c * coordinate (0 : Fin 1) ^ n) :
    ∃ u : Germ 2, IsUnit u ∧ ofFunction F hF = coordinate (0 : Fin 2) ^ n * u := by
  have hcUnit : IsUnit (constRingHom 1 c) :=
    (isUnit_iff_ne_zero.mpr hc).map (constRingHom 1)
  have haxisNe : lineRestriction (![1, 0] : Source 2) (ofFunction F hF) ≠ 0 := by
    rw [haxis]
    exact mul_ne_zero hcUnit.ne_zero (pow_ne_zero n (coordinate_ne_zero _))
  have hne : ofFunction F hF ≠ 0 := by
    intro hz
    apply haxisNe
    rw [hz, map_zero]
  obtain ⟨a, b, u, hfactor⟩ :=
    exists_coordinate_factorization_of_zeros_supported_on_axes F hF hne hsupport
  have haxisFactor := congrArg (lineRestriction (![1, 0] : Source 2)) hfactor
  simp only [map_mul, map_pow, lineRestriction_coordinate_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    map_one, map_zero, one_mul, zero_mul] at haxisFactor
  have hb : b = 0 := by
    by_contra hb
    apply haxisNe
    simpa only [zero_pow hb, mul_zero, zero_mul] using haxisFactor
  simp only [hb, pow_zero, mul_one] at haxisFactor hfactor
  have ha := vanishingOrder_eq_of_eq_coordinate_pow_mul_unit
    (u.isUnit.map (lineRestriction (![1, 0] : Source 2))) haxisFactor
  have hn := vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hcUnit
    (haxis.trans (mul_comm _ _))
  have han : a = n := by exact_mod_cast ha.symm.trans hn
  exact ⟨u, u.isUnit, by simpa only [han] using hfactor⟩

end OnLeConjecture.Analytic.Germ

namespace OnLeConjecture.Analytic.CyclicCover

/-- The zero-set and special-axis hypotheses give the unit factorization
on the hypersurface. Neither coordinate factorization nor invariant-unit
descent is an additional hypothesis. -/
theorem exists_unit_factor_mod_relation_of_axes_support
    (r N : ℕ) (hr : 0 < r) (D : Germ 3)
    (F : Source 2 → ℂ) (hF : AnalyticAt ℂ F 0)
    (hrepresentative : Germ.ofFunction F hF = (coverGerm r hr).pullbackRingHom D)
    (c : ℂ) (hc : c ≠ 0)
    (hsupport : ∀ᶠ z in 𝓝 (0 : Source 2), F z = 0 → z 0 = 0 ∨ z 1 = 0)
    (haxis : Germ.lineRestriction (![1, 0] : Source 2) (Germ.ofFunction F hF) =
      Germ.constRingHom 1 c * Germ.coordinate (0 : Fin 1) ^ (r * N)) :
    ∃ ε : Germ 3, IsUnit ε ∧
      D - Germ.coordinate (0 : Fin 3) ^ N * ε ∈ Ideal.span {relationGerm r} := by
  obtain ⟨u, hu, hfactor⟩ := Germ.exists_first_coordinate_power_mul_unit_of_axes_support
    F hF (r * N) c hc hsupport haxis
  rw [hrepresentative] at hfactor
  exact exists_unit_factor_mod_relation_of_cover_factorization r N hr D u hu hfactor

end OnLeConjecture.Analytic.CyclicCover
