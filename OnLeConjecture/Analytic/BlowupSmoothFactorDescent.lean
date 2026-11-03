/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.FreeChainCoefficientOrder
public import OnLeConjecture.Analytic.OrderOnePreparation
public import OnLeConjecture.Analytic.SmoothDivision
import Mathlib.Tactic.Ring

/-!
# Descending a smooth factor from the first point blowup

A smooth branch of the strict transform written as `x+a(y)=0` gives
the original branch `x+y*a(y)=0`. Analytic division constructs the
quotient downstairs. Its remainder vanishes by restricting the exact
blowup identity to the smooth branch upstairs.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- Translation by an analytic function of the second coordinate is an
analytic source equivalence fixing every coefficient germ. -/
theorem exists_analytic_coefficient_shift_equiv
    (a : Germ 1) (ha : a ∈ maximalIdeal 1) :
    ∃ e : PointedEquivGerm 2,
      e.pullbackAlgEquiv (coordinate (0 : Fin 2)) =
        coordinate (0 : Fin 2) + hyperplaneExtension 1 a ∧
      ∀ q : Germ 1, e.pullbackAlgEquiv (hyperplaneExtension 1 q) = hyperplaneExtension 1 q := by
  have hmax : coordinate (0 : Fin 2) + hyperplaneExtension 1 a ∈ maximalIdeal 2 :=
    Ideal.add_mem _ (coordinate_mem_maximalIdeal 0)
      ((hyperplaneTailGerm 1).pullback_mem_maximalIdeal ha)
  have hderiv : differential (coordinate (0 : Fin 2) + hyperplaneExtension 1 a)
      (firstCoordinateVector 1) ≠ 0 := by
    have hext : differential (hyperplaneExtension 1 a) (firstCoordinateVector 1) = 0 := by
      change differential (hyperplaneExtension 1 a) (coordinateVector (0 : Fin 2)) = 0
      rw [← valueRingHom_partialDerivative, partialDerivative_zero_hyperplaneExtension, map_zero]
    rw [differential_add]
    change differential (coordinate (0 : Fin 2)) (firstCoordinateVector 1) +
      differential (hyperplaneExtension 1 a) (firstCoordinateVector 1) ≠ 0
    rw [differential_coordinate_apply, hext, add_zero]
    simp [firstCoordinateVector]
  exact exists_equiv_pullback_coordinate_eq_preserving_hyperplaneExtension _ hmax hderiv

/-- A smooth factor in the zero-chart transform descends to an analytic
factor of the original germ. No divisibility downstairs is assumed. -/
theorem dvd_of_zero_chart_smooth_factor
    (v U : Germ 2) (a : Germ 1) (ha : a ∈ maximalIdeal 1)
    (hfactor : (pointBlowupChartGerm 0).pullbackRingHom v =
      coordinate (1 : Fin 2) ^ 2 *
        ((coordinate (0 : Fin 2) + hyperplaneExtension 1 a) * U)) :
    coordinate (0 : Fin 2) + coordinate (1 : Fin 2) * hyperplaneExtension 1 a ∣ v := by
  let H := coordinate (0 : Fin 2) + coordinate (1 : Fin 2) * hyperplaneExtension 1 a
  have hya : coordinate (0 : Fin 1) * a ∈ maximalIdeal 1 :=
    Ideal.mul_mem_left _ _ ha
  obtain ⟨eH, heH, heHfix⟩ := exists_analytic_coefficient_shift_equiv
    (coordinate (0 : Fin 1) * a) hya
  have heH' : eH.pullbackAlgEquiv (coordinate (0 : Fin 2)) = H := by
    simpa only [H, map_mul, hyperplaneExtension_coordinate,
      show (0 : Fin 1).succ = (1 : Fin 2) from rfl] using heH
  obtain ⟨qr, hdivision, _hunique⟩ := exists_unique_smooth_division eH v
  rw [heH', heHfix] at hdivision
  have hbfix (q : Germ 1) : (pointBlowupChartGerm 0).pullbackRingHom (hyperplaneExtension 1 q) =
      hyperplaneExtension 1 q := by
    simpa only [freeChainChartGerm_one] using freeChainChartGerm_pullback_hyperplaneExtension 1 q
  have hbH : (pointBlowupChartGerm 0).pullbackRingHom H =
      coordinate (1 : Fin 2) * (coordinate (0 : Fin 2) + hyperplaneExtension 1 a) := by
    simp only [H, map_add, map_mul, pointBlowupChartGerm_pullback_zero,
      pointBlowupChartGerm_pullback_one, hbfix, map_zero, add_zero]
    ring
  have hpull := congrArg (pointBlowupChartGerm 0).pullbackRingHom hdivision
  rw [hfactor, map_add, map_mul, hbH, hbfix] at hpull
  obtain ⟨eA, heA, heAfix⟩ := exists_analytic_coefficient_shift_equiv a ha
  let ρ := smoothRestriction eA
  have hρzero : ρ (coordinate (0 : Fin 2) + hyperplaneExtension 1 a) = 0 := by
    rw [← heA]
    change hyperplaneRestriction 1
      (eA.pullbackAlgEquiv.symm (eA.pullbackAlgEquiv (coordinate (0 : Fin 2)))) = 0
    rw [eA.pullbackAlgEquiv.symm_apply_apply, hyperplaneRestriction_coordinate_zero]
  have hρext (r : Germ 1) : ρ (hyperplaneExtension 1 r) = r := by
    change hyperplaneRestriction 1 (eA.symm.pullbackAlgEquiv (hyperplaneExtension 1 r)) = r
    rw [PointedEquivGerm.symm_pullback_hyperplaneExtension_eq eA heAfix]
    exact DFunLike.congr_fun (hyperplaneRestriction_comp_extension 1) r
  have hr := congrArg ρ hpull
  simp only [map_mul, map_add, hρzero, mul_zero, zero_mul, hρext, zero_add] at hr
  refine ⟨qr.1, ?_⟩
  simpa only [← hr, map_zero, add_zero] using hdivision

end OnLeConjecture.Analytic.Germ
