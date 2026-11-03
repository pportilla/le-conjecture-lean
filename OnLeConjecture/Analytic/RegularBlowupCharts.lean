/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ScaledPolynomialFreeCharts
public import OnLeConjecture.Analytic.WeierstrassPreparation
public import OnLeConjecture.Analytic.AnalyticPointBasis

/-!
# Transverse regularity and the complementary blowup point

Exact first-axis order makes the complementary strict transform a unit.
In a finite chart, a strict transform retaining the full parent order is
again regular of that order along its first coordinate. Both statements
concern actual analytic pullbacks and do not require a prepared polynomial.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open Filter
open scoped Topology

/-- Multiplication by a unit preserves the exact transverse order. -/
theorem isRegularInFirstCoordinateOfOrder_unit_mul_iff
    {m : ℕ} (U f : Germ 2) (hU : IsUnit U) :
    IsRegularInFirstCoordinateOfOrder (U * f) m ↔
      IsRegularInFirstCoordinateOfOrder f m := by
  unfold IsRegularInFirstCoordinateOfOrder
  rw [map_mul, vanishingOrder_mul,
    vanishingOrder_eq_zero_iff_isUnit.mpr (hU.map _), zero_add]

theorem pointBlowupExceptionalLine_eq_lineGerm :
    pointBlowupExceptionalLine = lineGerm (firstCoordinateVector 1) := by
  apply Subtype.ext
  apply Subtype.ext
  change ((fun z : Source 1 ↦ (![z 0, 0] : Source 2)) : FunctionMapGerm 1 2) =
    ((lineMap (firstCoordinateVector 1)) : FunctionMapGerm 1 2)
  apply Filter.Germ.coe_eq.mpr
  apply Filter.Eventually.of_forall
  intro z
  ext i
  fin_cases i <;> simp [lineMap_apply, firstCoordinateVector]

/-- Restriction of the complementary chart to its transverse axis is
the original first-axis restriction. -/
theorem complementaryBlowupChart_secondAxisRestriction (f : Germ 2) :
    hyperplaneRestriction 1 ((pointBlowupChartGerm 0).pullbackRingHom
      ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom f)) =
      lineRestriction (firstCoordinateVector 1) f := by
  change _ = (lineGerm (firstCoordinateVector 1)).pullbackRingHom f
  rw [← pointBlowupExceptionalLine_eq_lineGerm]
  obtain ⟨F, hF, rfl⟩ := exists_ofFunction f
  change compPointed (compPointed (compPointed (ofFunction F hF)
    (coordinateSwapPointedEquiv (1 : Fin 2)).forward) (pointBlowupChartGerm 0))
    (hyperplaneInclusionGerm 1) = compPointed (ofFunction F hF) pointBlowupExceptionalLine
  simp only [coordinateSwapPointedEquiv, pointedEquivGermOfContinuousLinearEquiv,
    pointBlowupChartGerm, hyperplaneInclusionGerm, pointBlowupExceptionalLine,
    compPointed_ofFunction]
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  refine Filter.Eventually.of_forall fun t ↦ ?_
  change F (coordinateSwapEquiv (1 : Fin 2)
    (pointBlowupChart 0 (hyperplaneInclusion 1 t))) = F (![t 0, 0])
  congr 1
  ext i
  fin_cases i
  · simp [coordinateSwapEquiv_apply_zero, pointBlowupChart, hyperplaneInclusion]
    rfl
  · change (Equiv.piCongrLeft (fun _ : Fin 2 ↦ ℂ) (Equiv.swap 0 1)
      (pointBlowupChart 0 (hyperplaneInclusion 1 t))) 1 = 0
    simp [Equiv.piCongrLeft, pointBlowupChart, hyperplaneInclusion]

/-- Exact first-axis regularity excludes the complementary point: the
analytic strict transform there is a unit. This includes order zero. -/
theorem complementaryBlowupTransform_isUnit_of_regular
    (m : ℕ) (f g : Germ 2) (hregular : IsRegularInFirstCoordinateOfOrder f m)
    (htransform : (pointBlowupChartGerm 0).pullbackRingHom
      ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom f) =
        coordinate (1 : Fin 2) ^ m * g) : IsUnit g := by
  have h := congrArg (hyperplaneRestriction 1) htransform
  have hy : hyperplaneRestriction 1 (coordinate (1 : Fin 2)) =
      coordinate (0 : Fin 1) := by
    convert hyperplaneRestriction_coordinate_succ 1 (0 : Fin 1) using 1
    congr 2
  rw [complementaryBlowupChart_secondAxisRestriction, map_mul, map_pow, hy] at h
  have horder := congrArg vanishingOrder h
  rw [hregular, vanishingOrder_mul, vanishingOrder_coordinate_pow] at horder
  have hgorder : vanishingOrder (hyperplaneRestriction 1 g) = 0 := by
    apply ENat.add_right_injective_of_ne_top (ENat.natCast_ne_top m)
    simpa only [add_zero] using horder.symm
  have hvalue := valueRingHom_ne_zero_of_isUnit
    (vanishingOrder_eq_zero_iff_isUnit.mp hgorder)
  rw [hyperplaneRestriction, PointedMapGerm.valueRingHom_pullback] at hvalue
  exact isUnit_of_valueRingHom_ne_zero hvalue

/-- When a finite strict transform retains the exact parent order,
its first-axis restriction has that same exact order. -/
theorem pointBlowupTransform_regular_of_full_order
    (c : ℂ) (m : ℕ) (f g : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hnext : f ∉ maximalIdeal 2 ^ (m + 1))
    (hg : g ∈ maximalIdeal 2 ^ m)
    (htransform : (pointBlowupChartGerm c).pullbackRingHom f =
      coordinate (1 : Fin 2) ^ m * g) :
    IsRegularInFirstCoordinateOfOrder g m := by
  obtain ⟨g', P, T, hfactor, _hP, _hPhom, _htail, _hchart, hT, hdegree,
    hrestriction, _hg'⟩ := exists_pointBlowupTransform_with_initial c m f hf hnext
  have heq := pointBlowupTransform_unique c m f g g' htransform hfactor
  have hnot : pointBlowupExceptionalLine.pullbackRingHom g ∉ maximalIdeal 1 ^ (m + 1) := by
    rw [heq, hrestriction]
    exact oneVariablePolynomialEvaluation_not_mem_pow m T hT hdegree
  have hmem := PointedMapGerm.pullback_mem_maximalIdeal_pow pointBlowupExceptionalLine hg
  have hlow := mem_maximalIdeal_one_pow_iff.mp hmem
  have hhigh : vanishingOrder (pointBlowupExceptionalLine.pullbackRingHom g) <
      ((m + 1 : ℕ) : ℕ∞) :=
    lt_of_not_ge (fun h ↦ hnot (mem_maximalIdeal_one_pow_iff.mpr h))
  have heqorder : vanishingOrder (pointBlowupExceptionalLine.pullbackRingHom g) = m := by
    apply le_antisymm _ hlow
    apply ENat.lt_natCast_add_one_iff.mp
    simpa only [Nat.cast_add, Nat.cast_one] using hhigh
  rw [pointBlowupExceptionalLine_eq_lineGerm] at heqorder
  exact heqorder

end OnLeConjecture.Analytic.Germ
