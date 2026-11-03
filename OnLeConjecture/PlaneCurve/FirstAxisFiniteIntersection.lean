/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.PlaneCurve.ExceptionalAxisIntersection
public import OnLeConjecture.PlaneCurve.IrreducibleFiniteIntersection
public import OnLeConjecture.Analytic.PointBlowupSmoothIntersection

/-!
# Finite intersection with the second coordinate axis

A nonzero first-axis restriction gives a finite local intersection with
the second coordinate equation. Its order is the restriction order.
-/

public section

namespace OnLeConjecture.PlaneCurve

open Analytic Analytic.Germ

/-- Nonvanishing of the restriction to `y = 0` gives finite intersection
with that coordinate axis. -/
theorem hasFiniteIntersection_secondCoordinate_of_firstAxisRestriction_ne_zero
    (f : Germ 2) (hne : lineRestriction (firstCoordinateVector 1) f ≠ 0) :
    HasFiniteIntersection (coordinate (1 : Fin 2)) f := by
  have hy : Irreducible (coordinate (1 : Fin 2)) := by
    apply (smooth_irreducible_of_mem_maximalIdeal_not_mem_sq _
      (coordinate_mem_maximalIdeal 1) _).2
    intro hmem
    have hd := (mem_firstOrderIdeal_iff.mp (maximalIdeal_sq_le_firstOrderIdeal 2 hmem)).2
    have hv := congrArg (fun L : Source 2 →L[ℂ] ℂ ↦ L (coordinateVector 1)) hd
    simp [coordinateVector] at hv
  apply hasFiniteIntersection_of_irreducible_not_dvd _ _ hy
  intro hdiv
  have hline := pointBlowupExceptionalLine.pullbackRingHom.map_dvd hdiv
  change pointBlowupExceptionalLine.pullbackRingHom (coordinate 1) ∣
    pointBlowupExceptionalLine.pullbackRingHom f at hline
  rw [pointBlowupExceptionalLine_pullback_one, zero_dvd_iff,
    pointBlowupExceptionalLine_eq_lineGerm] at hline
  exact hne hline

/-- A finite first-axis order gives finite intersection with `y = 0`. -/
theorem hasFiniteIntersection_secondCoordinate_of_regular
    (f : Germ 2) (m : ℕ) (hregular : IsRegularInFirstCoordinateOfOrder f m) :
    HasFiniteIntersection (coordinate (1 : Fin 2)) f := by
  apply hasFiniteIntersection_secondCoordinate_of_firstAxisRestriction_ne_zero
  intro hz
  have h := hregular
  change vanishingOrder (lineRestriction (firstCoordinateVector 1) f) = (m : ℕ∞) at h
  rw [hz, vanishingOrder_zero] at h
  exact (ENat.natCast_ne_top m) h.symm

/-- The specified first-axis order is the actual intersection multiplicity. -/
theorem intersectionMultiplicity_secondCoordinate_of_regular
    (f : Germ 2) (m : ℕ) (hregular : IsRegularInFirstCoordinateOfOrder f m)
    (hfinite : HasFiniteIntersection (coordinate (1 : Fin 2)) f) :
    intersectionMultiplicity (coordinate (1 : Fin 2)) f hfinite = m := by
  rw [intersectionMultiplicity_secondCoordinate_eq_firstAxisRestrictionOrder,
    hregular, ENat.toNat_natCast]

end OnLeConjecture.PlaneCurve
