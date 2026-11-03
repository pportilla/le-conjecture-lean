/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.TransverseSmoothPreparation
public import OnLeConjecture.Analytic.RegularBlowupCharts

/-!
# Intersection with the exceptional coordinate axis

Intersection with the second coordinate equation is the vanishing order
of restriction to the first coordinate axis. The proof transports the
coordinate-branch quotient formula through the inverse coordinate swap.
-/

public section

namespace OnLeConjecture.PlaneCurve

open Analytic Analytic.Germ

private theorem inverseSwap_secondCoordinate :
    (coordinateSwapPointedEquiv (1 : Fin 2)).symm.pullbackAlgEquiv
      (coordinate (1 : Fin 2)) = coordinate (0 : Fin 2) := by
  have hx : (coordinateSwapPointedEquiv (1 : Fin 2)).pullbackAlgEquiv
      (coordinate (0 : Fin 2)) = coordinate (1 : Fin 2) := by
    change (coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom
      (coordinate (0 : Fin 2)) = _
    rw [PointedMapGerm.pullback_coordinate]
    exact coordinateSwapPointedEquiv_component_zero 1
  change (coordinateSwapPointedEquiv (1 : Fin 2)).pullbackAlgEquiv.symm
    (coordinate (1 : Fin 2)) = _
  rw [← hx, AlgEquiv.symm_apply_apply]

private theorem inverseSwap_axisRestriction (f : Germ 2) :
    hyperplaneRestriction 1
      ((coordinateSwapPointedEquiv (1 : Fin 2)).symm.pullbackAlgEquiv f) =
    lineRestriction (firstCoordinateVector 1) f := by
  have h := firstAxisRestriction_swap
    ((coordinateSwapPointedEquiv (1 : Fin 2)).symm.pullbackAlgEquiv f)
  change lineRestriction (firstCoordinateVector 1)
      ((coordinateSwapPointedEquiv (1 : Fin 2)).pullbackAlgEquiv
        ((coordinateSwapPointedEquiv (1 : Fin 2)).pullbackAlgEquiv.symm f)) = _ at h
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

theorem intersectionMultiplicity_secondCoordinate_eq_firstAxisRestrictionOrder
    (f : Germ 2) (hfinite : HasFiniteIntersection (coordinate (1 : Fin 2)) f) :
    intersectionMultiplicity (coordinate (1 : Fin 2)) f hfinite =
      (vanishingOrder (lineRestriction (firstCoordinateVector 1) f)).toNat := by
  have hfinite' := hfinite.pullback (coordinateSwapPointedEquiv (1 : Fin 2)).symm
  rw [inverseSwap_secondCoordinate] at hfinite'
  have hne := restriction_ne_zero_of_hasFiniteIntersection_coordinate _ hfinite'
  have hi := intersectionMultiplicity_pullback
    (coordinateSwapPointedEquiv (1 : Fin 2)).symm hfinite
  simpa only [inverseSwap_secondCoordinate,
    intersectionMultiplicity_coordinate_eq_restrictionOrder _ hne,
    inverseSwap_axisRestriction] using hi

theorem intersectionMultiplicity_secondCoordinate_eq_exceptionalRestrictionOrder
    (f : Germ 2) (hfinite : HasFiniteIntersection (coordinate (1 : Fin 2)) f) :
    intersectionMultiplicity (coordinate (1 : Fin 2)) f hfinite =
      (vanishingOrder (pointBlowupExceptionalLine.pullbackRingHom f)).toNat := by
  rw [pointBlowupExceptionalLine_eq_lineGerm]
  exact intersectionMultiplicity_secondCoordinate_eq_firstAxisRestrictionOrder f hfinite

end OnLeConjecture.PlaneCurve
