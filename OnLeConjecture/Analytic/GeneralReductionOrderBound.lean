/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GeneralResolutionReductionData
public import OnLeConjecture.Analytic.ReductionOrderBound
public import OnLeConjecture.Analytic.OrdinaryIntersectionBound

/-!
# The coordinate order bound for the general reduction

The coordinate order is identified with the root weak-ideal order. A member
chosen in the prescribed open set has exactly that order, so the ordinary
intersection bound supplies the lower bound needed by the numerical reduction.
-/

public section

namespace OnLeConjecture.Analytic.GeneralResolutionReductionData

open OnLeConjecture.Analytic.Germ PlaneCurve Numerical

/-- The general reduction supplies the numerical coordinate-order reduction
without a separate root-order or intersection-bound hypothesis. -/
theorem exists_coordinateOrderReductionData {g : PointedMapGerm 2 3}
    (D : GeneralResolutionReductionData g) (hfinite : g.IsFiniteAtOrigin) :
    Nonempty (PointedMapGerm.CoordinateOrderReductionData g hfinite) := by
  obtain ⟨q, hqU, hq, _⟩ :=
    D.weakData.exists_coefficients_exact_orders_linear_conditions_mem_open
      (fun _ : Fin 0 => (0 : (Fin 3 → ℂ) →ₗ[ℂ] ℂ))
      (fun i => Fin.elim0 i) D.coefficientOpen D.coefficientOpen_isOpen
      D.coefficientOpen_nonempty
  obtain ⟨R⟩ := D.generalMemberReduction q hqU
  have hgens : D.weakData.generators D.pointBasis.root = g.1.component :=
    funext D.root_generators
  have horder := hq D.pointBasis.root
  rw [hgens] at horder
  have hcriticalFinite := (hasFiniteIntersection_comm _ _).mp R.critical_finite
  have hlower := ordinary_intersection_lower_bound
    (D.pointBasis.multiplicity D.pointBasis.root) 1
    (D.pointBasis.multiplicity_pos D.pointBasis.root)
    (germLinearCombination g.1.component q) D.critical horder.1 horder.2
    (by simpa only [pow_one] using D.critical_mem) hcriticalFinite
  have hcomm := intersectionMultiplicity_comm D.critical
    (germLinearCombination g.1.component q) R.critical_finite
  refine ⟨{
    N := D.cardinality
    certificate := D.proximityData.proximity
    connected := D.proximityData.proximity.root_reachable_of_generation
      D.pointBasis.generation D.proximityData.generation_decreases
    m := D.exponent
    n := intersectionMultiplicity D.critical
      (germLinearCombination g.1.component q) R.critical_finite
    coordinateOrder_eq_root := ?_
    branchCount_positive := D.branchCount_pos
    global_estimate := ?_
    root_le_n := ?_
    polar_estimate := ?_ }⟩
  · simpa only [D.proximityData.multiplicity_eq, D.proximityData.root_eq] using
      D.coordinateOrder_eq_root hfinite
  · simpa only [ProximityCertificate.squareMultiplicity,
      ProximityCertificate.totalMultiplicity, MultiplicityCounts.sum,
      D.proximityData.multiplicity_eq] using
      D.global_estimate
  · simpa only [mul_one, D.proximityData.multiplicity_eq,
      D.proximityData.root_eq, hcomm] using hlower
  · simpa only [ProximityCertificate.squareMultiplicity,
      ProximityCertificate.totalMultiplicity, MultiplicityCounts.sum,
      D.proximityData.multiplicity_eq] using R.polar

theorem coordinateOrder_le_four {g : PointedMapGerm 2 3}
    (D : GeneralResolutionReductionData g) (hfinite : g.IsFiniteAtOrigin)
    (hdifferential : g.differential = 0) :
    g.coordinateOrder (by decide) hfinite ≤ 4 := by
  obtain ⟨R⟩ := D.exists_coordinateOrderReductionData hfinite
  exact R.coordinateOrder_le_four hdifferential

theorem coordinateOrder_eq_two_or_three_or_four {g : PointedMapGerm 2 3}
    (D : GeneralResolutionReductionData g) (hfinite : g.IsFiniteAtOrigin)
    (hdifferential : g.differential = 0) :
    g.coordinateOrder (by decide) hfinite = 2 ∨
      g.coordinateOrder (by decide) hfinite = 3 ∨
        g.coordinateOrder (by decide) hfinite = 4 := by
  obtain ⟨R⟩ := D.exists_coordinateOrderReductionData hfinite
  exact R.coordinateOrder_eq_two_or_three_or_four hdifferential

end OnLeConjecture.Analytic.GeneralResolutionReductionData
