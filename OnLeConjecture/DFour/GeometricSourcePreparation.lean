/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.MaximalCriticalSmoothness
public import OnLeConjecture.Analytic.SmoothReductionCoordinates

/-!
# Quartic source preparation from the maximal critical component

The analytic point basis and the reduction inequalities construct a
smooth critical coordinate and a depressed monic quartic, with its
analytic unit retained. Smoothness, intersection four, and the prepared
polynomial are not separately assumed.
-/

public section

namespace OnLeConjecture.DFour

open Analytic Analytic.Germ Numerical.MultiplicityCounts
open scoped BigOperators

/-- The first coordinate of the map admits the required quartic
preparation from the actual generic member and maximal polar estimates. -/
theorem exists_quartic_source_preparation_of_maximal_critical
    (g : PointedMapGerm 2 3) {N : ℕ} (c : AnalyticPointBasis N)
    (hmember : c.germ c.root = g.1.component 0)
    (t b : ℕ) (hroot : c.multiplicity c.root = 4) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (h : Germ 2) (hh : h ∈ maximalIdeal 2)
    (hfinite : PlaneCurve.HasFiniteIntersection (c.germ c.root) h)
    (hglobal : squareSum c.multiplicity + (∑ p, c.multiplicity p) ≤ 3 * t)
    (hpolar : PlaneCurve.intersectionMultiplicity (c.germ c.root) h hfinite * (t - 1) +
      (∑ p, c.multiplicity p) + b ≤ 2 * squareSum c.multiplicity) :
    Nonempty (SmoothReductionCoordinates g h 4) := by
  obtain ⟨hinter, hsmooth, _hirred⟩ := c.quartic_maximal_critical_equation_smooth
    t b hroot hb ht h hh hfinite hglobal hpolar
  have hfinite' : PlaneCurve.HasFiniteIntersection h (g.1.component 0) := by
    rw [← hmember]
    exact (PlaneCurve.hasFiniteIntersection_comm _ _).mp hfinite
  apply exists_smoothReductionCoordinates g h hh hsmooth hfinite' 4 (Or.inr rfl)
  rw [PlaneCurve.intersectionMultiplicity_comm] at hinter
  simpa only [hmember] using hinter

end OnLeConjecture.DFour
