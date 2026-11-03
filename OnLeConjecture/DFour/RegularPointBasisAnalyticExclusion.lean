/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PreparedTopOrderMap
public import OnLeConjecture.DFour.CompleteQuarticExclusion

/-!
# Quartic exclusion without a prepared-polynomial hypothesis

First-axis regularity constructs the depressed polynomial, analytic unit,
and the coordinates of the matched point basis. Only terminal top-order
finite-chart completeness is used and transported. The initial adapted
atlas remains part of the supplied principalization data.
-/

public section

namespace OnLeConjecture.DFour

open OnLeConjecture.Analytic
open OnLeConjecture.Analytic.Germ

/-- The genuine regular quartic map and matched reduction data are
incompatible. No prepared polynomial or normalized weighted form is
assumed. The numerical polar bound is the reduction input. -/
theorem PointedMapGerm.quartic_regular_point_basis_excluded
    (g : PointedMapGerm 2 3)
    {N : ℕ} (c : AnalyticPointBasis N) (d : AnalyticProximityData c)
    (hcoordinates : TopOrderChartCompatibility d)
    (hcomplete : TerminalSingularChartCompleteness c)
    (hroot : c.multiplicity c.root = 4)
    (hfirst : c.germ c.root = g.1.component 0)
    (hregular : IsRegularInFirstCoordinateOfOrder (g.1.component 0) 4)
    (hsquarefree : Squarefree (g.1.component 0))
    (hsecond : g.1.component 1 ∈ maximalIdeal 2 ^ 4)
    (hfinite : PlaneCurve.HasFiniteIntersection (g.1.component 0) (g.1.component 1))
    (hintersection : PlaneCurve.intersectionMultiplicity
      (g.1.component 0) (g.1.component 1) hfinite =
        Numerical.MultiplicityCounts.squareSum c.multiplicity)
    (t b : ℕ) (hb : 0 < b)
    (hnumber : PlaneCurve.intersectionMultiplicity
      (g.1.component 0) (g.1.component 1) hfinite +
        Numerical.MultiplicityCounts.sum c.multiplicity ≤ 3 * t)
    (hpolar : 4 * (t - 1) + Numerical.MultiplicityCounts.sum c.multiplicity + b ≤
      2 * PlaneCurve.intersectionMultiplicity (g.1.component 0) (g.1.component 1) hfinite)
    (hdiv : coordinate (1 : Fin 2) ^ (t - 1) ∣
      jacobian (g.1.component 0) (g.1.component 1)) : False := by
  obtain ⟨e⟩ := exists_preparedTopOrderCoordinates c d hcoordinates
    (by simpa only [hfirst, hroot] using hregular)
  have hroot' : e.basis.multiplicity e.basis.root = 4 := by
    rw [e.multiplicity_eq, e.root_eq, hroot]
  have hfirst' := e.first_prepared g hfirst
  have hfinite' : PlaneCurve.HasFiniteIntersection
      (e.multiplier * firstCoordinatePolynomialEvaluation e.polynomial)
      ((e.map g).1.component 1) := by
    rw [← hfirst']
    exact e.pair_finite g hfinite
  have hI : PlaneCurve.intersectionMultiplicity
      (e.multiplier * firstCoordinatePolynomialEvaluation e.polynomial) ((e.map g).1.component 1)
        hfinite' = PlaneCurve.intersectionMultiplicity
          (g.1.component 0) (g.1.component 1) hfinite := by
    simpa only [hfirst'] using e.intersection_eq g hfinite
  exact prepared_quartic_excluded_of_terminal_complete_proximity
    e.proximity e.chart_compatibility (e.terminal_complete hcomplete) hroot'
    e.polynomial e.monic (by simpa only [hroot] using e.degree)
    (by simpa only [hroot, Nat.reduceSub] using e.depressed)
    e.multiplier ((e.map g).1.component 1) e.multiplier_unit
    (e.proximity.topOrderChain.straightenedGerm_root.symm.trans
      (e.straightened_root.trans e.prepared))
    (by rw [← hfirst']; exact e.first_squarefree g hsquarefree)
    (e.component_mem_pow g 1 4 hsecond) hfinite' t b hb
    (by rw [hI, e.multiplicity_eq]; exact hintersection)
    (by rw [hI, e.multiplicity_eq]; exact hnumber)
    (by rw [hI, e.multiplicity_eq]; exact hpolar)
    (by rw [← hfirst']; exact e.jacobian_divisor g 0 1 t hdiv)

end OnLeConjecture.DFour
