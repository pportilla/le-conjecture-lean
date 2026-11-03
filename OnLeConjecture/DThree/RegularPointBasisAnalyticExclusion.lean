/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PreparedTopOrderMap
public import OnLeConjecture.DThree.MatchedPointBasisAnalyticExclusion

/-!
# Cubic exclusion without a prepared-polynomial hypothesis

The map and its matched point basis are given in coordinates adapted to
the critical component. First-axis regularity constructs the depressed
preparation and all subsequent point-basis coordinates. The original
top-chart compatibility still describes the supplied principalization.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- A regular cubic first component with the matched reduction data
excludes injectivity. No Weierstrass polynomial, unit, Newton weight,
normalized initial form, or coordinate lift is an input. -/
theorem PointedMapGerm.not_hasInjectiveRepresentative_of_cubic_regular_point_basis
    (g : PointedMapGerm 2 3)
    {N : ℕ} (c : AnalyticPointBasis N) (d : AnalyticProximityData c)
    (hcoordinates : DFour.TopOrderChartCompatibility d)
    (hroot : c.multiplicity c.root = 3)
    (hfirst : c.germ c.root = g.1.component 0)
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder (g.1.component 0) 3)
    (hsquarefree : Squarefree (g.1.component 0))
    (hsecond : g.1.component 1 ∈ Germ.maximalIdeal 2 ^ 3)
    (hfinite : PlaneCurve.HasFiniteIntersection (g.1.component 0) (g.1.component 1))
    (hintersection : PlaneCurve.intersectionMultiplicity
      (g.1.component 0) (g.1.component 1) hfinite =
        Numerical.MultiplicityCounts.squareSum c.multiplicity)
    (t : ℕ)
    (hnumber : PlaneCurve.intersectionMultiplicity
      (g.1.component 0) (g.1.component 1) hfinite +
        Numerical.MultiplicityCounts.sum c.multiplicity ≤ 3 * t)
    (hdivZeroOne : Germ.coordinate (1 : Fin 2) ^ (t - 1) ∣
      Germ.jacobian (g.1.component 0) (g.1.component 1))
    (hdivZeroTwo : Germ.coordinate (1 : Fin 2) ^ (t - 1) ∣
      Germ.jacobian (g.1.component 0) (g.1.component 2))
    (hdivOneTwo : Germ.coordinate (1 : Fin 2) ^ (t - 1) ∣
      Germ.jacobian (g.1.component 1) (g.1.component 2)) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨e⟩ := exists_preparedTopOrderCoordinates c d hcoordinates
    (by simpa only [hfirst, hroot] using hregular)
  have hroot' : e.basis.multiplicity e.basis.root = 3 := by
    rw [e.multiplicity_eq, e.root_eq, hroot]
  have hI := e.intersection_eq g hfinite
  have hnot := PointedMapGerm.not_hasInjectiveRepresentative_of_cubic_matched_point_basis
    (e.map g) e.basis e.proximity e.chart_compatibility hroot'
    e.polynomial e.monic (by simpa only [hroot] using e.degree)
    (by simpa only [hroot, Nat.reduceSub] using e.depressed)
    e.multiplier e.multiplier_unit (e.first_prepared g hfirst)
    (e.straightened_root.trans e.prepared) (e.first_squarefree g hsquarefree)
    (e.component_mem_pow g 1 3 hsecond) (e.pair_finite g hfinite)
    (by rw [hI, e.multiplicity_eq]; exact hintersection) t
    (by rw [hI, e.multiplicity_eq]; exact hnumber)
    (e.jacobian_divisor g 0 1 t hdivZeroOne) (e.jacobian_divisor g 0 2 t hdivZeroTwo)
    (e.jacobian_divisor g 1 2 t hdivOneTwo)
  exact fun hg ↦ hnot ((e.rightLeftEquivalent g).hasInjectiveRepresentative hg)

end OnLeConjecture.DThree

