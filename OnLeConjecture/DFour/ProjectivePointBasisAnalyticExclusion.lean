/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SmoothReductionAtlas
public import OnLeConjecture.DFour.RegularPointBasisAnalyticExclusion
public import OnLeConjecture.DFour.GeometricSourcePreparation

/-!
# Quartic exclusion from original projective principalization data

The maximal critical estimates construct the smooth critical coordinates.
The analytic atlas, terminal completeness, and depressed preparation are
then constructed and transported. The original hypotheses refer only to
the supplied analytic point basis, its projective charts, and the actual
intersection and Jacobian-divisor estimates.
-/

public section

namespace OnLeConjecture.DFour

open Analytic Analytic.Germ
open scoped BigOperators

/-- The quartic contradiction with constructed critical coordinates
requires no originally adapted atlas or prepared first member. -/
theorem PointedMapGerm.quartic_projective_point_basis_excluded
    (g : PointedMapGerm 2 3) {N : ℕ} (c : AnalyticPointBasis N)
    (d : AnalyticProximityData c) (hseparation : TopOrderProjectiveSeparation c)
    (hcomplete : TerminalTwoChartSingularCompleteness c)
    (hroot : c.multiplicity c.root = 4) (hmember : c.germ c.root = g.1.component 0)
    (h : Germ 2) (S : SmoothReductionCoordinates g h 4)
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
    (hdiv : h ^ (t - 1) ∣ jacobian (g.1.component 0) (g.1.component 1)) : False := by
  have hregular : IsRegularInFirstCoordinateOfOrder
      (S.source.forward.pullbackRingHom (c.germ c.root)) (c.multiplicity c.root) := by
    simpa only [hmember, hroot] using S.source_first_regular
  let C := c.regularAtlas S.source hregular
  let D := c.regularAtlasProximity d S.source hregular
  have hfirst : C.germ C.root = S.map.1.component 0 := by
    change (c.regularAtlas S.source hregular).germ c.root = _
    rw [c.regularAtlas_root_germ, S.component, hmember]
  have hsecond' : S.map.1.component 1 ∈ maximalIdeal 2 ^ 4 := by
    rw [S.component]
    exact S.source.forward.pullback_mem_maximalIdeal_pow hsecond
  have hdiv' : coordinate (1 : Fin 2) ^ (t - 1) ∣
      jacobian (S.map.1.component 0) (S.map.1.component 1) := by
    rw [S.component, S.component]
    exact S.source.coordinate_pow_dvd_jacobian_of_pullback_equation h _ _ (t - 1)
      S.branch_coordinate hdiv
  have hI := S.intersection_eq hfinite
  exact PointedMapGerm.quartic_regular_point_basis_excluded S.map C D
    (c.regularAtlas_topOrderChartCompatibility d hseparation S.source hregular)
    (c.regularAtlas_terminalCompleteness hcomplete S.source hregular)
    hroot hfirst S.first_regular (S.first_squarefree hsquarefree) hsecond'
    (S.pair_finite hfinite) (by rw [hI]; exact hintersection) t b hb
    (by rw [hI]; exact hnumber) (by rw [hI]; exact hpolar) hdiv'

/-- The maximal critical-component estimates construct both the adapted
source coordinates and the compatible complete atlas. -/
theorem PointedMapGerm.quartic_maximal_critical_projective_data_excluded
    (g : PointedMapGerm 2 3) {N : ℕ} (c : AnalyticPointBasis N)
    (d : AnalyticProximityData c) (hseparation : TopOrderProjectiveSeparation c)
    (hcomplete : TerminalTwoChartSingularCompleteness c)
    (hroot : c.multiplicity c.root = 4) (hmember : c.germ c.root = g.1.component 0)
    (t b : ℕ) (ht : 2 ≤ t) (hb : 0 < b)
    (h : Germ 2) (hh : h ∈ maximalIdeal 2)
    (hcriticalFinite : PlaneCurve.HasFiniteIntersection (c.germ c.root) h)
    (hsquarefree : Squarefree (g.1.component 0))
    (hsecond : g.1.component 1 ∈ maximalIdeal 2 ^ 4)
    (hfinite : PlaneCurve.HasFiniteIntersection (g.1.component 0) (g.1.component 1))
    (hintersection : PlaneCurve.intersectionMultiplicity
      (g.1.component 0) (g.1.component 1) hfinite =
        Numerical.MultiplicityCounts.squareSum c.multiplicity)
    (hnumber : PlaneCurve.intersectionMultiplicity
      (g.1.component 0) (g.1.component 1) hfinite +
        Numerical.MultiplicityCounts.sum c.multiplicity ≤ 3 * t)
    (hpolar : PlaneCurve.intersectionMultiplicity (c.germ c.root) h hcriticalFinite * (t - 1) +
      Numerical.MultiplicityCounts.sum c.multiplicity + b ≤
        2 * PlaneCurve.intersectionMultiplicity (g.1.component 0) (g.1.component 1) hfinite)
    (hdiv : h ^ (t - 1) ∣ jacobian (g.1.component 0) (g.1.component 1)) : False := by
  have hglobal : Numerical.MultiplicityCounts.squareSum c.multiplicity +
      (∑ p, c.multiplicity p) ≤ 3 * t := by
    rw [hintersection] at hnumber
    simpa only [Numerical.MultiplicityCounts.sum] using hnumber
  have hpolar' : PlaneCurve.intersectionMultiplicity (c.germ c.root) h hcriticalFinite * (t - 1) +
      (∑ p, c.multiplicity p) + b ≤ 2 * Numerical.MultiplicityCounts.squareSum c.multiplicity := by
    simpa only [hintersection, Numerical.MultiplicityCounts.sum] using hpolar
  obtain ⟨S⟩ := exists_quartic_source_preparation_of_maximal_critical g c hmember t b
    hroot hb ht h hh hcriticalFinite hglobal hpolar'
  obtain ⟨hcriticalFour, _hsmooth, _hirred⟩ := c.quartic_maximal_critical_equation_smooth
    t b hroot hb ht h hh hcriticalFinite hglobal hpolar'
  apply PointedMapGerm.quartic_projective_point_basis_excluded g c d hseparation hcomplete
    hroot hmember h S hsquarefree hsecond hfinite hintersection t b hb hnumber _ hdiv
  simpa only [hcriticalFour] using hpolar

end OnLeConjecture.DFour
