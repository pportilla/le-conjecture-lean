/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.MaximalCriticalProjectiveFirstBlowup
public import OnLeConjecture.DThree.ProjectivePointBasisAnalyticExclusion

/-!
# Cubic exclusion from two-chart weak-basepoint coverage

The original critical equation need not have finite tangent in the given
root coordinates. Its smoothness and intersection three are proved using
both root charts. The subsequent critical coordinates and adapted atlas
are constructed by the existing source preparation and atlas theorems.
-/

public section

namespace OnLeConjecture.DThree

open Analytic Analytic.Germ

theorem PointedMapGerm.not_hasInjectiveRepresentative_of_cubic_twoChart_point_basis
    (g : PointedMapGerm 2 3) {N : ℕ} (c : AnalyticPointBasis N)
    (d : AnalyticProximityData c) (hseparation : TopOrderProjectiveSeparation c)
    (hroot : c.multiplicity c.root = 3) (hcomponent : c.germ c.root = g.1.component 0)
    {ι : Type*} [Fintype ι] (w : WeakTransformIdealData c ι)
    (hcomplete : RootTwoChartWeakBasepointCompleteness w) (q : ι → ℂ)
    (hmember : c.germ c.root = germLinearCombination (w.generators c.root) q)
    (hdepth : ∀ p, c.ParentRelation p c.root →
      c.generation p = c.generation c.root + 1)
    (t : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ d.proximity.branchCount)
    (h : Germ 2) (hh : h ∈ maximalIdeal 2)
    (havoid : w.AvoidsRootProjectiveTangentCancellation q (criticalProjectiveTangent h))
    (hcriticalFinite : PlaneCurve.HasFiniteIntersection h (c.germ c.root))
    (hpolar : PlaneCurve.intersectionMultiplicity h (c.germ c.root) hcriticalFinite * (t - 1) +
      d.proximity.totalMultiplicity + d.proximity.branchCount ≤
        2 * d.proximity.squareMultiplicity)
    (hsquarefree : Squarefree (g.1.component 0))
    (hsecond : g.1.component 1 ∈ maximalIdeal 2 ^ 3)
    (hfinite : PlaneCurve.HasFiniteIntersection (g.1.component 0) (g.1.component 1))
    (hintersection : PlaneCurve.intersectionMultiplicity
      (g.1.component 0) (g.1.component 1) hfinite =
        Numerical.MultiplicityCounts.squareSum c.multiplicity)
    (hnumber : PlaneCurve.intersectionMultiplicity
      (g.1.component 0) (g.1.component 1) hfinite +
        Numerical.MultiplicityCounts.sum c.multiplicity ≤ 3 * t)
    (hdiv : ∀ i j : Fin 3, i < j → h ^ (t - 1) ∣
      jacobian (g.1.component i) (g.1.component j)) : ¬ g.HasInjectiveRepresentative := by
  have hglobal : d.proximity.squareMultiplicity + d.proximity.totalMultiplicity ≤ 3 * t := by
    rw [hintersection] at hnumber
    simpa only [Numerical.ProximityCertificate.squareMultiplicity,
      Numerical.ProximityCertificate.totalMultiplicity, d.multiplicity_eq,
      Numerical.MultiplicityCounts.sum] using hnumber
  obtain ⟨S⟩ := exists_cubic_source_preparation_of_maximal_critical_projective_first_blowup
    g c d hcomponent w hcomplete q hmember hroot hdepth t ht hb h hh havoid
    hcriticalFinite hglobal hpolar
  exact PointedMapGerm.not_hasInjectiveRepresentative_of_cubic_projective_point_basis
    g c d hseparation hroot hcomponent h S hsquarefree hsecond hfinite hintersection t hnumber hdiv

end OnLeConjecture.DThree
