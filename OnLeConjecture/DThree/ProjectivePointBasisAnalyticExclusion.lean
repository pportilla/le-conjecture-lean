/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SmoothReductionAtlas
public import OnLeConjecture.DThree.RegularPointBasisAnalyticExclusion
public import OnLeConjecture.DThree.MaximalCriticalFirstBlowup

/-!
# Cubic exclusion from the original projective point basis

The critical source coordinates and the compatible point-basis atlas are
constructed. Projective separation concerns only the actual original
chart maps. The final theorem obtains the smooth critical coordinates
from first-blowup completeness and explicit generic tangent avoidance.
-/

public section

namespace OnLeConjecture.DThree

open Analytic Analytic.Germ

/-- The original cubic map is noninjective once the critical coordinates
have been constructed. No adapted point-basis atlas is assumed. -/
theorem PointedMapGerm.not_hasInjectiveRepresentative_of_cubic_projective_point_basis
    (g : PointedMapGerm 2 3) {N : ℕ} (c : AnalyticPointBasis N)
    (d : AnalyticProximityData c) (hseparation : TopOrderProjectiveSeparation c)
    (hroot : c.multiplicity c.root = 3) (hmember : c.germ c.root = g.1.component 0)
    (h : Germ 2) (S : SmoothReductionCoordinates g h 3)
    (hsquarefree : Squarefree (g.1.component 0))
    (hsecond : g.1.component 1 ∈ maximalIdeal 2 ^ 3)
    (hfinite : PlaneCurve.HasFiniteIntersection (g.1.component 0) (g.1.component 1))
    (hintersection : PlaneCurve.intersectionMultiplicity
      (g.1.component 0) (g.1.component 1) hfinite =
        Numerical.MultiplicityCounts.squareSum c.multiplicity)
    (t : ℕ)
    (hnumber : PlaneCurve.intersectionMultiplicity
      (g.1.component 0) (g.1.component 1) hfinite +
        Numerical.MultiplicityCounts.sum c.multiplicity ≤ 3 * t)
    (hdiv : ∀ i j : Fin 3, i < j → h ^ (t - 1) ∣
      jacobian (g.1.component i) (g.1.component j)) : ¬ g.HasInjectiveRepresentative := by
  have hregular : IsRegularInFirstCoordinateOfOrder
      (S.source.forward.pullbackRingHom (c.germ c.root)) (c.multiplicity c.root) := by
    simpa only [hmember, hroot] using S.source_first_regular
  let C := c.regularAtlas S.source hregular
  let D := c.regularAtlasProximity d S.source hregular
  have hfirst : C.germ C.root = S.map.1.component 0 := by
    change (c.regularAtlas S.source hregular).germ c.root = _
    rw [c.regularAtlas_root_germ, S.component, hmember]
  have hsecond' : S.map.1.component 1 ∈ maximalIdeal 2 ^ 3 := by
    rw [S.component]
    exact S.source.forward.pullback_mem_maximalIdeal_pow hsecond
  have hI := S.intersection_eq hfinite
  have hdiv' := S.common_jacobian_divisors t hdiv
  have hnot := PointedMapGerm.not_hasInjectiveRepresentative_of_cubic_regular_point_basis
    S.map C D (c.regularAtlas_topOrderChartCompatibility d hseparation S.source hregular)
    hroot hfirst S.first_regular (S.first_squarefree hsquarefree) hsecond' (S.pair_finite hfinite)
    (by rw [hI]; exact hintersection) t (by rw [hI]; exact hnumber)
    (hdiv' 0 1 (by decide)) (hdiv' 0 2 (by decide)) (hdiv' 1 2 (by decide))
  exact fun hg ↦ hnot (S.rightLeftEquivalent.hasInjectiveRepresentative hg)

/-- First-blowup generic avoidance constructs the critical coordinates,
and genuine projective separation constructs the entire adapted atlas. -/
theorem PointedMapGerm.not_hasInjectiveRepresentative_of_cubic_first_blowup_projective_data
    (g : PointedMapGerm 2 3) {N : ℕ} (c : AnalyticPointBasis N)
    (d : AnalyticProximityData c) (hseparation : TopOrderProjectiveSeparation c)
    (hroot : c.multiplicity c.root = 3) (hcomponent : c.germ c.root = g.1.component 0)
    {ι : Type*} [Fintype ι] (w : WeakTransformIdealData c ι)
    (hcomplete : FiniteWeakBasepointCompleteness w) (q : ι → ℂ)
    (hmember : c.germ c.root = germLinearCombination (w.generators c.root) q)
    (hdepth : ∀ p, c.ParentRelation p c.root →
      c.generation p = c.generation c.root + 1)
    (t : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ d.proximity.branchCount)
    (h : Germ 2) (hh : h ∈ maximalIdeal 2)
    (hdx : valueRingHom 2 (partialDerivative (0 : Fin 2) h) ≠ 0)
    (havoid : w.AvoidsRootTangentCancellation q (finiteCriticalTangent h))
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
  obtain ⟨S⟩ := exists_cubic_source_preparation_of_maximal_critical_first_blowup
    g c d hcomponent w hcomplete q hmember hroot hdepth t ht hb h hh hdx havoid
    hcriticalFinite hglobal hpolar
  exact PointedMapGerm.not_hasInjectiveRepresentative_of_cubic_projective_point_basis
    g c d hseparation hroot hcomponent h S hsquarefree hsecond hfinite hintersection t hnumber hdiv

end OnLeConjecture.DThree
