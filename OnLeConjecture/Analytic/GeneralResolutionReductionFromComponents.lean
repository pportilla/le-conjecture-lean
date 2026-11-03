/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.MaximalTransverseComponentSelection

/-!
# The general reduction package from all transverse components

The geometric hypotheses are unchanged: an analytic weak-ideal point
basis, matched proximity, projective charts, and the general members'
curve invariants and terminal completeness. The critical inputs have the
original all-component form. Their finite maximum selects one equation
and exponent before any member coefficient vector is chosen.

This is a constructor from explicit hypotheses, not an existence theorem
for principalization, the component equations, or the reduction estimates.
-/

public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ PlaneCurve Numerical

/-- General-member curve invariants which do not specify any critical
component or assume a single-component polar estimate. -/
structure GeneralMemberCurveInvariants {N : ℕ}
    (g : PointedMapGerm 2 3) (c : AnalyticPointBasis N)
    (d : AnalyticProximityData c) (q : Fin 3 → ℂ) where
  companion : Fin 3 → ℂ
  pair_finite : HasFiniteIntersection (germLinearCombination g.1.component q)
    (germLinearCombination g.1.component companion)
  pair_intersection : intersectionMultiplicity (germLinearCombination g.1.component q)
    (germLinearCombination g.1.component companion) pair_finite =
      MultiplicityCounts.squareSum c.multiplicity
  reduced : Squarefree (germLinearCombination g.1.component q)
  isolated : HasIsolatedCriticalPoint (germLinearCombination g.1.component q)
  branches : d.proximity.branchCount =
    irreducibleBranchCount (germLinearCombination g.1.component q)
  genus : MultiplicityCounts.squareSum c.multiplicity + 1 =
    milnorNumber (germLinearCombination g.1.component q) isolated +
      MultiplicityCounts.sum c.multiplicity + d.proximity.branchCount

/-- The literal projective atlas already supplies the root compatibility
used by the common-linear quadratic argument. -/
theorem TopOrderTwoChartAtlas.rootWeakChartCompatibility
    {N : ℕ} {c : AnalyticPointBasis N} (A : TopOrderTwoChartAtlas c)
    (w : WeakTransformIdealData c (Fin 3)) : DTwo.RootWeakChartCompatibility w where
  charts := by
    intro q hq
    have hcoordinates := A.coordinates c.root rfl q hq
    cases hpoint : A.chartPoint q with
    | none =>
      rw [hpoint] at hcoordinates
      exact Or.inr (fun i => by rw [hcoordinates.2])
    | some ζ =>
      rw [hpoint] at hcoordinates
      exact Or.inl (fun i => by
        rw [hcoordinates.2, PointedMapGerm.pullbackRingHom_identity]
        rfl)

/-- An all-component polar sum and product divisor supply a single fixed
maximal component in the general reduction package. No selected-component
or case-exclusion hypothesis is required. -/
theorem exists_generalResolutionReductionData_of_component_estimates
    (g : PointedMapGerm 2 3) {N : ℕ} (c : AnalyticPointBasis N)
    (w : WeakTransformIdealData c (Fin 3))
    (hroot : ∀ i, w.generators c.root i = g.1.component i)
    (d : AnalyticProximityData c) (A : TopOrderTwoChartAtlas c)
    (hcomplete : FiniteWeakBasepointCompleteness w)
    (hrootComplete : RootTwoChartWeakBasepointCompleteness w)
    (hdepth : ∀ p, c.ParentRelation p c.root → c.generation p = c.generation c.root + 1)
    (U : Set (Fin 3 → ℂ)) (hopen : IsOpen U) (hne : U.Nonempty)
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (R : CriticalComponentReductionData g
      (MultiplicityCounts.sum c.multiplicity) (MultiplicityCounts.squareSum c.multiplicity)
      d.proximity.branchCount U ι)
    (hcurves : ∀ q ∈ U, Nonempty (GeneralMemberCurveInvariants g c d q))
    (hterminal : ∀ q ∈ U,
      ∀ hq : ∀ p, germLinearCombination (w.generators p) q ∈ maximalIdeal 2 ^ c.multiplicity p ∧
        germLinearCombination (w.generators p) q ∉ maximalIdeal 2 ^ (c.multiplicity p + 1),
      TerminalTwoChartSingularCompleteness (w.pointBasisOfLinearCombination q hq)) :
    Nonempty (GeneralResolutionReductionData g) := by
  obtain ⟨i, _hmax, _hupper, _htwo, hmem, hM, hglobal, hdiv, hpolar⟩ :=
    R.exists_maximal_component
  refine ⟨{
    cardinality := N
    pointBasis := c
    weakData := w
    root_generators := hroot
    proximityData := d
    twoChartAtlas := A
    root_charts := A.rootWeakChartCompatibility w
    complete := hcomplete
    root_complete := hrootComplete
    root_depth := hdepth
    critical := R.component i
    exponent := R.transverseMultiplicity i
    critical_mem := hmem
    totalMultiplicity_le := hM
    global_estimate := hglobal
    common_minors := hdiv
    coefficientOpen := U
    coefficientOpen_isOpen := hopen
    coefficientOpen_nonempty := hne
    generalMemberReduction := ?_
    member_terminal_complete := hterminal }⟩
  intro q hq
  obtain ⟨C⟩ := hcurves q hq
  exact ⟨{
    companion := C.companion
    pair_finite := C.pair_finite
    pair_intersection := C.pair_intersection
    reduced := C.reduced
    isolated := C.isolated
    branches := C.branches
    genus := C.genus
    critical_finite := R.intersection_finite q hq i
    polar := hpolar q hq }⟩

end OnLeConjecture.Analytic
