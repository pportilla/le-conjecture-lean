/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.QuadraticMilnorReductionData
public import OnLeConjecture.Analytic.ProjectiveFixedTangentGenericAvoidance
public import OnLeConjecture.Analytic.ProjectivePointBasisCompleteness
public import OnLeConjecture.Analytic.WeakPointBasisCoordinateOrder
public import OnLeConjecture.Numerical.PositiveProximityBranchCount

/-!
# The common reduction and principalization input

The critical equation and its transverse exponent are fixed before any
general member is chosen. The open coefficient set supplies the reduced
member, companion intersection, branch and Milnor identities, and polar
estimate. Completeness of singular transforms is required for each chosen
member, not transferred from a different member.

This module records the input from the reduction and generic principalization
statements. It does not assert their existence. No special multiplicity,
critical smoothness, prepared equation, or case exclusion is a field.
-/

public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ PlaneCurve Numerical

/-- The curve and intersection assertions for a specified general coefficient
row, with the critical component fixed independently of that row. -/
structure GeneralMemberCurveReduction {N : ℕ}
    (g : PointedMapGerm 2 3) (c : AnalyticPointBasis N)
    (d : AnalyticProximityData c) (h : Germ 2) (t : ℕ) (q : Fin 3 → ℂ) where
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
  critical_finite : HasFiniteIntersection h (germLinearCombination g.1.component q)
  polar : intersectionMultiplicity h (germLinearCombination g.1.component q)
      critical_finite * (t - 1) + MultiplicityCounts.sum c.multiplicity +
        d.proximity.branchCount ≤ 2 * MultiplicityCounts.squareSum c.multiplicity

/-- Actual weak transforms, projective charts and the common numerical
reduction, with a nonempty open set of admissible general members. -/
structure GeneralResolutionReductionData (g : PointedMapGerm 2 3) where
  cardinality : ℕ
  pointBasis : AnalyticPointBasis cardinality
  weakData : WeakTransformIdealData pointBasis (Fin 3)
  root_generators : ∀ i, weakData.generators pointBasis.root i = g.1.component i
  proximityData : AnalyticProximityData pointBasis
  twoChartAtlas : TopOrderTwoChartAtlas pointBasis
  root_charts : DTwo.RootWeakChartCompatibility weakData
  complete : FiniteWeakBasepointCompleteness weakData
  root_complete : RootTwoChartWeakBasepointCompleteness weakData
  root_depth : ∀ p, pointBasis.ParentRelation p pointBasis.root →
    pointBasis.generation p = pointBasis.generation pointBasis.root + 1
  critical : Germ 2
  exponent : ℕ
  critical_mem : critical ∈ maximalIdeal 2
  totalMultiplicity_le : MultiplicityCounts.sum pointBasis.multiplicity ≤ exponent
  global_estimate : MultiplicityCounts.squareSum pointBasis.multiplicity +
    MultiplicityCounts.sum pointBasis.multiplicity ≤ 3 * exponent
  common_minors : ∀ i j, critical ^ (exponent - 1) ∣ jacobian (g.1.component i) (g.1.component j)
  coefficientOpen : Set (Fin 3 → ℂ)
  coefficientOpen_isOpen : IsOpen coefficientOpen
  coefficientOpen_nonempty : coefficientOpen.Nonempty
  generalMemberReduction : ∀ q ∈ coefficientOpen,
    Nonempty (GeneralMemberCurveReduction g pointBasis proximityData critical exponent q)
  member_terminal_complete : ∀ q ∈ coefficientOpen,
    ∀ hq : ∀ p,
      germLinearCombination (weakData.generators p) q ∈ maximalIdeal 2 ^ pointBasis.multiplicity p ∧
        germLinearCombination (weakData.generators p) q ∉
          maximalIdeal 2 ^ (pointBasis.multiplicity p + 1),
      TerminalTwoChartSingularCompleteness (weakData.pointBasisOfLinearCombination q hq)

namespace GeneralResolutionReductionData

theorem coordinateOrder_eq_root {g : PointedMapGerm 2 3}
    (D : GeneralResolutionReductionData g) (hfinite : g.IsFiniteAtOrigin) :
    g.coordinateOrder (by decide) hfinite = D.pointBasis.multiplicity D.pointBasis.root :=
  D.weakData.coordinateOrder_eq_root_multiplicity g hfinite D.root_generators

theorem branchCount_pos {g : PointedMapGerm 2 3} (D : GeneralResolutionReductionData g) :
    0 < D.proximityData.proximity.branchCount := by
  apply D.proximityData.proximity.branchCount_pos_of_positive_and_generation
    D.pointBasis.generation D.proximityData.generation_decreases
  intro p
  rw [D.proximityData.multiplicity_eq]
  exact D.pointBasis.multiplicity_pos p

/-- Specialization to root order two retains the actual generic members
and their complete curve invariants. -/
@[expose] noncomputable def toQuadraticMilnorReductionData
    {g : PointedMapGerm 2 3} (D : GeneralResolutionReductionData g)
    (hroot : D.pointBasis.multiplicity D.pointBasis.root = 2) :
    DTwo.QuadraticMilnorReductionData g where
  cardinality := D.cardinality
  pointBasis := D.pointBasis
  weakData := D.weakData
  root_generators := D.root_generators
  root_multiplicity := hroot
  root_charts := D.root_charts
  complete := D.complete
  coefficientOpen := D.coefficientOpen
  coefficientOpen_isOpen := D.coefficientOpen_isOpen
  coefficientOpen_nonempty := D.coefficientOpen_nonempty
  generalMemberReduction q hq := by
    obtain ⟨R⟩ := D.generalMemberReduction q hq
    exact ⟨{
      companion := R.companion
      pair_finite := R.pair_finite
      pair_intersection := R.pair_intersection
      critical := D.critical
      exponent := D.exponent
      critical_mem := D.critical_mem
      totalMultiplicity_le := D.totalMultiplicity_le
      common_minors := D.common_minors
      critical_finite := R.critical_finite
      polar := by simpa only [R.branches] using R.polar }⟩
  proximityData := D.proximityData
  member_reduced q hq := (Classical.choice (D.generalMemberReduction q hq)).reduced
  member_isolated q hq := (Classical.choice (D.generalMemberReduction q hq)).isolated
  branchCount_eq q hq := (Classical.choice (D.generalMemberReduction q hq)).branches
  genus_identity q hq := (Classical.choice (D.generalMemberReduction q hq)).genus

end GeneralResolutionReductionData

end OnLeConjecture.Analytic
