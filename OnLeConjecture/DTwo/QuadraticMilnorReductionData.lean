/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.QuadraticResolutionReductionData
public import OnLeConjecture.Analytic.ProximityTopOrderChain
public import OnLeConjecture.PlaneCurve.Milnor

/-!
# The general-member curve invariants in the quadratic reduction

This extends the imported weak-ideal and polar reduction data by matched
proximity and the reduced generic member's Milnor and branch identities.
The genus formula is stated with the full point-basis sums. No quadratic
normal form, exponent, parity, or special point count is a field.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ PlaneCurve

structure QuadraticMilnorReductionData (g : PointedMapGerm 2 3)
    extends QuadraticResolutionReductionData g where
  proximityData : AnalyticProximityData pointBasis
  member_reduced : ∀ q ∈ coefficientOpen, Squarefree (germLinearCombination g.1.component q)
  member_isolated : ∀ q ∈ coefficientOpen,
    HasIsolatedCriticalPoint (germLinearCombination g.1.component q)
  branchCount_eq : ∀ q ∈ coefficientOpen,
    proximityData.proximity.branchCount =
      irreducibleBranchCount (germLinearCombination g.1.component q)
  genus_identity : ∀ q (hq : q ∈ coefficientOpen),
    Numerical.MultiplicityCounts.squareSum pointBasis.multiplicity + 1 =
      milnorNumber (germLinearCombination g.1.component q) (member_isolated q hq) +
        Numerical.MultiplicityCounts.sum pointBasis.multiplicity +
          proximityData.proximity.branchCount

end OnLeConjecture.DTwo
