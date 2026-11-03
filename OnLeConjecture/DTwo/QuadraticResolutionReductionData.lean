/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GenericPointBasisReconstruction
public import OnLeConjecture.DTwo.CommonLinearQuadraticPointBasis
public import OnLeConjecture.PlaneCurve.AnalyticBranchCount

/-!
# Imported geometric reduction data for order two

These records state actual weak transforms and general-member intersection
and polar properties. They contain no quadratic-jet classification, branch
count, special point count, or noninjectivity conclusion. Their existence is
a separate reduction/principalization input, not a theorem of this module.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

/-- Reduction data for one chosen first linear form and a companion linear
form. Independence of their coefficient vectors is not assumed. -/
structure QuadraticGeneralMemberReduction {N : ℕ}
    (g : PointedMapGerm 2 3) (multiplicity : Fin N → ℕ) (q : Fin 3 → ℂ) where
  companion : Fin 3 → ℂ
  pair_finite : PlaneCurve.HasFiniteIntersection
    (germLinearCombination g.1.component q) (germLinearCombination g.1.component companion)
  pair_intersection : PlaneCurve.intersectionMultiplicity
    (germLinearCombination g.1.component q) (germLinearCombination g.1.component companion)
      pair_finite = Numerical.MultiplicityCounts.squareSum multiplicity
  critical : Germ 2
  exponent : ℕ
  critical_mem : critical ∈ maximalIdeal 2
  totalMultiplicity_le : Numerical.MultiplicityCounts.sum multiplicity ≤ exponent
  common_minors : ∀ i j,
    critical ^ (exponent - 1) ∣ jacobian (g.1.component i) (g.1.component j)
  critical_finite : PlaneCurve.HasFiniteIntersection critical
    (germLinearCombination g.1.component q)
  polar : PlaneCurve.intersectionMultiplicity critical (germLinearCombination g.1.component q)
      critical_finite * (exponent - 1) + Numerical.MultiplicityCounts.sum multiplicity +
      PlaneCurve.irreducibleBranchCount (germLinearCombination g.1.component q) ≤
    2 * Numerical.MultiplicityCounts.squareSum multiplicity

/-- A finite weak-ideal point basis and a nonempty open set of general-member
reduction data. The root generators are the components of the specified map. -/
structure QuadraticResolutionReductionData (g : PointedMapGerm 2 3) where
  cardinality : ℕ
  pointBasis : AnalyticPointBasis cardinality
  weakData : WeakTransformIdealData pointBasis (Fin 3)
  root_generators : ∀ i, weakData.generators pointBasis.root i = g.1.component i
  root_multiplicity : pointBasis.multiplicity pointBasis.root = 2
  root_charts : RootWeakChartCompatibility weakData
  complete : FiniteWeakBasepointCompleteness weakData
  coefficientOpen : Set (Fin 3 → ℂ)
  coefficientOpen_isOpen : IsOpen coefficientOpen
  coefficientOpen_nonempty : coefficientOpen.Nonempty
  generalMemberReduction : ∀ q ∈ coefficientOpen,
    Nonempty (QuadraticGeneralMemberReduction g pointBasis.multiplicity q)

namespace QuadraticResolutionReductionData

theorem totalMultiplicity_ge_two {g : PointedMapGerm 2 3}
    (D : QuadraticResolutionReductionData g) :
    2 ≤ Numerical.MultiplicityCounts.sum D.pointBasis.multiplicity := by
  calc
    2 = D.pointBasis.multiplicity D.pointBasis.root := D.root_multiplicity.symm
    _ ≤ Numerical.MultiplicityCounts.sum D.pointBasis.multiplicity :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ D.pointBasis.root)

/-- A maximal component has exponent at least two, so its divisor supplies
a nonunit common divisor of all original coordinate minors. -/
theorem exists_common_minor_divisor {g : PointedMapGerm 2 3}
    (D : QuadraticResolutionReductionData g) :
    ∃ c : Germ 2, c ∈ maximalIdeal 2 ∧
      ∀ i j, c ∣ jacobian (g.1.component i) (g.1.component j) := by
  obtain ⟨q, hq⟩ := D.coefficientOpen_nonempty
  obtain ⟨R⟩ := D.generalMemberReduction q hq
  have ht : 2 ≤ R.exponent := D.totalMultiplicity_ge_two.trans R.totalMultiplicity_le
  refine ⟨R.critical ^ (R.exponent - 1), ?_, R.common_minors⟩
  have heq : R.exponent - 1 = (R.exponent - 2) + 1 := by omega
  rw [heq, pow_succ]
  exact (maximalIdeal 2).mul_mem_left _ R.critical_mem

end QuadraticResolutionReductionData
end OnLeConjecture.DTwo
