/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GeneralResolutionReductionData
public import OnLeConjecture.Analytic.TargetPairLinearCompletion
public import OnLeConjecture.Analytic.JacobianLinearSpan
public import OnLeConjecture.DThree.TwoChartPointBasisAnalyticExclusion

/-!
# Cubic exclusion from the common reduction data

The critical equation is fixed by the reduction record before selecting
the general member. A coefficient vector is chosen inside the given open
set with exact orders and projective tangent avoidance. Finite intersection
constructs an invertible target change retaining the member and companion.
The analytic point basis is reconstructed from the chosen coefficients.
-/

public section

namespace OnLeConjecture.DThree

open Analytic Analytic.Germ

theorem cubic_excluded_of_general_resolution_reduction
    (g : PointedMapGerm 2 3) (D : GeneralResolutionReductionData g)
    (hroot : D.pointBasis.multiplicity D.pointBasis.root = 3) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨q, hqU, hq, havoid⟩ :=
    D.weakData.exists_coefficients_exact_orders_projective_tangent_avoidance_mem_open
      (fun _ : Unit => criticalProjectiveTangent D.critical)
      D.coefficientOpen D.coefficientOpen_isOpen D.coefficientOpen_nonempty
  obtain ⟨R⟩ := D.generalMemberReduction q hqU
  obtain ⟨F, hGF, hFzero, hFone, hFspan⟩ :=
    exists_target_pair_of_finite_intersection g q R.companion R.pair_finite
  let c := D.weakData.pointBasisOfLinearCombination q hq
  let d := D.weakData.proximityOfLinearCombination q hq D.proximityData
  let w := D.weakData.weakDataOfLinearCombination q hq
  have hgenerators : D.weakData.generators D.pointBasis.root = g.1.component :=
    funext D.root_generators
  have hcomponent : c.germ c.root = F.1.component 0 := by
    change germLinearCombination (D.weakData.generators D.pointBasis.root) q = _
    rw [hgenerators, hFzero]
  have hFfinite : PlaneCurve.HasFiniteIntersection (F.1.component 0) (F.1.component 1) := by
    simpa only [hFzero, hFone] using R.pair_finite
  have hFintersection : PlaneCurve.intersectionMultiplicity
      (F.1.component 0) (F.1.component 1) hFfinite =
        Numerical.MultiplicityCounts.squareSum c.multiplicity := by
    change PlaneCurve.intersectionMultiplicity
      (F.1.component 0) (F.1.component 1) hFfinite =
        Numerical.MultiplicityCounts.squareSum D.pointBasis.multiplicity
    simpa only [hFzero, hFone] using R.pair_intersection
  have hFnumber : PlaneCurve.intersectionMultiplicity
      (F.1.component 0) (F.1.component 1) hFfinite +
        Numerical.MultiplicityCounts.sum c.multiplicity ≤ 3 * D.exponent := by
    rw [hFintersection]
    exact D.global_estimate
  have hFsecond : F.1.component 1 ∈ maximalIdeal 2 ^ 3 := by
    rw [hFone]
    apply germLinearCombination_mem _ _ (fun i => ?_) R.companion
    simpa only [D.root_generators, hroot] using
      D.weakData.generator_mem_pow D.pointBasis.root i
  have hcriticalFinite : PlaneCurve.HasFiniteIntersection D.critical (c.germ c.root) := by
    change PlaneCurve.HasFiniteIntersection D.critical
      (germLinearCombination (D.weakData.generators D.pointBasis.root) q)
    simpa only [hgenerators] using R.critical_finite
  have hpolar : PlaneCurve.intersectionMultiplicity D.critical (c.germ c.root)
        hcriticalFinite * (D.exponent - 1) +
      d.proximity.totalMultiplicity + d.proximity.branchCount ≤
        2 * d.proximity.squareMultiplicity := by
    change PlaneCurve.intersectionMultiplicity D.critical
        (germLinearCombination (D.weakData.generators D.pointBasis.root) q)
          hcriticalFinite * (D.exponent - 1) +
      D.proximityData.proximity.totalMultiplicity + D.proximityData.proximity.branchCount ≤
        2 * D.proximityData.proximity.squareMultiplicity
    simpa only [hgenerators, Numerical.ProximityCertificate.totalMultiplicity,
      Numerical.ProximityCertificate.squareMultiplicity, D.proximityData.multiplicity_eq,
      Numerical.MultiplicityCounts.sum] using R.polar
  have hrootle : D.pointBasis.multiplicity D.pointBasis.root ≤
      Numerical.MultiplicityCounts.sum D.pointBasis.multiplicity := by
    exact Finset.single_le_sum (fun p _ => Nat.zero_le (D.pointBasis.multiplicity p))
      (Finset.mem_univ D.pointBasis.root)
  have ht : 2 ≤ D.exponent := by
    have htotal := D.totalMultiplicity_le
    omega
  have hFdiv : ∀ i j : Fin 3, i < j → D.critical ^ (D.exponent - 1) ∣
      jacobian (F.1.component i) (F.1.component j) := by
    intro i j _
    exact dvd_jacobian_of_mem_linear_span g.1.component _ D.common_minors
      (hFspan i) (hFspan j)
  have hnot := PointedMapGerm.not_hasInjectiveRepresentative_of_cubic_twoChart_point_basis
    F c d
    (D.weakData.projectiveSeparation_linearCombination q hq D.twoChartAtlas.projectiveSeparation)
    hroot hcomponent w
    (D.weakData.rootTwoChartWeakBasepointCompleteness_linearCombination q hq D.root_complete)
    q rfl D.root_depth D.exponent ht D.branchCount_pos D.critical D.critical_mem
    (D.weakData.avoidsRootProjectiveTangentCancellation_linearCombination q hq
      (criticalProjectiveTangent D.critical) (havoid ()))
    hcriticalFinite hpolar (by simpa only [hFzero] using R.reduced)
    hFsecond hFfinite hFintersection hFnumber hFdiv
  exact fun hg => hnot (hGF.hasInjectiveRepresentative hg)

theorem cubic_coordinateOrder_excluded_of_general_resolution_reduction
    (g : PointedMapGerm 2 3) (D : GeneralResolutionReductionData g)
    (hfinite : g.IsFiniteAtOrigin)
    (horder : g.coordinateOrder (by decide) hfinite = 3) :
    ¬ g.HasInjectiveRepresentative := by
  apply cubic_excluded_of_general_resolution_reduction g D
  rw [← D.coordinateOrder_eq_root hfinite]
  exact horder

end OnLeConjecture.DThree
