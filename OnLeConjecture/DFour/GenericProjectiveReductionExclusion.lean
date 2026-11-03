/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GeneralResolutionReductionData
public import OnLeConjecture.Analytic.GenericPointBasisGeometryTransport
public import OnLeConjecture.Analytic.TargetPairLinearCompletion
public import OnLeConjecture.Analytic.JacobianLinearSpan
public import OnLeConjecture.DFour.ProjectivePointBasisAnalyticExclusion

/-!
# Quartic exclusion after generic-member selection

The selected coefficient vector lies in the reduction's prescribed open
set and has the recorded exact orders at all centers. Its analytic point
basis retains the original proximity data and projective atlas. Completeness
of the singular transforms is taken for this selected member, as specified
by the reduction data, rather than transported from a different member.

The finite companion pair determines an invertible target change. Its
second member has order at least four by the original weak-generator order.
The projective quartic theorem then constructs all needed source coordinates
and excludes the supplied reduction data.
-/

public section

namespace OnLeConjecture.DFour

open Analytic Analytic.Germ PlaneCurve

theorem quartic_excluded_of_general_resolution_reduction
    (g : PointedMapGerm 2 3) (D : GeneralResolutionReductionData g)
    (hroot : D.pointBasis.multiplicity D.pointBasis.root = 4) : False := by
  obtain ⟨q, hqU, hq, _⟩ :=
    D.weakData.exists_coefficients_exact_orders_linear_conditions_mem_open
      (fun _ : Fin 0 => (0 : (Fin 3 → ℂ) →ₗ[ℂ] ℂ))
      (fun i => Fin.elim0 i) D.coefficientOpen D.coefficientOpen_isOpen
      D.coefficientOpen_nonempty
  obtain ⟨R⟩ := D.generalMemberReduction q hqU
  obtain ⟨f, _hgf, hf0, hf1, hspan⟩ :=
    exists_target_pair_of_finite_intersection g q R.companion R.pair_finite
  let c := D.weakData.pointBasisOfLinearCombination q hq
  let d := D.weakData.proximityOfLinearCombination q hq D.proximityData
  let A := D.weakData.twoChartAtlasOfLinearCombination q hq D.twoChartAtlas
  have hmult : c.multiplicity = D.pointBasis.multiplicity := rfl
  have hrootGenerators : D.weakData.generators D.pointBasis.root = g.1.component := by
    funext i
    exact D.root_generators i
  have hmemberCombo : c.germ c.root = germLinearCombination g.1.component q := by
    change germLinearCombination (D.weakData.generators D.pointBasis.root) q = _
    rw [hrootGenerators]
  have hmember : c.germ c.root = f.1.component 0 := hmemberCombo.trans hf0.symm
  have hroot' : c.multiplicity c.root = 4 := hroot
  have hsecond : f.1.component 1 ∈ maximalIdeal 2 ^ 4 := by
    rw [hf1]
    apply germLinearCombination_mem g.1.component (maximalIdeal 2 ^ 4)
    intro i
    have hi := D.weakData.generator_mem_pow D.pointBasis.root i
    simpa only [D.root_generators, hroot] using hi
  have hfinite : HasFiniteIntersection (f.1.component 0) (f.1.component 1) := by
    simpa only [hf0, hf1] using R.pair_finite
  have hintersection : intersectionMultiplicity (f.1.component 0) (f.1.component 1) hfinite =
      Numerical.MultiplicityCounts.squareSum c.multiplicity := by
    simpa only [hf0, hf1, hmult] using R.pair_intersection
  have hcriticalFinite : HasFiniteIntersection (c.germ c.root) D.critical := by
    rw [hmemberCombo]
    exact (hasFiniteIntersection_comm _ _).mp R.critical_finite
  have hsquarefree : Squarefree (f.1.component 0) := by
    simpa only [hf0] using R.reduced
  have hnumber : intersectionMultiplicity (f.1.component 0) (f.1.component 1) hfinite +
      Numerical.MultiplicityCounts.sum c.multiplicity ≤ 3 * D.exponent := by
    rw [hintersection, hmult]
    exact D.global_estimate
  have hpolar : intersectionMultiplicity (c.germ c.root) D.critical hcriticalFinite *
      (D.exponent - 1) + Numerical.MultiplicityCounts.sum c.multiplicity +
      D.proximityData.proximity.branchCount ≤
        2 * intersectionMultiplicity (f.1.component 0) (f.1.component 1) hfinite := by
    have hcomm := intersectionMultiplicity_comm D.critical
      (germLinearCombination g.1.component q) R.critical_finite
    simpa only [hmemberCombo, hintersection, hmult, hcomm] using R.polar
  have hdiv : D.critical ^ (D.exponent - 1) ∣
      jacobian (f.1.component 0) (f.1.component 1) :=
    dvd_jacobian_of_mem_linear_span g.1.component _ D.common_minors (hspan 0) (hspan 1)
  have hsum : 4 ≤ Numerical.MultiplicityCounts.sum D.pointBasis.multiplicity := by
    rw [← hroot]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ D.pointBasis.root)
  have ht : 2 ≤ D.exponent := by have := D.totalMultiplicity_le; omega
  exact PointedMapGerm.quartic_maximal_critical_projective_data_excluded f c d
    A.projectiveSeparation (D.member_terminal_complete q hqU hq) hroot' hmember
    D.exponent D.proximityData.proximity.branchCount ht D.branchCount_pos
    D.critical D.critical_mem hcriticalFinite hsquarefree hsecond hfinite
    hintersection hnumber hpolar hdiv

theorem quartic_coordinateOrder_excluded_of_general_resolution_reduction
    (g : PointedMapGerm 2 3) (hfinite : g.IsFiniteAtOrigin)
    (D : GeneralResolutionReductionData g)
    (horder : g.coordinateOrder (by decide) hfinite = 4) : False := by
  apply quartic_excluded_of_general_resolution_reduction g D
  rw [← D.coordinateOrder_eq_root hfinite]
  exact horder

end OnLeConjecture.DFour
