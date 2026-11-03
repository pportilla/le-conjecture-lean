/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CriticalJacobianDivisor
public import OnLeConjecture.Analytic.ConstructedResolutionReduction

/-!
# Reduction to two bounds on the common Jacobian divisor

The coordinate minors determine a nonzero greatest common divisor for an
injective plane germ. Its irreducible factor orders define a finite maximum.
If that maximum satisfies the two displayed bounds on the constructed
weak-transform tree, a factor attaining it supplies the critical equation
in the reduction. All curve, resolution, divisor, and polar data are then
constructed internally.

The two bounds are hypotheses in this file. They are not consequences of
unique factorization, and no geometric interpretation of the factor orders
is assumed or proved here.
-/

public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ Numerical
open scoped BigOperators

/-- A factor attaining the maximal common-minor order supplies the divisor
estimate record whenever its two numerical bounds are given. -/
theorem CriticalJacobianFactorization.exists_estimate_data
    {g : PointedMapGerm 2 3} (D : CriticalJacobianFactorization g)
    (M S : ℕ) (hMpos : 0 < M)
    (hM : M ≤ D.maxMultiplicity) (hglobal : S + M ≤ 3 * D.maxMultiplicity) :
    Nonempty (CriticalDivisorEstimateData g M S (Fin 1)) := by
  classical
  obtain ⟨p, hp, heq⟩ := D.exists_order_add_one_eq_maxMultiplicity (hMpos.trans_le hM)
  refine ⟨{
    component := fun _ => p
    transverseMultiplicity := fun _ => D.order p + 1
    component_mem := fun _ => D.component_mem p hp
    two_le_multiplicity := fun _ => by have h := D.order_pos p hp; omega
    total_le_max := ?_
    global_estimate := ?_
    product_dvd_ordered_minors := ?_ }⟩
  · simpa [heq] using hM
  · simpa [heq] using hglobal
  · intro j k _hjk
    simpa using D.pow_dvd_minors p hp j k

/-- The two bounds on the factorization of the common Jacobian divisor
construct every remaining input to the case proofs. -/
theorem exists_constructedResolutionRemainingData_of_criticalJacobian_bounds
    (g : PointedMapGerm 2 3) (hdifferential : g.differential = 0)
    (hinjective : g.HasInjectiveRepresentative)
    (T : RawProjectiveWeakBlowupTree g.1.component) (q₀ : Fin 3 → ℂ)
    (hq₀ : ∀ p, germLinearCombination (T.generators p) q₀ ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (hM : (∑ p, T.multiplicity p) ≤
      (g.criticalJacobianFactorization hinjective).maxMultiplicity)
    (hglobal : (∑ p, (T.multiplicity p) ^ 2) + (∑ p, T.multiplicity p) ≤
      3 * (g.criticalJacobianFactorization hinjective).maxMultiplicity) :
    Nonempty (ConstructedResolutionRemainingData g hdifferential T q₀ hq₀) := by
  classical
  have hMpos : 0 < ∑ p, T.multiplicity p :=
    (T.multiplicity_pos T.root).trans_le
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ T.root))
  obtain ⟨D⟩ := (g.criticalJacobianFactorization hinjective).exists_estimate_data
    (∑ p, T.multiplicity p) (∑ p, (T.multiplicity p) ^ 2) hMpos hM hglobal
  refine ⟨{
    componentCardinality := 1
    componentCardinality_pos := by omega
    components := ?_ }⟩
  rw [T.pointBasis_sum q₀ hq₀, T.pointBasis_squareSum q₀ hq₀]
  exact D

end OnLeConjecture.Analytic

namespace OnLeConjecture

open Analytic
open scoped BigOperators

/-- Conditional reduction of Lê's conjecture to two explicit inequalities
for the common Jacobian divisor. The inequalities remain unproved. -/
theorem leConjecture_of_criticalJacobian_bounds
    (hbounds : ∀ (g : PointedMapGerm 2 3), g.differential = 0 →
      ∀ hinjective : g.HasInjectiveRepresentative,
      ∀ T : RawProjectiveWeakBlowupTree g.1.component,
      (∑ p, T.multiplicity p) ≤
          (g.criticalJacobianFactorization hinjective).maxMultiplicity ∧
        (∑ p, (T.multiplicity p) ^ 2) + (∑ p, T.multiplicity p) ≤
          3 * (g.criticalJacobianFactorization hinjective).maxMultiplicity) :
    LeConjecture := by
  apply leConjecture_of_constructed_resolution_remaining_estimates
  intro g hdifferential hinjective T q₀ hq₀
  obtain ⟨hM, hglobal⟩ := hbounds g hdifferential hinjective T
  exact exists_constructedResolutionRemainingData_of_criticalJacobian_bounds
    g hdifferential hinjective T q₀ hq₀ hM hglobal

end OnLeConjecture
