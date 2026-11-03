/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.MilnorDelta
public import OnLeConjecture.Analytic.RawWeakBlowupMilnorIdentity

/-!
# The delta invariant on the constructed weak-transform tree

On a finite weak-transform tree with reduced members and complete
singular children, the Milnor branch quantity of the root member is the
sum of `m (m - 1)` over the vertices. Milnor's formula identifies it with
twice the delta invariant of the root member, defined through the
normalization quotient. Adding the total multiplicity gives the square sum
of the multiplicities.
-/

public section

namespace OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree

open OnLeConjecture.Analytic.Germ PlaneCurve Numerical
open scoped BigOperators

variable {ι : Type*} [Fintype ι] {F : ι → Germ 2}

/-- For reduced members with complete singular children, twice the delta
invariant of the root member plus the total multiplicity equals the square
sum of the multiplicities. -/
theorem two_mul_deltaInvariant_add_sum_of_singular_complete
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (hsq : ∀ p, Squarefree (germLinearCombination (T.generators p) q))
    (hcomplete : ∀ (p : T.Vertex) (t : Option ℂ),
      projectiveStrictTransform (T.multiplicity p) (germLinearCombination (T.generators p) q)
        (germLinearCombination_mem _ _ (T.generator_mem p) q) t ∈ maximalIdeal 2 ^ 2 →
      ∃ r, r ≠ T.root ∧ T.predecessor r = p ∧ T.chartPoint r = t) :
    2 * deltaInvariant (germLinearCombination F q) + (∑ p, T.multiplicity p) =
      ∑ p, (T.multiplicity p) ^ 2 := by
  have hsqroot : Squarefree (germLinearCombination F q) := by
    simpa only [T.generators_root] using hsq T.root
  rw [two_mul_deltaInvariant hsqroot,
    T.milnorBranchDefect_eq_sum_of_singular_complete q hq hsq hcomplete,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (T.multiplicity_pos p).ne'
  rw [hk, Nat.succ_sub_one, Nat.succ_eq_add_one]
  ring

/-- On a nonempty open set of coefficients inside any given nonempty open
set, the members are reduced of exact ordinary order, and twice the delta
invariant of the root member plus the total multiplicity equals the square
sum of the multiplicities. -/
theorem exists_open_reduced_members_delta_identity
    (T : RawProjectiveWeakBlowupTree F) (q₀ : ι → ℂ)
    (hq₀ : ∀ p, germLinearCombination (T.generators p) q₀ ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ V : Set (ι → ℂ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∀ q ∈ V,
        (∀ p, germLinearCombination (T.generators p) q ∉
          maximalIdeal 2 ^ (T.multiplicity p + 1) ∧
          Squarefree (germLinearCombination (T.generators p) q)) ∧
        2 * deltaInvariant (germLinearCombination F q) + (∑ p, T.multiplicity p) =
          ∑ p, (T.multiplicity p) ^ 2 := by
  obtain ⟨V, hVo, hVne, hVU, hV⟩ :=
    T.exists_open_reduced_members_milnor_identity q₀ hq₀ U hU hUne
  refine ⟨V, hVo, hVne, hVU, fun q hqV => ?_⟩
  obtain ⟨hq, hb, hmilnor⟩ := hV q hqV
  refine ⟨hq, ?_⟩
  have hsqroot : Squarefree (germLinearCombination F q) := by
    simpa only [T.generators_root] using (hq T.root).2
  have hrootmem : germLinearCombination F q ∈ maximalIdeal 2 := by
    have hmem := germLinearCombination_mem _ _ (T.generator_mem T.root) q
    have hmax := Ideal.pow_le_self (T.multiplicity_pos T.root).ne' hmem
    simpa only [T.generators_root] using hmax
  have hformula := jacobianColength_add_irreducibleBranchCount hrootmem hsqroot
  rw [T.pointBasis_squareSum, T.pointBasis_sum, hb] at hmilnor
  omega

end OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree
