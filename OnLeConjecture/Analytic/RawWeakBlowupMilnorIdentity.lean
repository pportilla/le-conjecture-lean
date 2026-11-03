/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.MilnorBlowupRecurrence
public import OnLeConjecture.Analytic.RawWeakBlowupBranchExcess
public import OnLeConjecture.Analytic.RawWeakBlowupCompanionIntersection

/-!
# The Milnor identity on the constructed weak-transform tree

The local blowup formula for μ + b - 1 telescopes on the finite tree.
Unrecorded transforms are smooth or units and contribute zero. On the
constructed open coefficient set, the branch/excess identity and exact
ordinary orders therefore give the global Milnor formula.
-/

public section

namespace OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree

open OnLeConjecture.Analytic.Germ PlaneCurve Numerical
open scoped BigOperators

variable {ι : Type*} [Fintype ι] {F : ι → Germ 2}

/-- The indexed point basis has the same total multiplicity as the
constructed vertex type. -/
theorem pointBasis_sum
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1)) :
    MultiplicityCounts.sum (T.pointBasis q hq).multiplicity = ∑ p, T.multiplicity p := by
  change (∑ p, T.multiplicity (T.indexEquiv.symm p)) = _
  exact T.indexEquiv.symm.sum_comp T.multiplicity

/-- The Milnor branch quantity at the root is the sum of `m * (m - 1)`
over all recorded vertices. -/
theorem milnorBranchDefect_eq_sum_of_singular_complete
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (hsq : ∀ p, Squarefree (germLinearCombination (T.generators p) q))
    (hcomplete : ∀ (p : T.Vertex) (t : Option ℂ),
      projectiveStrictTransform (T.multiplicity p) (germLinearCombination (T.generators p) q)
        (germLinearCombination_mem _ _ (T.generator_mem p) q) t ∈ maximalIdeal 2 ^ 2 →
      ∃ r, r ≠ T.root ∧ T.predecessor r = p ∧ T.chartPoint r = t) :
    milnorBranchDefect (germLinearCombination F q) =
      ∑ p, T.multiplicity p * (T.multiplicity p - 1) := by
  classical
  have hroot : milnorBranchDefect (germLinearCombination F q) =
      milnorBranchDefect (germLinearCombination (T.generators T.root) q) := by
    rw [T.generators_root]
  rw [hroot]
  apply T.root_value_eq_sum_of_child_recurrence
    (fun p => milnorBranchDefect (germLinearCombination (T.generators p) q))
    (fun p => T.multiplicity p * (T.multiplicity p - 1))
  intro p
  have hrec := projectiveStrictTransform_milnorBranchDefect_recurrence_of_indexed_singular_cover
    (T.multiplicity p) (T.multiplicity_pos p)
    (germLinearCombination (T.generators p) q)
    (germLinearCombination_mem _ _ (T.generator_mem p) q) (hq p) (hsq p)
    (T.childFinset p) T.chartPoint (T.chartPoint_injOn_childFinset p) (by
      intro t ht
      obtain ⟨r, hr, hp, hchart⟩ := hcomplete p t ht
      exact ⟨r, (T.mem_childFinset p r).mpr ⟨hr, hp⟩, hchart⟩)
  rw [hrec]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [← T.member_eq_projectiveStrictTransform q p r hr]

/-- The total multiplicity restores the square sum from the Milnor
branch quantity. -/
theorem squareSum_eq_milnorBranchDefect_add_sum_of_singular_complete
    (T : RawProjectiveWeakBlowupTree F) (q₀ q : ι → ℂ)
    (hq₀ : ∀ p, germLinearCombination (T.generators p) q₀ ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (hsq : ∀ p, Squarefree (germLinearCombination (T.generators p) q))
    (hcomplete : ∀ (p : T.Vertex) (t : Option ℂ),
      projectiveStrictTransform (T.multiplicity p) (germLinearCombination (T.generators p) q)
        (germLinearCombination_mem _ _ (T.generator_mem p) q) t ∈ maximalIdeal 2 ^ 2 →
      ∃ r, r ≠ T.root ∧ T.predecessor r = p ∧ T.chartPoint r = t) :
    MultiplicityCounts.squareSum (T.pointBasis q₀ hq₀).multiplicity =
      milnorBranchDefect (germLinearCombination F q) +
        MultiplicityCounts.sum (T.pointBasis q₀ hq₀).multiplicity := by
  rw [T.pointBasis_squareSum, T.pointBasis_sum,
    T.milnorBranchDefect_eq_sum_of_singular_complete q hq hsq hcomplete,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  have hm : T.multiplicity p - 1 + 1 = T.multiplicity p :=
    Nat.sub_add_cancel (T.multiplicity_pos p)
  calc
    (T.multiplicity p) ^ 2 = T.multiplicity p * T.multiplicity p := by ring
    _ = T.multiplicity p * (T.multiplicity p - 1 + 1) := by rw [hm]
    _ = _ := by ring

/-- A nonempty open coefficient set with exact reduced members, the
branch/excess identity, and the full Milnor identity is constructed from
the finite weak-transform tree. -/
theorem exists_open_reduced_members_milnor_identity
    (T : RawProjectiveWeakBlowupTree F) (q₀ : ι → ℂ)
    (hq₀ : ∀ p, germLinearCombination (T.generators p) q₀ ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ V : Set (ι → ℂ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∀ q ∈ V,
        (∀ p, germLinearCombination (T.generators p) q ∉
          maximalIdeal 2 ^ (T.multiplicity p + 1) ∧
          Squarefree (germLinearCombination (T.generators p) q)) ∧
        (T.analyticProximityData q₀ hq₀).proximity.branchCount =
          irreducibleBranchCount (germLinearCombination F q) ∧
        MultiplicityCounts.squareSum (T.pointBasis q₀ hq₀).multiplicity + 1 =
          Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal (germLinearCombination F q)) +
            MultiplicityCounts.sum (T.pointBasis q₀ hq₀).multiplicity +
            (T.analyticProximityData q₀ hq₀).proximity.branchCount := by
  obtain ⟨W, hWo, hWne, hWU, hW⟩ :=
    T.exists_open_reduced_members_indexed_branch_excess q₀ hq₀ U hU hUne
  obtain ⟨V, hVo, hVne, hVW, hV⟩ := T.exists_open_member_singular_complete W hWo hWne
  refine ⟨V, hVo, hVne, hVW.trans hWU, ?_⟩
  intro q hqV
  obtain ⟨hq, hb⟩ := hW q (hVW hqV)
  obtain ⟨_, hcomplete⟩ := hV q hqV
  refine ⟨hq, hb, ?_⟩
  have hsqsum := T.squareSum_eq_milnorBranchDefect_add_sum_of_singular_complete q₀ q hq₀
    (fun p => (hq p).1) (fun p => (hq p).2) (by
      intro p t ht
      exact hcomplete p t _ (pointBlowupTransform_factor _ _ _ _) ht)
  have hrootne : germLinearCombination F q ≠ 0 := by
    simpa only [T.generators_root] using (hq T.root).2.ne_zero
  have hrootmem : germLinearCombination F q ∈ maximalIdeal 2 := by
    have hmem := germLinearCombination_mem _ _ (T.generator_mem T.root) q
    have hmax := Ideal.pow_le_self (T.multiplicity_pos T.root).ne' hmem
    simpa only [T.generators_root] using hmax
  have hrootunit : ¬ IsUnit (germLinearCombination F q) := by
    intro hu
    exact (valueRingHom_ne_zero_of_isUnit hu) (mem_maximalIdeal_iff.mp hrootmem)
  have hdefect := milnorBranchDefect_add_one (germLinearCombination F q) hrootne hrootunit
  rw [← hb] at hdefect
  omega

end OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree
