/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GenericCompanionSeparation
public import OnLeConjecture.Analytic.RawWeakBlowupChildIntersection
public import OnLeConjecture.Analytic.ProjectiveExceptionalIntersectionExact
public import OnLeConjecture.Analytic.ProjectiveBlowupIntersection
public import OnLeConjecture.Numerical.PointBasisCountIdentities

/-!
# Companion intersections on the constructed weak-blowup tree

The local intersection recurrence sums over the finite tree because each
nonroot vertex occurs exactly once as an immediate child.
-/

public section

namespace OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree

open OnLeConjecture.Analytic.Germ
open OnLeConjecture.Numerical
open scoped BigOperators

variable {ι : Type*} {F : ι → Germ 2}

/-- Every nonroot vertex contributes once to the sum over all child lists. -/
theorem sum_childFinset_eq_sum_erase_root
    (T : RawProjectiveWeakBlowupTree F) (I : T.Vertex → ℕ) :
    (∑ p, ∑ v ∈ T.childFinset p, I v) = ∑ v ∈ Finset.univ.erase T.root, I v := by
  classical
  simp only [childFinset, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [ite_and]
  calc
    (∑ v, ∑ p, if v ≠ T.root then if T.predecessor v = p then I v else 0 else 0) =
        ∑ v, if v ≠ T.root then I v else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v = T.root
      · simp [hv]
      · simp [hv]
    _ = _ := by
      rw [← Finset.sum_filter]
      congr 1
      ext v
      simp [and_comm]

/-- Summing local recurrences cancels every nonroot intersection term. -/
theorem root_value_eq_sum_of_child_recurrence
    (T : RawProjectiveWeakBlowupTree F) (I a : T.Vertex → ℕ)
    (hrec : ∀ p, I p = a p + ∑ v ∈ T.childFinset p, I v) :
    I T.root = ∑ p, a p := by
  classical
  have hsum : (∑ p, I p) = (∑ p, a p) + ∑ v ∈ Finset.univ.erase T.root, I v := by
    calc
      _ = ∑ p, (a p + ∑ v ∈ T.childFinset p, I v) :=
        Finset.sum_congr rfl (fun p _ => hrec p)
      _ = _ := by rw [Finset.sum_add_distrib, T.sum_childFinset_eq_sum_erase_root]
  have hroot : (∑ p, I p) = I T.root + ∑ v ∈ Finset.univ.erase T.root, I v := by
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ T.root)).symm
  omega

variable [Fintype ι]

/-- Reindexing the constructed vertices does not alter the square sum. -/
theorem pointBasis_squareSum
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1)) :
    MultiplicityCounts.squareSum (T.pointBasis q hq).multiplicity =
      ∑ p, (T.multiplicity p) ^ 2 := by
  change (∑ p, (T.multiplicity (T.indexEquiv.symm p)) ^ 2) = _
  exact T.indexEquiv.symm.sum_comp (fun p => (T.multiplicity p) ^ 2)

/-- The member at each child is the canonical projective strict transform. -/
theorem member_eq_projectiveStrictTransform
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (p v : T.Vertex) (hv : v ∈ T.childFinset p) :
    germLinearCombination (T.generators v) q =
      projectiveStrictTransform (T.multiplicity p)
        (germLinearCombination (T.generators p) q)
        (germLinearCombination_mem _ _ (T.generator_mem p) q) (T.chartPoint v) := by
  obtain ⟨hvroot, hvpred⟩ := (T.mem_childFinset p v).mp hv
  subst p
  exact T.member_eq_projective_transform q v hvroot

/-- If all common projective transforms are recorded, the original
intersection is the sum of the squared weak-ideal orders. -/
theorem companion_intersection_eq_squareSum_of_common_zero_cover
    (T : RawProjectiveWeakBlowupTree F) (q r : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (hr : ∀ p, germLinearCombination (T.generators p) r ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (hfinite : ∀ p, PlaneCurve.HasFiniteIntersection
      (germLinearCombination (T.generators p) q)
      (germLinearCombination (T.generators p) r))
    (hcover : ∀ p t,
      ¬ IsUnit (projectiveStrictTransform (T.multiplicity p)
        (germLinearCombination (T.generators p) q)
        (germLinearCombination_mem _ _ (T.generator_mem p) q) t) →
      ¬ IsUnit (projectiveStrictTransform (T.multiplicity p)
        (germLinearCombination (T.generators p) r)
        (germLinearCombination_mem _ _ (T.generator_mem p) r) t) →
      ∃ v ∈ T.childFinset p, T.chartPoint v = t) :
    PlaneCurve.intersectionMultiplicity
      (germLinearCombination (T.generators T.root) q)
      (germLinearCombination (T.generators T.root) r) (hfinite T.root) =
        MultiplicityCounts.squareSum (T.pointBasis q hq).multiplicity := by
  classical
  let I : T.Vertex → ℕ := fun p => PlaneCurve.intersectionMultiplicity
    (germLinearCombination (T.generators p) q)
    (germLinearCombination (T.generators p) r) (hfinite p)
  rw [T.pointBasis_squareSum q hq]
  apply T.root_value_eq_sum_of_child_recurrence I (fun p => (T.multiplicity p) ^ 2)
  intro p
  obtain ⟨hlocal, hrec⟩ := projectiveBlowup_intersection_recurrence_of_indexed_common_zero_cover
    (T.multiplicity p) (T.multiplicity p) (T.multiplicity_pos p) (T.multiplicity_pos p)
    (germLinearCombination (T.generators p) q) (germLinearCombination (T.generators p) r)
    (germLinearCombination_mem _ _ (T.generator_mem p) q)
    (germLinearCombination_mem _ _ (T.generator_mem p) r) (hq p) (hr p) (hfinite p)
    (T.childFinset p) T.chartPoint (T.chartPoint_injOn_childFinset p) (hcover p)
  calc
    I p = _ := hrec
    _ = (T.multiplicity p) ^ 2 + ∑ v ∈ T.childFinset p, I v := by
      rw [pow_two]
      congr 1
      apply Finset.sum_congr rfl
      intro v hv
      simp only [← T.member_eq_projectiveStrictTransform q p v hv,
        ← T.member_eq_projectiveStrictTransform r p v hv, I]

/-- Every member of exact order on the constructed tree admits a companion
in any prescribed nonempty open coefficient set whose intersection is
the square sum of the constructed point basis. -/
theorem exists_companion_intersection_eq_squareSum_mem_open
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ r ∈ U, ∃ hfinite : PlaneCurve.HasFiniteIntersection
      (germLinearCombination F q) (germLinearCombination F r),
      PlaneCurve.intersectionMultiplicity
        (germLinearCombination F q) (germLinearCombination F r) hfinite =
          MultiplicityCounts.squareSum (T.pointBasis q hq).multiplicity := by
  obtain ⟨r, hrU, hr, hfinite, hcomplete⟩ :=
    T.exists_exact_finite_companion_common_zero_complete q hq U hU hUne
  have hcover (p : T.Vertex) (t : Option ℂ)
      (hqzero : ¬ IsUnit (projectiveStrictTransform (T.multiplicity p)
        (germLinearCombination (T.generators p) q)
        (germLinearCombination_mem _ _ (T.generator_mem p) q) t))
      (hrzero : ¬ IsUnit (projectiveStrictTransform (T.multiplicity p)
        (germLinearCombination (T.generators p) r)
        (germLinearCombination_mem _ _ (T.generator_mem p) r) t)) :
      ∃ v ∈ T.childFinset p, T.chartPoint v = t := by
    obtain ⟨v, hv, hpred, hchart⟩ := hcomplete p t _ _
      (pointBlowupTransform_factor _ _ _
        ((projectiveChartSource t).forward.pullback_mem_maximalIdeal_pow
          (germLinearCombination_mem _ _ (T.generator_mem p) q)))
      (pointBlowupTransform_factor _ _ _
        ((projectiveChartSource t).forward.pullback_mem_maximalIdeal_pow
          (germLinearCombination_mem _ _ (T.generator_mem p) r)))
      (by simpa only [mem_maximalIdeal_iff, isUnit_iff_valueRingHom_ne_zero, not_not,
          projectiveStrictTransform]
        using hqzero)
      (by simpa only [mem_maximalIdeal_iff, isUnit_iff_valueRingHom_ne_zero, not_not,
          projectiveStrictTransform]
        using hrzero)
    exact ⟨v, (T.mem_childFinset p v).mpr ⟨hv, hpred⟩, hchart⟩
  have hroot : PlaneCurve.HasFiniteIntersection
      (germLinearCombination F q) (germLinearCombination F r) := by
    simpa only [T.generators_root] using hfinite T.root
  refine ⟨r, hrU, hroot, ?_⟩
  simpa only [T.generators_root] using
    T.companion_intersection_eq_squareSum_of_common_zero_cover q r hq hr hfinite hcover

end OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree
