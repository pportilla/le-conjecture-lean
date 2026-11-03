/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RawWeakBlowupGenericTransversality
public import OnLeConjecture.Analytic.ProjectiveExceptionalIntersectionExact

/-!
# Local excess and unrecorded transverse branches

The projective exceptional intersection identity splits into contributions
from recorded children and from unrecorded nonunit transforms. For the
constructed open coefficient set, each latter contribution is one. Exact
proximity accounting identifies their number with the local excess.
-/

public section

namespace OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree

open OnLeConjecture.Analytic.Germ
open scoped BigOperators

variable {ι : Type*} [Fintype ι] {F : ι → Germ 2}

theorem projectiveMemberTransform_eq_projectiveStrictTransform
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ) (p : T.Vertex) (t : Option ℂ) :
    T.projectiveMemberTransform q p t =
      projectiveStrictTransform (T.multiplicity p) (germLinearCombination (T.generators p) q)
        (germLinearCombination_mem _ _ (T.generator_mem p) q) t := by
  exact pointBlowupTransform_unique _ _ _ _ _
    (T.projectiveMemberTransform_factor q p t) (pointBlowupTransform_factor _ _ _ _)

theorem member_mem_maximalIdeal
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ) (p : T.Vertex) :
    germLinearCombination (T.generators p) q ∈ maximalIdeal 2 := by
  simpa only [pow_one] using
    (Ideal.pow_le_pow_right (T.multiplicity_pos p))
      (germLinearCombination_mem _ _ (T.generator_mem p) q)

/-- The unrecorded nonunit projective transforms form a finite set.
Its cardinality is the difference between the parent order and the sum
of its children's exceptional intersection orders. -/
theorem exists_unrecorded_branches_local_intersection
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ) (p : T.Vertex)
    (hq : germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (htransverse : ∀ t, t ∉ (T.childFinset p).image T.chartPoint →
      ¬ IsUnit (T.projectiveMemberTransform q p t) →
      (vanishingOrder (pointBlowupExceptionalLine.pullbackRingHom
        (T.projectiveMemberTransform q p t))).toNat = 1 ∧
      PlaneCurve.irreducibleBranchCount (T.projectiveMemberTransform q p t) = 1) :
    ∃ R : Finset (Option ℂ),
      (∀ t, t ∈ R ↔ t ∉ (T.childFinset p).image T.chartPoint ∧
        ¬ IsUnit (T.projectiveMemberTransform q p t)) ∧
      T.multiplicity p = (∑ r ∈ T.childFinset p, T.newestAxisOrder q r) + R.card ∧
      ∀ t ∈ R, PlaneCurve.irreducibleBranchCount (T.projectiveMemberTransform q p t) = 1 := by
  classical
  let f := germLinearCombination (T.generators p) q
  have hf : f ∈ maximalIdeal 2 ^ T.multiplicity p :=
    germLinearCombination_mem _ _ (T.generator_mem p) q
  let b := projectiveExceptionalIntersectionOrder (T.multiplicity p) f hf
  let D := (T.childFinset p).image T.chartPoint
  obtain ⟨s, hscover, hsum⟩ := exists_projective_exceptional_orders_sum_eq
    (T.multiplicity p) f hf hq
  have hstrict (t : Option ℂ) : T.projectiveMemberTransform q p t =
      projectiveStrictTransform (T.multiplicity p) f hf t :=
    T.projectiveMemberTransform_eq_projectiveStrictTransform q p t
  have hcover (t : Option ℂ) (ht : ¬ IsUnit (T.projectiveMemberTransform q p t)) : t ∈ s := by
    apply hscover
    rw [← hstrict, mem_maximalIdeal_iff]
    by_contra hz
    exact ht (isUnit_of_valueRingHom_ne_zero hz)
  have hDunit (t : Option ℂ) (ht : t ∈ D) :
      ¬ IsUnit (T.projectiveMemberTransform q p t) := by
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ht
    rw [T.projectiveMemberTransform_eq_child q p r hr]
    intro hunit
    exact valueRingHom_ne_zero_of_isUnit hunit
      (mem_maximalIdeal_iff.mp (T.member_mem_maximalIdeal q r))
  have hDs : D ⊆ s := fun t ht => hcover t (hDunit t ht)
  let R := s.filter fun t => t ∉ D ∧ ¬ IsUnit (T.projectiveMemberTransform q p t)
  have hR (t : Option ℂ) : t ∈ R ↔ t ∉ D ∧
      ¬ IsUnit (T.projectiveMemberTransform q p t) := by
    simp only [R, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hcover t h.2, h⟩⟩
  have hchild : ∑ t ∈ D, b t = ∑ r ∈ T.childFinset p, T.newestAxisOrder q r := by
    rw [Finset.sum_image (T.chartPoint_injOn_childFinset p)]
    apply Finset.sum_congr rfl
    intro r hr
    change (vanishingOrder (pointBlowupExceptionalLine.pullbackRingHom
      (projectiveStrictTransform (T.multiplicity p) f hf (T.chartPoint r)))).toNat = _
    rw [← hstrict, T.projectiveMemberTransform_eq_child q p r hr]
    simp only [newestAxisOrder, pointBlowupExceptionalLine_eq_lineGerm]
    rfl
  have hrest : ∑ t ∈ s \ D, b t = R.card := by
    have hsumR : ∑ t ∈ R, b t = R.card := by
      calc
        _ = ∑ _t ∈ R, 1 := by
          apply Finset.sum_congr rfl
          intro t ht
          have h := htransverse t ((hR t).mp ht).1 ((hR t).mp ht).2
          change (vanishingOrder (pointBlowupExceptionalLine.pullbackRingHom
            (projectiveStrictTransform (T.multiplicity p) f hf t))).toNat = 1
          rw [← hstrict]
          exact h.1
        _ = _ := by simp
    rw [← hsumR]
    symm
    apply Finset.sum_subset
    · intro t ht
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp ht).1, ((hR t).mp ht).1⟩
    · intro t ht hn
      have hunit : IsUnit (T.projectiveMemberTransform q p t) := by
        by_contra hnu
        exact hn ((hR t).mpr ⟨(Finset.mem_sdiff.mp ht).2, hnu⟩)
      exact projectiveExceptionalIntersectionOrder_eq_zero_of_isUnit _ _ hf t
        ((hstrict t) ▸ hunit)
  refine ⟨R, hR, ?_, fun t ht => (htransverse t ((hR t).mp ht).1 ((hR t).mp ht).2).2⟩
  have hsplit := Finset.sum_sdiff hDs (f := b)
  change (∑ t ∈ s, b t) = T.multiplicity p at hsum
  rw [hchild, hrest] at hsplit
  omega

/-- One open coefficient set realizes every local excess as the number
of unrecorded smooth transverse branches at that vertex. -/
theorem exists_open_local_excess_branch_counts
    (T : RawProjectiveWeakBlowupTree F)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ V : Set (ι → ℂ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∀ q ∈ V,
        (∀ p, germLinearCombination (T.generators p) q ∉
          maximalIdeal 2 ^ (T.multiplicity p + 1)) ∧
        ∀ p, ∃ R : Finset (Option ℂ),
          (∀ t, t ∈ R ↔ t ∉ (T.childFinset p).image T.chartPoint ∧
            ¬ IsUnit (T.projectiveMemberTransform q p t)) ∧
          T.proximityCertificate.excess p = R.card ∧
          ∀ t ∈ R, PlaneCurve.irreducibleBranchCount (T.projectiveMemberTransform q p t) = 1 := by
  obtain ⟨W, hWopen, hWne, hWU, hW⟩ := T.exists_open_unrecorded_transverse_members U hU hUne
  obtain ⟨V, hVopen, hVne, hVW, hV⟩ := T.exists_open_exact_proximity_intersections W hWopen hWne
  refine ⟨V, hVopen, hVne, hVW.trans hWU, ?_⟩
  intro q hq
  obtain ⟨hqexact, hproximity⟩ := hV q hq
  refine ⟨hqexact, ?_⟩
  intro p
  obtain ⟨R, hR, hlocal, hbranches⟩ := T.exists_unrecorded_branches_local_intersection
    q p (hqexact p) ((hW q (hVW hq)).2 p)
  refine ⟨R, hR, ?_, hbranches⟩
  have hprox := hproximity p
  change (∑ r ∈ Finset.univ.filter (fun r => p ∈ T.rootedChartData.parents r),
    T.multiplicity r) = _ at hprox
  change T.multiplicity p - (∑ r ∈ Finset.univ.filter
    (fun r => p ∈ T.rootedChartData.parents r), T.multiplicity r) = R.card
  rw [hprox]
  omega

end OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree
