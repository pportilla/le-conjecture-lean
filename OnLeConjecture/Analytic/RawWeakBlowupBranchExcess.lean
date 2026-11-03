/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RawWeakBlowupLocalExcess
public import OnLeConjecture.Analytic.RawWeakBlowupReducedMembers
public import OnLeConjecture.Analytic.ProjectiveReducedBlowupBranchCount

/-!
# Branch count and proximity excess for the constructed weak tree

On a nonempty open coefficient set, every vertex equation is reduced and
every unrecorded branch is smooth and transverse to the new exceptional
divisor. The projective branch-count identity and finite-tree summation
therefore identify the root's irreducible branch count with the sum of
all proximity excesses.
-/

public section

namespace OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree

open OnLeConjecture.Analytic.Germ
open scoped BigOperators

variable {ι : Type*} [Fintype ι] {F : ι → Germ 2}

omit [Fintype ι] in
/-- Every nonroot vertex occurs once among all child sets. -/
theorem sum_child_sums (T : RawProjectiveWeakBlowupTree F) (b : T.Vertex → ℕ) :
    (∑ p, ∑ r ∈ T.childFinset p, b r) = ∑ r ∈ Finset.univ.erase T.root, b r := by
  classical
  have herase : Finset.univ.erase T.root =
      Finset.univ.filter (fun r : T.Vertex => r ≠ T.root) := by
    ext r
    simp [Finset.mem_erase]
  rw [herase]
  simp only [childFinset, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : r = T.root
  · subst r
    simp
  · simp [hr, Finset.mem_univ]

/-- The local branch identity separates recorded child equations from
unrecorded nonunit transforms. -/
theorem member_branchCount_eq_children_add_residual
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ) (p : T.Vertex)
    (hq : germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (hsq : Squarefree (germLinearCombination (T.generators p) q))
    (R : Finset (Option ℂ))
    (hR : ∀ t, t ∈ R ↔ t ∉ (T.childFinset p).image T.chartPoint ∧
      ¬ IsUnit (T.projectiveMemberTransform q p t))
    (hbranches : ∀ t ∈ R,
      PlaneCurve.irreducibleBranchCount (T.projectiveMemberTransform q p t) = 1) :
    PlaneCurve.irreducibleBranchCount (germLinearCombination (T.generators p) q) =
      (∑ r ∈ T.childFinset p,
        PlaneCurve.irreducibleBranchCount (germLinearCombination (T.generators r) q)) + R.card := by
  classical
  let D := (T.childFinset p).image T.chartPoint
  let f := germLinearCombination (T.generators p) q
  have hf : f ∈ maximalIdeal 2 ^ T.multiplicity p :=
    germLinearCombination_mem _ _ (T.generator_mem p) q
  have hstrict (t : Option ℂ) : T.projectiveMemberTransform q p t =
      projectiveStrictTransform (T.multiplicity p) f hf t :=
    T.projectiveMemberTransform_eq_projectiveStrictTransform q p t
  have hcover : ∀ t, ¬ IsUnit (projectiveStrictTransform (T.multiplicity p) f hf t) →
      t ∈ D ∪ R := by
    intro t ht
    by_cases hD : t ∈ D
    · exact Finset.mem_union_left _ hD
    · exact Finset.mem_union_right _ ((hR t).mpr ⟨hD, by rwa [hstrict]⟩)
  have hsum := projectiveStrictTransform_branchCount_sum_of_finite_cover
    (T.multiplicity p) f hf hq hsq (D ∪ R) hcover
  have hdisj : Disjoint D R := by
    apply Finset.disjoint_left.mpr
    intro t ht htr
    exact ((hR t).mp htr).1 ht
  rw [Finset.sum_union hdisj] at hsum
  have hchild : (∑ t ∈ D, PlaneCurve.irreducibleBranchCount
      (projectiveStrictTransform (T.multiplicity p) f hf t)) =
      ∑ r ∈ T.childFinset p,
        PlaneCurve.irreducibleBranchCount (germLinearCombination (T.generators r) q) := by
    rw [Finset.sum_image (T.chartPoint_injOn_childFinset p)]
    apply Finset.sum_congr rfl
    intro r hr
    rw [← hstrict, T.projectiveMemberTransform_eq_child q p r hr]
  have hresidual : (∑ t ∈ R, PlaneCurve.irreducibleBranchCount
      (projectiveStrictTransform (T.multiplicity p) f hf t)) = R.card := by
    calc
      _ = ∑ _t ∈ R, 1 := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [← hstrict]
        exact hbranches t ht
      _ = _ := by simp
  rwa [hchild, hresidual] at hsum

/-- Summing local branch identities cancels all nonroot branch counts. -/
theorem root_branchCount_eq_proximity_branchCount_of_local_identities
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hlocal : ∀ p,
      PlaneCurve.irreducibleBranchCount (germLinearCombination (T.generators p) q) =
        (∑ r ∈ T.childFinset p,
          PlaneCurve.irreducibleBranchCount (germLinearCombination (T.generators r) q)) +
          T.proximityCertificate.excess p) :
    PlaneCurve.irreducibleBranchCount (germLinearCombination F q) =
      T.proximityCertificate.branchCount := by
  classical
  let b := fun p => PlaneCurve.irreducibleBranchCount (germLinearCombination (T.generators p) q)
  have hsum : (∑ p, b p) = (∑ p, ∑ r ∈ T.childFinset p, b r) +
      T.proximityCertificate.branchCount := by
    unfold Numerical.ProximityCertificate.branchCount
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p _ => hlocal p)
  rw [T.sum_child_sums b] at hsum
  have hsplit := Finset.sum_erase_add (s := Finset.univ) b (Finset.mem_univ T.root)
  have hroot : b T.root = PlaneCurve.irreducibleBranchCount (germLinearCombination F q) := by
    simp only [b, T.generators_root]
  rw [hroot] at hsplit
  omega

/-- The generic branch/excess identity is constructed from the finite
weak-blowup tree itself. No reducedness, branch count, or excess identity
is assumed. -/
theorem exists_open_reduced_members_branch_excess
    (T : RawProjectiveWeakBlowupTree F)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ V : Set (ι → ℂ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∀ q ∈ V,
        (∀ p, germLinearCombination (T.generators p) q ∉
          maximalIdeal 2 ^ (T.multiplicity p + 1) ∧
          Squarefree (germLinearCombination (T.generators p) q)) ∧
        PlaneCurve.irreducibleBranchCount (germLinearCombination F q) =
          T.proximityCertificate.branchCount := by
  obtain ⟨W, hWo, hWne, hWU, hW⟩ := T.exists_open_local_excess_branch_counts U hU hUne
  obtain ⟨V, hVo, hVne, hVW, hV⟩ := T.exists_open_reduced_members W hWo hWne
  refine ⟨V, hVo, hVne, hVW.trans hWU, ?_⟩
  intro q hq
  refine ⟨hV q hq, T.root_branchCount_eq_proximity_branchCount_of_local_identities q ?_⟩
  intro p
  obtain ⟨R, hR, hexcess, hbranches⟩ := (hW q (hVW hq)).2 p
  rw [hexcess]
  exact T.member_branchCount_eq_children_add_residual q p (hV q hq p).1
    (hV q hq p).2 R hR hbranches

/-- Indexing the constructed point basis by `Fin` preserves each excess. -/
theorem analyticProximityData_excess_eq
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (p : Fin (Fintype.card T.Vertex)) :
    (T.analyticProximityData q hq).proximity.excess p =
      T.proximityCertificate.excess (T.indexEquiv.symm p) := by
  classical
  unfold Numerical.ProximityCertificate.excess Numerical.ProximityCertificate.successorMultiplicity
  simp only [analyticProximityData, proximityCertificate, Finset.sum_filter,
    mem_indexedParents_iff]
  congr 1
  change (∑ a, if T.indexEquiv.symm p ∈ T.rootedChartData.parents (T.indexEquiv.symm a)
      then T.multiplicity (T.indexEquiv.symm a) else 0) =
    ∑ r ∈ Finset.univ.filter (fun r => T.indexEquiv.symm p ∈ T.rootedChartData.parents r),
      T.multiplicity r
  rw [Finset.sum_filter]
  exact Equiv.sum_comp T.indexEquiv.symm
    (fun r => if T.indexEquiv.symm p ∈ T.rootedChartData.parents r
      then T.multiplicity r else 0)

/-- Indexing the constructed point basis preserves the sum of excesses. -/
theorem analyticProximityData_branchCount_eq
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1)) :
    (T.analyticProximityData q hq).proximity.branchCount =
      T.proximityCertificate.branchCount := by
  unfold Numerical.ProximityCertificate.branchCount
  simp_rw [T.analyticProximityData_excess_eq q hq]
  exact Equiv.sum_comp T.indexEquiv.symm T.proximityCertificate.excess

/-- The open branch/excess identity refers to any chosen exact-order
point-basis member, so it applies directly to the reduction record. -/
theorem exists_open_reduced_members_indexed_branch_excess
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
          PlaneCurve.irreducibleBranchCount (germLinearCombination F q) := by
  obtain ⟨V, hVo, hVne, hVU, hV⟩ := T.exists_open_reduced_members_branch_excess U hU hUne
  refine ⟨V, hVo, hVne, hVU, ?_⟩
  intro q hq
  refine ⟨(hV q hq).1, ?_⟩
  rw [T.analyticProximityData_branchCount_eq q₀ hq₀]
  exact (hV q hq).2.symm

end OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree
