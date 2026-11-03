/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ProjectiveBlowupSquareFactor
public import OnLeConjecture.Analytic.RawWeakBlowupGenericCompleteness

/-!
# Reduced general members on the finite weak-transform tree

Every repeated factor persists at some projective point after blowup.
Singular-transform completeness would therefore give a later nonreduced
vertex. A vertex of maximal generation among the nonreduced vertices
rules this out. The already constructed open set of complete members
thus consists of reduced equations at every vertex.
-/

public section

namespace OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree

open OnLeConjecture.Analytic.Germ

variable {ι : Type*} [Fintype ι] {F : ι → Germ 2}

/-- Finite singular-transform completeness implies reducedness at every
vertex, provided the member has the specified exact order everywhere. -/
theorem squarefree_members_of_singular_complete
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (hcomplete : ∀ (p : T.Vertex) (t : Option ℂ),
      projectiveStrictTransform (T.multiplicity p) (germLinearCombination (T.generators p) q)
        (germLinearCombination_mem _ _ (T.generator_mem p) q) t ∈ maximalIdeal 2 ^ 2 →
      ∃ r, r ≠ T.root ∧ T.predecessor r = p ∧ T.chartPoint r = t) :
    ∀ p, Squarefree (germLinearCombination (T.generators p) q) := by
  classical
  by_contra hnot
  push Not at hnot
  let bad : Finset T.Vertex := Finset.univ.filter
    (fun p => ¬ Squarefree (germLinearCombination (T.generators p) q))
  have hbad : bad.Nonempty := by
    obtain ⟨p, hp⟩ := hnot
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩
  obtain ⟨p, hp, hmax⟩ := bad.exists_max_image T.generation hbad
  obtain ⟨t, htsq, htsing⟩ := exists_nonreduced_projectiveStrictTransform
    (T.multiplicity p) (germLinearCombination (T.generators p) q)
    (germLinearCombination_mem _ _ (T.generator_mem p) q) (hq p)
    (Finset.mem_filter.mp hp).2
  obtain ⟨r, hrroot, hrpred, hrchart⟩ := hcomplete p t htsing
  have hrtransform : germLinearCombination (T.generators r) q =
      projectiveStrictTransform (T.multiplicity p) (germLinearCombination (T.generators p) q)
        (germLinearCombination_mem _ _ (T.generator_mem p) q) t := by
    have h := T.member_eq_projective_transform q r hrroot
    simpa only [hrpred, hrchart, projectiveStrictTransform] using h
  have hrbad : r ∈ bad := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rwa [hrtransform]
  have hle := hmax r hrbad
  have hlt := T.generation_decreases r hrroot
  rw [hrpred] at hlt
  omega

/-- A nonempty open subset of every prescribed nonempty open coefficient
set consists of reduced members of the exact weak-ideal orders. -/
theorem exists_open_reduced_members
    (T : RawProjectiveWeakBlowupTree F)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ V : Set (ι → ℂ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∀ q ∈ V, ∀ p,
        germLinearCombination (T.generators p) q ∉
          maximalIdeal 2 ^ (T.multiplicity p + 1) ∧
        Squarefree (germLinearCombination (T.generators p) q) := by
  obtain ⟨V, hVo, hVne, hVU, hV⟩ := T.exists_open_member_singular_complete U hU hUne
  refine ⟨V, hVo, hVne, hVU, ?_⟩
  intro q hqV
  obtain ⟨hq, hcomplete⟩ := hV q hqV
  have hsq := T.squarefree_members_of_singular_complete q hq (by
    intro p t hsing
    exact hcomplete p t _ (pointBlowupTransform_factor _ _ _ _) hsing)
  intro p
  exact ⟨hq p, hsq p⟩

end OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree
