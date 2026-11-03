/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RawWeakBlowupTreeVertices

/-!
# Separation of sibling positions in the constructed blowup tree

The recursive vertex type is a disjoint union over the distinct projective
points of each node. Induction on the constructed tree proves that two
nonroot vertices with the same predecessor and chart point coincide.
-/

public section

namespace OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree

open OnLeConjecture.Analytic.Germ

universe u
variable {ι : Type u}

/-- Two children of one vertex at one projective chart point are equal.
This separation follows from the tree construction. -/
theorem eq_of_predecessor_eq_chartPoint_eq
    {F : ι → Germ 2} (T : RawProjectiveWeakBlowupTree F) :
    ∀ q r : T.Vertex, q ≠ T.root → r ≠ T.root →
      T.predecessor q = T.predecessor r → T.chartPoint q = T.chartPoint r → q = r := by
  induction T with
  | node F m hm horder hexact hfinite points hcard hcomplete children ih =>
      intro q r hq hr hpred hchart
      cases q with
      | inl q =>
          cases q
          exact (hq rfl).elim
      | inr q =>
          rcases q with ⟨t, q⟩
          cases r with
          | inl r =>
              cases r
              exact (hr rfl).elim
          | inr r =>
              rcases r with ⟨s, r⟩
              by_cases hqt : q = (children t).root
              · by_cases hrs : r = (children s).root
                · subst q
                  subst r
                  simp only [chartPoint, ↓reduceIte] at hchart
                  have hts : t = s := Subtype.ext hchart
                  subst s
                  rfl
                · simp only [predecessor, if_pos hqt, if_neg hrs] at hpred
                  cases hpred
              · by_cases hrs : r = (children s).root
                · simp only [predecessor, if_neg hqt, if_pos hrs] at hpred
                  cases hpred
                · simp only [predecessor, if_neg hqt, if_neg hrs] at hpred
                  have heq := Sum.inr.inj hpred
                  have hts : t = s := congrArg Sigma.fst heq
                  subst s
                  have hchildPred : (children t).predecessor q =
                      (children t).predecessor r := by
                    exact eq_of_heq (Sigma.mk.inj_iff.mp heq).2
                  have hchildChart : (children t).chartPoint q = (children t).chartPoint r := by
                    simpa only [chartPoint, if_neg hqt, if_neg hrs] using hchart
                  have hqr := ih t q r hqt hrs hchildPred hchildChart
                  subst r
                  rfl

/-- The finite set of immediate children of a constructed vertex. -/
@[expose] noncomputable def childFinset
    {F : ι → Germ 2} (T : RawProjectiveWeakBlowupTree F) (p : T.Vertex) : Finset T.Vertex :=
  Finset.univ.filter fun q ↦ q ≠ T.root ∧ T.predecessor q = p

@[simp] theorem mem_childFinset
    {F : ι → Germ 2} (T : RawProjectiveWeakBlowupTree F) (p q : T.Vertex) :
    q ∈ T.childFinset p ↔ q ≠ T.root ∧ T.predecessor q = p := by
  classical
  simp only [childFinset, Finset.mem_filter, Finset.mem_univ, true_and]

theorem chartPoint_injOn_childFinset
    {F : ι → Germ 2} (T : RawProjectiveWeakBlowupTree F) (p : T.Vertex) :
    Set.InjOn T.chartPoint (T.childFinset p) := by
  intro q hq r hr hchart
  obtain ⟨hqroot, hqpred⟩ := (T.mem_childFinset p q).mp hq
  obtain ⟨hrroot, hrpred⟩ := (T.mem_childFinset p r).mp hr
  exact T.eq_of_predecessor_eq_chartPoint_eq q r hqroot hrroot
    (hqpred.trans hrpred.symm) hchart

/-- Every common zero of the weak transforms has exactly one child. -/
theorem existsUnique_child_of_common_zero
    {F : ι → Germ 2} (T : RawProjectiveWeakBlowupTree F)
    (p : T.Vertex) (t : Option ℂ)
    (hzero : ∀ i, projectiveWeakGenerators (T.multiplicity p) (T.generators p)
      (T.generator_mem p) t i ∈ maximalIdeal 2) :
    ∃! q : T.Vertex, q ∈ T.childFinset p ∧ T.chartPoint q = t := by
  obtain ⟨q, hq, hpred, hchart⟩ := T.realizes_common_zero p t hzero
  refine ⟨q, ⟨(T.mem_childFinset p q).mpr ⟨hq, hpred⟩, hchart⟩, ?_⟩
  intro r hr
  exact T.chartPoint_injOn_childFinset p hr.1
    ((T.mem_childFinset p q).mpr ⟨hq, hpred⟩) (hr.2.trans hchart.symm)

/-- A child label is the constructed projective weak transform of its
predecessor label, by cancellation of the exceptional coordinate power. -/
theorem generators_eq_projectiveWeakGenerators
    {F : ι → Germ 2} (T : RawProjectiveWeakBlowupTree F)
    (q : T.Vertex) (hq : q ≠ T.root) (i : ι) :
    T.generators q i =
      projectiveWeakGenerators (T.multiplicity (T.predecessor q))
        (T.generators (T.predecessor q)) (T.generator_mem (T.predecessor q))
        (T.chartPoint q) i := by
  apply pointBlowupTransform_unique (projectiveChartCenter (T.chartPoint q))
    (T.multiplicity (T.predecessor q)) _ _ _ (T.transform_identity q hq i)
  exact pointBlowupTransform_factor _ _ _ _

theorem common_zero_of_mem_childFinset
    {F : ι → Germ 2} (T : RawProjectiveWeakBlowupTree F)
    (p q : T.Vertex) (hq : q ∈ T.childFinset p) :
    ∀ i, projectiveWeakGenerators (T.multiplicity p) (T.generators p)
      (T.generator_mem p) (T.chartPoint q) i ∈ maximalIdeal 2 := by
  obtain ⟨hqroot, hpred⟩ := (T.mem_childFinset p q).mp hq
  subst p
  intro i
  rw [← T.generators_eq_projectiveWeakGenerators q hqroot i]
  simpa only [pow_one] using
    (Ideal.pow_le_pow_right (T.multiplicity_pos q)) (T.generator_mem q i)

/-- The image of the constructed child list is exactly the set of common
weak zeros in both projective charts. -/
theorem mem_image_chartPoint_childFinset_iff
    {F : ι → Germ 2} (T : RawProjectiveWeakBlowupTree F)
    (p : T.Vertex) (t : Option ℂ) :
    t ∈ (T.childFinset p).image T.chartPoint ↔
      ∀ i, projectiveWeakGenerators (T.multiplicity p) (T.generators p)
        (T.generator_mem p) t i ∈ maximalIdeal 2 := by
  classical
  constructor
  · rintro ht
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ht
    exact T.common_zero_of_mem_childFinset p q hq
  · intro ht
    obtain ⟨q, ⟨hq, hchart⟩, _⟩ := T.existsUnique_child_of_common_zero p t ht
    exact Finset.mem_image.mpr ⟨q, hq, hchart⟩

theorem card_image_chartPoint_childFinset
    {F : ι → Germ 2} (T : RawProjectiveWeakBlowupTree F) (p : T.Vertex) :
    ((T.childFinset p).image T.chartPoint).card = (T.childFinset p).card := by
  classical
  exact Finset.card_image_iff.mpr (T.chartPoint_injOn_childFinset p)

end OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree
