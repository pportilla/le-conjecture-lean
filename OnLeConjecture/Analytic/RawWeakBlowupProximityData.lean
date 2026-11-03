/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RawWeakBlowupChildIntersection
public import OnLeConjecture.Analytic.RawWeakBlowupPointBasisAtlas
public import OnLeConjecture.Analytic.RawWeakBlowupPointBasisCompleteness
public import OnLeConjecture.Analytic.ProximityTopOrderChain
public import OnLeConjecture.Analytic.PlaneInjectiveFiniteness
public import OnLeConjecture.Analytic.FiniteColength

/-!
# Proximity data constructed from actual weak transforms

Exceptional-axis labels and the proved intersection inequalities construct
an analytic proximity certificate for the point basis of a finite weak
blowup tree. Finite colength therefore supplies the point basis, weak
transforms, proximity, both projective charts, and weak-basepoint
completeness together. The branch-count identification and the curve and
critical-component estimates are not asserted here.
-/

public section

namespace OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree

open OnLeConjecture.Analytic.Germ

variable {ι : Type*} [Fintype ι] {F : ι → Germ 2}

/-- The numerical certificate uses the actual exceptional-divisor labels
and weak-ideal multiplicities of the constructed tree. -/
@[expose] noncomputable def proximityCertificate
    (T : RawProjectiveWeakBlowupTree F) : Numerical.ProximityCertificate T.Vertex where
  multiplicity := T.multiplicity
  root := T.root
  parents := T.rootedChartData.parents
  root_has_no_parent := T.rootedChartData.parents_root
  nonroot_parent_card := T.rootedChartData.nonroot_parent_card
  proximity_inequality := T.proximity_inequality

/-- The proximity parents after indexing the finite vertex set by `Fin`. -/
@[expose] noncomputable def indexedParents
    (T : RawProjectiveWeakBlowupTree F) (p : Fin (Fintype.card T.Vertex)) :
    Finset (Fin (Fintype.card T.Vertex)) :=
  (T.rootedChartData.parents (T.indexEquiv.symm p)).map T.indexEquiv.toEmbedding

omit [Fintype ι] in
@[simp] theorem mem_indexedParents_iff
    (T : RawProjectiveWeakBlowupTree F) (p r : Fin (Fintype.card T.Vertex)) :
    r ∈ T.indexedParents p ↔
      T.indexEquiv.symm r ∈ T.rootedChartData.parents (T.indexEquiv.symm p) := by
  classical
  simp [indexedParents]

/-- The proved proximity inequalities and the geometric exceptional-axis
incidence match the constructed analytic point basis. -/
@[expose] noncomputable def analyticProximityData
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1)) :
    AnalyticProximityData (T.pointBasis q hq) where
  proximity := {
    multiplicity := fun p => T.multiplicity (T.indexEquiv.symm p)
    root := T.indexEquiv T.root
    parents := T.indexedParents
    root_has_no_parent := by
      simp only [indexedParents, Equiv.symm_apply_apply]
      rw [show T.rootedChartData.parents T.root = ∅ from T.rootedChartData.parents_root]
      simp
    nonroot_parent_card := by
      intro p hp
      have hp' : T.indexEquiv.symm p ≠ T.root := by
        intro h
        apply hp
        exact (T.indexEquiv.eq_symm_apply.mp h.symm).symm
      simpa only [indexedParents, Finset.card_map] using
        T.rootedChartData.nonroot_parent_card _ hp'
    proximity_inequality := by
      intro p
      simp only [Finset.sum_filter, mem_indexedParents_iff]
      have h := T.proximity_inequality (T.indexEquiv.symm p)
      simp only [Finset.sum_filter] at h
      convert h using 1
      exact Equiv.sum_comp T.indexEquiv.symm
        (fun v => if T.indexEquiv.symm p ∈ T.rootedChartData.parents v
          then T.multiplicity v else 0) }
  root_eq := rfl
  multiplicity_eq := rfl
  predecessor_mem := by
    intro p hp
    apply (T.mem_indexedParents_iff p _).mpr
    simp only [pointBasis, Equiv.symm_apply_apply]
    apply T.rootedChartData.predecessor_mem
    intro h
    apply hp
    exact (T.indexEquiv.eq_symm_apply.mp h.symm).symm
  generation_decreases := by
    intro p r h
    exact T.rootedChartData.generation_lt_of_mem_parents
      ((T.mem_indexedParents_iff p r).mp h)
  nested_parents := by
    intro p hp
    have hcard : (T.rootedChartData.parents (T.indexEquiv.symm p)).card = 2 := by
      simpa only [indexedParents, Finset.card_map] using hp
    obtain ⟨r, s, hr, hs, hsr⟩ := T.rootedChartData.nested_parents _ hcard
    refine ⟨T.indexEquiv r, T.indexEquiv s, ?_, ?_, ?_⟩
    · exact (T.mem_indexedParents_iff p _).mpr (by simpa only [Equiv.symm_apply_apply] using hr)
    · exact (T.mem_indexedParents_iff p _).mpr (by simpa only [Equiv.symm_apply_apply] using hs)
    · exact (T.mem_indexedParents_iff _ _).mpr (by simpa only [Equiv.symm_apply_apply] using hsr)

/-- Finite colength constructs the geometric weak-transform and proximity
parts of the reduction data with a single exact-order member chosen inside
the prescribed nonempty open coefficient set. -/
theorem exists_pointBasis_weakData_proximity_complete_mem_open
    (F : ι → Germ 2) (hproper : ∀ i, F i ∈ maximalIdeal 2)
    (hfinite : Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range F)))
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ (N : ℕ) (c : AnalyticPointBasis N) (d : WeakTransformIdealData c ι)
      (q : ι → ℂ),
      q ∈ U ∧ d.generators c.root = F ∧
      (∀ p, c.germ p = germLinearCombination (d.generators p) q) ∧
      Nonempty (AnalyticProximityData c) ∧ Nonempty (TopOrderTwoChartAtlas c) ∧
      FiniteWeakBasepointCompleteness d ∧ RootTwoChartWeakBasepointCompleteness d ∧
      ∀ p, c.ParentRelation p c.root → c.generation p = c.generation c.root + 1 := by
  obtain ⟨T⟩ := RawProjectiveWeakBlowupTree.exists_of_finite_colength F hproper hfinite
  obtain ⟨q, hqU, hq⟩ := T.exists_exact_coefficients U hU hUne
  exact ⟨Fintype.card T.Vertex, T.pointBasis q hq, T.weakData q hq, q, hqU,
    T.weakData_root q hq, fun _ => rfl, ⟨T.analyticProximityData q hq⟩,
    ⟨T.twoChartAtlas q hq⟩, T.finiteWeakBasepointCompleteness q hq,
    T.rootTwoChartWeakBasepointCompleteness q hq, T.pointBasis_root_depth q hq⟩

/-- An injective pointed analytic germ with plane source supplies the
constructed weak-transform and proximity data. No assumption on its
differential is needed for this geometric conclusion. -/
theorem exists_pointBasis_weakData_proximity_of_injective
    {m : ℕ} (g : PointedMapGerm 2 m) (hinjective : g.HasInjectiveRepresentative)
    (U : Set (Fin m → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ (N : ℕ) (c : AnalyticPointBasis N) (d : WeakTransformIdealData c (Fin m))
      (q : Fin m → ℂ),
      q ∈ U ∧ d.generators c.root = g.1.component ∧
      (∀ p, c.germ p = germLinearCombination (d.generators p) q) ∧
      Nonempty (AnalyticProximityData c) ∧ Nonempty (TopOrderTwoChartAtlas c) ∧
      FiniteWeakBasepointCompleteness d ∧ RootTwoChartWeakBasepointCompleteness d ∧
      ∀ p, c.ParentRelation p c.root → c.generation p = c.generation c.root + 1 := by
  apply exists_pointBasis_weakData_proximity_complete_mem_open g.1.component
    (fun i => g.coordinateIdeal_le_maximalIdeal (g.1.component_mem_coordinateIdeal i))
    _ U hU hUne
  have hIdeal : g.1.coordinateIdeal = Ideal.span (Set.range g.1.component) := by
    apply le_antisymm
    · rw [MapGerm.coordinateIdeal_le]
      intro i
      exact Ideal.subset_span (Set.mem_range_self i)
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact g.1.component_mem_coordinateIdeal i
  rw [← hIdeal]
  exact g.coordinateQuotient_moduleFinite (g.injective_isFiniteAtOrigin_two hinjective)

end OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree
