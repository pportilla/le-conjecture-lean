/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GenericPointBasisMember

/-!
# Point-basis reconstruction from one coefficient vector

A fixed linear combination having the recorded exact order at every center
defines a new analytic point basis on the same rooted chart data. The weak
generators and their base-ideal completeness are unchanged.
-/

public section

namespace OnLeConjecture.Analytic.WeakTransformIdealData

open OnLeConjecture.Analytic.Germ

variable {N : ℕ} {c : AnalyticPointBasis N} {ι : Type*} [Fintype ι]

@[expose] noncomputable def pointBasisOfLinearCombination
    (d : WeakTransformIdealData c ι) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (d.generators p) q ∈ maximalIdeal 2 ^ c.multiplicity p ∧
      germLinearCombination (d.generators p) q ∉ maximalIdeal 2 ^ (c.multiplicity p + 1)) :
    AnalyticPointBasis N :=
  { c with
    germ := fun p => germLinearCombination (d.generators p) q
    germ_mem := fun p => (hq p).1
    germ_not_mem_succ := fun p => (hq p).2
    transform_identity := d.linearCombination_transform q }

@[expose] noncomputable def weakDataOfLinearCombination
    (d : WeakTransformIdealData c ι) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (d.generators p) q ∈ maximalIdeal 2 ^ c.multiplicity p ∧
      germLinearCombination (d.generators p) q ∉ maximalIdeal 2 ^ (c.multiplicity p + 1)) :
    WeakTransformIdealData (d.pointBasisOfLinearCombination q hq) ι where
  generators := d.generators
  generator_mem_pow := d.generator_mem_pow
  generic_member_mem p := by
    change (∑ i, q i • d.generators p i) ∈ Ideal.span (Set.range (d.generators p))
    exact ((Ideal.span (Set.range (d.generators p))).restrictScalars ℂ).sum_mem
      (fun i _ => ((Ideal.span (Set.range (d.generators p))).restrictScalars ℂ).smul_mem
        (q i) (Ideal.subset_span (Set.mem_range_self i)))
  transform_identity := d.transform_identity

/-- Completeness concerns the weak generators and the chart data, which do
not change when the general member is replaced by this linear combination. -/
theorem finiteWeakBasepointCompleteness_linearCombination
    (d : WeakTransformIdealData c ι) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (d.generators p) q ∈ maximalIdeal 2 ^ c.multiplicity p ∧
      germLinearCombination (d.generators p) q ∉ maximalIdeal 2 ^ (c.multiplicity p + 1))
    (hcomplete : FiniteWeakBasepointCompleteness d) :
    FiniteWeakBasepointCompleteness (d.weakDataOfLinearCombination q hq) := by
  constructor
  intro p ζ G hG hzero
  exact hcomplete.realizes_common_zero p ζ G hG hzero

end OnLeConjecture.Analytic.WeakTransformIdealData
