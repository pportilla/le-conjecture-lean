/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RawWeakBlowupSiblingSeparation
public import OnLeConjecture.Analytic.RawWeakBlowupExceptionalIntersection
public import OnLeConjecture.Analytic.ProjectiveExceptionalIntersectionBound
public import OnLeConjecture.Analytic.ExceptionalIntersectionBound

/-!
# Exceptional intersection bounds for children of a weak-blowup vertex

Distinct children occupy distinct projective points. The restriction of an
exact-order member to each new exceptional axis agrees with the restriction
of its constructed strict transform. Consequently the polynomial root-order
bound applies to the actual analytic members at those children.
-/

public section

namespace OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree

open OnLeConjecture.Analytic.Germ

variable {ι : Type*} [Fintype ι] {F : ι → Germ 2}

/-- A member at a child is the constructed projective strict transform
of the member at its predecessor. -/
theorem member_eq_projective_transform
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (p : T.Vertex) (hp : p ≠ T.root) :
    germLinearCombination (T.generators p) q =
      pointBlowupTransform (projectiveChartCenter (T.chartPoint p))
        (T.multiplicity (T.predecessor p))
        ((projectiveChartSource (T.chartPoint p)).forward.pullbackRingHom
          (germLinearCombination (T.generators (T.predecessor p)) q))
        ((projectiveChartSource (T.chartPoint p)).forward.pullback_mem_maximalIdeal_pow
          (germLinearCombination_mem _ _ (T.generator_mem (T.predecessor p)) q)) := by
  apply pointBlowupTransform_unique _ _ _ _ _ (T.linearCombination_transform q p hp)
  exact pointBlowupTransform_factor _ _ _ _

/-- The total exceptional intersection order at any set of finite-chart
children is at most the parent's order. -/
theorem sum_finite_child_exceptional_orders_le
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ) (p : T.Vertex)
    (hq : germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (s : Finset T.Vertex) (hs : s ⊆ T.childFinset p)
    (hfinite : ∀ v ∈ s, T.chartPoint v ≠ none) :
    ∑ v ∈ s, (vanishingOrder (lineRestriction (firstCoordinateVector 1)
      (germLinearCombination (T.generators v) q))).toNat ≤ T.multiplicity p := by
  classical
  let center : T.Vertex → ℂ := fun v => (T.chartPoint v).getD 0
  have hchart (v : T.Vertex) (hv : v ∈ s) : T.chartPoint v = some (center v) := by
    cases h : T.chartPoint v with
    | none => exact (hfinite v hv h).elim
    | some c => simp [center, h]
  have hinj : Set.InjOn center s := by
    intro v hv w hw heq
    apply T.chartPoint_injOn_childFinset p (hs hv) (hs hw)
    rw [hchart v hv, hchart w hw, heq]
  let f := germLinearCombination (T.generators p) q
  have hf : f ∈ maximalIdeal 2 ^ T.multiplicity p :=
    germLinearCombination_mem _ _ (T.generator_mem p) q
  have htransform (v : T.Vertex) (hv : v ∈ s) :
      germLinearCombination (T.generators v) q =
        pointBlowupTransform (center v) (T.multiplicity p) f hf := by
    obtain ⟨hvroot, hvpred⟩ := (T.mem_childFinset p v).mp (hs hv)
    have h := T.member_eq_projective_transform q v hvroot
    simpa only [hvpred, hchart v hv, projectiveChartCenter, projectiveChartSource,
      PointedEquivGerm.identity_forward, PointedMapGerm.pullbackRingHom_identity,
      RingHom.id_apply] using h
  calc
    _ = ∑ v ∈ s, (vanishingOrder (pointBlowupExceptionalLine.pullbackRingHom
          (pointBlowupTransform (center v) (T.multiplicity p) f hf))).toNat := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [htransform v hv, pointBlowupExceptionalLine_eq_lineGerm]
      rfl
    _ = ∑ c ∈ s.image center, (vanishingOrder (pointBlowupExceptionalLine.pullbackRingHom
          (pointBlowupTransform c (T.multiplicity p) f hf))).toNat :=
      by
        symm
        apply Finset.sum_image
        exact hinj
    _ ≤ T.multiplicity p := sum_exceptional_restriction_orders_le _ _ hf hq _

omit [Fintype ι] in
/-- Summing the ordinary multiplicities of finite-chart children gives a
bound by the parent multiplicity. -/
theorem sum_finite_child_multiplicities_le [Finite ι]
    (T : RawProjectiveWeakBlowupTree F) (p : T.Vertex)
    (s : Finset T.Vertex) (hs : s ⊆ T.childFinset p)
    (hfinite : ∀ v ∈ s, T.chartPoint v ≠ none) :
    ∑ v ∈ s, T.multiplicity v ≤ T.multiplicity p := by
  let := Fintype.ofFinite ι
  obtain ⟨q, _, hq⟩ := T.exists_exact_coefficients Set.univ isOpen_univ Set.univ_nonempty
  apply (Finset.sum_le_sum (fun v hv =>
    T.multiplicity_le_newestAxisOrder q hq v
      ((T.mem_childFinset p v).mp (hs hv)).1)).trans
  exact T.sum_finite_child_exceptional_orders_le q p (hq p) s hs hfinite

/-- The exceptional intersection bound holds over all children, including
the complementary projective point. -/
theorem sum_child_newestAxisOrders_le
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ) (p : T.Vertex)
    (hq : germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1)) :
    ∑ v ∈ T.childFinset p, T.newestAxisOrder q v ≤ T.multiplicity p := by
  classical
  let f := germLinearCombination (T.generators p) q
  have hf : f ∈ maximalIdeal 2 ^ T.multiplicity p :=
    germLinearCombination_mem _ _ (T.generator_mem p) q
  let b : Option ℂ → ℕ := fun t =>
    (vanishingOrder (pointBlowupExceptionalLine.pullbackRingHom
      (pointBlowupTransform (projectiveChartCenter t) (T.multiplicity p)
        ((projectiveChartSource t).forward.pullbackRingHom f)
        ((projectiveChartSource t).forward.pullback_mem_maximalIdeal_pow hf)))).toNat
  have htransform (v : T.Vertex) (hv : v ∈ T.childFinset p) :
      T.newestAxisOrder q v = b (T.chartPoint v) := by
    obtain ⟨hvroot, hvpred⟩ := (T.mem_childFinset p v).mp hv
    unfold newestAxisOrder
    rw [T.member_eq_projective_transform q v hvroot]
    simp only [hvpred, b, f, pointBlowupExceptionalLine_eq_lineGerm]
    rfl
  calc
    _ = ∑ v ∈ T.childFinset p, b (T.chartPoint v) :=
      Finset.sum_congr rfl htransform
    _ = ∑ t ∈ (T.childFinset p).image T.chartPoint, b t := by
      symm
      exact Finset.sum_image (T.chartPoint_injOn_childFinset p)
    _ ≤ T.multiplicity p := sum_projective_exceptional_restriction_orders_le _ _ hf hq _

omit [Fintype ι] in
/-- Actual weak-transform multiplicities satisfy every proximity
inequality. The sum includes all later satellite points on the exceptional
divisor, not only the immediate children. -/
theorem proximity_inequality [Finite ι]
    (T : RawProjectiveWeakBlowupTree F) (p : T.Vertex) :
    (∑ v ∈ Finset.univ.filter (fun v => p ∈ T.rootedChartData.parents v),
      T.multiplicity v) ≤ T.multiplicity p := by
  let := Fintype.ofFinite ι
  obtain ⟨q, _, hq⟩ := T.exists_exact_coefficients Set.univ isOpen_univ Set.univ_nonempty
  exact (T.sum_proximate_multiplicities_le_child_newestAxisOrders q hq p).trans
    (T.sum_child_newestAxisOrders_le q p (hq p))

omit [Fintype ι] in
/-- The sum of the multiplicities of the immediate children is bounded
by the parent multiplicity in both projective charts. -/
theorem sum_child_multiplicities_le [Finite ι]
    (T : RawProjectiveWeakBlowupTree F) (p : T.Vertex) :
    ∑ v ∈ T.childFinset p, T.multiplicity v ≤ T.multiplicity p := by
  apply (Finset.sum_le_sum_of_subset ?_).trans (T.proximity_inequality p)
  intro v hv
  obtain ⟨hvroot, hvpred⟩ := (T.mem_childFinset p v).mp hv
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, hvpred ▸ T.rootedChartData.predecessor_mem v hvroot⟩

end OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree
