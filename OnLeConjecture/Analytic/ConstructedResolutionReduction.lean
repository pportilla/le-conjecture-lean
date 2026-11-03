/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RawWeakBlowupMilnorIdentity
public import OnLeConjecture.Analytic.RawWeakBlowupCompanionIntersection
public import OnLeConjecture.Analytic.CriticalComponentPolarConstruction
public import OnLeConjecture.Analytic.GeneralResolutionReductionFromComponents
public import OnLeConjecture.Analytic.ReducedPlaneIsolatedCritical
public import OnLeConjecture.Case234

/-!
# Reduction after constructing the weak-transform geometry

Finite colength supplies the actual weak-transform tree, its analytic point
basis, proximity inequalities, projective charts, and weak-basepoint
completeness. A nonempty open subset of any admissible coefficient set
has complete singular transforms, reduced members, companion intersection
identities, and the branch and Milnor identities. For a zero-differential
map, these members also have isolated critical points. Teissier's identity
and the common critical divisor give their polar estimates.

The only remaining hypotheses in `ConstructedResolutionRemainingData` are
the critical-component equations, their transverse multiplicities and
common-minor divisibility, and the two global numerical estimates.
Their existence is not proved in this file.
-/

public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ PlaneCurve Numerical

/-- Reduced linear members of a zero-differential map have isolated
critical points. This conclusion requires no resolution input. -/
theorem PointedMapGerm.member_hasIsolatedCriticalPoint_of_reduced
    {m : ℕ} (g : PointedMapGerm 2 m) (hdifferential : g.differential = 0)
    (q : Fin m → ℂ) (hreduced : Squarefree (germLinearCombination g.1.component q)) :
    HasIsolatedCriticalPoint (germLinearCombination g.1.component q) := by
  apply hasIsolatedCriticalPoint_of_squarefree_mem_maximalIdeal_sq _ _ hreduced
  apply germLinearCombination_mem
  intro i
  exact (g.differential_eq_zero_iff_coordinateIdeal_le_sq.mp hdifferential)
    (g.1.component_mem_coordinateIdeal i)

/-- The remaining critical-divisor and global numerical inputs on a
constructed weak-transform tree. All general-member properties, including
the coefficient set, are proved when assembling the reduction. -/
structure ConstructedResolutionRemainingData
    (g : PointedMapGerm 2 3) (hdifferential : g.differential = 0)
    (T : RawProjectiveWeakBlowupTree g.1.component) (q₀ : Fin 3 → ℂ)
    (hq₀ : ∀ p, germLinearCombination (T.generators p) q₀ ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1)) where
  componentCardinality : ℕ
  componentCardinality_pos : 0 < componentCardinality
  components : CriticalDivisorEstimateData g
    (MultiplicityCounts.sum (T.pointBasis q₀ hq₀).multiplicity)
    (MultiplicityCounts.squareSum (T.pointBasis q₀ hq₀).multiplicity)
    (Fin componentCardinality)

/-- Restrict the all-component estimates to a smaller coefficient set. -/
@[expose] def CriticalComponentReductionData.restrict
    {g : PointedMapGerm 2 3} {M S b : ℕ} {U V : Set (Fin 3 → ℂ)}
    {ι : Type*} [Fintype ι] (D : CriticalComponentReductionData g M S b U ι)
    (hVU : V ⊆ U) : CriticalComponentReductionData g M S b V ι where
  component := D.component
  transverseMultiplicity := D.transverseMultiplicity
  component_mem := D.component_mem
  two_le_multiplicity := D.two_le_multiplicity
  total_le_max := D.total_le_max
  global_estimate := D.global_estimate
  product_dvd_ordered_minors := D.product_dvd_ordered_minors
  intersection_finite q hq i := D.intersection_finite q (hVU hq) i
  polar_sum q hq := D.polar_sum q (hVU hq)

/-- Constructed geometry and the explicitly remaining estimates assemble
the original common reduction record. -/
theorem ConstructedResolutionRemainingData.exists_generalResolutionReductionData
    {g : PointedMapGerm 2 3} {hdifferential : g.differential = 0}
    {T : RawProjectiveWeakBlowupTree g.1.component} {q₀ : Fin 3 → ℂ}
    {hq₀ : ∀ p, germLinearCombination (T.generators p) q₀ ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1)}
    (R : ConstructedResolutionRemainingData g hdifferential T q₀ hq₀) :
    Nonempty (GeneralResolutionReductionData g) := by
  let : Nonempty (Fin R.componentCardinality) := ⟨⟨0, R.componentCardinality_pos⟩⟩
  obtain ⟨W, hWopen, hWne, _hWU, hcurves⟩ := T.exists_open_reduced_members_milnor_identity
    q₀ hq₀ Set.univ isOpen_univ Set.univ_nonempty
  obtain ⟨V, hVopen, hVne, hVW, hterminal⟩ :=
    T.exists_open_weakData_terminal_complete q₀ hq₀ W hWopen hWne
  have hcurvesV : ∀ q ∈ V, Nonempty (GeneralMemberCurveInvariants g
      (T.pointBasis q₀ hq₀) (T.analyticProximityData q₀ hq₀) q) := by
    intro q hq
    have hqexact := fun p => ((hcurves q (hVW hq)).1 p).1
    obtain ⟨r, _hr, hpair, hintersection⟩ :=
      T.exists_companion_intersection_eq_squareSum_mem_open q hqexact
        Set.univ isOpen_univ Set.univ_nonempty
    have hintersection₀ : intersectionMultiplicity
        (germLinearCombination g.1.component q) (germLinearCombination g.1.component r) hpair =
        MultiplicityCounts.squareSum (T.pointBasis q₀ hq₀).multiplicity := by
      rw [T.pointBasis_squareSum q hqexact] at hintersection
      rw [T.pointBasis_squareSum q₀ hq₀]
      exact hintersection
    have hreduced : Squarefree (germLinearCombination g.1.component q) := by
      simpa only [T.generators_root] using ((hcurves q (hVW hq)).1 T.root).2
    let hisolated := g.member_hasIsolatedCriticalPoint_of_reduced hdifferential q hreduced
    exact ⟨{
      companion := r
      pair_finite := hpair
      pair_intersection := hintersection₀
      reduced := hreduced
      isolated := hisolated
      branches := (hcurves q (hVW hq)).2.1
      genus := by simpa only [milnorNumber] using (hcurves q (hVW hq)).2.2 }⟩
  apply exists_generalResolutionReductionData_of_component_estimates g
    (T.pointBasis q₀ hq₀) (T.weakData q₀ hq₀)
    (fun i => congrFun (T.weakData_root q₀ hq₀) i)
    (T.analyticProximityData q₀ hq₀) (T.twoChartAtlas q₀ hq₀)
    (T.finiteWeakBasepointCompleteness q₀ hq₀)
    (T.rootTwoChartWeakBasepointCompleteness q₀ hq₀) (T.pointBasis_root_depth q₀ hq₀)
    V hVopen hVne
    (R.components.toCriticalComponentReductionData (T.pointBasis q₀ hq₀)
      (T.analyticProximityData q₀ hq₀) V hcurvesV) hcurvesV hterminal

/-- Injectivity constructs the weak-transform tree and proximity data
before the remaining critical-divisor and numerical estimates are used. -/
theorem exists_generalResolutionReductionData_of_remaining_estimates
    (g : PointedMapGerm 2 3) (hdifferential : g.differential = 0)
    (hinjective : g.HasInjectiveRepresentative)
    (hremaining : ∀ (T : RawProjectiveWeakBlowupTree g.1.component) (q₀ : Fin 3 → ℂ)
      (hq₀ : ∀ p, germLinearCombination (T.generators p) q₀ ∉
        maximalIdeal 2 ^ (T.multiplicity p + 1)),
      Nonempty (ConstructedResolutionRemainingData g hdifferential T q₀ hq₀)) :
    Nonempty (GeneralResolutionReductionData g) := by
  have hIdeal : g.1.coordinateIdeal = Ideal.span (Set.range g.1.component) := by
    apply le_antisymm
    · rw [MapGerm.coordinateIdeal_le]
      intro i
      exact Ideal.subset_span (Set.mem_range_self i)
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact g.1.component_mem_coordinateIdeal i
  have hfinite : Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range g.1.component)) := by
    rw [← hIdeal]
    exact g.coordinateQuotient_moduleFinite (g.injective_isFiniteAtOrigin_two hinjective)
  obtain ⟨T⟩ := RawProjectiveWeakBlowupTree.exists_of_finite_colength g.1.component
    (fun i => g.coordinateIdeal_le_maximalIdeal (g.1.component_mem_coordinateIdeal i)) hfinite
  obtain ⟨q₀, _, hq₀⟩ := T.exists_exact_coefficients Set.univ isOpen_univ Set.univ_nonempty
  obtain ⟨R⟩ := hremaining T q₀ hq₀
  exact R.exists_generalResolutionReductionData

end OnLeConjecture.Analytic

namespace OnLeConjecture

open Analytic Analytic.Germ

/-- The remaining estimates imply Lê's conjecture after constructing
weak-transform geometry and proving the three coordinate-order exclusions.
This is a conditional theorem: the displayed remaining estimates are not
proved here. -/
theorem leConjecture_of_constructed_resolution_remaining_estimates
    (hremaining : ∀ (g : PointedMapGerm 2 3) (hdifferential : g.differential = 0),
      g.HasInjectiveRepresentative →
      ∀ (T : RawProjectiveWeakBlowupTree g.1.component) (q₀ : Fin 3 → ℂ)
      (hq₀ : ∀ p, germLinearCombination (T.generators p) q₀ ∉
        maximalIdeal 2 ^ (T.multiplicity p + 1)),
      Nonempty (ConstructedResolutionRemainingData g hdifferential T q₀ hq₀)) :
    LeConjecture := by
  apply leConjecture_of_general_resolution_reduction
  intro g hdifferential hinjective
  exact exists_generalResolutionReductionData_of_remaining_estimates g hdifferential hinjective
    (hremaining g hdifferential hinjective)

end OnLeConjecture
