/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.NonsquareGenericMember
public import OnLeConjecture.DTwo.ScalarNodeQuadraticTailExclusion
public import OnLeConjecture.DTwo.QuadraticResolutionReductionData
public import OnLeConjecture.DTwo.QuadraticJetClassificationBoundary
public import OnLeConjecture.Analytic.TargetPairLinearCompletion
public import OnLeConjecture.Analytic.JacobianLinearSpan

/-!
# Nonsquare rank-one exclusion with a genuine general-member choice

The source coordinates are fixed before the supplied resolution data is
chosen. Inside its nonempty coefficient-open set, exact orders and a nonzero
node coefficient are imposed simultaneously. The chosen finite companion
pair is retained by an invertible target change. All relative scalar jets
and minor divisibilities are then derived before applying node exclusion.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ PlaneCurve

theorem scalar_node_excluded_of_open_general_member_reduction
    (g : PointedMapGerm 2 3) (D : QuadraticResolutionReductionData g)
    (a : Fin 3 → ℂ)
    (htail : ∀ i, g.1.component i - constRingHom 2 (a i) *
      coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈ maximalIdeal 2 ^ 3) :
    ¬ g.HasInjectiveRepresentative := by
  have hweakTail (i : Fin 3) : D.weakData.generators D.pointBasis.root i -
      constRingHom 2 (a i) * coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈
        maximalIdeal 2 ^ 3 := by
    rw [D.root_generators]
    exact htail i
  obtain ⟨q, hqU, haq, hq, hnode⟩ := exists_scalar_node_point_basis_member_mem_open
    D.weakData D.root_multiplicity a hweakTail D.coefficientOpen
    D.coefficientOpen_isOpen D.coefficientOpen_nonempty
  obtain ⟨R⟩ := D.generalMemberReduction q hqU
  have hqne : q ≠ 0 := by
    intro hz
    exact haq (by rw [hz, map_zero])
  obtain ⟨s, f, hgf, hf⟩ := exists_target_pair_linearCombination_of_finite_intersection
    g q R.companion hqne R.pair_finite
  have hf0 : f.1.component 0 = germLinearCombination g.1.component q := by
    simpa only [Matrix.cons_val_zero] using hf 0
  have hf1 : f.1.component 1 = germLinearCombination g.1.component R.companion := by
    simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using hf 1
  let c' := D.weakData.pointBasisOfLinearCombination q hq
  let d' := D.weakData.weakDataOfLinearCombination q hq
  have hmult : c'.multiplicity = D.pointBasis.multiplicity := rfl
  have hrootGenerators : D.weakData.generators D.pointBasis.root = g.1.component := by
    funext i
    exact D.root_generators i
  have hmember : c'.germ c'.root = f.1.component 0 := by
    change germLinearCombination (D.weakData.generators D.pointBasis.root) q = _
    rw [hrootGenerators, hf0]
  have hv : f.1.component 0 - constRingHom 2 (scalarJetCoefficient a q) *
      coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈ maximalIdeal 2 ^ 3 := by
    rw [← hmember]
    exact hnode
  have hweakRelative (i : Fin 3) : ∃ b : ℂ,
      d'.generators c'.root i - constRingHom 2 b * c'.germ c'.root ∈ maximalIdeal 2 ^ 3 := by
    refine ⟨a i / scalarJetCoefficient a q, ?_⟩
    change D.weakData.generators D.pointBasis.root i -
      constRingHom 2 (a i / scalarJetCoefficient a q) * c'.germ c'.root ∈ _
    exact scalar_jet_relative_member_tail _ _ _ _ _ haq 3 (hweakTail i) hnode
  have hlastRelative (i : Fin 2) : ∃ b : ℂ,
      f.1.component i.succ - constRingHom 2 b * f.1.component 0 ∈ maximalIdeal 2 ^ 3 := by
    refine ⟨scalarJetCoefficient a (![q, R.companion, s] i.succ) /
      scalarJetCoefficient a q, ?_⟩
    apply scalar_jet_relative_member_tail _ _ _ _ _ haq 3 ?_ hv
    rw [hf]
    exact linearCombination_scalar_jet_tail g.1.component a _ 3 htail _
  have hspan (i : Fin 3) : f.1.component i ∈ Submodule.span ℂ (Set.range g.1.component) := by
    rw [hf]
    change (∑ j, ![q, R.companion, s] i j • g.1.component j) ∈ _
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j)))
  have hminors (i : Fin 2) : R.critical ^ (R.exponent - 1) ∣
      jacobian (f.1.component 0) (f.1.component i.succ) :=
    dvd_jacobian_of_mem_linear_span g.1.component _ R.common_minors (hspan 0) (hspan i.succ)
  have hfinite : HasFiniteIntersection (f.1.component 0) R.critical := by
    rw [hf0]
    exact (hasFiniteIntersection_comm _ _).mp R.critical_finite
  have hpolar : intersectionMultiplicity (f.1.component 0) R.critical hfinite *
      (R.exponent - 1) + Numerical.MultiplicityCounts.sum c'.multiplicity +
      irreducibleBranchCount (f.1.component 0) ≤
        2 * Numerical.MultiplicityCounts.squareSum c'.multiplicity := by
    have hcomm := intersectionMultiplicity_comm R.critical
      (germLinearCombination g.1.component q) R.critical_finite
    simpa only [hf0, hcomm, hmult] using R.polar
  have hfinitePair : HasFiniteIntersection (f.1.component 0) (f.1.component 1) := by
    simpa only [hf0, hf1] using R.pair_finite
  have hpair : intersectionMultiplicity (f.1.component 0) (f.1.component 1) hfinitePair =
      Numerical.MultiplicityCounts.squareSum c'.multiplicity := by
    simpa only [hf0, hf1, hmult] using R.pair_intersection
  intro hinjective
  exact scalar_rank_one_node_jet_reduction_not_hasInjectiveRepresentative f d'
    (D.weakData.finiteWeakBasepointCompleteness_linearCombination q hq D.complete)
    D.root_multiplicity hmember (scalarJetCoefficient a q) haq hv hweakRelative hlastRelative
    R.critical R.critical_mem R.exponent hfinite R.totalMultiplicity_le hpolar hminors
    0 hfinitePair hpair (hgf.hasInjectiveRepresentative hinjective)

/-- The source normalization is performed before invoking the imported
resolution data. No transport of weak-basepoint completeness is assumed. -/
theorem nonsquare_scalar_jets_not_hasInjectiveRepresentative_of_resolution_reduction
    (g : PointedMapGerm 2 3) (Q : OrbitSourceForm) (hQ : Q.IsHomogeneous 2)
    (hdisc : binaryQuadraticDiscriminant Q ≠ 0) (a : Fin 3 → ℂ)
    (htail : ∀ i, g.1.component i - constRingHom 2 (a i) *
      coordinatePolynomialAlgHom 2 Q ∈ maximalIdeal 2 ^ 3)
    (hresolution : ∀ f : PointedMapGerm 2 3, g.RightLeftEquivalent f →
      Nonempty (QuadraticResolutionReductionData f)) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨e, he⟩ := exists_nonsquare_quadratic_source_normalization Q hQ hdisc
  let f := g.comp e.forward
  have hgf : g.RightLeftEquivalent f := by
    refine ⟨e, PointedEquivGerm.identity 3, ?_⟩
    rw [PointedEquivGerm.identity_forward, PointedMapGerm.identity_comp]
  have hf (i : Fin 3) : f.1.component i - constRingHom 2 (a i) *
      coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈ maximalIdeal 2 ^ 3 := by
    have hpull := e.forward.pullback_mem_maximalIdeal_pow (htail i)
    rw [map_sub, map_mul, PointedMapGerm.pullback_constRingHom, he] at hpull
    simpa only [f, PointedMapGerm.component_comp_eq_pullback] using hpull
  obtain ⟨D⟩ := hresolution f hgf
  intro hinjective
  exact scalar_node_excluded_of_open_general_member_reduction f D a hf
    (hgf.hasInjectiveRepresentative hinjective)

theorem quadraticJetNonsquareLineExcluded_of_resolution_reduction
    (g : PointedMapGerm 2 3) (hinjective : g.HasInjectiveRepresentative)
    (hresolution : ∀ f : PointedMapGerm 2 3, g.RightLeftEquivalent f →
      Nonempty (QuadraticResolutionReductionData f)) :
    QuadraticJetNonsquareLineExcluded g := by
  intro P _hP htail _hnonzero hline
  obtain ⟨Q, hQ, _hQne, hdisc, hcoeff⟩ := hline
  choose a ha using hcoeff
  have hscalar (i : Fin 3) : g.1.component i - constRingHom 2 (a i) *
      coordinatePolynomialAlgHom 2 Q ∈ maximalIdeal 2 ^ 3 := by
    simpa only [ha, map_mul, coordinatePolynomialAlgHom_C] using htail i
  exact nonsquare_scalar_jets_not_hasInjectiveRepresentative_of_resolution_reduction
    g Q hQ hdisc a hscalar hresolution hinjective

end OnLeConjecture.DTwo
