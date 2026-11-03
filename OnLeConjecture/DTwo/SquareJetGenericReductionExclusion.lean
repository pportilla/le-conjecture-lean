/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.QuadraticMilnorReductionData
public import OnLeConjecture.DTwo.QuadraticGenericJets
public import OnLeConjecture.DTwo.SquareJetUnpreparedExclusion
public import OnLeConjecture.Analytic.TargetPairLinearCompletion
public import OnLeConjecture.Analytic.JacobianLinearSpan

/-!
# The square-jet case with an actual generic-member choice

The first coefficient row is chosen inside the open set of the reduction,
with nonzero quadratic coefficient and exact order at every recorded center.
Finite intersection with the companion row constructs an invertible target
completion. The curve invariants and numerical alternatives are then proved
for that specified first member.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ PlaneCurve Numerical

theorem square_jet_excluded_of_general_member_reduction
    (g : PointedMapGerm 2 3) (hdifferential : g.differential = 0)
    (D : QuadraticMilnorReductionData g)
    (u v : ℂ) (huv : u ≠ 0 ∨ v ≠ 0) (a : Fin 3 → ℂ)
    (htail : ∀ i, g.1.component i - coordinatePolynomialAlgHom 2
      (MvPolynomial.C (a i) * binaryLinearForm u v ^ 2) ∈ maximalIdeal 2 ^ 3) :
    ¬ g.HasInjectiveRepresentative := by
  let P := coordinatePolynomialAlgHom 2 (binaryLinearForm u v ^ 2)
  have htail' (i : Fin 3) : g.1.component i - constRingHom 2 (a i) * P ∈
      maximalIdeal 2 ^ 3 := by
    simpa only [map_mul, coordinatePolynomialAlgHom_C] using htail i
  have hweak (i : Fin 3) : D.weakData.generators D.pointBasis.root i -
      constRingHom 2 (a i) * P ∈ maximalIdeal 2 ^ 3 := by
    simpa only [D.root_generators] using htail' i
  have hlinear := root_scalarJetCoefficient_ne_zero D.weakData D.root_multiplicity a P hweak
  obtain ⟨q, hqU, _hqorder, hnonzero⟩ :=
    D.weakData.exists_coefficients_exact_orders_linear_conditions_mem_open
      (fun _ : Fin 1 => scalarJetCoefficient a) (fun _ => hlinear)
      D.coefficientOpen D.coefficientOpen_isOpen D.coefficientOpen_nonempty
  have hqa : scalarJetCoefficient a q ≠ 0 := hnonzero 0
  have hqne : q ≠ 0 := by
    intro hz
    exact hqa (by rw [hz, map_zero])
  obtain ⟨R⟩ := D.generalMemberReduction q hqU
  obtain ⟨s, F, hgF, hF⟩ :=
    exists_target_pair_linearCombination_of_finite_intersection g q R.companion hqne R.pair_finite
  have hF0 : F.1.component 0 = germLinearCombination g.1.component q := hF 0
  have hF1 : F.1.component 1 = germLinearCombination g.1.component R.companion := hF 1
  let Q := MvPolynomial.C (scalarJetCoefficient a q) * binaryLinearForm u v ^ 2
  have hQ : Q.IsHomogeneous 2 := ((binaryLinearForm_isHomogeneous u v).pow 2).C_mul _
  have hQne : Q ≠ 0 := mul_ne_zero (MvPolynomial.C_ne_zero.mpr hqa)
    (pow_ne_zero 2 (binaryLinearForm_ne_zero_of_coefficients huv))
  have hdisc : binaryQuadraticDiscriminant Q = 0 :=
    binaryQuadraticDiscriminant_C_mul_binaryLinearForm_sq _ _ _
  have hfirst : F.1.component 0 - coordinatePolynomialAlgHom 2 Q ∈ maximalIdeal 2 ^ 3 := by
    rw [hF0]
    simpa only [Q, map_mul, coordinatePolynomialAlgHom_C] using
      linearCombination_scalar_jet_tail g.1.component a P 3 htail' q
  have hreduced : Squarefree (F.1.component 0) := by rw [hF0]; exact D.member_reduced q hqU
  have hdiff : F.differential = 0 :=
    (PointedMapGerm.rightLeftEquivalent_differential_eq_zero_iff hgF).mpr hdifferential
  let c := D.proximityData.proximity
  have hcroot : c.multiplicity c.root = 2 := by
    rw [D.proximityData.multiplicity_eq, D.proximityData.root_eq]
    exact D.root_multiplicity
  have hcpositive (p : Fin D.cardinality) : 1 ≤ c.multiplicity p := by
    rw [D.proximityData.multiplicity_eq]
    exact D.pointBasis.multiplicity_pos p
  have hbranches : c.branchCount = irreducibleBranchCount (F.1.component 0) := by
    rw [hF0]
    exact D.branchCount_eq q hqU
  have hisolated : HasIsolatedCriticalPoint (F.1.component 0) := by
    rw [hF0]
    exact D.member_isolated q hqU
  have hgenusFull : c.squareMultiplicity + 1 =
      milnorNumber (F.1.component 0) hisolated + c.totalMultiplicity + c.branchCount := by
    simpa only [c, ProximityCertificate.squareMultiplicity, ProximityCertificate.totalMultiplicity,
      D.proximityData.multiplicity_eq, MultiplicityCounts.sum, hF0] using D.genus_identity q hqU
  have hgenus := quadratic_genus_identity_of_point_basis_sums c D.pointBasis.generation
    D.proximityData.generation_decreases hcroot hcpositive _ hgenusFull
  have hfiniteCritical : HasFiniteIntersection (F.1.component 0) R.critical := by
    rw [hF0]
    exact (hasFiniteIntersection_comm _ _).mp R.critical_finite
  have hcriticalI : intersectionMultiplicity (F.1.component 0) R.critical hfiniteCritical =
      intersectionMultiplicity R.critical (germLinearCombination g.1.component q)
        R.critical_finite := by
    simpa only [hF0] using
      (intersectionMultiplicity_comm _ _ R.critical_finite).symm
  have htransverse : c.totalMultiplicity ≤ R.exponent := by
    simpa only [c, ProximityCertificate.totalMultiplicity, D.proximityData.multiplicity_eq,
      MultiplicityCounts.sum] using R.totalMultiplicity_le
  have hpolar : intersectionMultiplicity (F.1.component 0) R.critical hfiniteCritical *
        (R.exponent - 1) + c.totalMultiplicity + c.branchCount ≤ 2 * c.squareMultiplicity := by
    rw [hcriticalI, hbranches, hF0]
    simpa only [c, ProximityCertificate.totalMultiplicity,
      ProximityCertificate.squareMultiplicity, D.proximityData.multiplicity_eq,
      MultiplicityCounts.sum] using R.polar
  have hspan (i : Fin 3) : F.1.component i ∈ Submodule.span ℂ (Set.range g.1.component) := by
    rw [hF]
    change (∑ j, (![q, R.companion, s] i) j • g.1.component j) ∈ _
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j))
  have hminors (i : Fin 2) : R.critical ^ (R.exponent - 1) ∣
      jacobian (F.1.component 0) (F.1.component i.succ) :=
    dvd_jacobian_of_mem_linear_span g.1.component _ R.common_minors (hspan 0) (hspan i.succ)
  have hfinitePair : HasFiniteIntersection (F.1.component 0) (F.1.component 1) := by
    rw [hF0, hF1]
    exact R.pair_finite
  have hpair : intersectionMultiplicity (F.1.component 0) (F.1.component 1) hfinitePair =
      c.squareMultiplicity := by
    simpa only [hF0, hF1, c, ProximityCertificate.squareMultiplicity,
      D.proximityData.multiplicity_eq] using R.pair_intersection
  intro hinjective
  exact square_quadratic_jet_reduction_not_hasInjectiveRepresentative F c D.pointBasis.generation
    D.proximityData.generation_decreases hcroot hcpositive Q hQ hQne hdisc hfirst hreduced hdiff
    hbranches hisolated hgenus R.critical R.critical_mem hfiniteCritical R.exponent
    htransverse hpolar hminors 0 hfinitePair hpair (hgF.hasInjectiveRepresentative hinjective)

end OnLeConjecture.DTwo
