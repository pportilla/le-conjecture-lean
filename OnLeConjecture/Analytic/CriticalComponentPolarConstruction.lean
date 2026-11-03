/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GeneralTeissierPolarIdentity
public import OnLeConjecture.Analytic.ProductDivisorIntersectionBound
public import OnLeConjecture.Analytic.GeneralResolutionReductionFromComponents
public import OnLeConjecture.Analytic.JacobianLinearSpan

/-!
# Polar estimates from a common critical divisor

The component data in this file contains only equations, transverse
multiplicities, divisibility of the coordinate minors, and the two global
numerical estimates. Teissier's identity and intersection additivity
construct the component intersections and their polar bound from the
member's companion intersection and Milnor identity.
-/

public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ PlaneCurve Numerical
open scoped BigOperators

/-- The remaining critical-divisor and global numerical data, independent
of the member coefficients. No polar estimate or finite intersection is
assumed. -/
structure CriticalDivisorEstimateData
    (g : PointedMapGerm 2 3) (M S : ℕ) (ι : Type*) [Fintype ι] where
  component : ι → Germ 2
  transverseMultiplicity : ι → ℕ
  component_mem : ∀ i, component i ∈ maximalIdeal 2
  two_le_multiplicity : ∀ i, 2 ≤ transverseMultiplicity i
  total_le_max : M ≤ Finset.univ.sup transverseMultiplicity
  global_estimate : S + M ≤ 3 * Finset.univ.sup transverseMultiplicity
  product_dvd_ordered_minors : ∀ j k : Fin 3, j < k →
    (∏ i, component i ^ (transverseMultiplicity i - 1)) ∣
      jacobian (g.1.component j) (g.1.component k)

namespace CriticalDivisorEstimateData

variable {g : PointedMapGerm 2 3} {M S : ℕ} {ι : Type*} [Fintype ι]

/-- Alternation extends the ordered-minor divisibility to all pairs. -/
theorem product_dvd_minors (D : CriticalDivisorEstimateData g M S ι) (j k : Fin 3) :
    (∏ i, D.component i ^ (D.transverseMultiplicity i - 1)) ∣
      jacobian (g.1.component j) (g.1.component k) := by
  rcases lt_trichotomy j k with hlt | heq | hgt
  · exact D.product_dvd_ordered_minors j k hlt
  · subst k
    rw [jacobian_self]
    exact dvd_zero _
  · rw [jacobian_swap]
    exact dvd_neg.mpr (D.product_dvd_ordered_minors k j hgt)

/-- The full polar inequality follows algebraically from the companion
intersection and Milnor identities. -/
theorem exists_member_polar_estimate
    (D : CriticalDivisorEstimateData g M S ι) (b : ℕ) (q r : Fin 3 → ℂ)
    (hsquarefree : Squarefree (germLinearCombination g.1.component q))
    (hisolated : HasIsolatedCriticalPoint (germLinearCombination g.1.component q))
    (hpair : HasFiniteIntersection (germLinearCombination g.1.component q)
      (germLinearCombination g.1.component r))
    (hintersection : intersectionMultiplicity (germLinearCombination g.1.component q)
      (germLinearCombination g.1.component r) hpair = S)
    (hgenus : S + 1 = milnorNumber (germLinearCombination g.1.component q) hisolated + M + b) :
    ∃ hfinite : ∀ i, HasFiniteIntersection (D.component i) (germLinearCombination g.1.component q),
      (∑ i, intersectionMultiplicity (D.component i) (germLinearCombination g.1.component q)
        (hfinite i) * (D.transverseMultiplicity i - 1)) + M + b ≤ 2 * S := by
  classical
  let f := germLinearCombination g.1.component q
  let u := germLinearCombination g.1.component r
  have hpointed (a : Fin 3 → ℂ) : germLinearCombination g.1.component a ∈ maximalIdeal 2 :=
    germLinearCombination_mem _ _
      (fun i => g.coordinateIdeal_le_maximalIdeal (g.1.component_mem_coordinateIdeal i)) a
  have hspan (a : Fin 3 → ℂ) : germLinearCombination g.1.component a ∈
      Submodule.span ℂ (Set.range g.1.component) := by
    change (∑ i, a i • g.1.component i) ∈ Submodule.span ℂ (Set.range g.1.component)
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  have hdiv : (∏ i, D.component i ^ (D.transverseMultiplicity i - 1)) ∣ jacobian f u :=
    dvd_jacobian_of_mem_linear_span g.1.component _ D.product_dvd_minors (hspan q) (hspan r)
  obtain ⟨hpolar, _hJ, hidentity⟩ := exists_polar_intersection_identity f u
    (hpointed q) (hpointed r) hsquarefree hpair
  have hJfinite : HasFiniteIntersection (jacobian f u) f :=
    (hasFiniteIntersection_comm _ _).mp
      ((hasFinitePolarIntersection_iff_hasFiniteIntersection f u).mp hpolar)
  have hprod := hJfinite.of_dvd_left hdiv
  have hfinite (i : ι) : HasFiniteIntersection (D.component i) f := by
    apply hprod.of_dvd_left
    apply (dvd_pow_self _ (n := D.transverseMultiplicity i - 1)
      (by have h := D.two_le_multiplicity i; omega)).trans
    exact Finset.dvd_prod_of_mem (fun i => D.component i ^ (D.transverseMultiplicity i - 1))
      (Finset.mem_univ i)
  have hbound := weighted_intersection_sum_le_of_product_pow_dvd D.component
    (fun i => D.transverseMultiplicity i - 1) f (jacobian f u) hfinite hJfinite hdiv
  have hpolarEq : intersectionMultiplicity (jacobian f u) f hJfinite =
      polarIntersectionMultiplicity f u hpolar := by
    rw [intersectionMultiplicity_comm]
    exact (polarIntersectionMultiplicity_eq_intersectionMultiplicity f u hpolar).symm
  rw [hpolarEq] at hbound
  change polarIntersectionMultiplicity f u hpolar + 1 =
    milnorNumber f hisolated + intersectionMultiplicity f u hpair at hidentity
  rw [hintersection] at hidentity
  refine ⟨hfinite, ?_⟩
  change (∑ i, intersectionMultiplicity (D.component i) f (hfinite i) *
    (D.transverseMultiplicity i - 1)) + M + b ≤ 2 * S
  change S + 1 = milnorNumber f hisolated + M + b at hgenus
  omega

/-- Curve invariants supply all member-dependent fields of the original
critical-component record. -/
@[expose] noncomputable def toCriticalComponentReductionData
    {N : ℕ} (c : AnalyticPointBasis N) (d : AnalyticProximityData c)
    (D : CriticalDivisorEstimateData g (MultiplicityCounts.sum c.multiplicity)
      (MultiplicityCounts.squareSum c.multiplicity) ι)
    (U : Set (Fin 3 → ℂ))
    (hcurves : ∀ q ∈ U, Nonempty (GeneralMemberCurveInvariants g c d q)) :
    CriticalComponentReductionData g (MultiplicityCounts.sum c.multiplicity)
      (MultiplicityCounts.squareSum c.multiplicity) d.proximity.branchCount U ι := by
  classical
  let C := fun q hq => Classical.choice (hcurves q hq)
  choose hfinite hpolar using fun q hq => D.exists_member_polar_estimate
    d.proximity.branchCount q (C q hq).companion (C q hq).reduced (C q hq).isolated
    (C q hq).pair_finite (C q hq).pair_intersection (C q hq).genus
  exact {
    component := D.component
    transverseMultiplicity := D.transverseMultiplicity
    component_mem := D.component_mem
    two_le_multiplicity := D.two_le_multiplicity
    total_le_max := D.total_le_max
    global_estimate := D.global_estimate
    product_dvd_ordered_minors := D.product_dvd_ordered_minors
    intersection_finite := hfinite
    polar_sum := hpolar }

end CriticalDivisorEstimateData

end OnLeConjecture.Analytic
