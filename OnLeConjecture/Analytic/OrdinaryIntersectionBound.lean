/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ExactLinearCoordinates
public import OnLeConjecture.Analytic.WeightedParameterTranslation
public import OnLeConjecture.Analytic.UnitIntersection
public import OnLeConjecture.Analytic.OrdinaryNodeFactorization

/-!
# Ordinary order and local intersection

An invertible linear change makes a germ regular of its exact ordinary
order. Convergent preparation and the weighted intersection estimate with
both weights equal to one then give the product lower bound. Neither a
prepared equation nor a chosen tangent direction is an additional input.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- The intersection multiplicity is at least the exact order of the first
germ times any ordinary-order lower bound for the second germ. -/
theorem ordinary_intersection_lower_bound
    (m n : ℕ) (hm : 0 < m) (f h : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hfnext : f ∉ maximalIdeal 2 ^ (m + 1))
    (hh : h ∈ maximalIdeal 2 ^ n) (hfinite : PlaneCurve.HasFiniteIntersection f h) :
    m * n ≤ PlaneCurve.intersectionMultiplicity f h hfinite := by
  obtain ⟨e, hregular⟩ := exists_linear_equiv_regularInFirstCoordinateOfOrder hf hfnext
  have hforder : e.forward.pullbackRingHom f ∈ weightedOrderIdeal 1 (1 * m) := by
    simpa only [one_mul, weightedOrderIdeal_one_eq_maximalIdeal_pow] using
      e.forward.pullback_mem_maximalIdeal_pow hf
  obtain ⟨P, U, hP, hdegree, hU, hfactor, hcoeff⟩ :=
    exists_weierstrass_preparation_with_weighted_coefficients 1 m hm _ hregular hforder
  have hhorder : e.forward.pullbackRingHom h ∈ weightedOrderIdeal 1 n := by
    simpa only [weightedOrderIdeal_one_eq_maximalIdeal_pow] using
      e.forward.pullback_mem_maximalIdeal_pow hh
  have hefinite : PlaneCurve.HasFiniteIntersection
      (e.forward.pullbackRingHom f) (e.forward.pullbackRingHom h) := hfinite.pullback e
  rw [PlaneCurve.intersectionMultiplicity_pullback e hfinite]
  change m * n ≤ PlaneCurve.intersectionMultiplicity
    (e.forward.pullbackRingHom f) (e.forward.pullbackRingHom h) hefinite
  have hfactor' : e.forward.pullbackRingHom f = U * firstCoordinatePolynomialEvaluation P :=
    hfactor.trans (mul_comm _ _)
  have hpreparedFinite : PlaneCurve.HasFiniteIntersection
      (U * firstCoordinatePolynomialEvaluation P) (e.forward.pullbackRingHom h) := by
    rwa [← hfactor']
  have hbound := weighted_intersection_unit_lower_bound_any_order 1 n m (by omega) hm
    P hP hdegree (fun j _ ↦ hcoeff j) U _ hU hhorder hpreparedFinite
  simpa only [hfactor'] using hbound

/-- A vanishing germ meeting an order-`m` germ with intersection less than
`2m` has a nonzero linear term, hence defines a smooth irreducible branch. -/
theorem smooth_irreducible_of_intersection_lt_twice_order
    (m : ℕ) (hm : 0 < m) (f h : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hfnext : f ∉ maximalIdeal 2 ^ (m + 1))
    (hh : h ∈ maximalIdeal 2) (hfinite : PlaneCurve.HasFiniteIntersection f h)
    (hsmall : PlaneCurve.intersectionMultiplicity f h hfinite < 2 * m) :
    differential h ≠ 0 ∧ Irreducible h := by
  apply smooth_irreducible_of_mem_maximalIdeal_not_mem_sq h hh
  intro hsquare
  have hbound := ordinary_intersection_lower_bound m 2 hm f h hf hfnext hsquare hfinite
  omega

end OnLeConjecture.Analytic.Germ
