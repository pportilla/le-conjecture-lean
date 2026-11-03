/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ParameterTranslationBlowup
public import OnLeConjecture.Analytic.AllOrdersPreparation
public import OnLeConjecture.Analytic.FreeChainCoefficientOrder
public import OnLeConjecture.Analytic.WeightedInitialFormDivisibility
public import OnLeConjecture.Analytic.WeightedPrincipalClosure

/-!
# Weighted preparation and translations along a free chain

Weighted membership of an analytic first member gives the corresponding
coefficient orders of its convergent Weierstrass polynomial. Translation
by a parameter germ of order at least the first weight preserves every
weighted order ideal in both directions. These are the analytic facts
used when depressing the polynomial without changing the chain valuation.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- Extension of a parameter germ preserves its parameter-order lower
bound in every positive integral weighting. -/
theorem hyperplaneExtension_mem_weightedOrderIdeal_of_mem_pow
    (A D : ℕ) (hA : 0 < A) (a : Germ 1) (ha : a ∈ maximalIdeal 1 ^ D) :
    hyperplaneExtension 1 a ∈ weightedOrderIdeal A D := by
  have hdiv : coordinate (0 : Fin 1) ^ D ∣ a := by
    rwa [← Ideal.mem_span_singleton, ← maximalIdeal_one_pow_eq_span_coordinate_pow]
  obtain ⟨b, rfl⟩ := hdiv
  rw [map_mul, map_pow, hyperplaneExtension_coordinate_plane]
  apply (weightedOrderIdeal A D).mul_mem_right
  simpa only [pow_zero, one_mul] using
    monomial_mem_weightedOrderIdeal_of_threshold A D 0 D hA (by simp)

/-- A prepared equation has the coefficient bounds determined by its
analytic weighted order. Its arbitrary unit factor is retained. -/
theorem coefficient_mem_pow_of_prepared_weighted_order
    (A m : ℕ) (f U : Germ 2) (P : _root_.Polynomial (Germ 1)) (hU : IsUnit U)
    (hfactor : f = firstCoordinatePolynomialEvaluation P * U)
    (hf : f ∈ weightedOrderIdeal A (A * m)) (j : ℕ) :
    P.coeff j ∈ maximalIdeal 1 ^ (A * (m - j)) := by
  obtain ⟨V, hUV⟩ := hU.exists_right_inv
  have hpoly : firstCoordinatePolynomialEvaluation P ∈ weightedOrderIdeal A (A * m) := by
    have h := (weightedOrderIdeal A (A * m)).mul_mem_right V hf
    simpa only [hfactor, mul_assoc, hUV, mul_one] using h
  have hdiv := coordinate_pow_dvd_firstCoordinateTaylorCoefficient_of_mem_weightedOrderIdeal
    A (A * m) _ hpoly j
  rw [firstCoordinateTaylorCoefficient_polynomialEvaluation,
    ← Nat.mul_sub_left_distrib] at hdiv
  rwa [maximalIdeal_one_pow_eq_span_coordinate_pow, Ideal.mem_span_singleton]

/-- Convergent preparation constructs all weighted coefficient bounds
from the first member's regularity and analytic weighted order. -/
theorem exists_weierstrass_preparation_with_weighted_coefficients
    (A m : ℕ) (hm : 0 < m) (f : Germ 2)
    (hregular : IsRegularInFirstCoordinateOfOrder f m)
    (hf : f ∈ weightedOrderIdeal A (A * m)) :
    ∃ P : _root_.Polynomial (Germ 1), ∃ U : Germ 2,
      P.Monic ∧ P.natDegree = m ∧ IsUnit U ∧
      f = firstCoordinatePolynomialEvaluation P * U ∧
      ∀ j, P.coeff j ∈ maximalIdeal 1 ^ (A * (m - j)) := by
  obtain ⟨P, U, hP, hdegree, _hdistinguished, hU, hfactor⟩ :=
    hasAnalyticWeierstrassFactorizationOfOrder_of_pos hm hregular
  exact ⟨P, U, hP, hdegree, hU, hfactor,
    coefficient_mem_pow_of_prepared_weighted_order A m f U P hU hfactor hf⟩

private theorem coordinate_mem_own_weight (A : ℕ) (hA : 0 < A) :
    coordinate (0 : Fin 2) ∈ weightedOrderIdeal A A ∧
    coordinate (1 : Fin 2) ∈ weightedOrderIdeal A 1 := by
  constructor
  · simpa only [pow_one, pow_zero, mul_one] using
      monomial_mem_weightedOrderIdeal_of_threshold A A 1 0 hA (by simp)
  · simpa only [pow_zero, pow_one, one_mul] using
      monomial_mem_weightedOrderIdeal_of_threshold A 1 0 1 hA (by simp)

/-- Coordinate-image order bounds suffice for an analytic map to
preserve every weighted order ideal. -/
theorem pullback_mem_weightedOrderIdeal_of_coordinate_orders
    (F : PointedMapGerm 2 2) (A D : ℕ) (hA : 0 < A)
    (hx : F.pullbackRingHom (coordinate (0 : Fin 2)) ∈ weightedOrderIdeal A A)
    (hy : F.pullbackRingHom (coordinate (1 : Fin 2)) ∈ weightedOrderIdeal A 1)
    (f : Germ 2) (hf : f ∈ weightedOrderIdeal A D) :
    F.pullbackRingHom f ∈ weightedOrderIdeal A D := by
  obtain ⟨c, hc⟩ := (mem_weightedOrderIdeal_iff A D f).mp hf
  rw [← hc, map_sum]
  apply Ideal.sum_mem
  intro j _
  rw [map_mul]
  apply (weightedOrderIdeal A D).mul_mem_left
  rw [weightedOrderGenerator, map_mul, map_pow, map_pow]
  apply weightedOrderIdeal_antitone A D (A * j.1 + (D - A * j.1)) hA (by omega)
  exact weightedOrderIdeal_mul_mem A _ _ hA
    (pow_mem_weightedOrderIdeal_mul A A j.1 hA hx)
    (by simpa only [one_mul] using
      pow_mem_weightedOrderIdeal_mul A 1 (D - A * j.1) hA hy)

/-- A parameter translation of order at least `A` preserves the full
weight-`(A,1)` filtration, including the converse implication. -/
theorem parameterTranslation_mem_weightedOrderIdeal_iff
    (A D : ℕ) (hA : 0 < A) (a : Germ 1) (ha : a ∈ maximalIdeal 1 ^ A)
    (e : PointedEquivGerm 2)
    (hex : e.forward.pullbackRingHom (coordinate (0 : Fin 2)) =
      coordinate 0 + hyperplaneExtension 1 a)
    (hea : ∀ q : Germ 1, e.forward.pullbackRingHom (hyperplaneExtension 1 q) =
      hyperplaneExtension 1 q) (f : Germ 2) :
    e.forward.pullbackRingHom f ∈ weightedOrderIdeal A D ↔ f ∈ weightedOrderIdeal A D := by
  have hext := hyperplaneExtension_mem_weightedOrderIdeal_of_mem_pow A A hA a ha
  have hx := (coordinate_mem_own_weight A hA).1
  have hy := (coordinate_mem_own_weight A hA).2
  have hey := parameterTranslation_preserves_y e hea
  have hix : e.inverse.pullbackRingHom (coordinate (0 : Fin 2)) =
      coordinate 0 - hyperplaneExtension 1 a := by
    have hfix := congrArg e.pullbackRingEquiv.symm (hea a)
    change e.pullbackRingEquiv.symm (e.pullbackRingEquiv (hyperplaneExtension 1 a)) =
      e.inverse.pullbackRingHom (hyperplaneExtension 1 a) at hfix
    rw [RingEquiv.symm_apply_apply] at hfix
    have h := congrArg e.pullbackRingEquiv.symm hex
    change e.pullbackRingEquiv.symm (e.pullbackRingEquiv (coordinate (0 : Fin 2))) =
      e.inverse.pullbackRingHom (coordinate 0 + hyperplaneExtension 1 a) at h
    rw [RingEquiv.symm_apply_apply, map_add, ← hfix] at h
    exact eq_sub_of_add_eq h.symm
  have hiy : e.inverse.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 := by
    have h := congrArg e.pullbackRingEquiv.symm hey
    change e.pullbackRingEquiv.symm (e.pullbackRingEquiv (coordinate (1 : Fin 2))) =
      e.inverse.pullbackRingHom (coordinate 1) at h
    simpa only [RingEquiv.symm_apply_apply] using h.symm
  constructor
  · intro hf
    have hpull := pullback_mem_weightedOrderIdeal_of_coordinate_orders e.inverse A D hA
      (by rw [hix]; exact (weightedOrderIdeal A A).sub_mem hx hext)
      (by rwa [hiy]) _ hf
    change e.pullbackRingEquiv.symm (e.pullbackRingEquiv f) ∈ weightedOrderIdeal A D at hpull
    simpa only [RingEquiv.symm_apply_apply] using hpull
  · exact pullback_mem_weightedOrderIdeal_of_coordinate_orders e.forward A D hA
      (by rw [hex]; exact (weightedOrderIdeal A A).add_mem hx hext) (by rwa [hey]) f

end OnLeConjecture.Analytic.Germ
