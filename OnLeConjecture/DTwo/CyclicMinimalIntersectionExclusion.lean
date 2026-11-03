/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicCriticalAxisExclusion
public import OnLeConjecture.Analytic.OrdinaryIntersectionBound
public import OnLeConjecture.Analytic.PointBlowupChart
public import OnLeConjecture.PlaneCurve.PairGeneratorChange

/-!
# Minimal intersection along a smooth critical axis

After removing the terms divisible by the first component, the second
component is `y^k H`. If `H` vanished, the ordinary intersection bound
would exceed `2k`. Thus the selected intersection supplies the unit
coefficient required by the cyclic exclusion.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

theorem cyclicFirst_exact_order_two (k : ℕ) (hk : 2 ≤ k) :
    cyclicFirst k ∈ maximalIdeal 2 ^ 2 ∧ cyclicFirst k ∉ maximalIdeal 2 ^ 3 := by
  constructor
  · exact (maximalIdeal 2 ^ 2).add_mem
      (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 0) 2)
      (Ideal.pow_le_pow_right hk (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 1) k))
  · intro hh
    have hr := pointBlowupExceptionalLine.pullback_mem_maximalIdeal_pow hh
    simp only [cyclicFirst, map_add, map_pow, pointBlowupExceptionalLine_pullback_zero,
      pointBlowupExceptionalLine_pullback_one, zero_pow (by omega : k ≠ 0), add_zero,
      mem_maximalIdeal_one_pow_iff, vanishingOrder_coordinate_pow] at hr
    norm_num at hr

theorem transverse_coefficient_nonzero_of_cyclic_minimal_intersection
    (k : ℕ) (hk : 2 ≤ k) (Q : Germ 2) (A B : Germ 1) (H : Germ 2)
    (hA : A ∈ maximalIdeal 1) (hB : B ∈ maximalIdeal 1)
    (hQ : Q = (cyclicScalarMap k (by omega)).pullbackRingHom A +
      coordinate 0 * (cyclicScalarMap k (by omega)).pullbackRingHom B + coordinate 1 ^ k * H)
    (hfinite : PlaneCurve.HasFiniteIntersection (cyclicFirst k) Q)
    (hsmall : PlaneCurve.intersectionMultiplicity (cyclicFirst k) Q hfinite ≤ 2 * k) :
    valueRingHom 2 H ≠ 0 := by
  intro hzero
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp
    (show A ∈ Ideal.span {coordinate (0 : Fin 1)} by
      rwa [← maximalIdeal_one_eq_span_coordinate])
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp
    (show B ∈ Ideal.span {coordinate (0 : Fin 1)} by
      rwa [← maximalIdeal_one_eq_span_coordinate])
  let σ := cyclicScalarMap k (by omega : 1 ≤ k)
  let q := σ.pullbackRingHom a + coordinate 0 * σ.pullbackRingHom b
  have hcoord : σ.pullbackRingHom (coordinate 0) = cyclicFirst k := by
    rw [PointedMapGerm.pullback_coordinate, cyclicScalarMap_component]
    rfl
  have heq : Q - cyclicFirst k * q = coordinate 1 ^ k * H := by
    rw [hQ, ha, hb, map_mul, map_mul]
    change (σ.pullbackRingHom (coordinate 0) * σ.pullbackRingHom a +
      coordinate 0 * (σ.pullbackRingHom (coordinate 0) * σ.pullbackRingHom b) +
      coordinate 1 ^ k * H) - cyclicFirst k * q = _
    rw [hcoord]
    dsimp only [q]
    ring
  have hideal : PlaneCurve.pairIdeal (cyclicFirst k) Q =
      PlaneCurve.pairIdeal (cyclicFirst k) (coordinate 1 ^ k * H) := by
    rw [← heq, PlaneCurve.pairIdeal_sub_mul_right]
  have hfinite' := hfinite.of_pairIdeal_eq hideal
  have hi := PlaneCurve.intersectionMultiplicity_eq_of_pairIdeal_eq hfinite hfinite' hideal
  have horder : coordinate (1 : Fin 2) ^ k * H ∈ maximalIdeal 2 ^ (k + 1) := by
    simpa only [pow_succ] using Ideal.mul_mem_mul
      (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 1) k)
      (mem_maximalIdeal_iff.mpr hzero)
  obtain ⟨hP, hPnext⟩ := cyclicFirst_exact_order_two k hk
  have hbound := ordinary_intersection_lower_bound 2 (k + 1) (by omega)
    (cyclicFirst k) (coordinate 1 ^ k * H) hP hPnext horder hfinite'
  omega

/-- The critical-axis divisibility and a selected intersection at most
`2k` exclude an injective representative. No unit or odd axis
coefficient is supplied as an assumption. -/
theorem critical_axis_minimal_intersection_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (k : ℕ) (hk : 2 ≤ k)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQderivative : valueRingHom 2 (partialDerivative 0 (g.1.component 1)) = 0)
    (hZderivative : valueRingHom 2 (partialDerivative 0 (g.1.component 2)) = 0)
    (hJQ : coordinate (1 : Fin 2) ^ (k - 1) ∣ jacobian (g.1.component 0) (g.1.component 1))
    (hJZ : coordinate (1 : Fin 2) ^ (k - 1) ∣ jacobian (g.1.component 0) (g.1.component 2))
    (hfinite : PlaneCurve.HasFiniteIntersection (g.1.component 0) (g.1.component 1))
    (hsmall : PlaneCurve.intersectionMultiplicity (g.1.component 0) (g.1.component 1)
      hfinite ≤ 2 * k) :
    ¬ g.HasInjectiveRepresentative := by
  rw [hP] at hJQ hJZ
  obtain ⟨A, B, H₂, hQ⟩ := exists_cyclic_axis_decomposition k (by omega) (g.1.component 1) hJQ
  obtain ⟨C, D, H₃, hZ⟩ := exists_cyclic_axis_decomposition k (by omega) (g.1.component 2) hJZ
  have hcomponentzero (i : Fin 3) : valueRingHom 2 (g.1.component i) = 0 := by
    rw [← PointedMapGerm.pullback_coordinate, PointedMapGerm.valueRingHom_pullback,
      valueRingHom_coordinate]
  have hA : A ∈ maximalIdeal 1 := by
    rw [mem_maximalIdeal_iff, value_even_coefficient_of_cyclic_axis_decomposition
      k (by omega) _ A B H₂ hQ]
    exact hcomponentzero 1
  have hC : C ∈ maximalIdeal 1 := by
    rw [mem_maximalIdeal_iff, value_even_coefficient_of_cyclic_axis_decomposition
      k (by omega) _ C D H₃ hZ]
    exact hcomponentzero 2
  have hB : valueRingHom 1 B = 0 :=
    (value_odd_coefficient_of_cyclic_axis_decomposition k (by omega) _ A B H₂ hQ).trans hQderivative
  have hD : valueRingHom 1 D = 0 :=
    (value_odd_coefficient_of_cyclic_axis_decomposition k (by omega) _ C D H₃ hZ).trans hZderivative
  have hunit : valueRingHom 2 H₂ ≠ 0 := by
    have hf : PlaneCurve.HasFiniteIntersection (cyclicFirst k) (g.1.component 1) := by
      rwa [← hP]
    apply transverse_coefficient_nonzero_of_cyclic_minimal_intersection k hk _ A B H₂
      hA (mem_maximalIdeal_iff.mpr hB) hQ hf
    simpa only [hP] using hsmall
  exact not_hasInjectiveRepresentative_of_critical_axis_decompositions
    g k hk A B C D hA hC hB hD H₂ H₃ (Or.inl hunit) hP hQ hZ

end OnLeConjecture.DTwo
