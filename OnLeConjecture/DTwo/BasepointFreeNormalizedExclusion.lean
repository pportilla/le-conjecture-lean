/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.BasepointFreeCriticalFactor
public import OnLeConjecture.DTwo.CriticalAxisQuadraticJetExclusion
public import OnLeConjecture.Analytic.SmoothCriticalNodeNormalization
public import OnLeConjecture.Analytic.SmoothCriticalPlusNodeNormalization

/-!
# The normalized basepoint-free quadratic pencil

The normalized pair has quadratic initial forms `x²+y²` and `y²`.
Their quadratic jets stay independent under every analytic source
equivalence. Together with the constructed smooth critical factor, this
allows the critical-axis exclusion to apply.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

theorem not_scalar_mod_cube_of_normalized_basepointFree_jets
    (v u : Germ 2)
    (hv : v - (coordinate (0 : Fin 2) ^ 2 + coordinate 1 ^ 2) ∈ maximalIdeal 2 ^ 3)
    (hu : u - coordinate (1 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3) :
    ¬ ∃ c : ℂ, u - constRingHom 2 c * v ∈ maximalIdeal 2 ^ 3 := by
  rintro ⟨c, hc⟩
  let P : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 1 ^ 2 -
    MvPolynomial.C c * (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2)
  have hX := MvPolynomial.isWeightedHomogeneous_X ℂ (![1, 1] : Fin 2 → ℕ) (0 : Fin 2)
  have hY := MvPolynomial.isWeightedHomogeneous_X ℂ (![1, 1] : Fin 2 → ℕ) (1 : Fin 2)
  have hP : P.IsWeightedHomogeneous ![1, 1] 2 :=
    (hY.pow 2).sub (((hX.pow 2).add (hY.pow 2)).C_mul c)
  have hmem : coordinatePolynomialAlgHom 2 P ∈ maximalIdeal 2 ^ 3 := by
    have h := (maximalIdeal 2 ^ 3).sub_mem hc
      ((maximalIdeal 2 ^ 3).sub_mem hu ((maximalIdeal 2 ^ 3).mul_mem_left (constRingHom 2 c) hv))
    convert h using 1
    simp only [P, map_sub, map_mul, map_add, map_pow,
      coordinatePolynomialAlgHom_C, coordinatePolynomialAlgHom_X]
    ring
  have hzero : P = 0 :=
    eq_zero_of_isWeightedHomogeneous_coordinatePolynomial_mem_succ 1 2 (by omega) hP
      (by simpa only [weightedOrderIdeal_one_eq_maximalIdeal_pow] using hmem)
  have hx := congrArg (MvPolynomial.eval (![1, 0] : Fin 2 → ℂ)) hzero
  have hc0 : c = 0 := by simpa [P] using hx
  have hy := congrArg (MvPolynomial.eval (![0, 1] : Fin 2 → ℂ)) hzero
  norm_num [P, hc0] at hy

private theorem germ_mem_square_of_quadratic_tail
    (f q : Germ 2) (ht : f - q ∈ maximalIdeal 2 ^ 3) (hq : q ∈ maximalIdeal 2 ^ 2) :
    f ∈ maximalIdeal 2 ^ 2 := by
  simpa only [sub_add_cancel] using (maximalIdeal 2 ^ 2).add_mem
    (Ideal.pow_le_pow_right (by decide : 2 ≤ 3) ht) hq

/-- The analytic exclusion is invariant under a supplied normalized node
coordinate system. This helper retains all exact pullback equations. -/
theorem not_hasInjectiveRepresentative_of_normalized_basepointFree_node_coordinates
    (g : PointedMapGerm 2 3) (h U : Germ 2) (e : PointedEquivGerm 2)
    (hv : g.1.component 0 - (coordinate (0 : Fin 2) ^ 2 + coordinate 1 ^ 2) ∈ maximalIdeal 2 ^ 3)
    (hu : g.1.component 1 - coordinate (1 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3)
    (hw : g.1.component 2 ∈ maximalIdeal 2 ^ 2)
    (heP : e.forward.pullbackRingHom (g.1.component 0) = cyclicFirst 2)
    (heh : e.forward.pullbackRingHom h = coordinate (1 : Fin 2) * U)
    (hJQ : h ∣ jacobian (g.1.component 0) (g.1.component 1))
    (hJZ : h ∣ jacobian (g.1.component 0) (g.1.component 2)) :
    ¬ g.HasInjectiveRepresentative := by
  let f := g.comp e.forward
  have hgf : g.RightLeftEquivalent f := by
    refine ⟨e, PointedEquivGerm.identity 3, ?_⟩
    rw [PointedEquivGerm.identity_forward, PointedMapGerm.identity_comp]
  have hf0 : f.1.component 0 = cyclicFirst 2 := by
    rw [PointedMapGerm.component_comp_eq_pullback]
    exact heP
  have hu2 := germ_mem_square_of_quadratic_tail _ _ hu
    (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 1) 2)
  have hderivative (i : Fin 3) (hmem : g.1.component i ∈ maximalIdeal 2 ^ 2) :
      valueRingHom 2 (partialDerivative 0 (f.1.component i)) = 0 := by
    have hfpull := e.forward.pullback_mem_maximalIdeal_pow hmem
    have hh := partialDerivative_mem_maximalIdeal_pow_of_mem_pow_succ (0 : Fin 2) hfpull
    rw [PointedMapGerm.component_comp_eq_pullback]
    exact mem_maximalIdeal_iff.mp (by simpa only [pow_one] using hh)
  have hdiv (i : Fin 3) (hJ : h ∣ jacobian (g.1.component 0) (g.1.component i)) :
      coordinate (1 : Fin 2) ^ (2 - 1) ∣ jacobian (f.1.component 0) (f.1.component i) := by
    rw [PointedMapGerm.component_comp_eq_pullback, PointedMapGerm.component_comp_eq_pullback]
    exact e.coordinate_pow_dvd_jacobian_of_pullback_multiple h _ _ U 1 heh
      (by simpa only [pow_one] using hJ)
  have hquad : ¬ ((∃ c : ℂ, f.1.component 1 - constRingHom 2 c * cyclicFirst 2 ∈
        maximalIdeal 2 ^ 3) ∧
      (∃ c : ℂ, f.1.component 2 - constRingHom 2 c * cyclicFirst 2 ∈ maximalIdeal 2 ^ 3)) := by
    rintro ⟨⟨c, hc⟩, _⟩
    apply not_scalar_mod_cube_of_normalized_basepointFree_jets _ _ hv hu
    refine ⟨c, ?_⟩
    have hpull : e.forward.pullbackRingHom
        (g.1.component 1 - constRingHom 2 c * g.1.component 0) ∈ maximalIdeal 2 ^ 3 := by
      simpa only [f, map_sub, map_mul, PointedMapGerm.pullback_constRingHom, heP,
        PointedMapGerm.component_comp_eq_pullback] using hc
    have hback := e.inverse.pullback_mem_maximalIdeal_pow hpull
    change e.pullbackRingEquiv.symm (e.pullbackRingEquiv
      (g.1.component 1 - constRingHom 2 c * g.1.component 0)) ∈ maximalIdeal 2 ^ 3 at hback
    simpa only [e.pullbackRingEquiv.symm_apply_apply] using hback
  intro hg
  exact critical_axis_independent_quadratic_jets_not_hasInjectiveRepresentative f 2 (by omega)
    hf0 (hderivative 1 hu2) (hderivative 2 hw) (hdiv 1 hJQ) (hdiv 2 hJZ) hquad
      (hgf.hasInjectiveRepresentative hg)

/-- A normalized basepoint-free quadratic pencil and a nonunit common
Jacobian divisor exclude injectivity. Smoothness of a critical factor,
its exact intersection, and preserving node coordinates are all derived. -/
theorem normalized_basepointFree_pencil_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (c : Germ 2)
    (hv : g.1.component 0 - (coordinate (0 : Fin 2) ^ 2 + coordinate 1 ^ 2) ∈ maximalIdeal 2 ^ 3)
    (hu : g.1.component 1 - coordinate (1 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3)
    (hw : g.1.component 2 ∈ maximalIdeal 2 ^ 2)
    (hc : c ∈ maximalIdeal 2)
    (hvu : c ∣ jacobian (g.1.component 0) (g.1.component 1))
    (hvw : c ∣ jacobian (g.1.component 0) (g.1.component 2))
    (huw : c ∣ jacobian (g.1.component 1) (g.1.component 2)) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨h, hh, hdh, _hi, _hc, hJQ, hJZ, _huw, htail⟩ :=
    exists_smooth_common_factor_of_normalized_basepointFree_jets
      _ _ _ c hv hu hc hvu hvw huw
  obtain ⟨hfinite, hinter⟩ := intersection_two_of_sum_squares_and_axis_tail _ h hv htail
  have hfinite' := (PlaneCurve.hasFiniteIntersection_comm _ _).mp hfinite
  have hinter' : PlaneCurve.intersectionMultiplicity h (g.1.component 0) hfinite' = 2 :=
    (PlaneCurve.intersectionMultiplicity_comm _ _ hfinite).symm.trans hinter
  obtain ⟨e, U, _hU, heP, heh⟩ :=
    exists_smooth_critical_plus_node_normalization _ h hv hh hdh hfinite' hinter'
  exact not_hasInjectiveRepresentative_of_normalized_basepointFree_node_coordinates
    g h U e hv hu hw heP heh hJQ hJZ

end OnLeConjecture.DTwo
