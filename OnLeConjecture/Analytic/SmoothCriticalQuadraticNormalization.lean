/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SmoothCriticalNodeNormalization

/-!
# Reduced quadratic preparation preserving a smooth critical curve

The parameter remainder is nonzero because the original equation is
squarefree. Its order is at least two because the original equation is
in the square of the maximal ideal. An analytic root of its unit factor
normalizes it to a pure power and retains the specified curve up to a unit.
No parity or relation between this power and resolution counts is assumed.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- Pure-power normalization of a nonzero parameter remainder, including
the unit multiple relating the old parameter to the new parameter. -/
theorem exists_parameter_power_normalization_preserving_curve
    (r : Germ 1) (hrne : r ≠ 0) (hr : r ∈ maximalIdeal 1) :
    ∃ k : ℕ, 0 < k ∧ vanishingOrder r = k ∧
      ∃ e : PointedEquivGerm 2, ∃ U : Germ 2, IsUnit U ∧
        e.pullbackAlgEquiv (coordinate (0 : Fin 2) ^ 2 + hyperplaneExtension 1 r) =
          coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ k ∧
        e.pullbackAlgEquiv (coordinate (0 : Fin 2)) = coordinate (0 : Fin 2) ∧
        e.pullbackAlgEquiv (coordinate (1 : Fin 2)) = coordinate (1 : Fin 2) * U := by
  obtain ⟨k, hk, w, hw, hrw⟩ :=
    exists_eq_coordinate_mul_unit_pow_of_mem_maximalIdeal hrne hr
  have horder : vanishingOrder r = k :=
    vanishingOrder_eq_of_eq_coordinate_pow_mul_unit (hw.pow k) (by rw [hrw, mul_pow])
  let V := hyperplaneExtension 1 w
  have hV : IsUnit V := hw.map (hyperplaneExtension 1)
  let parameter := coordinate (1 : Fin 2) * V
  have hparameter : parameter ∈ maximalIdeal 2 :=
    (maximalIdeal 2).mul_mem_right V (coordinate_mem_maximalIdeal 1)
  have hregular : valueRingHom 2 (partialDerivative (1 : Fin 2) parameter) ≠ 0 := by
    change valueRingHom 2 (partialDerivative (1 : Fin 2) (coordinate (1 : Fin 2) * V)) ≠ 0
    rw [partialDerivative_mul, partialDerivative_coordinate_same]
    simpa using valueRingHom_ne_zero_of_isUnit hV
  obtain ⟨c, hc1, hc0⟩ := PlaneCurve.exists_equiv_pullback_coordinate_one_eq_preserving_zero
    parameter hparameter hregular
  have hparameterPow : parameter ^ k = hyperplaneExtension 1 r := by
    rw [hrw, map_pow, map_mul, hyperplaneExtension_coordinate]
    rfl
  have hc : c.pullbackAlgEquiv (coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ k) =
      coordinate (0 : Fin 2) ^ 2 + hyperplaneExtension 1 r := by
    rw [map_add, map_pow, map_pow, hc0, hc1, hparameterPow]
  let e := c.symm
  have he : e.pullbackAlgEquiv (coordinate (0 : Fin 2) ^ 2 + hyperplaneExtension 1 r) =
      coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ k := by
    have h := congrArg c.pullbackAlgEquiv.symm hc
    rw [c.pullbackAlgEquiv.symm_apply_apply] at h
    exact h.symm
  have he0 : e.pullbackAlgEquiv (coordinate (0 : Fin 2)) = coordinate (0 : Fin 2) := by
    have h := congrArg c.pullbackAlgEquiv.symm hc0
    rw [c.pullbackAlgEquiv.symm_apply_apply] at h
    exact h.symm
  have heparameter : e.pullbackAlgEquiv (coordinate (1 : Fin 2)) * e.pullbackAlgEquiv V =
      coordinate (1 : Fin 2) := by
    have h := congrArg c.pullbackAlgEquiv.symm hc1
    rw [c.pullbackAlgEquiv.symm_apply_apply] at h
    exact (map_mul e.pullbackAlgEquiv _ _).symm.trans h.symm
  obtain ⟨v, hv⟩ := hV.map e.pullbackAlgEquiv.toRingHom
  change (v : Germ 2) = e.pullbackAlgEquiv V at hv
  refine ⟨k, hk, horder, e, ↑v⁻¹, (v⁻¹).isUnit, he, he0, ?_⟩
  rw [← hv] at heparameter
  calc
    e.pullbackAlgEquiv (coordinate (1 : Fin 2)) =
      (e.pullbackAlgEquiv (coordinate (1 : Fin 2)) * ↑v) * ↑v⁻¹ := by simp
    _ = coordinate (1 : Fin 2) * ↑v⁻¹ := by rw [heparameter]

/-- A reduced equation of order at least two with intersection two with
a specified smooth curve admits quadratic power coordinates preserving
that curve. The power and the convergent equivalence are constructed. -/
theorem exists_smooth_critical_quadratic_normalization
    (v h : Germ 2) (hv : v ∈ maximalIdeal 2 ^ 2) (hvsq : Squarefree v)
    (hh : h ∈ maximalIdeal 2) (hdh : differential h ≠ 0)
    (hfinite : PlaneCurve.HasFiniteIntersection h v)
    (hi : PlaneCurve.intersectionMultiplicity h v hfinite = 2) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ e : PointedEquivGerm 2, ∃ U : Germ 2, IsUnit U ∧
      e.forward.pullbackRingHom v = coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ k ∧
      e.forward.pullbackRingHom h = coordinate (1 : Fin 2) * U := by
  obtain ⟨a, ha, hregular⟩ := exists_smooth_second_coordinate_regular_first
    h v hh hdh hfinite 2 hi
  obtain ⟨b, r, hform, _hfix, hb1, hr⟩ :=
    PlaneCurve.exists_parametric_morse_normal_form_of_regular_order_two
      (a.forward.pullbackRingHom v) hregular
  let e₀ := a.comp b
  have he₀h : e₀.pullbackAlgEquiv h = coordinate (1 : Fin 2) := by
    rw [PointedEquivGerm.pullbackAlgEquiv_comp_apply]
    change b.pullbackAlgEquiv (a.forward.pullbackRingHom h) = _
    rw [ha]
    exact (b.forward.pullback_coordinate (1 : Fin 2)).trans hb1
  have he₀v : e₀.pullbackAlgEquiv v = coordinate (0 : Fin 2) ^ 2 + hyperplaneExtension 1 r := by
    rw [PointedEquivGerm.pullbackAlgEquiv_comp_apply]
    exact hform
  have hrne : r ≠ 0 := by
    intro hz
    have hs := e₀.squarefree_pullback v hvsq
    change Squarefree (e₀.pullbackAlgEquiv v) at hs
    rw [he₀v, hz, map_zero, add_zero] at hs
    have hu : IsUnit (coordinate (0 : Fin 2)) :=
      hs _ (by rw [← pow_two])
    exact valueRingHom_ne_zero_of_isUnit hu (by simp)
  have hr2 : r ∈ maximalIdeal 1 ^ 2 := by
    have hvpull := e₀.forward.pullback_mem_maximalIdeal_pow hv
    have hrest := (hyperplaneInclusionGerm 1).pullback_mem_maximalIdeal_pow hvpull
    change hyperplaneRestriction 1 (e₀.pullbackAlgEquiv v) ∈ maximalIdeal 1 ^ 2 at hrest
    rw [he₀v, map_add, map_pow, hyperplaneRestriction_coordinate_zero,
      zero_pow (by decide), zero_add] at hrest
    have hrestrict : hyperplaneRestriction 1 (hyperplaneExtension 1 r) = r :=
      DFunLike.congr_fun (hyperplaneRestriction_comp_extension 1) r
    rwa [hrestrict] at hrest
  obtain ⟨k, _hk, horder, c, U, hU, hcform, _hcx, hcy⟩ :=
    exists_parameter_power_normalization_preserving_curve r hrne hr
  have hk2 : 2 ≤ k := by
    rw [mem_maximalIdeal_one_pow_iff, horder] at hr2
    exact_mod_cast hr2
  refine ⟨k, hk2, e₀.comp c, U, hU, ?_, ?_⟩
  · change (e₀.comp c).pullbackAlgEquiv v = _
    rw [PointedEquivGerm.pullbackAlgEquiv_comp_apply, he₀v]
    exact hcform
  · change (e₀.comp c).pullbackAlgEquiv h = _
    rw [PointedEquivGerm.pullbackAlgEquiv_comp_apply, he₀h]
    exact hcy

private theorem sumSquares_transverse_factors :
    ∃ f g : Germ 2, coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ 2 = f * g ∧
      f ∈ maximalIdeal 2 ∧ g ∈ maximalIdeal 2 ∧ IsUnit (jacobian f g) := by
  let f := coordinate (0 : Fin 2) + constRingHom 2 Complex.I * coordinate (1 : Fin 2)
  let g := coordinate (0 : Fin 2) - constRingHom 2 Complex.I * coordinate (1 : Fin 2)
  have hI : constRingHom 2 Complex.I ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  refine ⟨f, g, ?_, ?_, ?_, ?_⟩
  · dsimp only [f, g]
    linear_combination coordinate (1 : Fin 2) ^ 2 * hI
  · exact (maximalIdeal 2).add_mem (coordinate_mem_maximalIdeal 0)
      ((maximalIdeal 2).mul_mem_left _ (coordinate_mem_maximalIdeal 1))
  · exact (maximalIdeal 2).sub_mem (coordinate_mem_maximalIdeal 0)
      ((maximalIdeal 2).mul_mem_left _ (coordinate_mem_maximalIdeal 1))
  · apply isUnit_iff_valueRingHom_ne_zero.mpr
    dsimp only [f, g]
    norm_num [jacobian_eq, partialDerivative_add, partialDerivative_sub, partialDerivative_mul,
      partialDerivative_const, partialDerivative_coordinate_same, partialDerivative_coordinate_ne]
    intro hz
    have him := congrArg Complex.im hz
    norm_num at him

/-- In the rank-one square case the constructed exponent is at least
three. An exponent two would give transverse analytic factors of the
original equation, contradicting its square quadratic initial form. -/
theorem exists_smooth_critical_square_jet_normalization
    (v h : Germ 2)
    (hv : v - coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3)
    (hvsq : Squarefree v) (hh : h ∈ maximalIdeal 2) (hdh : differential h ≠ 0)
    (hfinite : PlaneCurve.HasFiniteIntersection h v)
    (hi : PlaneCurve.intersectionMultiplicity h v hfinite = 2) :
    ∃ k : ℕ, 3 ≤ k ∧ ∃ e : PointedEquivGerm 2, ∃ U : Germ 2, IsUnit U ∧
      e.forward.pullbackRingHom v = coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ k ∧
      e.forward.pullbackRingHom h = coordinate (1 : Fin 2) * U := by
  have hv2 : v ∈ maximalIdeal 2 ^ 2 := by
    have htail := (Ideal.pow_le_pow_right (by decide : 2 ≤ 3)) hv
    have hx := Ideal.pow_mem_pow (coordinate_mem_maximalIdeal (0 : Fin 2)) 2
    simpa only [sub_add_cancel] using (maximalIdeal 2 ^ 2).add_mem htail hx
  obtain ⟨k, hk, e, U, hU, hev, heh⟩ :=
    exists_smooth_critical_quadratic_normalization v h hv2 hvsq hh hdh hfinite hi
  have hkne : k ≠ 2 := by
    intro hk2
    subst k
    obtain ⟨f, g, hfactor, hf, hg, hjac⟩ := sumSquares_transverse_factors
    have hform : v = e.symm.pullbackAlgEquiv f * e.symm.pullbackAlgEquiv g := by
      have he : e.pullbackAlgEquiv v = f * g := hev.trans hfactor
      have hpull := congrArg e.pullbackAlgEquiv.symm he
      rw [e.pullbackAlgEquiv.symm_apply_apply, map_mul] at hpull
      exact hpull
    have hnot := transverse_product_sub_first_square_not_mem_cube
      (e.symm.pullbackAlgEquiv f) (e.symm.pullbackAlgEquiv g)
      (e.symm.forward.pullback_mem_maximalIdeal hf)
      (e.symm.forward.pullback_mem_maximalIdeal hg)
      (jacobian_isUnit_pullback_equiv e.symm f g hjac)
    apply hnot
    rwa [← hform]
  exact ⟨k, by omega, e, U, hU, hev, heh⟩

/-- The constructed quadratic power coordinates determine the original
Milnor number. In particular, the isolated-critical-point property need
not be included among the hypotheses of the coordinate construction. -/
theorem isolatedCriticalPoint_and_milnorNumber_of_quadratic_power_coordinates
    (v : Germ 2) (e : PointedEquivGerm 2) (k : ℕ) (hk : 2 ≤ k)
    (he : e.forward.pullbackRingHom v =
      coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ k) :
    ∃ hv : PlaneCurve.HasIsolatedCriticalPoint v,
      PlaneCurve.milnorNumber v hv = k - 1 := by
  have hshape : e.pullbackAlgEquiv v = PlaneCurve.morseCurve k := he
  have hpull : PlaneCurve.HasIsolatedCriticalPoint (e.pullbackAlgEquiv v) := by
    rw [hshape]
    exact PlaneCurve.morseCurve_hasIsolatedCriticalPoint k hk
  have hv := (PlaneCurve.hasIsolatedCriticalPoint_pullback_iff e v).mp hpull
  refine ⟨hv, ?_⟩
  calc
    PlaneCurve.milnorNumber v hv = PlaneCurve.milnorNumber (PlaneCurve.morseCurve k)
        (PlaneCurve.morseCurve_hasIsolatedCriticalPoint k hk) := by
      simpa only [hshape] using PlaneCurve.milnorNumber_pullback e v hv
    _ = k - 1 := PlaneCurve.milnorNumber_morseCurve k hk

/-- A supplied genus identity for the original equation determines the
power in any constructed quadratic normal form. The branch number `b`
is not replaced by an assumed formula for the normal form. -/
theorem quadratic_power_exponent_of_milnor_genus_identity
    (v : Germ 2) (e : PointedEquivGerm 2) (k A₂ b : ℕ) (hk : 2 ≤ k)
    (he : e.forward.pullbackRingHom v =
      coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ k)
    (hv : PlaneCurve.HasIsolatedCriticalPoint v)
    (hgenus : 2 * A₂ + 1 = PlaneCurve.milnorNumber v hv + b) :
    2 * A₂ + 2 = k + b := by
  obtain ⟨_hv, hmilnor⟩ :=
    isolatedCriticalPoint_and_milnorNumber_of_quadratic_power_coordinates v e k hk he
  have hkpred : k - 1 + 1 = k := by omega
  rw [hmilnor] at hgenus
  omega

end OnLeConjecture.Analytic.Germ
