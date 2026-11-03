/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SmoothCriticalQuadraticNormalization

/-!
# Normalizing a specified reduced square-jet member

The auxiliary coordinate axis meets the specified member with multiplicity
two. Quadratic normalization therefore applies independently of the critical
equation. No replacement of the specified member by another linear
combination is involved.
-/

public section

namespace OnLeConjecture.Analytic.Germ

private theorem oneVariable_order_of_square_tail (r : Germ 1)
    (hr : r - coordinate (0 : Fin 1) ^ 2 ∈ maximalIdeal 1 ^ 3) :
    r ≠ 0 ∧ vanishingOrder r = 2 := by
  have hr2 : r ∈ maximalIdeal 1 ^ 2 := by
    have ht := (Ideal.pow_le_pow_right (by decide : 2 ≤ 3)) hr
    simpa only [sub_add_cancel] using (maximalIdeal 1 ^ 2).add_mem ht
      (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 0) 2)
  have hr3 : r ∉ maximalIdeal 1 ^ 3 := by
    intro h
    have hp := (maximalIdeal 1 ^ 3).sub_mem h hr
    simp only [sub_sub_cancel] at hp
    rw [mem_maximalIdeal_one_pow_iff, vanishingOrder_coordinate_pow] at hp
    norm_num at hp
  have hne : r ≠ 0 := by
    intro hz
    exact hr3 (hz ▸ (maximalIdeal 1 ^ 3).zero_mem)
  obtain ⟨n, u, hu, hru⟩ := exists_eq_coordinate_pow_mul_unit hne
  have ho := vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hu hru
  have hlo : 2 ≤ n := by
    rw [mem_maximalIdeal_one_pow_iff, ho] at hr2
    exact_mod_cast hr2
  have hhi : n < 3 := by
    by_contra hn
    apply hr3
    rw [mem_maximalIdeal_one_pow_iff, ho]
    exact_mod_cast Nat.le_of_not_gt hn
  exact ⟨hne, by simpa [show n = 2 by omega] using ho⟩

theorem exists_square_jet_member_normalization
    (v : Germ 2)
    (hv : v - coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3)
    (hreduced : Squarefree v) :
    ∃ k : ℕ, 3 ≤ k ∧ ∃ e : PointedEquivGerm 2,
      e.forward.pullbackRingHom v = PlaneCurve.morseCurve k := by
  let s := coordinateSwapPointedEquiv (1 : Fin 2)
  have hsx : s.pullbackAlgEquiv (coordinate (0 : Fin 2)) =
      coordinate (1 : Fin 2) :=
    (s.forward.pullback_coordinate 0).trans (coordinateSwapPointedEquiv_component_zero 1)
  have ht := (hyperplaneInclusionGerm 1).pullback_mem_maximalIdeal_pow
    (s.forward.pullback_mem_maximalIdeal_pow hv)
  change hyperplaneRestriction 1 (s.pullbackAlgEquiv
    (v - coordinate (0 : Fin 2) ^ 2)) ∈ maximalIdeal 1 ^ 3 at ht
  rw [map_sub, map_pow, hsx, map_sub, map_pow] at ht
  change hyperplaneRestriction 1 (s.pullbackAlgEquiv v) -
    (hyperplaneRestriction 1 (coordinate (0 : Fin 1).succ)) ^ 2 ∈ maximalIdeal 1 ^ 3 at ht
  rw [hyperplaneRestriction_coordinate_succ] at ht
  obtain ⟨hrne, horder⟩ := oneVariable_order_of_square_tail _ ht
  have hfin := PlaneCurve.hasFiniteIntersection_coordinate_of_restriction_ne_zero
    (s.pullbackAlgEquiv v) hrne
  let h := s.symm.pullbackAlgEquiv (coordinate (0 : Fin 2))
  have hh : h ∈ maximalIdeal 2 :=
    s.symm.forward.pullback_mem_maximalIdeal (coordinate_mem_maximalIdeal 0)
  have hdh : differential h ≠ 0 := by
    intro hz
    have hp : differential (coordinate (0 : Fin 2)) = 0 := by
      have hid : s.pullbackAlgEquiv h = coordinate (0 : Fin 2) :=
        s.pullbackAlgEquiv.apply_symm_apply _
      have hp := differential_compPointed h s.forward
      change differential (s.pullbackAlgEquiv h) =
        (differential h).comp s.forward.differential at hp
      simpa only [hid, hz, ContinuousLinearMap.zero_comp] using hp
    have he := congrArg (fun L : Source 2 →L[ℂ] ℂ ↦ L (Pi.single 0 1)) hp
    simp at he
  have hback : s.symm.pullbackAlgEquiv (s.pullbackAlgEquiv v) = v :=
    s.pullbackAlgEquiv.symm_apply_apply v
  have hfinite : PlaneCurve.HasFiniteIntersection h v := by
    simpa only [hback] using hfin.pullback s.symm
  have hi : PlaneCurve.intersectionMultiplicity h v hfinite = 2 := by
    have hp := PlaneCurve.intersectionMultiplicity_pullback s.symm hfin
    have hi := PlaneCurve.intersectionMultiplicity_coordinate_eq_restrictionOrder
      (s.pullbackAlgEquiv v) hrne
    rw [horder] at hi
    simpa only [hback, ENat.toNat_ofNat] using hp.symm.trans hi
  obtain ⟨k, hk, e, U, hU, he, _⟩ :=
    exists_smooth_critical_square_jet_normalization v h hv hreduced hh hdh hfinite hi
  exact ⟨k, hk, e, he⟩

/-- The quadratic square may be the square of any smooth analytic germ.
The specified member is retained through the constructed source change. -/
theorem exists_smooth_square_jet_member_normalization
    (v l : Germ 2) (hl : l ∈ maximalIdeal 2) (hdl : differential l ≠ 0)
    (hv : v - l ^ 2 ∈ maximalIdeal 2 ^ 3) (hreduced : Squarefree v) :
    ∃ k : ℕ, 3 ≤ k ∧ ∃ e : PointedEquivGerm 2,
      e.forward.pullbackRingHom v = PlaneCurve.morseCurve k := by
  obtain ⟨a, ha⟩ := PlaneCurve.exists_equiv_pullback_eq_coordinate l hl hdl
  change a.forward.pullbackRingHom l = coordinate (0 : Fin 2) at ha
  have hv' : a.forward.pullbackRingHom v - coordinate (0 : Fin 2) ^ 2 ∈
      maximalIdeal 2 ^ 3 := by
    simpa only [map_sub, map_pow, ha] using a.forward.pullback_mem_maximalIdeal_pow hv
  obtain ⟨k, hk, b, hb⟩ := exists_square_jet_member_normalization
    (a.forward.pullbackRingHom v) hv' (a.squarefree_pullback v hreduced)
  refine ⟨k, hk, a.comp b, ?_⟩
  change (a.comp b).pullbackAlgEquiv v = _
  rw [PointedEquivGerm.pullbackAlgEquiv_comp_apply]
  exact hb

end OnLeConjecture.Analytic.Germ
