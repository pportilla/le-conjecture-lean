/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SmoothCriticalQuadraticNormalization

/-!
# Smooth intersections of quadratic power curves

For exponent at least four, a smooth branch cannot meet `x²+yᵏ` with
intersection multiplicity three. Restriction to the constructed smooth
parametrization reduces this to the fact that a one-variable square plus
a germ of order at least four cannot have order three.
-/

public section

namespace OnLeConjecture.Analytic.Germ

theorem oneVariable_square_add_four_not_order_three
    (u r : Germ 1) (hu : u ∈ maximalIdeal 1) (hr : r ∈ maximalIdeal 1 ^ 4) :
    vanishingOrder (u ^ 2 + r) ≠ 3 := by
  intro horder
  by_cases hu2 : u ∈ maximalIdeal 1 ^ 2
  · have husq : u ^ 2 ∈ maximalIdeal 1 ^ 4 := by
      simpa only [← pow_mul, Nat.reduceMul] using Ideal.pow_mem_pow hu2 2
    have h := (maximalIdeal 1 ^ 4).add_mem husq hr
    rw [mem_maximalIdeal_one_pow_iff, horder] at h
    norm_num at h
  · have hune : u ≠ 0 := fun hz => hu2 (hz ▸ (maximalIdeal 1 ^ 2).zero_mem)
    obtain ⟨a, w, hw, huw⟩ := exists_eq_coordinate_pow_mul_unit hune
    have huorder := vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hw huw
    have ha : a = 1 := by
      have hu1 : u ∈ maximalIdeal 1 ^ 1 := by simpa only [pow_one] using hu
      rw [mem_maximalIdeal_one_pow_iff, huorder] at hu1 hu2
      norm_cast at hu1 hu2
      omega
    have hsum3 : u ^ 2 + r ∈ maximalIdeal 1 ^ 3 := by
      rw [mem_maximalIdeal_one_pow_iff, horder]
      norm_num
    have hr3 := (Ideal.pow_le_pow_right (by decide : 3 ≤ 4)) hr
    have hsquare3 : u ^ 2 ∈ maximalIdeal 1 ^ 3 := by
      simpa only [add_sub_cancel_right] using (maximalIdeal 1 ^ 3).sub_mem hsum3 hr3
    rw [mem_maximalIdeal_one_pow_iff, vanishingOrder_pow, huorder, ha] at hsquare3
    norm_num at hsquare3

/-- The smooth parametrization and its intersection formula are
constructed from the smooth equation, not supplied separately. -/
theorem smooth_intersection_quadratic_power_ne_three
    (h : Germ 2) (k : ℕ) (hk : 4 ≤ k)
    (hh : h ∈ maximalIdeal 2) (hdh : differential h ≠ 0)
    (hfinite : PlaneCurve.HasFiniteIntersection h
      (coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ k)) :
    PlaneCurve.intersectionMultiplicity h
      (coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ k) hfinite ≠ 3 := by
  obtain ⟨e, _he, hne, hinter⟩ := PlaneCurve.exists_smoothBranch_intersection_formula h
    (coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ k) hh hdh hfinite
  let u := hyperplaneRestriction 1 (e.pullbackAlgEquiv (coordinate (0 : Fin 2)))
  let w := hyperplaneRestriction 1 (e.pullbackAlgEquiv (coordinate (1 : Fin 2)))
  have hmember (i : Fin 2) :
      hyperplaneRestriction 1 (e.pullbackAlgEquiv (coordinate i)) ∈ maximalIdeal 1 :=
    (hyperplaneInclusionGerm 1).pullback_mem_maximalIdeal
      (e.forward.pullback_mem_maximalIdeal (coordinate_mem_maximalIdeal i))
  have hwk : w ^ k ∈ maximalIdeal 1 ^ 4 :=
    (Ideal.pow_le_pow_right hk) (Ideal.pow_mem_pow (hmember 1) k)
  have hshape : hyperplaneRestriction 1 (e.pullbackAlgEquiv
      (coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ k)) = u ^ 2 + w ^ k := by
    rw [map_add, map_pow, map_pow, map_add, map_pow, map_pow]
  intro hI
  have horder := ENat.natCast_toNat (vanishingOrder_eq_top_iff.not.mpr hne)
  rw [← hinter, hI, hshape] at horder
  exact oneVariable_square_add_four_not_order_three u (w ^ k) (hmember 0) hwk horder.symm

end OnLeConjecture.Analytic.Germ
