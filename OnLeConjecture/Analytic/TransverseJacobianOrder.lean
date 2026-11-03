/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SmoothPolarCorrection
public import OnLeConjecture.Analytic.TransverseCriticalSection

/-!
# Transverse parameter order and coordinate Jacobian minors

For a map written as `(x,a,b)`, differentiation of its restriction to
`x=0` is restriction of the two minors `J(x,a)` and `J(x,b)`. The minimum
order of the two restricted components is one greater than the minimum
order of these restricted minors. A common power of the remaining source
coordinate, with at least one unit residual, therefore determines the
parameter order exactly.
-/

@[expose] public section

namespace OnLeConjecture.Analytic.Germ

/-- Differentiation decreases the extended vanishing order of a pointed
one-variable germ by one. The zero germ is included with order infinity. -/
theorem vanishingOrder_derivative_add_one (f : Germ 1) (hf : f ∈ maximalIdeal 1) :
    vanishingOrder (partialDerivative (0 : Fin 1) f) + 1 = vanishingOrder f := by
  by_cases hzero : f = 0
  · simp only [hzero, partialDerivative_zero, vanishingOrder_zero, top_add]
  · obtain ⟨k, hk, horder, u, hu, hfactor⟩ := exists_derivative_order_factorization f hf hzero
    rw [vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hu hfactor, horder]
    exact_mod_cast Nat.sub_add_cancel hk

/-- The minimum order of a pointed pair is one greater than the minimum
order of its two derivatives, including identically zero components. -/
theorem min_vanishingOrder_derivatives_add_one
    (a b : Germ 1) (ha : a ∈ maximalIdeal 1) (hb : b ∈ maximalIdeal 1) :
    min (vanishingOrder (partialDerivative (0 : Fin 1) a))
      (vanishingOrder (partialDerivative (0 : Fin 1) b)) + 1 =
        min (vanishingOrder a) (vanishingOrder b) := by
  rw [← min_add_add_right, vanishingOrder_derivative_add_one a ha,
    vanishingOrder_derivative_add_one b hb]

/-- The transverse derivative order of a map `(x,a,b)` is measured by
its first two coordinate minors restricted to `x=0`. -/
theorem min_transverse_orders_eq_restricted_jacobian_orders_add_one
    (a b : Germ 2) (ha : a ∈ maximalIdeal 2) (hb : b ∈ maximalIdeal 2) :
    min (vanishingOrder (hyperplaneRestriction 1 a))
      (vanishingOrder (hyperplaneRestriction 1 b)) =
        min (vanishingOrder (hyperplaneRestriction 1
          (jacobian (coordinate 0) a)))
          (vanishingOrder (hyperplaneRestriction 1
            (jacobian (coordinate 0) b))) + 1 := by
  have h := min_vanishingOrder_derivatives_add_one
    (hyperplaneRestriction 1 a) (hyperplaneRestriction 1 b)
    ((hyperplaneInclusionGerm 1).pullback_mem_maximalIdeal ha)
    ((hyperplaneInclusionGerm 1).pullback_mem_maximalIdeal hb)
  rw [partialDerivative_hyperplaneRestriction_plane,
    partialDerivative_hyperplaneRestriction_plane] at h
  simpa only [jacobian_coordinate_zero_left] using h.symm

/-- If the two relevant minors have a common coordinate power and one
residual is a unit, their transverse parameter order is exactly that
power plus one. All factors are analytic germs in the source plane. -/
theorem min_transverse_orders_eq_of_jacobian_factors
    (a b u v : Germ 2) (k : ℕ)
    (ha : a ∈ maximalIdeal 2) (hb : b ∈ maximalIdeal 2)
    (hja : jacobian (coordinate 0) a = coordinate (1 : Fin 2) ^ k * u)
    (hjb : jacobian (coordinate 0) b = coordinate (1 : Fin 2) ^ k * v)
    (hunit : IsUnit u ∨ IsUnit v) :
    min (vanishingOrder (hyperplaneRestriction 1 a))
      (vanishingOrder (hyperplaneRestriction 1 b)) = (k + 1 : ℕ) := by
  rw [min_transverse_orders_eq_restricted_jacobian_orders_add_one a b ha hb, hja, hjb]
  have hy : hyperplaneRestriction 1 (coordinate (1 : Fin 2)) = coordinate (0 : Fin 1) :=
    hyperplaneRestriction_coordinate_succ 1 0
  simp only [map_mul, map_pow, hy, vanishingOrder_mul, vanishingOrder_coordinate_pow]
  have hmin : min (vanishingOrder (hyperplaneRestriction 1 u))
      (vanishingOrder (hyperplaneRestriction 1 v)) = 0 := by
    rcases hunit with hu | hv
    · rw [vanishingOrder_eq_zero_iff_isUnit.mpr (hu.map (hyperplaneRestriction 1))]
      exact min_eq_left zero_le
    · rw [vanishingOrder_eq_zero_iff_isUnit.mpr (hv.map (hyperplaneRestriction 1))]
      exact min_eq_right zero_le
  rw [← add_min, hmin, add_zero]
  norm_cast

/-- In coordinates `(x,a,b)`, a unit residual of any of the three
Jacobian minors forces a unit residual of one of the first two minors. -/
theorem isUnit_residual_first_two_of_jacobian_factors
    (a b u v w : Germ 2) (k : ℕ)
    (hja : jacobian (coordinate 0) a = coordinate (1 : Fin 2) ^ k * u)
    (hjb : jacobian (coordinate 0) b = coordinate (1 : Fin 2) ^ k * v)
    (hjab : jacobian a b = coordinate (1 : Fin 2) ^ k * w)
    (hunit : IsUnit u ∨ IsUnit v ∨ IsUnit w) : IsUnit u ∨ IsUnit v := by
  rcases hunit with hu | hv | hw
  · exact Or.inl hu
  · exact Or.inr hv
  · have hres : w = partialDerivative (0 : Fin 2) a * v -
        u * partialDerivative (0 : Fin 2) b := by
      apply mul_left_cancel₀ (pow_ne_zero k (coordinate_ne_zero (1 : Fin 2)))
      rw [← hjab, jacobian_eq]
      rw [jacobian_coordinate_zero_left] at hja hjb
      rw [hja, hjb]
      ring
    by_contra h
    push Not at h
    have hu0 : valueRingHom 2 u = 0 := by
      by_contra hu0
      exact h.1 (isUnit_iff_valueRingHom_ne_zero.mpr hu0)
    have hv0 : valueRingHom 2 v = 0 := by
      by_contra hv0
      exact h.2 (isUnit_iff_valueRingHom_ne_zero.mpr hv0)
    apply (isUnit_iff_valueRingHom_ne_zero.mp hw)
    rw [hres, map_sub, map_mul, map_mul, hu0, hv0, mul_zero, zero_mul, sub_self]

/-- The exact common coordinate order of all three minors determines the
order of the transverse parametrization in normalized coordinates. -/
theorem min_transverse_orders_eq_of_three_jacobian_factors
    (a b u v w : Germ 2) (k : ℕ)
    (ha : a ∈ maximalIdeal 2) (hb : b ∈ maximalIdeal 2)
    (hja : jacobian (coordinate 0) a = coordinate (1 : Fin 2) ^ k * u)
    (hjb : jacobian (coordinate 0) b = coordinate (1 : Fin 2) ^ k * v)
    (hjab : jacobian a b = coordinate (1 : Fin 2) ^ k * w)
    (hunit : IsUnit u ∨ IsUnit v ∨ IsUnit w) :
    min (vanishingOrder (hyperplaneRestriction 1 a))
      (vanishingOrder (hyperplaneRestriction 1 b)) = (k + 1 : ℕ) :=
  min_transverse_orders_eq_of_jacobian_factors a b u v k ha hb hja hjb
    (isUnit_residual_first_two_of_jacobian_factors a b u v w k hja hjb hjab hunit)

end OnLeConjecture.Analytic.Germ
