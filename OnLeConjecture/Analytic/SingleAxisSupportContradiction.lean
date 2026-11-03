/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CyclicCoverUnitFactorization

/-!
# A positive axis order excludes support on the other axis

Coordinate factorization gives the needed persistence consequence
directly: a nonzero positive-order restriction on the first axis is
incompatible with every zero lying on the second-coordinate hyperplane.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.Analytic.Germ

theorem not_zeros_supported_on_second_axis_of_positive_first_axis_order
    (F : Source 2 → ℂ) (hF : AnalyticAt ℂ F 0)
    (N : ℕ) (hN : 0 < N) (c : ℂ) (hc : c ≠ 0)
    (haxis : lineRestriction (![1, 0] : Source 2) (ofFunction F hF) =
      constRingHom 1 c * coordinate (0 : Fin 1) ^ N) :
    ¬ (∀ᶠ q in 𝓝 (0 : Source 2), F q = 0 → q 1 = 0) := by
  intro hsupport
  have haxes : ∀ᶠ q in 𝓝 (0 : Source 2), F q = 0 → q 0 = 0 ∨ q 1 = 0 :=
    hsupport.mono fun _ h hzero => Or.inr (h hzero)
  obtain ⟨u, _, hfactor⟩ := exists_first_coordinate_power_mul_unit_of_axes_support
    F hF N c hc haxes haxis
  have hrestriction : hyperplaneRestriction 1 (ofFunction F hF) = 0 := by
    rw [hfactor, map_mul, map_pow]
    have hx : hyperplaneRestriction 1 (coordinate (0 : Fin 2)) = 0 := by
      apply Subtype.ext
      rfl
    rw [hx, zero_pow hN.ne', zero_mul]
  have hzero : ∀ᶠ q in 𝓝 (0 : Source 1), F (hyperplaneInclusion 1 q) = 0 :=
    Filter.Germ.coe_eq.mp (congrArg Subtype.val hrestriction)
  have ht : Tendsto (hyperplaneInclusion 1) (𝓝 (0 : Source 1)) (𝓝 (0 : Source 2)) := by
    simpa only [ContinuousAt, map_zero] using
      (hyperplaneInclusion 1).continuous.continuousAt (x := (0 : Source 1))
  have hcoord : ∀ᶠ q in 𝓝 (0 : Source 1), q 0 = 0 := by
    filter_upwards [ht.eventually hsupport, hzero] with q hq hz
    exact hq hz
  apply coordinate_ne_zero (0 : Fin 1)
  apply Subtype.ext
  exact Filter.Germ.coe_eq.mpr hcoord

end OnLeConjecture.Analytic.Germ
