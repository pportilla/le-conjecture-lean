/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CyclicHypersurfaceFactorization

/-!
# The axis restriction of the cyclic third-coordinate difference

After the hypersurface coordinate change, the first cover axis has
`s=U/2`, `S=-U/2`, and parameter zero. An odd initial difference therefore
restricts to a nonzero scalar times the required cover-coordinate power.
-/

public section

namespace OnLeConjecture.Analytic.CyclicCover

open OnLeConjecture.Analytic.Germ

@[expose] noncomputable def transportedAxisPullback
    (r : ℕ) (hr : 0 < r) (e : PointedEquivGerm 3) : Germ 3 →+* Germ 1 :=
  (lineRestriction (![1, 0] : Source 2)).comp
    ((coverGerm r hr).pullbackRingHom.comp e.inverse.pullbackRingHom)

theorem transportedAxisPullback_forward
    (r : ℕ) (hr : 0 < r) (e : PointedEquivGerm 3) (F : Germ 3) :
    transportedAxisPullback r hr e (e.forward.pullbackRingHom F) =
      lineRestriction (![1, 0] : Source 2) ((coverGerm r hr).pullbackRingHom F) := by
  change lineRestriction _ ((coverGerm r hr).pullbackRingHom
    (e.inverse.pullbackRingHom (e.forward.pullbackRingHom F))) = _
  rw [show e.inverse.pullbackRingHom (e.forward.pullbackRingHom F) = F from
    e.pullbackRingEquiv.symm_apply_apply F]

theorem transportedAxisPullback_const
    (r : ℕ) (hr : 0 < r) (e : PointedEquivGerm 3) (c : ℂ) :
    transportedAxisPullback r hr e (constRingHom 3 c) = constRingHom 1 c := by
  simp only [transportedAxisPullback, RingHom.comp_apply,
    PointedMapGerm.pullback_constRingHom, lineRestriction]

/-- The explicit nonzero axis restriction needed by cyclic-cover descent.
The correction and the third-coordinate tail are allowed arbitrary
analytic dependence, subject only to divisibility by the parameter. -/
theorem transportedAxisPullback_odd_difference
    (r N : ℕ) (hr : 0 < r) (hN : Odd N) (e : PointedEquivGerm 3)
    (h u D : Germ 3) (hu : IsUnit u)
    (he0 : e.forward.pullbackRingHom (coordinate (0 : Fin 3)) = coordinate 0 - coordinate 1)
    (he1 : e.forward.pullbackRingHom (coordinate (1 : Fin 3)) =
      (coordinate 0 + coordinate 1 + h) * u)
    (he2 : e.forward.pullbackRingHom (coordinate (2 : Fin 3)) = coordinate 2)
    (hh : coordinate (2 : Fin 3) ∣ h)
    (hD : coordinate (2 : Fin 3) ∣
      D - (coordinate (0 : Fin 3) ^ N - coordinate (1 : Fin 3) ^ N)) :
    transportedAxisPullback r hr e D =
      constRingHom 1 (2 * (1 / 2 : ℂ) ^ N) * coordinate (0 : Fin 1) ^ (r * N) := by
  let φ := transportedAxisPullback r hr e
  have hfirst : φ (coordinate (0 : Fin 3) - coordinate (1 : Fin 3)) =
      coordinate (0 : Fin 1) ^ r := by
    rw [← he0, transportedAxisPullback_forward, coverGerm_pullback_first,
      map_pow, lineRestriction_coordinate_eq]
    simp
  have hsecond : φ ((coordinate (0 : Fin 3) + coordinate 1 + h) * u) = 0 := by
    rw [← he1, transportedAxisPullback_forward, coverGerm_pullback_second,
      map_pow, lineRestriction_coordinate_eq]
    simp [zero_pow hr.ne']
  have hparameter : φ (coordinate (2 : Fin 3)) = 0 := by
    rw [← he2, transportedAxisPullback_forward, coverGerm_pullback_last,
      map_mul, lineRestriction_coordinate_eq, lineRestriction_coordinate_eq]
    simp
  have hzero_of_dvd (F : Germ 3) (hF : coordinate (2 : Fin 3) ∣ F) : φ F = 0 := by
    obtain ⟨q, rfl⟩ := hF
    rw [map_mul, hparameter, zero_mul]
  have hhzero := hzero_of_dvd h hh
  have hsum : φ (coordinate (0 : Fin 3)) + φ (coordinate (1 : Fin 3)) = 0 := by
    rw [map_mul, map_add, map_add, hhzero, add_zero] at hsecond
    exact (mul_eq_zero.mp hsecond).resolve_right (hu.map φ).ne_zero
  have hneg : φ (coordinate (1 : Fin 3)) = -φ (coordinate (0 : Fin 3)) := by
    linear_combination hsum
  have htwo : (constRingHom 1 (1 / 2 : ℂ) : Germ 1) * 2 = 1 := by
    rw [show (2 : Germ 1) = constRingHom 1 (2 : ℂ) from (map_ofNat _ 2).symm,
      ← map_mul]
    norm_num
  have hhalf : φ (coordinate (0 : Fin 3)) =
      constRingHom 1 (1 / 2 : ℂ) * coordinate (0 : Fin 1) ^ r := by
    rw [map_sub, hneg] at hfirst
    calc
      _ = ((constRingHom 1 (1 / 2 : ℂ) : Germ 1) * 2) *
          φ (coordinate (0 : Fin 3)) := by rw [htwo, one_mul]
      _ = constRingHom 1 (1 / 2 : ℂ) *
          (φ (coordinate (0 : Fin 3)) - -φ (coordinate (0 : Fin 3))) := by ring
      _ = _ := by rw [hfirst]
  have hDzero := hzero_of_dvd _ hD
  rw [map_sub, map_sub, map_pow, map_pow] at hDzero
  have hDeq := sub_eq_zero.mp hDzero
  rw [hDeq, hneg, hN.neg_pow, sub_neg_eq_add, hhalf, mul_pow, ← pow_mul,
    ← map_pow]
  change _ = _
  rw [map_mul, show (constRingHom 1 (2 : ℂ) : Germ 1) = 2 from map_ofNat _ 2]
  ring

theorem odd_difference_axis_coefficient_ne_zero (N : ℕ) :
    2 * (1 / 2 : ℂ) ^ N ≠ 0 :=
  mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))

end OnLeConjecture.Analytic.CyclicCover
