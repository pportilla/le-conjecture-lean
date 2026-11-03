/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OrdinaryNodeBlowup
import Mathlib.Tactic

/-!
# Smoothness after blowing up a cusp with exponents two and three

For transverse smooth germs `f,g` and units `B,C`, the equation
`f³ C + g² B` has a smooth strict transform in every analytic coordinate
chart. The proof uses the exact pullback identity and its derivative.
No normal-form theorem or invariance of a numerical singularity invariant
is assumed.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- The strict transform of `f³ C + g² B`, with transverse `f,g` and
unit coefficients, has ordinary order at most one. -/
theorem pointBlowup_cusp_not_mem_square
    (c : ℂ) (f g B C T : Germ 2) (hf : f ∈ maximalIdeal 2) (hg : g ∈ maximalIdeal 2)
    (hjac : IsUnit (jacobian f g)) (hB : IsUnit B) (hC : IsUnit C)
    (htransform : (pointBlowupChartGerm c).pullbackRingHom (f ^ 3 * C + g ^ 2 * B) =
      coordinate (1 : Fin 2) ^ 2 * T) : T ∉ maximalIdeal 2 ^ 2 := by
  let F := pointBlowupTransform c 1 f (by simpa only [pow_one] using hf)
  let G := pointBlowupTransform c 1 g (by simpa only [pow_one] using hg)
  let B' := (pointBlowupChartGerm c).pullbackRingHom B
  let C' := (pointBlowupChartGerm c).pullbackRingHom C
  have hF := pointBlowupTransform_factor c 1 f (by simpa only [pow_one] using hf)
  have hG := pointBlowupTransform_factor c 1 g (by simpa only [pow_one] using hg)
  change (pointBlowupChartGerm c).pullbackRingHom f = coordinate (1 : Fin 2) ^ 1 * F at hF
  change (pointBlowupChartGerm c).pullbackRingHom g = coordinate (1 : Fin 2) ^ 1 * G at hG
  have hT : T = coordinate (1 : Fin 2) * F ^ 3 * C' + G ^ 2 * B' := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (coordinate_ne_zero (1 : Fin 2)))
    rw [← htransform, map_add, map_mul, map_mul, map_pow, map_pow, hF, hG]
    dsimp only [B', C']
    ring
  intro hmem
  have hvalue : valueRingHom 2 T = 0 :=
    mem_maximalIdeal_iff.mp (by simpa only [pow_one] using
      (Ideal.pow_le_pow_right (by decide : 1 ≤ 2) hmem))
  rw [hT, map_add, map_mul, map_mul, map_mul, map_pow, map_pow,
    valueRingHom_coordinate, zero_mul, zero_mul, zero_add] at hvalue
  have hGzero : valueRingHom 2 G = 0 :=
    (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp
      ((mul_eq_zero.mp hvalue).resolve_right (valueRingHom_ne_zero_of_isUnit (hB.map _)))
  have hFunit : IsUnit F := by
    rcases pointBlowup_transverse_factors_one_isUnit c f g F G hjac
      (by simpa only [pow_one] using hF) (by simpa only [pow_one] using hG) with h | h
    · exact h
    · exact (valueRingHom_ne_zero_of_isUnit h hGzero).elim
  have hd := partialDerivative_mem_maximalIdeal_pow_of_mem_pow_succ (1 : Fin 2) hmem
  have hdvalue := mem_maximalIdeal_iff.mp (by simpa only [pow_one] using hd)
  rw [hT] at hdvalue
  simp only [partialDerivative_add, partialDerivative_mul, partialDerivative_pow,
    partialDerivative_coordinate_same, smul_eq_mul, nsmul_eq_mul, map_add, map_mul, map_pow,
    map_natCast, valueRingHom_coordinate, hGzero, Nat.reduceSub,
    zero_pow (by decide : (2 : ℕ) ≠ 0),
    pow_one, zero_mul, mul_zero, one_mul, add_zero] at hdvalue
  exact (mul_ne_zero (pow_ne_zero 3 (valueRingHom_ne_zero_of_isUnit hFunit))
    (valueRingHom_ne_zero_of_isUnit (hC.map (pointBlowupChartGerm c).pullbackRingHom))) hdvalue

/-- The two-three cusp calculation is valid after every analytic source
equivalence. Its unit coefficients include any outside preparation unit. -/
theorem pointBlowup_coordinate_cusp_not_mem_square
    (e : PointedEquivGerm 2) (c : ℂ) (B C T : Germ 2) (hB : IsUnit B) (hC : IsUnit C)
    (htransform : (pointBlowupChartGerm c).pullbackRingHom
      (e.forward.pullbackRingHom
        (coordinate (0 : Fin 2) ^ 3 * C + coordinate (1 : Fin 2) ^ 2 * B)) =
          coordinate (1 : Fin 2) ^ 2 * T) : T ∉ maximalIdeal 2 ^ 2 := by
  apply pointBlowup_cusp_not_mem_square c
    (e.forward.pullbackRingHom (coordinate (0 : Fin 2)))
    (e.forward.pullbackRingHom (coordinate (1 : Fin 2)))
    (e.forward.pullbackRingHom B) (e.forward.pullbackRingHom C) T
  · simpa only [pow_one] using e.forward.pullback_mem_maximalIdeal_pow
      (by simpa only [pow_one] using coordinate_mem_maximalIdeal (0 : Fin 2) :
        coordinate (0 : Fin 2) ∈ maximalIdeal 2 ^ 1)
  · simpa only [pow_one] using e.forward.pullback_mem_maximalIdeal_pow
      (by simpa only [pow_one] using coordinate_mem_maximalIdeal (1 : Fin 2) :
        coordinate (1 : Fin 2) ∈ maximalIdeal 2 ^ 1)
  · apply jacobian_isUnit_pullback_equiv
    simp only [jacobian_coordinate_one_right, partialDerivative_coordinate_same]
    exact isUnit_one
  · exact hB.map _
  · exact hC.map _
  · simpa only [map_add, map_mul, map_pow] using htransform

end OnLeConjecture.Analytic.Germ

namespace OnLeConjecture.Analytic.AnalyticPointBasis

open OnLeConjecture.Analytic.Germ

/-- Every recorded child of the specified cusp is smooth, with no
coordinate compatibility condition on its source equivalence. -/
theorem ordinary_cusp_child_not_mem_square
    {N : ℕ} (c : AnalyticPointBasis N) (p : Fin N) (hp : c.multiplicity p = 2)
    (B C : Germ 2) (hB : IsUnit B) (hC : IsUnit C)
    (hidentity : c.germ p = coordinate (0 : Fin 2) ^ 3 * C + coordinate (1 : Fin 2) ^ 2 * B)
    (q : Fin N) (hq : c.ParentRelation q p) : c.germ q ∉ maximalIdeal 2 ^ 2 := by
  apply pointBlowup_coordinate_cusp_not_mem_square (c.sourceCoordinates q) (c.chartCenter q)
    B C (c.germ q) hB hC
  have h := c.transform_identity q hq.1
  simpa only [hq.2, hp, hidentity] using h

end OnLeConjecture.Analytic.AnalyticPointBasis
