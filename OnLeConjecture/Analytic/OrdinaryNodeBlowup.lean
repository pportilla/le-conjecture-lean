/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OrdinaryNodeFactorization
public import OnLeConjecture.Analytic.PointBlowupPolar
public import OnLeConjecture.Analytic.AnalyticPointBasis
public import OnLeConjecture.Analytic.ScaledPolynomialFreeCharts
import Mathlib.Tactic

/-!
# Smoothness after blowing up an ordinary node

Two smooth transverse factors cannot both vanish at the same point of
the exceptional line. This follows from the actual transformed Jacobian
identity. Each factor has transform order at most one, so their product
has transform order at most one. Analytic coordinate equivalences and
outside unit factors are retained throughout.
-/

public section

namespace OnLeConjecture.Analytic.Germ

theorem partialDerivative_value_eq_of_sub_mem_square
    {n : ℕ} (f g : Germ n) (i : Fin n)
    (h : f - g ∈ maximalIdeal n ^ 2) :
    valueRingHom n (partialDerivative i f) = valueRingHom n (partialDerivative i g) := by
  have hd := partialDerivative_mem_maximalIdeal_pow_of_mem_pow_succ i h
  have hv := mem_maximalIdeal_iff.mp (by simpa only [pow_one] using hd)
  rw [partialDerivative_sub, map_sub] at hv
  exact sub_eq_zero.mp hv

theorem not_mem_square_of_jacobian_isUnit_left
    (f g : Germ 2) (hjac : IsUnit (jacobian f g)) : f ∉ maximalIdeal 2 ^ 2 := by
  intro hf
  have hz (i : Fin 2) : valueRingHom 2 (partialDerivative i f) = 0 :=
    mem_maximalIdeal_iff.mp (by simpa only [pow_one] using
      partialDerivative_mem_maximalIdeal_pow_of_mem_pow_succ i hf)
  apply valueRingHom_ne_zero_of_isUnit hjac
  simp only [jacobian_eq, map_sub, map_mul, hz, zero_mul, sub_self]

theorem not_mem_square_of_jacobian_isUnit_right
    (f g : Germ 2) (hjac : IsUnit (jacobian f g)) : g ∉ maximalIdeal 2 ^ 2 := by
  apply not_mem_square_of_jacobian_isUnit_left g f
  rw [jacobian_swap]
  exact hjac.neg

/-- The transformed factors of a transverse pair cannot both vanish at
the exceptional center. No leading-form identification is assumed. -/
theorem pointBlowup_transverse_factors_one_isUnit
    (c : ℂ) (f g F G : Germ 2) (hjac : IsUnit (jacobian f g))
    (hF : (pointBlowupChartGerm c).pullbackRingHom f = coordinate (1 : Fin 2) * F)
    (hG : (pointBlowupChartGerm c).pullbackRingHom g = coordinate (1 : Fin 2) * G) :
    IsUnit F ∨ IsUnit G := by
  by_cases hunit : IsUnit F
  · exact Or.inl hunit
  right
  apply isUnit_iff_valueRingHom_ne_zero.mpr
  intro hGzero
  have hFzero : valueRingHom 2 F = 0 := by
    by_contra hne
    exact hunit (isUnit_iff_valueRingHom_ne_zero.mpr hne)
  have h := pointBlowupTransform_jacobian c 1 1 (by decide) (by decide) f g F G
    (by simpa only [pow_one] using hF) (by simpa only [pow_one] using hG)
  have hv := congrArg (valueRingHom 2) h
  simp only [PointedMapGerm.valueRingHom_pullback, Nat.reduceAdd, Nat.sub_self,
    pow_zero, one_mul, Nat.cast_one, map_sub, map_add, map_mul, valueRingHom_coordinate,
    hFzero, hGzero, zero_mul, mul_zero, zero_add, sub_self] at hv
  exact valueRingHom_ne_zero_of_isUnit hjac hv

/-- The transform of the product of two transverse smooth germs has
order at most one in every finite chart. -/
theorem pointBlowup_transverse_product_not_mem_square
    (c : ℂ) (f g T : Germ 2) (hf : f ∈ maximalIdeal 2) (hg : g ∈ maximalIdeal 2)
    (hjac : IsUnit (jacobian f g))
    (htransform : (pointBlowupChartGerm c).pullbackRingHom (f * g) =
      coordinate (1 : Fin 2) ^ 2 * T) :
    T ∉ maximalIdeal 2 ^ 2 := by
  let F := pointBlowupTransform c 1 f (by simpa only [pow_one] using hf)
  let G := pointBlowupTransform c 1 g (by simpa only [pow_one] using hg)
  have hF := pointBlowupTransform_factor c 1 f (by simpa only [pow_one] using hf)
  have hG := pointBlowupTransform_factor c 1 g (by simpa only [pow_one] using hg)
  change (pointBlowupChartGerm c).pullbackRingHom f = coordinate (1 : Fin 2) ^ 1 * F at hF
  change (pointBlowupChartGerm c).pullbackRingHom g = coordinate (1 : Fin 2) ^ 1 * G at hG
  have hT : T = F * G := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (coordinate_ne_zero (1 : Fin 2)))
    rw [← htransform, map_mul, hF, hG]
    ring
  have hFnot : F ∉ maximalIdeal 2 ^ 2 :=
    pointBlowupTransform_order_bound c 1 f _ (not_mem_square_of_jacobian_isUnit_left f g hjac)
  have hGnot : G ∉ maximalIdeal 2 ^ 2 :=
    pointBlowupTransform_order_bound c 1 g _ (not_mem_square_of_jacobian_isUnit_right f g hjac)
  rcases pointBlowup_transverse_factors_one_isUnit c f g F G hjac
    (by simpa only [pow_one] using hF) (by simpa only [pow_one] using hG) with hunit | hunit
  · rw [hT, mul_comm]
    exact not_mem_pow_of_unit_multiple G F hunit 2 hGnot
  · rw [hT]
    exact not_mem_pow_of_unit_multiple F G hunit 2 hFnot

theorem jacobian_isUnit_pullback_equiv
    (e : PointedEquivGerm 2) (f g : Germ 2) (hjac : IsUnit (jacobian f g)) :
    IsUnit (jacobian (e.forward.pullbackRingHom f) (e.forward.pullbackRingHom g)) := by
  change IsUnit (jacobian (compPointed f e.forward) (compPointed g e.forward))
  rw [jacobian_compPointed]
  exact (hjac.map e.forward.pullbackRingHom).mul (PointedEquivGerm.coordinateJacobian_isUnit e)

theorem jacobian_isUnit_mul_unit_right
    (f g U : Germ 2) (hg : g ∈ maximalIdeal 2)
    (hjac : IsUnit (jacobian f g)) (hU : IsUnit U) :
    IsUnit (jacobian f (g * U)) := by
  apply isUnit_iff_valueRingHom_ne_zero.mpr
  rw [jacobian_mul_right, map_add, map_mul, map_mul, mem_maximalIdeal_iff.mp hg,
    zero_mul, zero_add]
  exact mul_ne_zero (valueRingHom_ne_zero_of_isUnit hU) (valueRingHom_ne_zero_of_isUnit hjac)

/-- The convergent node factorization has a unit Jacobian, as verified
from the linear tails of its two factors. -/
theorem exists_transverse_node_factorization
    (v : Germ 2) (α β : ℂ) (hβ : β ≠ 0)
    (hv : v - coordinate (0 : Fin 2) *
      (constRingHom 2 α * coordinate (0 : Fin 2) +
        constRingHom 2 β * coordinate (1 : Fin 2)) ∈ maximalIdeal 2 ^ 3) :
    ∃ F G : Germ 2, v = F * G ∧ F ∈ maximalIdeal 2 ∧ G ∈ maximalIdeal 2 ∧
      IsUnit (jacobian F G) := by
  obtain ⟨F, G, hfactor, hFt, hGt⟩ :=
    exists_ordinary_node_factorization_with_linear_tails v α β hβ hv
  have hF : F ∈ maximalIdeal 2 := by
    have htail : F - coordinate (0 : Fin 2) ∈ maximalIdeal 2 := by
      simpa only [pow_one] using Ideal.pow_le_pow_right (by decide : 1 ≤ 2) hFt
    simpa only [sub_add_cancel] using (maximalIdeal 2).add_mem htail (coordinate_mem_maximalIdeal 0)
  have hG : G ∈ maximalIdeal 2 := by
    have htail : G - (constRingHom 2 α * coordinate (0 : Fin 2) +
        constRingHom 2 β * coordinate (1 : Fin 2)) ∈ maximalIdeal 2 := by
      simpa only [pow_one] using Ideal.pow_le_pow_right (by decide : 1 ≤ 2) hGt
    have hlinear := (maximalIdeal 2).add_mem
      ((maximalIdeal 2).mul_mem_left (constRingHom 2 α) (coordinate_mem_maximalIdeal 0))
      ((maximalIdeal 2).mul_mem_left (constRingHom 2 β) (coordinate_mem_maximalIdeal 1))
    simpa only [sub_add_cancel] using (maximalIdeal 2).add_mem htail hlinear
  refine ⟨F, G, hfactor, hF, hG, isUnit_iff_valueRingHom_ne_zero.mpr ?_⟩
  have hF₀ := partialDerivative_value_eq_of_sub_mem_square F _ 0 hFt
  have hF₁ := partialDerivative_value_eq_of_sub_mem_square F _ 1 hFt
  have hG₁ := partialDerivative_value_eq_of_sub_mem_square G _ 1 hGt
  rw [jacobian_eq, map_sub, map_mul, map_mul, hF₀, hF₁, hG₁]
  simpa only [partialDerivative_coordinate_same,
    partialDerivative_coordinate_ne (by decide : (1 : Fin 2) ≠ 0), partialDerivative_add,
    partialDerivative_mul, partialDerivative_const, zero_mul, mul_zero, zero_add, add_zero,
    mul_one, map_zero, map_one, one_mul, sub_zero, valueRingHom_const] using hβ

/-- An ordinary node has smooth strict transforms after every analytic
source equivalence, including an arbitrary outside unit. -/
theorem pointBlowup_node_not_mem_square
    (e : PointedEquivGerm 2) (c : ℂ) (v U T : Germ 2) (hU : IsUnit U)
    (α β : ℂ) (hβ : β ≠ 0)
    (hv : v - coordinate (0 : Fin 2) *
      (constRingHom 2 α * coordinate (0 : Fin 2) +
        constRingHom 2 β * coordinate (1 : Fin 2)) ∈ maximalIdeal 2 ^ 3)
    (htransform : (pointBlowupChartGerm c).pullbackRingHom
      (e.forward.pullbackRingHom (v * U)) = coordinate (1 : Fin 2) ^ 2 * T) :
    T ∉ maximalIdeal 2 ^ 2 := by
  obtain ⟨F, G, hfactor, hF, hG, hJac⟩ := exists_transverse_node_factorization v α β hβ hv
  apply pointBlowup_transverse_product_not_mem_square c
    (e.forward.pullbackRingHom F) (e.forward.pullbackRingHom (G * U)) T
  · simpa only [pow_one] using e.forward.pullback_mem_maximalIdeal_pow
      (by simpa only [pow_one] using hF : F ∈ maximalIdeal 2 ^ 1)
  · have hGU := (maximalIdeal 2).mul_mem_right U hG
    simpa only [pow_one] using e.forward.pullback_mem_maximalIdeal_pow
      (by simpa only [pow_one] using hGU : G * U ∈ maximalIdeal 2 ^ 1)
  · exact jacobian_isUnit_pullback_equiv e F (G * U)
      (jacobian_isUnit_mul_unit_right F G U hG hJac hU)
  · simpa only [hfactor, mul_assoc, map_mul] using htransform

end OnLeConjecture.Analytic.Germ

namespace OnLeConjecture.Analytic.AnalyticPointBasis

open OnLeConjecture.Analytic.Germ

/-- The node calculation applies to the recorded chart of every child.
No further coordinate compatibility is imposed below the node. -/
theorem ordinary_node_child_not_mem_square
    {N : ℕ} (c : AnalyticPointBasis N) (p : Fin N) (hp : c.multiplicity p = 2)
    (v U : Germ 2) (hU : IsUnit U) (hidentity : c.germ p = v * U)
    (α β : ℂ) (hβ : β ≠ 0)
    (hv : v - coordinate (0 : Fin 2) *
      (constRingHom 2 α * coordinate (0 : Fin 2) +
        constRingHom 2 β * coordinate (1 : Fin 2)) ∈ maximalIdeal 2 ^ 3)
    (q : Fin N) (hq : c.ParentRelation q p) : c.germ q ∉ maximalIdeal 2 ^ 2 := by
  apply pointBlowup_node_not_mem_square (c.sourceCoordinates q) (c.chartCenter q)
    v U (c.germ q) hU α β hβ hv
  have h := c.transform_identity q hq.1
  simpa only [hq.2, hp, hidentity] using h

end OnLeConjecture.Analytic.AnalyticPointBasis
