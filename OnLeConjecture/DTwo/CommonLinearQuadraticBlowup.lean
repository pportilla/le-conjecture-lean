/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CommonLinearQuadraticJet
import Mathlib.Tactic

/-!
# The first blowup of the common-linear quadratic jet

The weak transform of the coordinate with jet `xy` has exceptional
restriction `x+c`, hence has order at most one at every finite chart
center. At the common center `c=0`, both the `x²` and `xy` transforms
vanish. These analytic facts do not assert that a resolution of the base
ideal records that smooth common base point.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ _root_.Polynomial

private theorem ordinary_initial_exact_order
    (m : ℕ) (f : Germ 2) (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![1, 1] m) (hPne : P ≠ 0)
    (htail : f - coordinatePolynomialAlgHom 2 P ∈ maximalIdeal 2 ^ (m + 1)) :
    f ∈ maximalIdeal 2 ^ m ∧ f ∉ maximalIdeal 2 ^ (m + 1) := by
  have hpoly : coordinatePolynomialAlgHom 2 P ∈ maximalIdeal 2 ^ m := by
    simpa only [weightedOrderIdeal_one_eq_maximalIdeal_pow] using
      coordinatePolynomial_mem_weightedOrderIdeal 1 m (by decide) hP
  refine ⟨?_, ?_⟩
  · simpa only [sub_add_cancel] using Ideal.add_mem _
      ((Ideal.pow_le_pow_right (by omega : m ≤ m + 1)) htail) hpoly
  · intro hnext
    apply hPne
    apply eq_zero_of_isWeightedHomogeneous_coordinatePolynomial_mem_succ 1 m (by decide) hP
    rw [weightedOrderIdeal_one_eq_maximalIdeal_pow]
    simpa only [sub_sub_cancel] using Ideal.sub_mem _ hnext htail

/-- The weak transform of `xy+O(m³)` has a nonzero linear exceptional
term in every finite chart. At `c=0` its ordinary order is exactly one. -/
theorem exists_common_linear_quadratic_second_transform
    (g : Germ 2)
    (hg : g - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈ maximalIdeal 2 ^ 3)
    (c : ℂ) :
    ∃ G : Germ 2,
      (pointBlowupChartGerm c).pullbackRingHom g = coordinate (1 : Fin 2) ^ 2 * G ∧
      pointBlowupExceptionalLine.pullbackRingHom G = coordinate (0 : Fin 1) + constRingHom 1 c ∧
      G ∉ maximalIdeal 2 ^ 2 ∧ valueRingHom 2 G = c := by
  let P : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 0 * MvPolynomial.X 1
  have hP : P.IsWeightedHomogeneous ![1, 1] 2 :=
    (MvPolynomial.isWeightedHomogeneous_X ℂ (![1, 1] : Fin 2 → ℕ) 0).mul
      (MvPolynomial.isWeightedHomogeneous_X ℂ (![1, 1] : Fin 2 → ℕ) 1)
  have ht : g - coordinatePolynomialAlgHom 2 P ∈ maximalIdeal 2 ^ 3 := by
    simpa only [P, map_mul, coordinatePolynomialAlgHom_X] using hg
  have hPne : P ≠ 0 := mul_ne_zero (MvPolynomial.X_ne_zero 0) (MvPolynomial.X_ne_zero 1)
  obtain ⟨hmem, hnext⟩ := ordinary_initial_exact_order 2 g P hP hPne ht
  let G := pointBlowupTransform c 2 g hmem
  have hfactor : (pointBlowupChartGerm c).pullbackRingHom g = coordinate (1 : Fin 2) ^ 2 * G :=
    pointBlowupTransform_factor c 2 g hmem
  have hres := pointBlowupTransform_exceptionalRestriction c 2 g G P hmem hnext hP ht hfactor
  have hres' : pointBlowupExceptionalLine.pullbackRingHom G =
      coordinate (0 : Fin 1) + constRingHom 1 c := by
    have halg : algebraMap ℂ (Germ 1) = constRingHom 1 := rfl
    simpa [P, oneVariablePolynomialEvaluation, halg] using hres
  refine ⟨G, hfactor, hres', ?_, ?_⟩
  · intro hsquare
    have h := PointedMapGerm.pullback_mem_maximalIdeal_pow pointBlowupExceptionalLine hsquare
    rw [hres'] at h
    exact oneVariablePolynomialEvaluation_not_mem_pow 1 (X + C c)
      (by exact Polynomial.monic_X_add_C c |>.ne_zero)
      (by simp) (by
        have halg : algebraMap ℂ (Germ 1) = constRingHom 1 := rfl
        simpa [oneVariablePolynomialEvaluation, halg] using h)
  · have h := congrArg (valueRingHom 1) hres'
    simpa only [PointedMapGerm.valueRingHom_pullback, map_add, valueRingHom_coordinate,
      valueRingHom_const, zero_add] using h

/-- The two actual weak transforms vanish at the common exceptional
center. The second has exact order one there. -/
theorem exists_common_linear_quadratic_common_basepoint
    (f g : Germ 2)
    (hf : f - coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3)
    (hg : g - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈ maximalIdeal 2 ^ 3) :
    ∃ F G : Germ 2,
      (pointBlowupChartGerm 0).pullbackRingHom f = coordinate (1 : Fin 2) ^ 2 * F ∧
      (pointBlowupChartGerm 0).pullbackRingHom g = coordinate (1 : Fin 2) ^ 2 * G ∧
      F ∈ maximalIdeal 2 ∧ G ∈ maximalIdeal 2 ∧ G ∉ maximalIdeal 2 ^ 2 := by
  obtain ⟨G, hG, _hresG, hGnot, hGvalue⟩ := exists_common_linear_quadratic_second_transform g hg 0
  let P : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 0 ^ 2
  have hP : P.IsWeightedHomogeneous ![1, 1] 2 := by
    simpa using (MvPolynomial.isWeightedHomogeneous_X ℂ (![1, 1] : Fin 2 → ℕ) 0).pow 2
  have ht : f - coordinatePolynomialAlgHom 2 P ∈ maximalIdeal 2 ^ 3 := by
    simpa only [P, map_pow, coordinatePolynomialAlgHom_X] using hf
  obtain ⟨hmem, hnext⟩ := ordinary_initial_exact_order 2 f P hP
    (pow_ne_zero 2 (MvPolynomial.X_ne_zero 0)) ht
  let F := pointBlowupTransform 0 2 f hmem
  have hF := pointBlowupTransform_factor 0 2 f hmem
  have hresF := pointBlowupTransform_exceptionalRestriction 0 2 f F P hmem hnext hP ht hF
  have hFvalue : valueRingHom 2 F = 0 := by
    have h := congrArg (valueRingHom 1) hresF
    rw [PointedMapGerm.valueRingHom_pullback] at h
    simpa [P, oneVariablePolynomialEvaluation] using h
  exact ⟨F, G, hF, hG, mem_maximalIdeal_iff.mpr hFvalue,
    mem_maximalIdeal_iff.mpr hGvalue, hGnot⟩

/-- When the third quadratic jet lies in the span of the first two, the
three weak transforms generate an ideal of exact order one at the common
exceptional point. -/
theorem exists_common_linear_quadratic_weak_ideal_order_one
    (f g w : Germ 2)
    (hf : f - coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3)
    (hg : g - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈ maximalIdeal 2 ^ 3)
    (α β : ℂ)
    (hw : w - (constRingHom 2 α * f + constRingHom 2 β * g) ∈ maximalIdeal 2 ^ 3) :
    ∃ F G W : Germ 2,
      (pointBlowupChartGerm 0).pullbackRingHom f = coordinate (1 : Fin 2) ^ 2 * F ∧
      (pointBlowupChartGerm 0).pullbackRingHom g = coordinate (1 : Fin 2) ^ 2 * G ∧
      (pointBlowupChartGerm 0).pullbackRingHom w = coordinate (1 : Fin 2) ^ 2 * W ∧
      Ideal.span {F, G, W} ≤ maximalIdeal 2 ∧
      ¬ Ideal.span {F, G, W} ≤ maximalIdeal 2 ^ 2 := by
  obtain ⟨F, G, hF, hG, hFmem, hGmem, hGnot⟩ :=
    exists_common_linear_quadratic_common_basepoint f g hf hg
  obtain ⟨D, hD⟩ := exists_pointBlowupChart_factor 0 3
    (w - (constRingHom 2 α * f + constRingHom 2 β * g)) hw
  let W := constRingHom 2 α * F + constRingHom 2 β * G + coordinate (1 : Fin 2) * D
  have hWmem : W ∈ maximalIdeal 2 := Ideal.add_mem _
    (Ideal.add_mem _ (Ideal.mul_mem_left _ _ hFmem) (Ideal.mul_mem_left _ _ hGmem))
    (Ideal.mul_mem_right _ _ (coordinate_mem_maximalIdeal 1))
  have hW : (pointBlowupChartGerm 0).pullbackRingHom w = coordinate (1 : Fin 2) ^ 2 * W := by
    rw [map_sub, map_add, map_mul, map_mul, PointedMapGerm.pullback_constRingHom,
      PointedMapGerm.pullback_constRingHom, hF, hG] at hD
    dsimp only [W]
    linear_combination hD
  refine ⟨F, G, W, hF, hG, hW, ?_, ?_⟩
  · rw [Ideal.span_le]
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact hFmem
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact hGmem
    exact Set.mem_singleton_iff.mp hz ▸ hWmem
  · intro hle
    apply hGnot
    apply hle
    exact Ideal.subset_span (by simp)

end OnLeConjecture.DTwo
