/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ProjectivePolynomialOrder
public import OnLeConjecture.Analytic.TwoChartBlowupLift
public import Mathlib.Algebra.BigOperators.Option

/-!
# The exceptional intersection bound over both projective charts

The finite chart restrictions are translations of one polynomial. The
complementary restriction reverses its coefficients in the original
ordinary degree. The polynomial degree and the complementary vanishing
order together are at most that degree. Thus the sum of exceptional
intersection orders over any finite set of projective centers is bounded
by the original multiplicity, without a transverse-coordinate assumption.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial
open scoped BigOperators

/-- Restriction of the actual strict transform is the translated
polynomial formed from the degree-`m` coefficients of a monomial expansion. -/
theorem exceptional_restriction_of_generator_expansion
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (a : Fin (m + 1) → Germ 2)
    (ha : ∑ k, a k * weightedOrderGenerator 1 m k = f) (c : ℂ) :
    pointBlowupExceptionalLine.pullbackRingHom (pointBlowupTransform c m f hf) =
      oneVariablePolynomialEvaluation
        ((∑ k : Fin (m + 1), C (valueRingHom 2 (a k)) * X ^ k.val).comp (X + C c)) := by
  let V : Germ 2 := ∑ k : Fin (m + 1),
    (pointBlowupChartGerm c).pullbackRingHom (a k) *
      (coordinate (0 : Fin 2) + constRingHom 2 c) ^ k.val
  have hV : (pointBlowupChartGerm c).pullbackRingHom f = coordinate (1 : Fin 2) ^ m * V := by
    rw [← ha, map_sum]
    simp only [V, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_mul, pointBlowupChart_pullback_generator]
    ring
  rw [pointBlowupTransform_unique c m f _ V (pointBlowupTransform_factor c m f hf) hV]
  simp only [V, map_sum, map_mul, map_pow, pointBlowupExceptionalLine_pullback_chart,
    map_add, pointBlowupExceptionalLine_pullback_zero, PointedMapGerm.pullback_constRingHom,
    sum_comp, mul_comp, C_comp, pow_comp, X_comp, oneVariablePolynomialEvaluation,
    aeval_C, aeval_X, RingHom.algebraMap_toAlgebra]

/-- The complementary exceptional restriction reverses the same
coefficient list in the original ordinary degree. -/
theorem complementary_restriction_of_generator_expansion
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (a : Fin (m + 1) → Germ 2)
    (ha : ∑ k, a k * weightedOrderGenerator 1 m k = f) :
    pointBlowupExceptionalLine.pullbackRingHom
      (pointBlowupTransform 0 m
        ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom f)
        ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullback_mem_maximalIdeal_pow hf)) =
      oneVariablePolynomialEvaluation
        (∑ k : Fin (m + 1), C (valueRingHom 2 (a k)) * X ^ (m - k.val)) := by
  let e := coordinateSwapPointedEquiv (1 : Fin 2)
  let V : Germ 2 := ∑ k : Fin (m + 1),
    (pointBlowupChartGerm 0).pullbackRingHom (e.forward.pullbackRingHom (a k)) *
      coordinate (0 : Fin 2) ^ (m - k.val)
  have hx : e.forward.pullbackRingHom (coordinate (0 : Fin 2)) = coordinate (1 : Fin 2) := by
    rw [PointedMapGerm.pullback_coordinate]
    exact coordinateSwapPointedEquiv_component_zero 1
  have hy : e.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate (0 : Fin 2) :=
    coordinateSwapPointedEquiv_pullback_second
  have hV : (pointBlowupChartGerm 0).pullbackRingHom (e.forward.pullbackRingHom f) =
      coordinate (1 : Fin 2) ^ m * V := by
    rw [← ha, map_sum, map_sum]
    simp only [V, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [weightedOrderGenerator, one_mul, map_mul, map_pow, hx, hy,
      pointBlowupChartGerm_pullback_zero, pointBlowupChartGerm_pullback_one,
      map_zero, add_zero, mul_pow]
    have hk : k.val + (m - k.val) = m := Nat.add_sub_of_le (by omega)
    calc
      _ = (pointBlowupChartGerm 0).pullbackRingHom (e.forward.pullbackRingHom (a k)) *
          (coordinate (1 : Fin 2) ^ k.val * coordinate (1 : Fin 2) ^ (m - k.val)) *
          coordinate (0 : Fin 2) ^ (m - k.val) := by ring
      _ = _ := by rw [← pow_add, hk]; ring
  have heq := pointBlowupTransform_unique 0 m (e.forward.pullbackRingHom f) _ V
    (pointBlowupTransform_factor 0 m _ (e.forward.pullback_mem_maximalIdeal_pow hf)) hV
  rw [heq]
  simp only [V, map_sum, map_mul, map_pow, pointBlowupExceptionalLine_pullback_chart,
    pointBlowupExceptionalLine_pullback_zero, PointedMapGerm.valueRingHom_pullback,
    oneVariablePolynomialEvaluation, aeval_C, aeval_X, RingHom.algebraMap_toAlgebra]

/-- The complementary point is included in the exceptional intersection
bound for any finite list of finite-chart centers. -/
theorem sum_exceptional_restriction_orders_add_complementary_le
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hnext : f ∉ maximalIdeal 2 ^ (m + 1)) (s : Finset ℂ) :
    (∑ c ∈ s, (vanishingOrder (pointBlowupExceptionalLine.pullbackRingHom
      (pointBlowupTransform c m f hf))).toNat) +
      (vanishingOrder (pointBlowupExceptionalLine.pullbackRingHom
        (pointBlowupTransform 0 m
          ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom f)
          ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullback_mem_maximalIdeal_pow
            hf)))).toNat
      ≤ m := by
  classical
  have hfweight : f ∈ weightedOrderIdeal 1 m := by
    simpa only [weightedOrderIdeal_one_eq_maximalIdeal_pow] using hf
  obtain ⟨a, ha⟩ := (mem_weightedOrderIdeal_iff 1 m f).mp hfweight
  let A : ℂ[X] := ∑ k : Fin (m + 1), C (valueRingHom 2 (a k)) * X ^ k.val
  have hA : A ≠ 0 := by
    intro hz
    apply hnext
    rw [← ha]
    apply (maximalIdeal 2 ^ (m + 1)).sum_mem
    intro k _
    have hak : a k ∈ maximalIdeal 2 := by
      rw [mem_maximalIdeal_iff]
      have hcoeff := coefficient_sum_C_mul_X_pow m (fun j => valueRingHom 2 (a j)) k
      change A.coeff k.val = _ at hcoeff
      rw [hz, coeff_zero] at hcoeff
      exact hcoeff.symm
    have hg : weightedOrderGenerator 1 m k ∈ maximalIdeal 2 ^ m := by
      rw [← weightedOrderIdeal_one_eq_maximalIdeal_pow]
      exact weightedOrderGenerator_mem 1 m k
    simpa only [pow_succ'] using Ideal.mul_mem_mul hak hg
  simp_rw [exceptional_restriction_of_generator_expansion m f hf a ha,
    complementary_restriction_of_generator_expansion m f hf a ha]
  exact (Nat.add_le_add_right
    (sum_vanishingOrder_polynomial_translation_le_degree A hA s) _).trans
      (polynomial_reverse_order_budget m (fun k => valueRingHom 2 (a k)) hA)

/-- Exceptional intersection orders over any finite set of projective
centers sum to at most the original exact ordinary order. -/
theorem sum_projective_exceptional_restriction_orders_le
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hnext : f ∉ maximalIdeal 2 ^ (m + 1)) (s : Finset (Option ℂ)) :
    ∑ t ∈ s, (vanishingOrder (pointBlowupExceptionalLine.pullbackRingHom
      (pointBlowupTransform (projectiveChartCenter t) m
        ((projectiveChartSource t).forward.pullbackRingHom f)
        ((projectiveChartSource t).forward.pullback_mem_maximalIdeal_pow hf)))).toNat ≤ m := by
  classical
  let b : Option ℂ → ℕ := fun t =>
    (vanishingOrder (pointBlowupExceptionalLine.pullbackRingHom
      (pointBlowupTransform (projectiveChartCenter t) m
        ((projectiveChartSource t).forward.pullbackRingHom f)
        ((projectiveChartSource t).forward.pullback_mem_maximalIdeal_pow hf)))).toNat
  change (∑ t ∈ s, b t) ≤ m
  have hsome (c : ℂ) : b (some c) =
      (vanishingOrder (pointBlowupExceptionalLine.pullbackRingHom
        (pointBlowupTransform c m f hf))).toNat := by
    dsimp only [b, projectiveChartSource, projectiveChartCenter]
    simp only [PointedEquivGerm.identity_forward, PointedMapGerm.pullbackRingHom_identity,
      RingHom.id_apply]
  have hnone : b none =
      (vanishingOrder (pointBlowupExceptionalLine.pullbackRingHom
        (pointBlowupTransform 0 m
          ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom f)
          ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullback_mem_maximalIdeal_pow
            hf)))).toNat :=
    rfl
  have hsub : s ⊆ Finset.insertNone s.eraseNone := by
    intro t ht
    cases t with
    | none => simp
    | some c => simpa using ht
  have hle : ∑ t ∈ s, b t ≤ ∑ t ∈ Finset.insertNone s.eraseNone, b t :=
    Finset.sum_le_sum_of_subset hsub
  apply hle.trans
  rw [Finset.sum_insertNone, hnone]
  simp_rw [hsome]
  rw [Nat.add_comm]
  exact sum_exceptional_restriction_orders_add_complementary_le m f hf hnext s.eraseNone

end OnLeConjecture.Analytic.Germ
