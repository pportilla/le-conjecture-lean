/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ProjectiveExceptionalIntersectionBound
public import OnLeConjecture.Analytic.ExceptionalPolynomialFamily
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Exact total intersection with the projective exceptional divisor

The order at the complementary point is exactly the ordinary degree minus
the finite-chart degree. Summing the orders at all complex roots therefore
recovers the original ordinary multiplicity, including order zero.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial
open scoped BigOperators

/-- A first nonzero polynomial coefficient determines the analytic order. -/
theorem polynomialEvaluation_order_eq_of_first_coeff
    (P : ℂ[X]) (n : ℕ) (hn : P.coeff n ≠ 0)
    (hlower : ∀ j < n, P.coeff j = 0) :
    vanishingOrder (oneVariablePolynomialEvaluation P) = (n : ℕ∞) := by
  have hP : P ≠ 0 := by intro hz; exact hn (by rw [hz, coeff_zero])
  have hroot : P.rootMultiplicity 0 = n := by
    apply le_antisymm
    · rw [rootMultiplicity_le_iff hP, map_zero, sub_zero, X_pow_dvd_iff]
      intro h
      exact hn (h n (by omega))
    · rw [le_rootMultiplicity_iff hP, map_zero, sub_zero, X_pow_dvd_iff]
      exact hlower
  have h := vanishingOrder_polynomial_translation P hP 0
  simpa only [map_zero, C_0, add_zero, comp_X, hroot] using h

/-- Coefficient reversal gives the exact order at the complementary
projective point. -/
theorem polynomial_reverse_order_exact
    (m : ℕ) (a : Fin (m + 1) → ℂ)
    (hne : (∑ k : Fin (m + 1), C (a k) * (X : ℂ[X]) ^ k.val) ≠ 0) :
    (∑ k : Fin (m + 1), C (a k) * (X : ℂ[X]) ^ k.val).natDegree +
      (vanishingOrder (oneVariablePolynomialEvaluation
        (∑ k : Fin (m + 1), C (a k) * (X : ℂ[X]) ^ (m - k.val)))).toNat = m := by
  classical
  let P : ℂ[X] := ∑ k : Fin (m + 1), C (a k) * X ^ k.val
  let Q : ℂ[X] := ∑ k : Fin (m + 1), C (a k) * X ^ (m - k.val)
  have hdegree : P.natDegree ≤ m := by
    apply natDegree_sum_le_of_forall_le
    intro k _
    exact (natDegree_C_mul_le _ _).trans
      (by simpa only [natDegree_X_pow] using (show k.val ≤ m by omega))
  let k : Fin (m + 1) := ⟨P.natDegree, by omega⟩
  have hak : a k ≠ 0 := by
    have hcoeff := coefficient_sum_C_mul_X_pow m a k
    change P.coeff P.natDegree = a k at hcoeff
    rw [coeff_natDegree] at hcoeff
    rw [← hcoeff]
    exact leadingCoeff_ne_zero.mpr hne
  have hcoeff : Q.coeff (m - P.natDegree) ≠ 0 := by
    change (∑ j : Fin (m + 1), C (a j) * X ^ (m - j.val)).coeff (m - k.val) ≠ 0
    rw [coefficient_sum_C_mul_X_pow_reverse]
    exact hak
  have hlower (j : ℕ) (hj : j < m - P.natDegree) : Q.coeff j = 0 := by
    change (∑ i : Fin (m + 1), C (a i) * X ^ (m - i.val)).coeff j = 0
    rw [finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : P.natDegree < i.val
    · have ha : a i = 0 := by
        rw [← coefficient_sum_C_mul_X_pow m a i]
        exact coeff_eq_zero_of_natDegree_lt hi
      simp only [ha, C_0, zero_mul, coeff_zero]
    · have hji : j ≠ m - i.val := by omega
      simp [coeff_C_mul, coeff_X_pow, hji]
  have horder := polynomialEvaluation_order_eq_of_first_coeff Q (m - P.natDegree)
    hcoeff hlower
  change P.natDegree + (vanishingOrder (oneVariablePolynomialEvaluation Q)).toNat = m
  rw [horder, ENat.toNat_natCast]
  exact Nat.add_sub_of_le hdegree

/-- All complex root multiplicities sum to the polynomial degree. -/
theorem sum_polynomial_rootMultiplicity_eq_degree (P : ℂ[X]) :
    ∑ c ∈ P.roots.toFinset, P.rootMultiplicity c = P.natDegree := by
  classical
  simp_rw [← count_roots]
  rw [Multiset.sum_count_eq_card (fun c hc => Multiset.mem_toFinset.mpr hc)]
  exact IsAlgClosed.card_roots_eq_natDegree

/-- The analytic orders at all finite exceptional polynomial roots sum
to the finite-chart degree. -/
theorem sum_vanishingOrder_polynomial_roots_eq_degree
    (P : ℂ[X]) (hP : P ≠ 0) :
    ∑ c ∈ P.roots.toFinset, (vanishingOrder
      (oneVariablePolynomialEvaluation (P.comp (X + C c)))).toNat = P.natDegree := by
  simp_rw [vanishingOrder_polynomial_translation P hP, ENat.toNat_natCast]
  exact sum_polynomial_rootMultiplicity_eq_degree P

/-- The strict transform in the projective chart indexed by `t`. -/
@[expose] noncomputable def projectiveStrictTransform
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m) (t : Option ℂ) : Germ 2 :=
  pointBlowupTransform (projectiveChartCenter t) m
    ((projectiveChartSource t).forward.pullbackRingHom f)
    ((projectiveChartSource t).forward.pullback_mem_maximalIdeal_pow hf)

/-- The intersection order of the projective strict transform with the
exceptional divisor. Exact ordinary order ensures that this order is finite. -/
@[expose] noncomputable def projectiveExceptionalIntersectionOrder
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m) (t : Option ℂ) : ℕ :=
  (vanishingOrder (pointBlowupExceptionalLine.pullbackRingHom
    (projectiveStrictTransform m f hf t))).toNat

theorem projectiveStrictTransform_some
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m) (c : ℂ) :
    projectiveStrictTransform m f hf (some c) = pointBlowupTransform c m f hf := by
  simp only [projectiveStrictTransform, projectiveChartSource, projectiveChartCenter,
    PointedEquivGerm.identity_forward, PointedMapGerm.pullbackRingHom_identity,
    RingHom.id_apply]

/-- A unit transform has zero intersection order with the exceptional divisor. -/
theorem projectiveExceptionalIntersectionOrder_eq_zero_of_isUnit
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m) (t : Option ℂ)
    (hunit : IsUnit (projectiveStrictTransform m f hf t)) :
    projectiveExceptionalIntersectionOrder m f hf t = 0 := by
  rw [projectiveExceptionalIntersectionOrder,
    vanishingOrder_eq_zero_iff_isUnit.mpr (hunit.map _), ENat.toNat_zero]

/-- All nonunit projective strict transforms lie in a finite set, and
the exceptional intersection orders over that set sum to the original order. -/
theorem exists_projective_exceptional_orders_sum_eq
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hnext : f ∉ maximalIdeal 2 ^ (m + 1)) :
    ∃ s : Finset (Option ℂ),
      (∀ t, projectiveStrictTransform m f hf t ∈ maximalIdeal 2 → t ∈ s) ∧
      ∑ t ∈ s, projectiveExceptionalIntersectionOrder m f hf t = m := by
  classical
  have hfweight : f ∈ weightedOrderIdeal 1 m := by
    simpa only [weightedOrderIdeal_one_eq_maximalIdeal_pow] using hf
  obtain ⟨a, ha⟩ := (mem_weightedOrderIdeal_iff 1 m f).mp hfweight
  let P : ℂ[X] := ∑ k : Fin (m + 1), C (valueRingHom 2 (a k)) * X ^ k.val
  have hP : P ≠ 0 := by
    intro hz
    apply hnext
    rw [← ha]
    apply (maximalIdeal 2 ^ (m + 1)).sum_mem
    intro k _
    have hak : a k ∈ maximalIdeal 2 := by
      rw [mem_maximalIdeal_iff]
      have hcoeff := coefficient_sum_C_mul_X_pow m (fun j => valueRingHom 2 (a j)) k
      change P.coeff k.val = _ at hcoeff
      rw [hz, coeff_zero] at hcoeff
      exact hcoeff.symm
    have hg : weightedOrderGenerator 1 m k ∈ maximalIdeal 2 ^ m := by
      rw [← weightedOrderIdeal_one_eq_maximalIdeal_pow]
      exact weightedOrderGenerator_mem 1 m k
    simpa only [pow_succ'] using Ideal.mul_mem_mul hak hg
  refine ⟨Finset.insertNone P.roots.toFinset, ?_, ?_⟩
  · intro t ht
    cases t with
    | none => simp
    | some c =>
      simp only [projectiveStrictTransform_some] at ht
      have hroot : P.IsRoot c :=
        (mem_maximalIdeal_iff_exceptional_polynomial_root _ P c
          (exceptional_restriction_of_generator_expansion m f hf a ha c)).mp ht
      simpa only [Finset.some_mem_insertNone, Multiset.mem_toFinset] using
        (mem_roots hP).mpr hroot
  · rw [Finset.sum_insertNone]
    have hfinite (c : ℂ) : projectiveExceptionalIntersectionOrder m f hf (some c) =
        (vanishingOrder (oneVariablePolynomialEvaluation (P.comp (X + C c)))).toNat := by
      rw [projectiveExceptionalIntersectionOrder, projectiveStrictTransform_some,
        exceptional_restriction_of_generator_expansion m f hf a ha c]
    have hnone : projectiveExceptionalIntersectionOrder m f hf none =
        (vanishingOrder (oneVariablePolynomialEvaluation
          (∑ k : Fin (m + 1), C (valueRingHom 2 (a k)) * X ^ (m - k.val)))).toNat := by
      exact congrArg (fun v => (vanishingOrder v).toNat)
        (complementary_restriction_of_generator_expansion m f hf a ha)
    simp_rw [hfinite]
    rw [sum_vanishingOrder_polynomial_roots_eq_degree P hP, hnone, Nat.add_comm]
    exact polynomial_reverse_order_exact m (fun k => valueRingHom 2 (a k)) hP

/-- Any finite set containing all nonunit projective transforms recovers
the full original multiplicity. Additional unit charts contribute zero. -/
theorem sum_projective_exceptional_restriction_orders_eq
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hnext : f ∉ maximalIdeal 2 ^ (m + 1)) (s : Finset (Option ℂ))
    (hcover : ∀ t, projectiveStrictTransform m f hf t ∈ maximalIdeal 2 → t ∈ s) :
    ∑ t ∈ s, projectiveExceptionalIntersectionOrder m f hf t = m := by
  classical
  obtain ⟨r, hr, hsum⟩ := exists_projective_exceptional_orders_sum_eq m f hf hnext
  have hzero (u : Finset (Option ℂ))
      (hu : ∀ t, projectiveStrictTransform m f hf t ∈ maximalIdeal 2 → t ∈ u)
      (t : Option ℂ) (ht : t ∉ u) :
      projectiveExceptionalIntersectionOrder m f hf t = 0 := by
    apply projectiveExceptionalIntersectionOrder_eq_zero_of_isUnit
    apply isUnit_iff_valueRingHom_ne_zero.mpr
    intro hz
    exact ht (hu t (mem_maximalIdeal_iff.mpr hz))
  calc
    _ = ∑ t ∈ s ∪ r, projectiveExceptionalIntersectionOrder m f hf t := by
      apply Finset.sum_subset Finset.subset_union_left
      intro t _ ht
      exact hzero s hcover t ht
    _ = ∑ t ∈ r, projectiveExceptionalIntersectionOrder m f hf t := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro t _ ht
      exact hzero r hr t ht
    _ = m := hsum

end OnLeConjecture.Analytic.Germ
