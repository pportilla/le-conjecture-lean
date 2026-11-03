/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RootClusterIntersection
public import OnLeConjecture.Analytic.ResultantRootOrder
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.ENat.BigOperators

/-!
# Decomposition over all residue roots

Iterated analytic Hensel factorization separates the finitely many
distinct roots of the residue polynomial, retaining their full
multiplicities. Resultant multiplicativity then expresses its order as
the sum of the analytic local intersections at these centers.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial
open scoped BigOperators

/-- Analytic lifting of a finite factorization by distinct residue roots.
The exponents need not be positive for this factorization statement. -/
theorem exists_analytic_factors_of_residue_root_product
    (s : Finset ℂ) (μ : ℂ → ℕ) (P : Polynomial (Germ 1)) (hP : P.Monic)
    (hresidue : P.map (valueRingHom 1) = ∏ c ∈ s, (X - C c) ^ μ c) :
    ∃ F : ℂ → Polynomial (Germ 1),
      (∀ c ∈ s, (F c).Monic ∧ (F c).natDegree = μ c ∧
        (F c).map (valueRingHom 1) = (X - C c) ^ μ c) ∧ P = ∏ c ∈ s, F c := by
  classical
  induction s using Finset.induction_on generalizing P with
  | empty =>
      have hdegree : P.natDegree = 0 := by
        rw [← hP.natDegree_map (valueRingHom 1), hresidue]
        simp
      refine ⟨fun _ ↦ 1, by simp, ?_⟩
      simpa using hP.natDegree_eq_zero.mp hdegree
  | @insert c s hc ih =>
      let B₀ : ℂ[X] := ∏ z ∈ s, (X - C z) ^ μ z
      have hB₀ : B₀.Monic := monic_prod_of_monic s _ fun z _ ↦ (monic_X_sub_C z).pow _
      have hA₀ : ((X - C c) ^ μ c : ℂ[X]).Monic := (monic_X_sub_C c).pow _
      have hres : P.map (valueRingHom 1) = (X - C c) ^ μ c * B₀ := by
        simpa only [Finset.prod_insert hc] using hresidue
      have hdegree : P.natDegree = μ c + B₀.natDegree := by
        rw [← hP.natDegree_map (valueRingHom 1), hres, hA₀.natDegree_mul hB₀]
        simp only [natDegree_pow, natDegree_X_sub_C, mul_one]
      have hcoprime : IsCoprime ((X - C c) ^ μ c) B₀ := by
        apply IsCoprime.prod_right
        intro z hz
        have hcz : c ≠ z := fun h ↦ hc (h ▸ hz)
        exact (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hcz).isUnit).pow_left.pow_right
      obtain ⟨A, B, hA, hAm, hB, _, hAres, hBres, hfactor⟩ :=
        exists_analytic_hensel_factorization (μ c) B₀.natDegree P hP hdegree
          ((X - C c) ^ μ c) B₀ hA₀ hB₀ (by simp) rfl hcoprime hres
      obtain ⟨F, hF, hBfactor⟩ := ih B hB hBres
      refine ⟨Function.update F c A, ?_, ?_⟩
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · simpa only [Function.update_self] using And.intro hA (And.intro hAm hAres)
        · rw [Function.update_of_ne (show z ≠ c from fun h ↦ hc (h ▸ hz))]
          exact hF z hz
      · rw [Finset.prod_insert hc, Function.update_self, hfactor, hBfactor]
        congr 1
        apply Finset.prod_congr rfl
        intro z hz
        rw [Function.update_of_ne (show z ≠ c from fun h ↦ hc (h ▸ hz))]

/-- All roots, with their exact multiplicities, determine analytic monic
factors whose product is the original polynomial. -/
theorem exists_analytic_factors_of_all_residue_roots
    (P : Polynomial (Germ 1)) (hP : P.Monic) :
    ∃ F : ℂ → Polynomial (Germ 1),
      (∀ c ∈ (P.map (valueRingHom 1)).roots.toFinset,
        (F c).Monic ∧ (F c).natDegree = (P.map (valueRingHom 1)).rootMultiplicity c ∧
          (F c).map (valueRingHom 1) =
            (X - C c) ^ (P.map (valueRingHom 1)).rootMultiplicity c) ∧
      P = ∏ c ∈ (P.map (valueRingHom 1)).roots.toFinset, F c := by
  classical
  apply exists_analytic_factors_of_residue_root_product _ _ P hP
  calc
    P.map (valueRingHom 1) =
        ((P.map (valueRingHom 1)).roots.map (fun c ↦ X - C c)).prod :=
      (IsAlgClosed.splits _).eq_prod_roots_of_monic (hP.map _)
    _ = _ := by simpa only [count_roots] using
      Finset.prod_multiset_map_count (P.map (valueRingHom 1)).roots (fun c ↦ X - C c)

/-- The order of the resultant is the sum of actual local intersection
multiplicities over every distinct residue root. Each translated first
polynomial has degree equal to that root's full multiplicity. -/
theorem exists_resultant_order_eq_sum_residue_root_intersections
    (P Q : Polynomial (Germ 1)) (hP : P.Monic) (hresultant : P.resultant Q ≠ 0) :
    ∃ F : ℂ → Polynomial (Germ 1),
      (∀ c ∈ (P.map (valueRingHom 1)).roots.toFinset,
        (F c).Monic ∧ (F c).natDegree = (P.map (valueRingHom 1)).rootMultiplicity c ∧
          (F c).map (valueRingHom 1) =
            (X - C c) ^ (P.map (valueRingHom 1)).rootMultiplicity c) ∧
      P = ∏ c ∈ (P.map (valueRingHom 1)).roots.toFinset, F c ∧
      ∃ hfinite : ∀ c : (P.map (valueRingHom 1)).roots.toFinset,
        PlaneCurve.HasFiniteIntersection
          (firstCoordinatePolynomialEvaluation (rootTranslation (F c) c))
          (firstCoordinatePolynomialEvaluation (rootTranslation Q c)),
        (vanishingOrder (P.resultant Q)).toNat =
          ∑ c : (P.map (valueRingHom 1)).roots.toFinset,
            PlaneCurve.intersectionMultiplicity
              (firstCoordinatePolynomialEvaluation (rootTranslation (F c) c))
              (firstCoordinatePolynomialEvaluation (rootTranslation Q c)) (hfinite c) := by
  classical
  let s := (P.map (valueRingHom 1)).roots.toFinset
  obtain ⟨F, hF, hfactor⟩ := exists_analytic_factors_of_all_residue_roots P hP
  have hres : P.resultant Q = ∏ c ∈ s, (F c).resultant Q := by
    rw [hfactor]
    apply resultant_prod_left _ _ _ _ _ le_rfl
    exact Finset.prod_ne_zero_iff.mpr fun c hc ↦ by rw [(hF c hc).1]; exact one_ne_zero
  have hne : ∀ c ∈ s, (F c).resultant Q ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (hres ▸ hresultant)
  have hlocal (c : s) : ∃ hf : PlaneCurve.HasFiniteIntersection
      (firstCoordinatePolynomialEvaluation (rootTranslation (F c) c))
      (firstCoordinatePolynomialEvaluation (rootTranslation Q c)),
      PlaneCurve.intersectionMultiplicity
        (firstCoordinatePolynomialEvaluation (rootTranslation (F c) c))
        (firstCoordinatePolynomialEvaluation (rootTranslation Q c)) hf =
          (vanishingOrder ((F c).resultant Q)).toNat := by
    have hroot := (mem_roots (hP.map (valueRingHom 1)).ne_zero).mp
      (Multiset.mem_toFinset.mp c.property)
    have hm := (rootMultiplicity_pos (hP.map (valueRingHom 1)).ne_zero).mpr hroot
    exact exists_root_cluster_intersection_eq_resultant_order (F c) Q c _ hm
      (hF c c.property).1 (hF c c.property).2.1 (hF c c.property).2.2 (hne c c.property)
  choose hf hi using hlocal
  refine ⟨F, hF, hfactor, hf, ?_⟩
  simp_rw [hi]
  rw [Finset.sum_coe_sort s (fun c ↦ (vanishingOrder ((F c).resultant Q)).toNat),
    hres, vanishingOrder_finset_prod,
    ENat.toNat_sum (fun c hc ↦ vanishingOrder_eq_top_iff.not.mpr (hne c hc))]

end OnLeConjecture.Analytic.Germ
