/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ScaledPolynomialFreeCharts
public import OnLeConjecture.Analytic.CompleteRootClusterIntersection
public import OnLeConjecture.Analytic.PlaneUniqueFactorization

/-!
# Irreducibility of the polynomial in a blowup chart

A factorization of the scaled chart polynomial descends by root scaling
to a factorization of the original analytic equation. Positive-degree
factors descend to nonunits. Analytic irreducibility therefore implies
polynomial irreducibility of the chart polynomial. Convergent Hensel
factorization then forces its residue to have a single root.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

theorem monic_eq_one_of_isUnit_scaled_polynomialEvaluation
    (A : Polynomial (Germ 1)) (hA : A.Monic)
    (hunit : IsUnit
      (firstCoordinatePolynomialEvaluation (A.scaleRoots (coordinate (0 : Fin 1))))) : A = 1 := by
  apply hA.natDegree_eq_zero.mp
  by_contra hdegree
  have hpos : 0 < A.natDegree := Nat.pos_of_ne_zero hdegree
  have hmem : firstCoordinatePolynomialEvaluation
      (A.scaleRoots (coordinate (0 : Fin 1))) ∈ maximalIdeal 2 := by
    have h := scaled_polynomialEvaluation_mem_degree A 1 (by decide)
    rw [pow_one] at h
    simpa only [pow_one] using (Ideal.pow_le_pow_right hpos) h
  exact (valueRingHom_ne_zero_of_isUnit hunit) (mem_maximalIdeal_iff.mp hmem)

/-- Polynomial irreducibility upstairs follows from analytic
irreducibility of its root-scaled equation downstairs. -/
theorem irreducible_of_irreducible_scaled_polynomialEvaluation
    (A : Polynomial (Germ 1)) (hA : A.Monic)
    (hirr : Irreducible
      (firstCoordinatePolynomialEvaluation (A.scaleRoots (coordinate (0 : Fin 1))))) :
    Irreducible A := by
  have hAone : A ≠ 1 := by
    intro h
    apply hirr.not_isUnit
    simp only [h, one_scaleRoots, firstCoordinatePolynomialEvaluation,
      eval₂_one, isUnit_one]
  apply (Polynomial.irreducible_of_monic hA hAone).mpr
  intro B C hB hC hfactor
  have hanalytic : firstCoordinatePolynomialEvaluation
        (A.scaleRoots (coordinate (0 : Fin 1))) =
      firstCoordinatePolynomialEvaluation (B.scaleRoots (coordinate (0 : Fin 1))) *
        firstCoordinatePolynomialEvaluation (C.scaleRoots (coordinate (0 : Fin 1))) := by
    rw [← hfactor, mul_scaleRoots_of_noZeroDivisors]
    exact map_mul firstCoordinatePolynomialEvaluationRingHom _ _
  exact (hirr.isUnit_or_isUnit hanalytic).imp
    (monic_eq_one_of_isUnit_scaled_polynomialEvaluation B hB)
    (monic_eq_one_of_isUnit_scaled_polynomialEvaluation C hC)

/-- An irreducible monic analytic polynomial has only one residue root.
The assertion uses convergent Hensel factorization, not completeness of
the one-variable analytic local ring. -/
theorem exists_residue_eq_root_power_of_monic_irreducible
    (A : Polynomial (Germ 1)) (hA : A.Monic) (hirr : Irreducible A) :
    ∃ c : ℂ, A.map (valueRingHom 1) = (X - C c) ^ A.natDegree := by
  classical
  have hdegree : 0 < A.natDegree := by
    by_contra h
    have hAone := hA.natDegree_eq_zero.mp (Nat.eq_zero_of_not_pos h)
    exact hirr.not_isUnit (hAone ▸ isUnit_one)
  have hresdegree : 0 < (A.map (valueRingHom 1)).degree := by
    rw [degree_eq_natDegree (hA.map _).ne_zero, hA.natDegree_map]
    exact_mod_cast hdegree
  obtain ⟨c, hc⟩ := Complex.exists_root hresdegree
  have hcmem : c ∈ (A.map (valueRingHom 1)).roots.toFinset :=
    Multiset.mem_toFinset.mpr ((mem_roots (hA.map _).ne_zero).mpr hc)
  have hcpos : 0 < (A.map (valueRingHom 1)).rootMultiplicity c :=
    (rootMultiplicity_pos (hA.map _).ne_zero).mpr hc
  obtain ⟨F, hF, hfactor⟩ := exists_analytic_factors_of_all_residue_roots A hA
  have hFunit : ¬ IsUnit (F c) := by
    intro h
    have hone := (hF c hcmem).1.eq_one_of_isUnit h
    have hdeg := (hF c hcmem).2.1
    rw [hone, natDegree_one] at hdeg
    omega
  have hdiv : F c ∣ A := by
    rw [hfactor]
    exact Finset.dvd_prod_of_mem F hcmem
  have hassociated : Associated A (F c) := (hirr.dvd_iff.mp hdiv).resolve_left hFunit
  have heq : A = F c := eq_of_monic_of_associated hA (hF c hcmem).1 hassociated
  refine ⟨c, ?_⟩
  rw [heq, (hF c hcmem).2.1]
  exact (hF c hcmem).2.2

theorem irreducible_rootTranslation
    (A : Polynomial (Germ 1)) (c : ℂ) (hirr : Irreducible A) :
    Irreducible (rootTranslation A c) :=
  (MulEquiv.irreducible_iff (taylorEquiv (constRingHom 1 c)).toRingEquiv.toMulEquiv).mpr hirr

/-- Centering the unique residue root gives an irreducible analytic
strict-transform equation, by the distinguished Weierstrass quotient. -/
theorem irreducible_polynomialEvaluation_rootTranslation_of_single_residue_root
    (A : Polynomial (Germ 1)) (hA : A.Monic) (hirr : Irreducible A)
    (c : ℂ) (hresidue : A.map (valueRingHom 1) = (X - C c) ^ A.natDegree) :
    Irreducible (firstCoordinatePolynomialEvaluation (rootTranslation A c)) := by
  have hdegree : 0 < A.natDegree := by
    by_contra h
    have hAone := hA.natDegree_eq_zero.mp (Nat.eq_zero_of_not_pos h)
    exact hirr.not_isUnit (hAone ▸ isUnit_one)
  apply (prime_firstCoordinatePolynomialEvaluation_of_distinguished
    (d := A.natDegree - 1)
    (irreducible_iff_prime.mp (irreducible_rootTranslation A c hirr))
    ((rootTranslation_monic A c).mpr hA)
    (by rw [rootTranslation_natDegree, Nat.sub_add_cancel hdegree])
    (by simpa only [Nat.sub_add_cancel hdegree] using
      rootTranslation_coeff_mem_maximalIdeal A c A.natDegree hresidue)).irreducible

end OnLeConjecture.Analytic.Germ
