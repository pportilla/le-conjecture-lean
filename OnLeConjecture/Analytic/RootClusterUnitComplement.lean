/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CompleteRootClusterIntersection
public import OnLeConjecture.Analytic.UnitIntersection
public import OnLeConjecture.Analytic.OrderTwoPreparation

/-!
# The full chart polynomial and its local root factor

At a residue root, all other analytic root factors are units. Therefore
the local intersection of the full translated polynomial equals the
intersection of its root cluster factor. This identifies the resultant
sum with intersections of the full chart polynomials.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial
open scoped BigOperators

theorem value_firstCoordinatePolynomialEvaluation (P : Polynomial (Germ 1)) :
    valueRingHom 2 (firstCoordinatePolynomialEvaluation P) =
      (P.map (valueRingHom 1)).eval 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simpa only [firstCoordinatePolynomialEvaluation, eval₂_add, map_add,
        Polynomial.map_add, eval_add] using
        congrArg₂ (· + ·) hP hQ
  | monomial n a =>
      simp only [firstCoordinatePolynomialEvaluation, eval₂_monomial, map_mul, map_pow,
        valueRingHom_hyperplaneExtension, valueRingHom_coordinate, map_monomial, eval_monomial]

theorem value_firstCoordinatePolynomialEvaluation_rootTranslation
    (P : Polynomial (Germ 1)) (c : ℂ) :
    valueRingHom 2 (firstCoordinatePolynomialEvaluation (rootTranslation P c)) =
      (P.map (valueRingHom 1)).eval c := by
  rw [value_firstCoordinatePolynomialEvaluation, rootTranslation_residue, taylor_eval, zero_add]

/-- A polynomial whose residue does not vanish at a center becomes an
analytic unit in that translated chart. -/
theorem isUnit_firstCoordinatePolynomialEvaluation_rootTranslation
    (P : Polynomial (Germ 1)) (c : ℂ)
    (hvalue : (P.map (valueRingHom 1)).eval c ≠ 0) :
    IsUnit (firstCoordinatePolynomialEvaluation (rootTranslation P c)) := by
  apply isUnit_iff_valueRingHom_ne_zero.mpr
  rwa [value_firstCoordinatePolynomialEvaluation_rootTranslation]

/-- In a factorization by distinct residue roots, the complement of the
factor at `c` is a unit at `c`. -/
theorem isUnit_root_cluster_complement
    (s : Finset ℂ) (μ : ℂ → ℕ) (F : ℂ → Polynomial (Germ 1)) (c : ℂ)
    (hresidue : ∀ z ∈ s, (F z).map (valueRingHom 1) = (X - C z) ^ μ z) :
    IsUnit (firstCoordinatePolynomialEvaluation
      (rootTranslation (∏ z ∈ s.erase c, F z) c)) := by
  apply isUnit_firstCoordinatePolynomialEvaluation_rootTranslation
  rw [Polynomial.map_prod, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro z hz
  rw [hresidue z (Finset.mem_of_mem_erase hz)]
  simp only [eval_pow, eval_sub, eval_X, eval_C]
  exact pow_ne_zero _ (sub_ne_zero.mpr (Finset.ne_of_mem_erase hz).symm)

/-- Replacing the full translated first polynomial by its root cluster
does not change the local intersection ideal. -/
theorem pairIdeal_root_cluster_eq
    (s : Finset ℂ) (μ : ℂ → ℕ) (P : Polynomial (Germ 1))
    (F : ℂ → Polynomial (Germ 1)) (hfactor : P = ∏ z ∈ s, F z)
    (hresidue : ∀ z ∈ s, (F z).map (valueRingHom 1) = (X - C z) ^ μ z)
    (c : ℂ) (hc : c ∈ s) (g : Germ 2) :
    PlaneCurve.pairIdeal (firstCoordinatePolynomialEvaluation (rootTranslation P c)) g =
      PlaneCurve.pairIdeal (firstCoordinatePolynomialEvaluation (rootTranslation (F c) c)) g := by
  have hunit := isUnit_root_cluster_complement s μ F c hresidue
  have hP : P = (∏ z ∈ s.erase c, F z) * F c := by
    rw [hfactor, Finset.prod_erase_mul _ _ hc]
  rw [hP]
  simp only [rootTranslation, taylor_mul, firstCoordinatePolynomialEvaluation, eval₂_mul]
  exact PlaneCurve.pairIdeal_unit_mul_left _ _ g hunit

/-- The resultant order is the sum of local intersections of the full
translated polynomials over every residue root. No cluster factor is
present in the conclusion. -/
theorem exists_resultant_order_eq_sum_translated_intersections
    (P Q : Polynomial (Germ 1)) (hP : P.Monic) (hresultant : P.resultant Q ≠ 0) :
    ∃ hfinite : ∀ c : (P.map (valueRingHom 1)).roots.toFinset,
      PlaneCurve.HasFiniteIntersection
        (firstCoordinatePolynomialEvaluation (rootTranslation P c))
        (firstCoordinatePolynomialEvaluation (rootTranslation Q c)),
      (vanishingOrder (P.resultant Q)).toNat =
        ∑ c : (P.map (valueRingHom 1)).roots.toFinset,
          PlaneCurve.intersectionMultiplicity
            (firstCoordinatePolynomialEvaluation (rootTranslation P c))
            (firstCoordinatePolynomialEvaluation (rootTranslation Q c)) (hfinite c) := by
  classical
  obtain ⟨F, hF, hfactor, hf, hinter⟩ :=
    exists_resultant_order_eq_sum_residue_root_intersections P Q hP hresultant
  have hideal (c : (P.map (valueRingHom 1)).roots.toFinset) :
      PlaneCurve.pairIdeal (firstCoordinatePolynomialEvaluation (rootTranslation P c))
          (firstCoordinatePolynomialEvaluation (rootTranslation Q c)) =
        PlaneCurve.pairIdeal (firstCoordinatePolynomialEvaluation (rootTranslation (F c) c))
          (firstCoordinatePolynomialEvaluation (rootTranslation Q c)) :=
    pairIdeal_root_cluster_eq _ _ P F hfactor (fun z hz ↦ (hF z hz).2.2) c c.property _
  have hf' (c : (P.map (valueRingHom 1)).roots.toFinset) :
      PlaneCurve.HasFiniteIntersection
        (firstCoordinatePolynomialEvaluation (rootTranslation P c))
        (firstCoordinatePolynomialEvaluation (rootTranslation Q c)) := by
    unfold PlaneCurve.HasFiniteIntersection
    rw [hideal c]
    exact hf c
  refine ⟨hf', hinter.trans ?_⟩
  apply Finset.sum_congr rfl
  intro c _
  change Module.finrank ℂ _ = Module.finrank ℂ _
  rw [hideal c]

end OnLeConjecture.Analytic.Germ
