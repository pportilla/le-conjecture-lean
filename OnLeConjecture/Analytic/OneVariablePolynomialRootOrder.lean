/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PointBlowupChart
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Analytic orders at polynomial roots

Evaluation at the translated analytic coordinate identifies the actual
vanishing order with polynomial root multiplicity. Their sum over any
finite set is bounded by the polynomial degree.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

theorem value_translated_polynomial_aeval (P : ℂ[X]) (c : ℂ) :
    valueRingHom 1 (aeval (coordinate (0 : Fin 1) + constRingHom 1 c) P) = P.eval c := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, eval_add, hP, hQ]
  | monomial n a =>
      simp [aeval_def, eval₂_monomial, valueRingHom_const,
        show algebraMap ℂ (Germ 1) = constRingHom 1 from rfl]

theorem vanishingOrder_translated_polynomial (P : ℂ[X]) (hP : P ≠ 0) (c : ℂ) :
    vanishingOrder (aeval (coordinate (0 : Fin 1) + constRingHom 1 c) P) =
      (P.rootMultiplicity c : ℕ∞) := by
  let R := P /ₘ (X - C c) ^ P.rootMultiplicity c
  have hfactor : (X - C c) ^ P.rootMultiplicity c * R = P :=
    pow_mul_divByMonic_rootMultiplicity_eq P c
  have hR : R.eval c ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero c hP
  have hunit : IsUnit (aeval (coordinate (0 : Fin 1) + constRingHom 1 c) R) := by
    apply isUnit_of_valueRingHom_ne_zero
    rwa [value_translated_polynomial_aeval]
  conv_lhs => rw [← hfactor]
  rw [map_mul, map_pow, map_sub, aeval_X, aeval_C]
  change vanishingOrder ((coordinate (0 : Fin 1) + constRingHom 1 c - constRingHom 1 c) ^
    P.rootMultiplicity c * _) = _
  rw [add_sub_cancel_right, vanishingOrder_mul, vanishingOrder_coordinate_pow,
    vanishingOrder_eq_zero_iff_isUnit.mpr hunit, add_zero]

theorem vanishingOrder_polynomial_translation (P : ℂ[X]) (hP : P ≠ 0) (c : ℂ) :
    vanishingOrder (oneVariablePolynomialEvaluation (P.comp (X + C c))) =
      (P.rootMultiplicity c : ℕ∞) := by
  have heval : oneVariablePolynomialEvaluation (P.comp (X + C c)) =
      aeval (coordinate (0 : Fin 1) + constRingHom 1 c) P := by
    simp [oneVariablePolynomialEvaluation, aeval_def, eval₂_comp,
      show algebraMap ℂ (Germ 1) = constRingHom 1 from rfl]
  rw [heval]
  exact vanishingOrder_translated_polynomial P hP c

theorem sum_polynomial_rootMultiplicity_le_degree (P : ℂ[X]) (s : Finset ℂ) :
    ∑ c ∈ s, P.rootMultiplicity c ≤ P.natDegree := by
  classical
  simp_rw [← count_roots]
  calc
    ∑ c ∈ s, P.roots.count c ≤ ∑ c ∈ s ∪ P.roots.toFinset, P.roots.count c :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (by intros; omega)
    _ = P.roots.card := Multiset.sum_count_eq_card
      (fun c hc => Finset.mem_union_right _ (Multiset.mem_toFinset.mpr hc))
    _ ≤ P.natDegree := P.card_roots'

theorem sum_vanishingOrder_polynomial_translation_le_degree
    (P : ℂ[X]) (hP : P ≠ 0) (s : Finset ℂ) :
    ∑ c ∈ s, (vanishingOrder
      (oneVariablePolynomialEvaluation (P.comp (X + C c)))).toNat ≤ P.natDegree := by
  simp_rw [vanishingOrder_polynomial_translation P hP, ENat.toNat_natCast]
  exact sum_polynomial_rootMultiplicity_le_degree P s

end OnLeConjecture.Analytic.Germ
