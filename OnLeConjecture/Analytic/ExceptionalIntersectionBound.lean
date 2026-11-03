/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OneVariablePolynomialRootOrder
import Mathlib.Tactic

/-!
# The exceptional intersection budget in a finite blowup chart

The exceptional restrictions of all strict transforms are translations
of one nonzero polynomial of degree at most the original order. Their
vanishing orders over any finite set therefore sum to at most that order.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

theorem ordinaryInitialChart_translation (P : MvPolynomial (Fin 2) ℂ) (c : ℂ) :
    (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P).comp (X + C c) =
      MvPolynomial.aeval (![X + C c, 1] : Fin 2 → ℂ[X]) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp only [map_add, add_comp, hP, hQ]
  | mul_X P i hP =>
      rw [map_mul, mul_comp, hP, map_mul]
      congr 1
      fin_cases i <;> simp

theorem exists_polynomial_exceptional_restrictions
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hnext : f ∉ maximalIdeal 2 ^ (m + 1)) :
    ∃ P : ℂ[X], P ≠ 0 ∧ P.natDegree ≤ m ∧ ∀ c : ℂ,
      pointBlowupExceptionalLine.pullbackRingHom (pointBlowupTransform c m f hf) =
        oneVariablePolynomialEvaluation (P.comp (X + C c)) := by
  obtain ⟨V, H, P, _hfactor, _hHne, hH, htail, hchart, hPne, hdegree,
    _hrestriction, _hVnext⟩ := exists_pointBlowupTransform_with_initial 0 m f hf hnext
  have hP : P = MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) H := by
    simpa only [map_zero, C_0, add_zero] using hchart
  refine ⟨P, hPne, hdegree, fun c => ?_⟩
  rw [pointBlowupTransform_exceptionalRestriction c m f _ H hf hnext hH htail
    (pointBlowupTransform_factor c m f hf), hP, ordinaryInitialChart_translation]

theorem sum_exceptional_restriction_orders_le
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hnext : f ∉ maximalIdeal 2 ^ (m + 1)) (s : Finset ℂ) :
    ∑ c ∈ s, (vanishingOrder (pointBlowupExceptionalLine.pullbackRingHom
      (pointBlowupTransform c m f hf))).toNat ≤ m := by
  obtain ⟨P, hPne, hdegree, hrestriction⟩ :=
    exists_polynomial_exceptional_restrictions m f hf hnext
  simp_rw [hrestriction]
  exact (sum_vanishingOrder_polynomial_translation_le_degree P hPne s).trans hdegree

end OnLeConjecture.Analytic.Germ
