/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.WeightedAnalyticRescaling
public import OnLeConjecture.DThree.WeightedTwoFormsClassification

/-!
# Rescaling classified weighted initial forms

The analytic Jacobian divisibility first supplies the nonzero differential
equation. The resulting source and target rescaling carries the two initial
forms to the E or H pair while preserving the third initial form and every
strict weighted tail.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- Nondegenerate weighted cubic and quartic initial forms can be carried to
the E or H pair by a right left equivalence. -/
theorem exists_rightLeft_weightedRescaling_to_E_or_H_of_analytic_initialForms
    (g : PointedMapGerm 2 3) (a D : ℕ) (ha : 0 < a) (R : Form ℂ)
    (hR : R.IsWeightedHomogeneous ![a, 1] D)
    (A B c₄ c₃ c₂ c₁ c₀ : ℂ)
    (hAB : A ≠ 0 ∨ B ≠ 0)
    (hquartic : weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀ ≠ 0)
    (htailZero :
      g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
          (weightedCubicPolynomial a A B) ∈
        Germ.weightedOrderIdeal a (3 * a + 1))
    (htailOne :
      g.1.component 1 - Germ.coordinatePolynomialAlgHom 2
          (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) ∈
        Germ.weightedOrderIdeal a (4 * a + 1))
    (htailTwo :
      g.1.component 2 - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.weightedOrderIdeal a (D + 1))
    (hdiv : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 0) (g.1.component 1)) :
    ∃ s : ℂ, ∃ h : PointedMapGerm 2 3,
      s ≠ 0 ∧ g.RightLeftEquivalent h ∧
      (h.HasInjectiveRepresentative ↔ g.HasInjectiveRepresentative) ∧
      (rescaleForm s 1 R).IsWeightedHomogeneous ![a, 1] D ∧
      ((h.1.component 0 - Germ.coordinatePolynomialAlgHom 2
              (weightedCubicPolynomial a 0 3) ∈
            Germ.weightedOrderIdeal a (3 * a + 1) ∧
          h.1.component 1 - Germ.coordinatePolynomialAlgHom 2
              (weightedQuarticPolynomial a 1 0 0 4 0) ∈
            Germ.weightedOrderIdeal a (4 * a + 1) ∧
          h.1.component 2 - Germ.coordinatePolynomialAlgHom 2
              (rescaleForm s 1 R) ∈
            Germ.weightedOrderIdeal a (D + 1)) ∨
       (h.1.component 0 - Germ.coordinatePolynomialAlgHom 2
              (weightedCubicPolynomial a 3 0) ∈
            Germ.weightedOrderIdeal a (3 * a + 1) ∧
          h.1.component 1 - Germ.coordinatePolynomialAlgHom 2
              (weightedQuarticPolynomial a 1 0 4 0 2) ∈
            Germ.weightedOrderIdeal a (4 * a + 1) ∧
          h.1.component 2 - Germ.coordinatePolynomialAlgHom 2
              (rescaleForm s 1 R) ∈
            Germ.weightedOrderIdeal a (D + 1))) := by
  have hJacobian := jacobian_weightedCubic_weightedQuartic_ne_zero
    a ha A B c₄ c₃ c₂ c₁ c₀ hAB hquartic
  obtain ⟨c, hc, hODE⟩ :=
    exists_ode_of_analytic_weighted_initial_forms
      a ha A B c₄ c₃ c₂ c₁ c₀
      (g.1.component 0) (g.1.component 1)
      htailZero htailOne hdiv hJacobian
  exact exists_rightLeft_weightedRescaling_to_E_or_H
    g a D R hR A B c₄ c₃ c₂ c₁ c₀ c hc hODE
      htailZero htailOne htailTwo

end OnLeConjecture.DThree
