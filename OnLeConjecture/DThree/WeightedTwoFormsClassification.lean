/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.TwoFormsNondegeneracy
public import OnLeConjecture.DThree.WeightedTwoFormsODE

/-!
# Classification from analytic weighted initial forms

The nonzero lower coefficient of the cubic and the nonzero quartic imply
that their polynomial Jacobian is nonzero. Thus divisibility of the analytic
Jacobian supplies the differential equation used in the classification.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

/-- The weighted cubic and quartic have a nonzero polynomial Jacobian when
the cubic has a nonzero lower coefficient and the quartic is nonzero. -/
theorem jacobian_weightedCubic_weightedQuartic_ne_zero
    (a : ℕ) (ha : 0 < a) (A B c₄ c₃ c₂ c₁ c₀ : ℂ)
    (hAB : A ≠ 0 ∨ B ≠ 0)
    (hquartic : weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀ ≠ 0) :
    OnLeConjecture.Polynomial.jacobian
        (weightedCubicPolynomial a A B)
        (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) ≠ 0 := by
  have haComplex : (a : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ha)
  have hdifferential :
      4 * (cubic A B).derivative * quartic c₄ c₃ c₂ c₁ c₀ -
          3 * cubic A B * (quartic c₄ c₃ c₂ c₁ c₀).derivative ≠ 0 :=
    cubic_quartic_differentialExpression_ne_zero
      A B c₄ c₃ c₂ c₁ c₀ hAB (by
        intro hzero
        have hc₄ : c₄ = 0 := by
          have hcoeff := congrArg (fun q : ℂ[X] ↦ q.coeff 4) hzero
          simpa [quartic] using hcoeff
        have hc₃ : c₃ = 0 := by
          have hcoeff := congrArg (fun q : ℂ[X] ↦ q.coeff 3) hzero
          simpa [quartic] using hcoeff
        have hc₂ : c₂ = 0 := by
          have hcoeff := congrArg (fun q : ℂ[X] ↦ q.coeff 2) hzero
          simpa [quartic] using hcoeff
        have hc₁ : c₁ = 0 := by
          have hcoeff := congrArg (fun q : ℂ[X] ↦ q.coeff 1) hzero
          simpa [quartic] using hcoeff
        have hc₀ : c₀ = 0 := by
          have hcoeff := congrArg (fun q : ℂ[X] ↦ q.coeff 0) hzero
          simpa [quartic] using hcoeff
        apply hquartic
        simp [weightedQuarticPolynomial, hc₄, hc₃, hc₂, hc₁, hc₀])
  intro hzero
  have hevaluated := congrArg weightedDehomogenize hzero
  rw [weightedDehomogenize_jacobian_weightedCubic_weightedQuartic,
    map_zero] at hevaluated
  exact (mul_ne_zero (C_ne_zero.mpr haComplex) hdifferential) hevaluated

/-- Strict weighted tails, analytic Jacobian divisibility, and the two
nondegeneracy hypotheses imply the two coefficient alternatives. -/
theorem classify_two_forms_of_analytic_weighted_initial_forms_of_nondegenerate
    (a : ℕ) (ha : 0 < a) (A B c₄ c₃ c₂ c₁ c₀ : ℂ)
    (f g : Germ 2)
    (hAB : A ≠ 0 ∨ B ≠ 0)
    (hquartic : weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀ ≠ 0)
    (hf : f - Germ.coordinatePolynomialAlgHom 2
        (weightedCubicPolynomial a A B) ∈
      Germ.weightedOrderIdeal a (3 * a + 1))
    (hg : g - Germ.coordinatePolynomialAlgHom 2
        (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) ∈
      Germ.weightedOrderIdeal a (4 * a + 1))
    (hdiv : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian f g) :
    c₄ ≠ 0 ∧
      ((A = 0 ∧ B ≠ 0 ∧
          quartic c₄ c₃ c₂ c₁ c₀ =
            C c₄ * (X ^ 4 + C (4 * B / 3) * X)) ∨
       (B = 0 ∧ A ≠ 0 ∧
          quartic c₄ c₃ c₂ c₁ c₀ =
            C c₄ * (X ^ 4 + C (4 * A / 3) * X ^ 2 +
              C (2 * A ^ 2 / 9)))) := by
  apply classify_two_forms_of_analytic_weighted_initial_forms
    a ha A B c₄ c₃ c₂ c₁ c₀ f g hf hg hdiv
  exact jacobian_weightedCubic_weightedQuartic_ne_zero
    a ha A B c₄ c₃ c₂ c₁ c₀ hAB hquartic

/-- Prepared first and second components, together with divisibility of their
analytic Jacobian, produce the two coefficient alternatives after making the
cubic initial form monic. -/
theorem PointedMapGerm.exists_classifiedWeightedCubicAndQuartic_of_preparedComponents
    (g : PointedMapGerm 2 3) (a : ℕ) (ha : 0 < a)
    (a₁ a₀ : Germ 1) (u : Germ 2)
    (hfirst : g.1.component 0 =
      (Germ.coordinate (0 : Fin 2) ^ 3 +
          Germ.planeCoefficientExtension a₁ *
            Germ.coordinate (0 : Fin 2) +
          Germ.planeCoefficientExtension a₀) * u)
    (hu : IsUnit u)
    (ha₁ : a₁ ∈ Germ.maximalIdeal 1 ^ (2 * a))
    (ha₀ : a₀ ∈ Germ.maximalIdeal 1 ^ (3 * a))
    (hcubicExact :
      a₁ ∉ Germ.maximalIdeal 1 ^ (2 * a + 1) ∨
        a₀ ∉ Germ.maximalIdeal 1 ^ (3 * a + 1))
    (hquartic : g.1.component 1 ∈ Germ.weightedOrderIdeal a (4 * a))
    (hquarticExact : g.1.component 1 ∉
      Germ.weightedOrderIdeal a (4 * a + 1))
    (hdiv : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian (g.1.component 0) (g.1.component 1)) :
    ∃ A B c₄ c₃ c₂ c₁ c₀ : ℂ,
      (A ≠ 0 ∨ B ≠ 0) ∧
      weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀ ≠ 0 ∧
      c₄ ≠ 0 ∧
      ((A = 0 ∧ B ≠ 0 ∧
          quartic c₄ c₃ c₂ c₁ c₀ =
            C c₄ * (X ^ 4 + C (4 * B / 3) * X)) ∨
       (B = 0 ∧ A ≠ 0 ∧
          quartic c₄ c₃ c₂ c₁ c₀ =
            C c₄ * (X ^ 4 + C (4 * A / 3) * X ^ 2 +
              C (2 * A ^ 2 / 9)))) := by
  obtain ⟨A, B, c₄, c₃, c₂, c₁, c₀, hAB, hU, hquarticPolynomial,
      hcubicTail, hquarticTail⟩ :=
    PointedMapGerm.exists_weightedCubicAndQuarticInitialForms_of_preparedComponents
      g a ha a₁ a₀ u hfirst hu ha₁ ha₀ hcubicExact
        hquartic hquarticExact
  let scaledFirst : Germ 2 :=
    Germ.constRingHom 2 (Germ.valueRingHom 2 u)⁻¹ * g.1.component 0
  have hconstantProduct :
      Germ.constRingHom 2 (Germ.valueRingHom 2 u)⁻¹ *
          Germ.constRingHom 2 (Germ.valueRingHom 2 u) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hU, map_one]
  have hcubicEvaluation :
      Germ.coordinatePolynomialAlgHom 2
          (MvPolynomial.C (Germ.valueRingHom 2 u) *
            weightedCubicPolynomial a A B) =
        Germ.constRingHom 2 (Germ.valueRingHom 2 u) *
          Germ.coordinatePolynomialAlgHom 2
            (weightedCubicPolynomial a A B) := by
    rw [map_mul, Germ.coordinatePolynomialAlgHom_C]
  have hscaledTail :
      scaledFirst - Germ.coordinatePolynomialAlgHom 2
          (weightedCubicPolynomial a A B) ∈
        Germ.weightedOrderIdeal a (3 * a + 1) := by
    have hequality :
        scaledFirst - Germ.coordinatePolynomialAlgHom 2
            (weightedCubicPolynomial a A B) =
          Germ.constRingHom 2 (Germ.valueRingHom 2 u)⁻¹ *
            (g.1.component 0 - Germ.coordinatePolynomialAlgHom 2
              (MvPolynomial.C (Germ.valueRingHom 2 u) *
                weightedCubicPolynomial a A B)) := by
      change
        Germ.constRingHom 2 (Germ.valueRingHom 2 u)⁻¹ *
              g.1.component 0 -
            Germ.coordinatePolynomialAlgHom 2
              (weightedCubicPolynomial a A B) = _
      rw [hcubicEvaluation]
      calc
        Germ.constRingHom 2 (Germ.valueRingHom 2 u)⁻¹ *
              g.1.component 0 -
            Germ.coordinatePolynomialAlgHom 2
              (weightedCubicPolynomial a A B) =
          Germ.constRingHom 2 (Germ.valueRingHom 2 u)⁻¹ *
                g.1.component 0 -
              (Germ.constRingHom 2 (Germ.valueRingHom 2 u)⁻¹ *
                Germ.constRingHom 2 (Germ.valueRingHom 2 u)) *
                  Germ.coordinatePolynomialAlgHom 2
                    (weightedCubicPolynomial a A B) := by
            rw [hconstantProduct, one_mul]
        _ = _ := by ring
    rw [hequality]
    exact Ideal.mul_mem_left _ _ hcubicTail
  have hscaledJacobian :
      Germ.jacobian scaledFirst (g.1.component 1) =
        Germ.constRingHom 2 (Germ.valueRingHom 2 u)⁻¹ *
          Germ.jacobian (g.1.component 0) (g.1.component 1) := by
    change
      Germ.jacobian
          (Germ.constRingHom 2 (Germ.valueRingHom 2 u)⁻¹ *
            g.1.component 0) (g.1.component 1) = _
    rw [Germ.jacobian_mul_left, Germ.jacobian_const_left,
      mul_zero, add_zero]
  have hscaledDivisibility :
      Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
        Germ.jacobian scaledFirst (g.1.component 1) := by
    obtain ⟨q, hq⟩ := hdiv
    refine ⟨Germ.constRingHom 2 (Germ.valueRingHom 2 u)⁻¹ * q, ?_⟩
    rw [hscaledJacobian, hq]
    ring
  have hclassification :=
    classify_two_forms_of_analytic_weighted_initial_forms_of_nondegenerate
      a ha A B c₄ c₃ c₂ c₁ c₀ scaledFirst (g.1.component 1)
      hAB hquarticPolynomial hscaledTail hquarticTail hscaledDivisibility
  exact ⟨A, B, c₄, c₃, c₂, c₁, c₀, hAB, hquarticPolynomial,
    hclassification⟩

end OnLeConjecture.DThree
