/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedPolynomialInitialForm
public import OnLeConjecture.DThree.TwoForms
public import OnLeConjecture.DThree.WeightedQuarticInitialForm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The weighted Jacobian equation for the cubic and quartic forms

Evaluation at the second variable equal to one converts the weighted
bivariate Jacobian equation into the polynomial differential equation used
to classify the two possible cubic and quartic forms.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

/-- Evaluate a bivariate polynomial at `(X,1)`. -/
@[expose]
noncomputable def weightedDehomogenize :
    MvPolynomial (Fin 2) ℂ →ₐ[ℂ] ℂ[X] :=
  MvPolynomial.aeval fun i => if i = 0 then X else 1

@[simp]
theorem weightedDehomogenize_X_zero :
    weightedDehomogenize (MvPolynomial.X (0 : Fin 2)) = X := by
  simp [weightedDehomogenize]

@[simp]
theorem weightedDehomogenize_X_one :
    weightedDehomogenize (MvPolynomial.X (1 : Fin 2)) = 1 := by
  simp [weightedDehomogenize]

/-- Evaluation at the second variable equal to one recovers the depressed
cubic. -/
theorem weightedDehomogenize_weightedCubicPolynomial
    (a : ℕ) (A B : ℂ) :
    weightedDehomogenize (weightedCubicPolynomial a A B) = cubic A B := by
  simp [weightedCubicPolynomial, cubic]

/-- Evaluation at the second variable equal to one recovers the quartic. -/
theorem weightedDehomogenize_weightedQuarticPolynomial
    (a : ℕ) (c₄ c₃ c₂ c₁ c₀ : ℂ) :
    weightedDehomogenize
        (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) =
      quartic c₄ c₃ c₂ c₁ c₀ := by
  simp [weightedQuarticPolynomial, quartic]

/-- The weighted bivariate Jacobian, evaluated at the second variable equal
to one, is `a` times the differential expression in the two forms. -/
theorem weightedDehomogenize_jacobian_weightedCubic_weightedQuartic
    (a : ℕ) (A B c₄ c₃ c₂ c₁ c₀ : ℂ) :
    weightedDehomogenize
        (OnLeConjecture.Polynomial.jacobian
          (weightedCubicPolynomial a A B)
          (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀)) =
      C (a : ℂ) *
        (4 * (cubic A B).derivative * quartic c₄ c₃ c₂ c₁ c₀ -
          3 * cubic A B * (quartic c₄ c₃ c₂ c₁ c₀).derivative) := by
  simp [OnLeConjecture.Polynomial.jacobian, weightedDehomogenize,
    weightedCubicPolynomial, weightedQuarticPolynomial, cubic, quartic]
  simp only [C_ofNat]
  ring

/-- A nonzero pure power value of the weighted Jacobian yields the nonzero
constant differential equation for the dehomogenized forms. -/
theorem exists_ode_of_weighted_jacobian_eq
    (a : ℕ) (ha : 0 < a) (A B c₄ c₃ c₂ c₁ c₀ c : ℂ)
    (hc : c ≠ 0)
    (hJacobian :
      OnLeConjecture.Polynomial.jacobian
          (weightedCubicPolynomial a A B)
          (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) =
        MvPolynomial.C c * MvPolynomial.X (1 : Fin 2) ^ (6 * a - 1)) :
    ∃ c' : ℂ, c' ≠ 0 ∧
      4 * (cubic A B).derivative * quartic c₄ c₃ c₂ c₁ c₀ -
          3 * cubic A B * (quartic c₄ c₃ c₂ c₁ c₀).derivative = C c' := by
  let E :=
    4 * (cubic A B).derivative * quartic c₄ c₃ c₂ c₁ c₀ -
      3 * cubic A B * (quartic c₄ c₃ c₂ c₁ c₀).derivative
  have haComplex : (a : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ha)
  have hEval := congrArg weightedDehomogenize hJacobian
  rw [weightedDehomogenize_jacobian_weightedCubic_weightedQuartic] at hEval
  rw [map_mul, map_pow, weightedDehomogenize_X_one, one_pow, mul_one,
    MvPolynomial.C_eq_algebraMap, weightedDehomogenize.commutes,
    Polynomial.algebraMap_apply, Algebra.algebraMap_self_apply] at hEval
  refine ⟨c / (a : ℂ), div_ne_zero hc haComplex, ?_⟩
  change E = C (c / (a : ℂ))
  apply mul_left_cancel₀ (C_ne_zero.mpr haComplex)
  calc
    C (a : ℂ) * E = C c := hEval
    _ = C (a : ℂ) * C (c / (a : ℂ)) := by
      rw [← map_mul]
      congr 1
      field_simp

/-- The pure power weighted Jacobian equation implies the two coefficient
alternatives for the cubic and quartic. -/
theorem classify_two_forms_of_weighted_jacobian
    (a : ℕ) (ha : 0 < a) (A B c₄ c₃ c₂ c₁ c₀ c : ℂ)
    (hc : c ≠ 0)
    (hJacobian :
      OnLeConjecture.Polynomial.jacobian
          (weightedCubicPolynomial a A B)
          (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) =
        MvPolynomial.C c * MvPolynomial.X (1 : Fin 2) ^ (6 * a - 1)) :
    c₄ ≠ 0 ∧
      ((A = 0 ∧ B ≠ 0 ∧
          quartic c₄ c₃ c₂ c₁ c₀ =
            C c₄ * (X ^ 4 + C (4 * B / 3) * X)) ∨
       (B = 0 ∧ A ≠ 0 ∧
          quartic c₄ c₃ c₂ c₁ c₀ =
            C c₄ * (X ^ 4 + C (4 * A / 3) * X ^ 2 +
              C (2 * A ^ 2 / 9)))) := by
  obtain ⟨c', hc', hODE⟩ :=
    exists_ode_of_weighted_jacobian_eq
      a ha A B c₄ c₃ c₂ c₁ c₀ c hc hJacobian
  exact classify_two_forms_of_ode A B c₄ c₃ c₂ c₁ c₀ c' hc' hODE

/-- Strict weighted tails and analytic Jacobian divisibility yield the
nonzero constant differential equation for the two polynomial initial
forms. -/
theorem exists_ode_of_analytic_weighted_initial_forms
    (a : ℕ) (ha : 0 < a) (A B c₄ c₃ c₂ c₁ c₀ : ℂ)
    (f g : Germ 2)
    (hf : f - Germ.coordinatePolynomialAlgHom 2
        (weightedCubicPolynomial a A B) ∈
      Germ.weightedOrderIdeal a (3 * a + 1))
    (hg : g - Germ.coordinatePolynomialAlgHom 2
        (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) ∈
      Germ.weightedOrderIdeal a (4 * a + 1))
    (hdiv : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian f g)
    (hJacobian :
      OnLeConjecture.Polynomial.jacobian
          (weightedCubicPolynomial a A B)
          (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧
      4 * (cubic A B).derivative * quartic c₄ c₃ c₂ c₁ c₀ -
          3 * cubic A B * (quartic c₄ c₃ c₂ c₁ c₀).derivative = C c := by
  have haThree : a ≤ 3 * a := by omega
  have haFour : a ≤ 4 * a := by omega
  obtain ⟨c, hc, hJacobianFormula⟩ :=
    Germ.exists_jacobian_eq_ne_zero_C_mul_second_pow_of_analytic_divisibility
      a (3 * a) (4 * a) ha haThree haFour
      (weightedCubicPolynomial a A B)
      (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀)
      (weightedCubicPolynomial_isWeightedHomogeneous a A B)
      (weightedQuarticPolynomial_isWeightedHomogeneous
        a c₄ c₃ c₂ c₁ c₀)
      f g hf hg (by
        simpa only [show 3 * a + 4 * a - a - 1 = 6 * a - 1 by omega] using
          hdiv)
      hJacobian
  apply exists_ode_of_weighted_jacobian_eq
    a ha A B c₄ c₃ c₂ c₁ c₀ c hc
  simpa only [show 3 * a + 4 * a - a - 1 = 6 * a - 1 by omega] using
    hJacobianFormula

/-- Strict weighted tails and analytic Jacobian divisibility imply the two
coefficient alternatives for the polynomial initial forms. -/
theorem classify_two_forms_of_analytic_weighted_initial_forms
    (a : ℕ) (ha : 0 < a) (A B c₄ c₃ c₂ c₁ c₀ : ℂ)
    (f g : Germ 2)
    (hf : f - Germ.coordinatePolynomialAlgHom 2
        (weightedCubicPolynomial a A B) ∈
      Germ.weightedOrderIdeal a (3 * a + 1))
    (hg : g - Germ.coordinatePolynomialAlgHom 2
        (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) ∈
      Germ.weightedOrderIdeal a (4 * a + 1))
    (hdiv : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian f g)
    (hJacobian :
      OnLeConjecture.Polynomial.jacobian
          (weightedCubicPolynomial a A B)
          (weightedQuarticPolynomial a c₄ c₃ c₂ c₁ c₀) ≠ 0) :
    c₄ ≠ 0 ∧
      ((A = 0 ∧ B ≠ 0 ∧
          quartic c₄ c₃ c₂ c₁ c₀ =
            C c₄ * (X ^ 4 + C (4 * B / 3) * X)) ∨
       (B = 0 ∧ A ≠ 0 ∧
          quartic c₄ c₃ c₂ c₁ c₀ =
            C c₄ * (X ^ 4 + C (4 * A / 3) * X ^ 2 +
              C (2 * A ^ 2 / 9)))) := by
  obtain ⟨c, hc, hODE⟩ :=
    exists_ode_of_analytic_weighted_initial_forms
      a ha A B c₄ c₃ c₂ c₁ c₀ f g hf hg hdiv hJacobian
  exact classify_two_forms_of_ode A B c₄ c₃ c₂ c₁ c₀ c hc hODE

end OnLeConjecture.DThree
