/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.TwoForms
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Nondegeneracy of the cubic and quartic differential expression

A depressed cubic with a nonzero lower coefficient and a nonzero quartic
cannot satisfy the zero differential equation of weights three and four.
-/

public section

namespace OnLeConjecture.DThree

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- A nonzero quartic and a depressed cubic with a nonzero lower coefficient
give a nonzero expression `4 p' q - 3 p q'`. -/
theorem cubic_quartic_differentialExpression_ne_zero
    (A B c₄ c₃ c₂ c₁ c₀ : K)
    (hAB : A ≠ 0 ∨ B ≠ 0)
    (hquartic : quartic c₄ c₃ c₂ c₁ c₀ ≠ 0) :
    4 * (cubic A B).derivative * quartic c₄ c₃ c₂ c₁ c₀ -
        3 * cubic A B * (quartic c₄ c₃ c₂ c₁ c₀).derivative ≠ 0 := by
  intro hzero
  have hExpansion :
      4 * (cubic A B).derivative * quartic c₄ c₃ c₂ c₁ c₀ -
          3 * cubic A B * (quartic c₄ c₃ c₂ c₁ c₀).derivative =
        (3 * C c₃) * X ^ 5 +
        (6 * C c₂ - 8 * C A * C c₄) * X ^ 4 +
        (9 * C c₁ - 5 * C A * C c₃ - 12 * C B * C c₄) * X ^ 3 +
        (12 * C c₀ - 2 * C A * C c₂ - 9 * C B * C c₃) * X ^ 2 +
        (C A * C c₁ - 6 * C B * C c₂) * X ^ 1 +
        (4 * C A * C c₀ - 3 * C B * C c₁) := by
    have hp : (cubic A B).derivative = 3 * X ^ 2 + C A := by
      simp [cubic]
      simp only [C_ofNat]
      ring
    have hq :
        (quartic c₄ c₃ c₂ c₁ c₀).derivative =
          4 * C c₄ * X ^ 3 + 3 * C c₃ * X ^ 2 + 2 * C c₂ * X + C c₁ := by
      simp [quartic]
      simp only [C_ofNat]
      ring
    rw [hp, hq]
    simp only [cubic, quartic]
    ring
  rw [hExpansion] at hzero
  have h₃ : c₃ = 0 := by
    have h := congrArg (fun q : K[X] ↦ q.coeff 5) hzero
    simpa [coeff_mul_X_pow'] using h
  have h₂ : c₂ = 4 * A * c₄ / 3 := by
    have h := congrArg (fun q : K[X] ↦ q.coeff 4) hzero
    simp [h₃, coeff_mul_X_pow'] at h
    linear_combination h / 6
  have h₁ : c₁ = 4 * B * c₄ / 3 := by
    have h := congrArg (fun q : K[X] ↦ q.coeff 3) hzero
    simp [h₃, coeff_mul_X_pow'] at h
    linear_combination h / 9
  have h₀ : c₀ = 2 * A ^ 2 * c₄ / 9 := by
    have h := congrArg (fun q : K[X] ↦ q.coeff 2) hzero
    simp [h₃, h₂, coeff_mul_X_pow'] at h
    linear_combination h / 12
  have hABc₄ : A * B * c₄ = 0 := by
    have h := congrArg (fun q : K[X] ↦ q.coeff 1) hzero
    simp [h₂, h₁, coeff_mul_X_pow'] at h
    linear_combination (-3 / 20 : K) * h
  have hconstant : (8 * A ^ 3 / 9 - 4 * B ^ 2) * c₄ = 0 := by
    have h := congrArg (fun q : K[X] ↦ q.coeff 0) hzero
    simp [h₃, h₁, h₀] at h
    linear_combination h
  have hc₄ : c₄ ≠ 0 := by
    intro hc₄
    apply hquartic
    rw [quartic, h₃, h₂, h₁, h₀, hc₄]
    simp
  have hABzero : A * B = 0 := by
    exact (mul_eq_zero.mp hABc₄).resolve_right hc₄
  rcases mul_eq_zero.mp hABzero with hA | hB
  · have hBzero : B = 0 := by
      simpa [hA, hc₄] using hconstant
    exact hAB.elim (fun hAne ↦ hAne hA) (fun hBne ↦ hBne hBzero)
  · have hAzero : A = 0 := by
      simpa [hB, hc₄] using hconstant
    exact hAB.elim (fun hAne ↦ hAne hAzero) (fun hBne ↦ hBne hB)

end OnLeConjecture.DThree
