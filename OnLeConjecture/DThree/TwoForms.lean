/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The two cubic and quartic initial forms in the case `d = 3`

This file formalizes the coefficient calculation in Lemma `dthree-twoforms`.
The conclusion is stated before the source and target rescalings.
Over an algebraically closed field, in the first case, rescaling the variable
so that `B = 3` gives
`(z^3 + 3, z^4 + 4z)`.  In the second case, rescaling it so that `A = 3`
gives `(z^3 + 3z, z^4 + 4z^2 + 2)`.
-/

public section

namespace OnLeConjecture.DThree

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- The depressed cubic occurring as the first weighted initial form. -/
@[expose]
noncomputable def cubic (A B : K) : K[X] :=
  X ^ 3 + C A * X + C B

/-- A general polynomial of degree at most four, with its coefficients listed
from degree four to degree zero. -/
@[expose]
noncomputable def quartic
    (c4 c3 c2 c1 c0 : K) : K[X] :=
  C c4 * X ^ 4 + C c3 * X ^ 3 + C c2 * X ^ 2 + C c1 * X + C c0

/-- A nonzero constant value of `4 p' χ - 3 p χ'` forces exactly one of the
linear and constant coefficients of the depressed cubic to vanish, and fixes
all coefficients of `χ`.  These are precisely the two pairs which normalize
to the `E` and `H` forms in Lemma `dthree-twoforms`. -/
theorem classify_two_forms_of_ode
    (A B c4 c3 c2 c1 c0 c : K)
    (hc : c ≠ 0)
    (hODE :
      4 * (cubic A B).derivative * quartic c4 c3 c2 c1 c0 -
          3 * cubic A B * (quartic c4 c3 c2 c1 c0).derivative = C c) :
    c4 ≠ 0 ∧
      ((A = 0 ∧ B ≠ 0 ∧
          quartic c4 c3 c2 c1 c0 =
            C c4 * (X ^ 4 + C (4 * B / 3) * X)) ∨
       (B = 0 ∧ A ≠ 0 ∧
          quartic c4 c3 c2 c1 c0 =
            C c4 * (X ^ 4 + C (4 * A / 3) * X ^ 2 + C (2 * A ^ 2 / 9)))) := by
  have hExpansion :
      4 * (cubic A B).derivative * quartic c4 c3 c2 c1 c0 -
          3 * cubic A B * (quartic c4 c3 c2 c1 c0).derivative =
        (3 * C c3) * X ^ 5 +
        (6 * C c2 - 8 * C A * C c4) * X ^ 4 +
        (9 * C c1 - 5 * C A * C c3 - 12 * C B * C c4) * X ^ 3 +
        (12 * C c0 - 2 * C A * C c2 - 9 * C B * C c3) * X ^ 2 +
        (C A * C c1 - 6 * C B * C c2) * X ^ 1 +
        (4 * C A * C c0 - 3 * C B * C c1) := by
    have hp : (cubic A B).derivative = 3 * X ^ 2 + C A := by
      simp [cubic]
      simp only [C_ofNat]
      ring
    have hq :
        (quartic c4 c3 c2 c1 c0).derivative =
          4 * C c4 * X ^ 3 + 3 * C c3 * X ^ 2 + 2 * C c2 * X + C c1 := by
      simp [quartic]
      simp only [C_ofNat]
      ring
    rw [hp, hq]
    simp only [cubic, quartic]
    ring
  rw [hExpansion] at hODE
  have h3 : c3 = 0 := by
    have h := congrArg (fun q : K[X] => q.coeff 5) hODE
    simpa [coeff_mul_X_pow'] using h
  have h2 : c2 = 4 * A * c4 / 3 := by
    have h := congrArg (fun q : K[X] => q.coeff 4) hODE
    simp [h3, coeff_mul_X_pow'] at h
    linear_combination h / 6
  have h1 : c1 = 4 * B * c4 / 3 := by
    have h := congrArg (fun q : K[X] => q.coeff 3) hODE
    simp [h3, coeff_mul_X_pow'] at h
    linear_combination h / 9
  have h0 : c0 = 2 * A ^ 2 * c4 / 9 := by
    have h := congrArg (fun q : K[X] => q.coeff 2) hODE
    simp [h3, h2, coeff_mul_X_pow'] at h
    linear_combination h / 12
  have hAB : A * B * c4 = 0 := by
    have h := congrArg (fun q : K[X] => q.coeff 1) hODE
    simp [h2, h1, coeff_mul_X_pow'] at h
    linear_combination (-3 / 20 : K) * h
  have hc_formula : c = (8 * A ^ 3 / 9 - 4 * B ^ 2) * c4 := by
    have h := congrArg (fun q : K[X] => q.coeff 0) hODE
    simp [h3, h1, h0] at h
    linear_combination -h
  have hc4 : c4 ≠ 0 := by
    intro hc4
    apply hc
    rw [hc_formula, hc4, mul_zero]
  refine ⟨hc4, ?_⟩
  rcases mul_eq_zero.mp hAB with hAorB | hc4zero
  · rcases mul_eq_zero.mp hAorB with hA | hB
    · left
      have hB0 : B ≠ 0 := by
        intro hB
        apply hc
        rw [hc_formula, hA, hB]
        norm_num
      refine ⟨hA, hB0, ?_⟩
      rw [quartic, h3, h2, h1, h0, hA]
      simp [div_eq_mul_inv, map_mul]
      ring
    · right
      have hA0 : A ≠ 0 := by
        intro hA
        apply hc
        rw [hc_formula, hA, hB]
        norm_num
      refine ⟨hB, hA0, ?_⟩
      rw [quartic, h3, h2, h1, h0, hB]
      simp [div_eq_mul_inv, map_mul]
      ring
  · exact (hc4 hc4zero).elim

end OnLeConjecture.DThree
