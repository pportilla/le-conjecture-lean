/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order

/-!
# Numerical arguments in the case of order three

This file proves the integer inequalities used before the classification of
the two weighted initial forms in the case of order three.
-/

public section

namespace OnLeConjecture.DThree

/-- The estimate obtained from an intersection number at least five is
incompatible with the point basis bounds in the case of order three. -/
theorem intersection_five_estimate_impossible
    (M S b : ℤ)
    (hM : M ≤ 3 * S)
    (hS : 3 ≤ S)
    (hb : 1 ≤ b)
    (hintersection : 5 * (M + S - 3) ≤ 3 * (2 * M - S - b)) :
    False := by
  linarith

/-- The global and polar estimates exclude an intersection number at least
five. -/
theorem intersection_at_least_five_impossible
    (M S b m n : ℤ)
    (hM : M ≤ 3 * S)
    (hS : 3 ≤ S)
    (hb : 1 ≤ b)
    (hm : 1 ≤ m)
    (hglobal : M + S ≤ 3 * m)
    (hn : 5 ≤ n)
    (hpolar : n * (m - 1) ≤ 2 * M - S - b) :
    False := by
  have hnonnegative : 0 ≤ (n - 5) * (m - 1) :=
    mul_nonneg (by omega) (by omega)
  have hfive : 5 * (m - 1) ≤ 2 * M - S - b := by
    nlinarith
  apply intersection_five_estimate_impossible M S b hM hS hb
  linarith

/-- The count of the free point on the branch and the satellite entries
excludes intersection number four. -/
theorem intersection_four_count_impossible
    (A₃ A₂ A₁ sigma : ℤ)
    (hA₃ : 1 ≤ A₃)
    (hcount : 0 ≤ -3 * (A₃ - 1) - 6 * A₂ - 5 * A₁ + 3 * sigma)
    (hfree : 5 + 3 * sigma ≤ 6 * A₂ + 5 * A₁) :
    False := by
  linarith

/-- The Newton inequalities force all numerical equalities used in the
classification of the two initial forms. -/
theorem newton_estimates_force_equalities
    (alpha A₃ k j b S m M : ℤ)
    (halpha : 1 ≤ alpha)
    (hA₃ : A₃ ≤ alpha)
    (hk : 4 ≤ k)
    (hjzero : 0 ≤ j)
    (hjone : j ≤ 1)
    (hdegree : (k - 4 + 2 * j) * alpha ≤ A₃)
    (hb : 1 ≤ b)
    (hbthree : b ≤ 3)
    (hS : S = 3 * alpha * (k - 2) - b + 3)
    (hSm : S ≤ m)
    (hm : m ≤ alpha * (k + 2 - j))
    (hM : M = 3 * k * alpha) :
    j = 0 ∧ k = 4 ∧ b = 3 ∧ S = 6 * alpha ∧
      m = 6 * alpha ∧ M = 12 * alpha := by
  have hj : j = 0 ∨ j = 1 := by omega
  have hj : j = 0 := by
    rcases hj with hj | hj
    · exact hj
    · subst j
      nlinarith
  subst j
  have hkfour : k = 4 := by
    by_contra hne
    have hkfive : 5 ≤ k := by omega
    have hpositive : 0 < alpha * (k - 4) :=
      mul_pos (by omega) (by omega)
    nlinarith
  subst k
  have hbthreeEq : b = 3 := by
    nlinarith
  subst b
  have hSEq : S = 6 * alpha := by
    linarith
  have hmEq : m = 6 * alpha := by
    linarith
  have hMEq : M = 12 * alpha := by
    nlinarith
  exact ⟨rfl, rfl, rfl, hSEq, hmEq, hMEq⟩

end OnLeConjecture.DThree
