/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

import Mathlib.Tactic.Order

/-!
# Numerical alternatives in the case of order two

This file formalizes the integer argument that remains after the branch order
estimate in the even case of the quadratic normal form.
-/

public section

namespace OnLeConjecture.DTwo

/-- The valuation estimate on the odd branch forces the unique numerical
possibility used before the Newton polygon contradiction. -/
theorem odd_numerical_reduction
    (k a₁ m M e : ℕ)
    (hk : 3 ≤ k)
    (ha₁ : a₁ ≤ k)
    (hM : M = 2 * k - 2 + a₁)
    (hm : k - 1 + a₁ ≤ m)
    (he : e = (m - 1) / k)
    (hzero : e = 0 → 2 * m ≤ M)
    (hpositive : 1 ≤ e → min (2 * m) ((2 * e + 1) * k) ≤ M) :
    a₁ = 0 ∧ m = k - 1 := by
  have hlargeContradiction (hepos : 1 ≤ e) (hkm : k < m) : False := by
    have hMthree : M < 3 * k := by omega
    have hfactor : 3 ≤ 2 * e + 1 := by omega
    have hthree : 3 * k ≤ (2 * e + 1) * k :=
      Nat.mul_le_mul_right k hfactor
    have hMtwo : M < 2 * m := by omega
    have hMother : M < (2 * e + 1) * k := lt_of_lt_of_le hMthree hthree
    have hMmin : M < min (2 * m) ((2 * e + 1) * k) :=
      lt_min hMtwo hMother
    exact (Nat.not_lt_of_ge (hpositive hepos)) hMmin
  have ha₁zero : a₁ = 0 := by
    by_contra ha₁ne
    have ha₁pos : 1 ≤ a₁ := Nat.one_le_iff_ne_zero.mpr ha₁ne
    have hkm : k ≤ m := by omega
    by_cases heq : m = k
    · have hezero : e = 0 := by
        rw [he, heq]
        exact Nat.div_eq_of_lt (by omega)
      have := hzero hezero
      omega
    · have hkltm : k < m := lt_of_le_of_ne hkm (Ne.symm heq)
      have hepos : 1 ≤ e := by
        rw [he]
        apply (Nat.le_div_iff_mul_le (by omega : 0 < k)).2
        omega
      exact (hlargeContradiction hepos hkltm).elim
  subst a₁
  have hmLower : k - 1 ≤ m := by simpa using hm
  have hmEq : m = k - 1 := by
    by_contra hne
    have hkm : k ≤ m := by omega
    by_cases heq : m = k
    · have hezero : e = 0 := by
        rw [he, heq]
        exact Nat.div_eq_of_lt (by omega)
      have := hzero hezero
      omega
    · have hkltm : k < m := lt_of_le_of_ne hkm (Ne.symm heq)
      have hepos : 1 ≤ e := by
        rw [he]
        apply (Nat.le_div_iff_mul_le (by omega : 0 < k)).2
        omega
      exact (hlargeContradiction hepos hkltm).elim
  exact ⟨rfl, hmEq⟩

/-- The branch order estimate and the polar inequalities leave exactly the
two numerical alternatives used in the case of order two. -/
theorem even_numerical_alternatives
    (a a₁ m : ℕ)
    (ha : 1 ≤ a)
    (ha₁ : a₁ ≤ 2 * a)
    (hm : 2 * a + a₁ ≤ m)
    (hpolar : 2 * (m - 1) ≤ 6 * a + a₁ - 2)
    (hbranch : 2 * a < m →
      2 * min m (3 * a) ≤ 4 * a + a₁) :
    (a₁ = 0 ∧ m = 2 * a) ∨
      (a₁ = 2 * a ∧ m = 4 * a) := by
  by_cases ha₁zero : a₁ = 0
  · left
    refine ⟨ha₁zero, ?_⟩
    subst a₁
    have hmLower : 2 * a ≤ m := by omega
    by_contra hmne
    have hmStrict : 2 * a < m := by omega
    have horder := hbranch hmStrict
    have hmUpper : m ≤ 3 * a := by omega
    rw [min_eq_left hmUpper] at horder
    omega
  · right
    have ha₁pos : 0 < a₁ := Nat.pos_of_ne_zero ha₁zero
    have hmStrict : 2 * a < m := by omega
    have horder := hbranch hmStrict
    by_cases hmThree : m ≤ 3 * a
    · rw [min_eq_left hmThree] at horder
      omega
    · have hThree : 3 * a ≤ m := by omega
      rw [min_eq_right hThree] at horder
      constructor
      · omega
      · omega

end OnLeConjecture.DTwo
