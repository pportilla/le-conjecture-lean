/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Numerical.Proximity
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

/-!
# Point basis count identities

This module counts the entries of a finite multiplicity function by their
values. It then specializes the identities to proximity certificates whose
positive entries are at most three or at most two. The geometric existence
of such a certificate and the interpretation of its numerical invariants
remain external hypotheses.
-/

public section

namespace OnLeConjecture.Numerical

open scoped BigOperators

namespace MultiplicityCounts

variable {α : Type*} [Fintype α]

/-- The number of points where a finite multiplicity function has value
`r`. -/
@[expose]
def valueCount (multiplicity : α → ℕ) (r : ℕ) : ℕ :=
  (Finset.univ.filter fun p ↦ multiplicity p = r).card

/-- The sum of a finite multiplicity function. -/
@[expose]
def sum (multiplicity : α → ℕ) : ℕ :=
  ∑ p, multiplicity p

/-- The sum of the squares of a finite multiplicity function. -/
@[expose]
def squareSum (multiplicity : α → ℕ) : ℕ :=
  ∑ p, multiplicity p ^ 2

private theorem sum_indicator_eq_mul_valueCount
    (multiplicity : α → ℕ) (r : ℕ) :
    (∑ p, if multiplicity p = r then r else 0) =
      r * valueCount multiplicity r := by
  rw [← Finset.sum_filter]
  simp [valueCount, Nat.mul_comm]

private theorem sum_squareIndicator_eq_mul_valueCount
    (multiplicity : α → ℕ) (r : ℕ) :
    (∑ p, if multiplicity p = r then r ^ 2 else 0) =
      r ^ 2 * valueCount multiplicity r := by
  rw [← Finset.sum_filter]
  simp [valueCount, Nat.mul_comm]

omit [Fintype α] in
private theorem finset_sum_commute
    {β : Type*} (s : Finset α) (t : Finset β) (f : α → β → ℕ) :
    (∑ a ∈ s, ∑ b ∈ t, f a b) =
      ∑ b ∈ t, ∑ a ∈ s, f a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, ih, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_insert ha]

/-- A positive finite multiplicity function bounded by `d` has total sum
equal to the sum of its values times their occurrence counts. -/
theorem sum_eq_sum_mul_valueCount
    (multiplicity : α → ℕ) (d : ℕ)
    (hpositive : ∀ p, 1 ≤ multiplicity p)
    (hbounded : ∀ p, multiplicity p ≤ d) :
    sum multiplicity =
      ∑ r ∈ Finset.Icc 1 d, r * valueCount multiplicity r := by
  classical
  calc
    sum multiplicity = ∑ p, ∑ r ∈ Finset.Icc 1 d,
        if multiplicity p = r then r else 0 := by
      rw [sum]
      apply Finset.sum_congr rfl
      intro p _hp
      have hmem : multiplicity p ∈ Finset.Icc 1 d :=
        Finset.mem_Icc.mpr ⟨hpositive p, hbounded p⟩
      simp [hmem]
    _ = ∑ r ∈ Finset.Icc 1 d, ∑ p,
        if multiplicity p = r then r else 0 := by
      exact finset_sum_commute Finset.univ (Finset.Icc 1 d)
        fun p r ↦ if multiplicity p = r then r else 0
    _ = ∑ r ∈ Finset.Icc 1 d,
        r * valueCount multiplicity r := by
      apply Finset.sum_congr rfl
      intro r _hr
      exact sum_indicator_eq_mul_valueCount multiplicity r

/-- Under the same hypotheses, the square sum is the sum of the squared
values times their occurrence counts. -/
theorem squareSum_eq_sum_sq_mul_valueCount
    (multiplicity : α → ℕ) (d : ℕ)
    (hpositive : ∀ p, 1 ≤ multiplicity p)
    (hbounded : ∀ p, multiplicity p ≤ d) :
    squareSum multiplicity =
      ∑ r ∈ Finset.Icc 1 d, r ^ 2 * valueCount multiplicity r := by
  classical
  calc
    squareSum multiplicity = ∑ p, ∑ r ∈ Finset.Icc 1 d,
        if multiplicity p = r then r ^ 2 else 0 := by
      rw [squareSum]
      apply Finset.sum_congr rfl
      intro p _hp
      have hmem : multiplicity p ∈ Finset.Icc 1 d :=
        Finset.mem_Icc.mpr ⟨hpositive p, hbounded p⟩
      simp [hmem]
    _ = ∑ r ∈ Finset.Icc 1 d, ∑ p,
        if multiplicity p = r then r ^ 2 else 0 := by
      exact finset_sum_commute Finset.univ (Finset.Icc 1 d)
        fun p r ↦ if multiplicity p = r then r ^ 2 else 0
    _ = ∑ r ∈ Finset.Icc 1 d,
        r ^ 2 * valueCount multiplicity r := by
      apply Finset.sum_congr rfl
      intro r _hr
      exact sum_squareIndicator_eq_mul_valueCount multiplicity r

end MultiplicityCounts

namespace ProximityCertificate

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The number of entries of a proximity certificate equal to `r`. -/
@[expose]
def multiplicityCount (c : ProximityCertificate α) (r : ℕ) : ℕ :=
  MultiplicityCounts.valueCount c.multiplicity r

/-- The sum of the squares of the entries of a proximity certificate. -/
@[expose]
def squareMultiplicity (c : ProximityCertificate α) : ℕ :=
  MultiplicityCounts.squareSum c.multiplicity

/-- If every entry is positive and at most three, the sum of the entries is
`3 A₃ + 2 A₂ + A₁`. -/
theorem totalMultiplicity_eq_three_mul_count_three_add_two_mul_count_two_add_count_one
    (c : ProximityCertificate α)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (hbounded : ∀ p, c.multiplicity p ≤ 3) :
    c.totalMultiplicity =
      3 * c.multiplicityCount 3 +
        2 * c.multiplicityCount 2 + c.multiplicityCount 1 := by
  change MultiplicityCounts.sum c.multiplicity =
    3 * MultiplicityCounts.valueCount c.multiplicity 3 +
      2 * MultiplicityCounts.valueCount c.multiplicity 2 +
        MultiplicityCounts.valueCount c.multiplicity 1
  rw [MultiplicityCounts.sum_eq_sum_mul_valueCount
    c.multiplicity 3 hpositive hbounded]
  norm_num [Finset.sum_Icc_succ_top]
  ring

/-- If every entry is positive and at most three, the sum of their squares
is `9 A₃ + 4 A₂ + A₁`. -/
theorem squareMultiplicity_eq_nine_mul_count_three_add_four_mul_count_two_add_count_one
    (c : ProximityCertificate α)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (hbounded : ∀ p, c.multiplicity p ≤ 3) :
    c.squareMultiplicity =
      9 * c.multiplicityCount 3 +
        4 * c.multiplicityCount 2 + c.multiplicityCount 1 := by
  change MultiplicityCounts.squareSum c.multiplicity =
    9 * MultiplicityCounts.valueCount c.multiplicity 3 +
      4 * MultiplicityCounts.valueCount c.multiplicity 2 +
        MultiplicityCounts.valueCount c.multiplicity 1
  rw [MultiplicityCounts.squareSum_eq_sum_sq_mul_valueCount
    c.multiplicity 3 hpositive hbounded]
  norm_num [Finset.sum_Icc_succ_top]
  ring

/-- Root multiplicity three and a positive branch count give
`b = 3 - σ` and `σ ≤ 2`. -/
theorem branchCount_eq_three_sub_satelliteMultiplicity_and_le_two
    (c : ProximityCertificate α)
    (hroot : c.multiplicity c.root = 3)
    (hbranch : 0 < c.branchCount) :
    c.branchCount = 3 - c.satelliteMultiplicity ∧
      c.satelliteMultiplicity ≤ 2 := by
  have hsum := c.branchCount_add_satelliteMultiplicity
  rw [hroot] at hsum
  omega

/-- If every entry is positive and at most two, the sum of the entries is
`2 A₂ + A₁`. -/
theorem totalMultiplicity_eq_two_mul_count_two_add_count_one
    (c : ProximityCertificate α)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (hbounded : ∀ p, c.multiplicity p ≤ 2) :
    c.totalMultiplicity =
      2 * c.multiplicityCount 2 + c.multiplicityCount 1 := by
  change MultiplicityCounts.sum c.multiplicity =
    2 * MultiplicityCounts.valueCount c.multiplicity 2 +
      MultiplicityCounts.valueCount c.multiplicity 1
  rw [MultiplicityCounts.sum_eq_sum_mul_valueCount
    c.multiplicity 2 hpositive hbounded]
  norm_num [Finset.sum_Icc_succ_top]
  ring

/-- If every entry is positive and at most two, the sum of their squares is
`4 A₂ + A₁`. -/
theorem squareMultiplicity_eq_four_mul_count_two_add_count_one
    (c : ProximityCertificate α)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (hbounded : ∀ p, c.multiplicity p ≤ 2) :
    c.squareMultiplicity =
      4 * c.multiplicityCount 2 + c.multiplicityCount 1 := by
  change MultiplicityCounts.squareSum c.multiplicity =
    4 * MultiplicityCounts.valueCount c.multiplicity 2 +
      MultiplicityCounts.valueCount c.multiplicity 1
  rw [MultiplicityCounts.squareSum_eq_sum_sq_mul_valueCount
    c.multiplicity 2 hpositive hbounded]
  norm_num [Finset.sum_Icc_succ_top]
  ring

/-- Root multiplicity two and a positive branch count give
`b = 2 - σ` and `σ ≤ 1`. -/
theorem branchCount_eq_two_sub_satelliteMultiplicity_and_le_one
    (c : ProximityCertificate α)
    (hroot : c.multiplicity c.root = 2)
    (hbranch : 0 < c.branchCount) :
    c.branchCount = 2 - c.satelliteMultiplicity ∧
      c.satelliteMultiplicity ≤ 1 := by
  have hsum := c.branchCount_add_satelliteMultiplicity
  rw [hroot] at hsum
  omega

end ProximityCertificate

end OnLeConjecture.Numerical
