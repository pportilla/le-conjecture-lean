/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Numerical.PointBasis
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fin.Basic
public import Mathlib.Tactic.Order

/-!
# Point basis counts in orders two and three

This file derives the formulas for `M`, `S`, and the genus sum when every
positive point basis entry is at most two or at most three.
-/

public section

namespace OnLeConjecture.Numerical

open scoped BigOperators

namespace PointBasisCertificate

/-- The number of point basis entries equal to `r`. -/
@[expose]
noncomputable def multiplicityCount {N : ℕ}
    (c : PointBasisCertificate N) (r : ℕ) : ℕ :=
  (Finset.univ.filter fun p ↦ c.multiplicity p = r).card

/-- The sum of `r_p(r_p-1)` over the point basis. -/
noncomputable def genusNumerator {N : ℕ}
    (c : PointBasisCertificate N) : ℕ :=
  ∑ p, c.multiplicity p * (c.multiplicity p - 1)

private theorem value_eq_one_or_two {N : ℕ}
    (c : PointBasisCertificate N) (hd : c.d = 2)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p) (p : Fin N) :
    c.multiplicity p = 1 ∨ c.multiplicity p = 2 := by
  have hle : c.multiplicity p ≤ 2 := by
    simpa only [hd] using c.multiplicity_le_root p
  have hpos := hpositive p
  omega

private theorem value_eq_one_or_two_or_three {N : ℕ}
    (c : PointBasisCertificate N) (hd : c.d = 3)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p) (p : Fin N) :
    c.multiplicity p = 1 ∨ c.multiplicity p = 2 ∨
      c.multiplicity p = 3 := by
  have hle : c.multiplicity p ≤ 3 := by
    simpa only [hd] using c.multiplicity_le_root p
  have hpos := hpositive p
  omega

private theorem sum_if_eq_two {N : ℕ}
    (c : PointBasisCertificate N) :
    ∑ p, (if c.multiplicity p = 2 then 2 else 0) =
      2 * c.multiplicityCount 2 := by
  rw [← Finset.sum_filter]
  simp [multiplicityCount, Nat.mul_comm]

private theorem sum_if_eq_three {N : ℕ}
    (c : PointBasisCertificate N) :
    ∑ p, (if c.multiplicity p = 3 then 3 else 0) =
      3 * c.multiplicityCount 3 := by
  rw [← Finset.sum_filter]
  simp [multiplicityCount, Nat.mul_comm]

private theorem sum_if_eq_one {N : ℕ}
    (c : PointBasisCertificate N) :
    ∑ p, (if c.multiplicity p = 1 then 1 else 0) =
      c.multiplicityCount 1 := by
  rw [← Finset.sum_filter]
  simp [multiplicityCount]

private theorem sum_if_square_eq_two {N : ℕ}
    (c : PointBasisCertificate N) :
    ∑ p, (if c.multiplicity p = 2 then 4 else 0) =
      4 * c.multiplicityCount 2 := by
  rw [← Finset.sum_filter]
  simp [multiplicityCount, Nat.mul_comm]

private theorem sum_if_square_eq_three {N : ℕ}
    (c : PointBasisCertificate N) :
    ∑ p, (if c.multiplicity p = 3 then 9 else 0) =
      9 * c.multiplicityCount 3 := by
  rw [← Finset.sum_filter]
  simp [multiplicityCount, Nat.mul_comm]

private theorem sum_if_genus_eq_two {N : ℕ}
    (c : PointBasisCertificate N) :
    ∑ p, (if c.multiplicity p = 2 then 2 else 0) =
      2 * c.multiplicityCount 2 :=
  sum_if_eq_two c

private theorem sum_if_genus_eq_three {N : ℕ}
    (c : PointBasisCertificate N) :
    ∑ p, (if c.multiplicity p = 3 then 6 else 0) =
      6 * c.multiplicityCount 3 := by
  rw [← Finset.sum_filter]
  simp [multiplicityCount, Nat.mul_comm]

/-- If every entry is positive and the root entry is two, then the sum of
the entries is `2a₂+a₁`. -/
theorem S_eq_two_mul_count_two_add_count_one {N : ℕ}
    (c : PointBasisCertificate N) (hd : c.d = 2)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p) :
    c.S = 2 * c.multiplicityCount 2 + c.multiplicityCount 1 := by
  calc
    c.S = ∑ p, c.multiplicity p := rfl
    _ = ∑ p, ((if c.multiplicity p = 2 then 2 else 0) +
        (if c.multiplicity p = 1 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro p _hp
      rcases value_eq_one_or_two c hd hpositive p with h | h
      · simp [h]
      · simp [h]
    _ = 2 * c.multiplicityCount 2 + c.multiplicityCount 1 := by
      rw [Finset.sum_add_distrib, sum_if_eq_two, sum_if_eq_one]

/-- If every entry is positive and the root entry is two, then the sum of
the squared entries is `4a₂+a₁`. -/
theorem M_eq_four_mul_count_two_add_count_one {N : ℕ}
    (c : PointBasisCertificate N) (hd : c.d = 2)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p) :
    c.M = 4 * c.multiplicityCount 2 + c.multiplicityCount 1 := by
  calc
    c.M = ∑ p, c.multiplicity p ^ 2 := rfl
    _ = ∑ p, ((if c.multiplicity p = 2 then 4 else 0) +
        (if c.multiplicity p = 1 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro p _hp
      rcases value_eq_one_or_two c hd hpositive p with h | h
      · simp [h]
      · simp [h]
    _ = 4 * c.multiplicityCount 2 + c.multiplicityCount 1 := by
      rw [Finset.sum_add_distrib, sum_if_square_eq_two, sum_if_eq_one]

/-- In order two, the genus numerator is twice the number of entries equal
to two. -/
theorem genusNumerator_eq_two_mul_count_two {N : ℕ}
    (c : PointBasisCertificate N) (hd : c.d = 2)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p) :
    c.genusNumerator = 2 * c.multiplicityCount 2 := by
  calc
    c.genusNumerator = ∑ p,
        c.multiplicity p * (c.multiplicity p - 1) := rfl
    _ = ∑ p, (if c.multiplicity p = 2 then 2 else 0) := by
      apply Finset.sum_congr rfl
      intro p _hp
      rcases value_eq_one_or_two c hd hpositive p with h | h
      · simp [h]
      · simp [h]
    _ = 2 * c.multiplicityCount 2 := sum_if_genus_eq_two c

/-- If every entry is positive and the root entry is three, then the sum of
the entries is `3a₃+2a₂+a₁`. -/
theorem S_eq_three_mul_count_three_add_two_mul_count_two_add_count_one
    {N : ℕ} (c : PointBasisCertificate N) (hd : c.d = 3)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p) :
    c.S = 3 * c.multiplicityCount 3 +
      2 * c.multiplicityCount 2 + c.multiplicityCount 1 := by
  calc
    c.S = ∑ p, c.multiplicity p := rfl
    _ = ∑ p, ((if c.multiplicity p = 3 then 3 else 0) +
        (if c.multiplicity p = 2 then 2 else 0) +
        (if c.multiplicity p = 1 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro p _hp
      rcases value_eq_one_or_two_or_three c hd hpositive p with h | h | h
      · simp [h]
      · simp [h]
      · simp [h]
    _ = 3 * c.multiplicityCount 3 +
        2 * c.multiplicityCount 2 + c.multiplicityCount 1 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        sum_if_eq_three, sum_if_eq_two, sum_if_eq_one]

/-- If every entry is positive and the root entry is three, then the sum of
the squared entries is `9a₃+4a₂+a₁`. -/
theorem M_eq_nine_mul_count_three_add_four_mul_count_two_add_count_one
    {N : ℕ} (c : PointBasisCertificate N) (hd : c.d = 3)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p) :
    c.M = 9 * c.multiplicityCount 3 +
      4 * c.multiplicityCount 2 + c.multiplicityCount 1 := by
  calc
    c.M = ∑ p, c.multiplicity p ^ 2 := rfl
    _ = ∑ p, ((if c.multiplicity p = 3 then 9 else 0) +
        (if c.multiplicity p = 2 then 4 else 0) +
        (if c.multiplicity p = 1 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro p _hp
      rcases value_eq_one_or_two_or_three c hd hpositive p with h | h | h
      · simp [h]
      · simp [h]
      · simp [h]
    _ = 9 * c.multiplicityCount 3 +
        4 * c.multiplicityCount 2 + c.multiplicityCount 1 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        sum_if_square_eq_three, sum_if_square_eq_two, sum_if_eq_one]

/-- In order three, the genus numerator is
`2(3a₃+a₂)`. -/
theorem genusNumerator_eq_two_mul_three_mul_count_three_add_count_two
    {N : ℕ} (c : PointBasisCertificate N) (hd : c.d = 3)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p) :
    c.genusNumerator =
      2 * (3 * c.multiplicityCount 3 + c.multiplicityCount 2) := by
  calc
    c.genusNumerator = ∑ p,
        c.multiplicity p * (c.multiplicity p - 1) := rfl
    _ = ∑ p, ((if c.multiplicity p = 3 then 6 else 0) +
        (if c.multiplicity p = 2 then 2 else 0)) := by
      apply Finset.sum_congr rfl
      intro p _hp
      rcases value_eq_one_or_two_or_three c hd hpositive p with h | h | h
      · simp [h]
      · simp [h]
      · simp [h]
    _ = 2 * (3 * c.multiplicityCount 3 +
        c.multiplicityCount 2) := by
      rw [Finset.sum_add_distrib, sum_if_genus_eq_three,
        sum_if_genus_eq_two]
      omega

end PointBasisCertificate

end OnLeConjecture.Numerical
