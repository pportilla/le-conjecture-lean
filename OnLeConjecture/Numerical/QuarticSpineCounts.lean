/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Numerical.PointBasisCountIdentities
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Point-basis sums with an order-four chain

An injective list of all order-four entries determines their count. If all
remaining entries are at most two, the square sum has the refined quartic
bound used after resolution of the square initial form.
-/

public section

namespace OnLeConjecture.Numerical.MultiplicityCounts

open scoped BigOperators

variable {α : Type*} [Fintype α]

theorem squareSum_le_three_sum_add_four_valueCount
    (multiplicity : α → ℕ) (hbounded : ∀ p, multiplicity p ≤ 4) :
    squareSum multiplicity ≤ 3 * sum multiplicity + 4 * valueCount multiplicity 4 := by
  classical
  have hpoint (p : α) : multiplicity p ^ 2 ≤
      3 * multiplicity p + (if multiplicity p = 4 then 4 else 0) := by
    split_ifs with hp
    · norm_num [hp]
    · have hle : multiplicity p ≤ 3 := by have := hbounded p; omega
      nlinarith
  calc
    squareSum multiplicity ≤ ∑ p, (3 * multiplicity p +
      if multiplicity p = 4 then 4 else 0) := Finset.sum_le_sum (fun p _ => hpoint p)
    _ = 3 * sum multiplicity + 4 * valueCount multiplicity 4 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter]
      simp [sum, valueCount, mul_comm]

theorem squareSum_le_two_sum_add_eight_valueCount
    (multiplicity : α → ℕ) (hbounded : ∀ p, multiplicity p ≤ 2 ∨ multiplicity p = 4) :
    squareSum multiplicity ≤ 2 * sum multiplicity + 8 * valueCount multiplicity 4 := by
  classical
  have hpoint (p : α) : multiplicity p ^ 2 ≤
      2 * multiplicity p + (if multiplicity p = 4 then 8 else 0) := by
    rcases hbounded p with hp | hp
    · have hn : multiplicity p ≠ 4 := by omega
      rw [if_neg hn]
      nlinarith
    · norm_num [hp]
  calc
    squareSum multiplicity ≤ ∑ p, (2 * multiplicity p +
      if multiplicity p = 4 then 8 else 0) := Finset.sum_le_sum (fun p _ => hpoint p)
    _ = 2 * sum multiplicity + 8 * valueCount multiplicity 4 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter]
      simp [sum, valueCount, mul_comm]

/-- The specified distinct order-four entries are exactly the order-four
entries, since every other entry is at most two. -/
theorem valueCount_four_eq_of_spine
    {A : ℕ} (multiplicity : α → ℕ) (spine : Fin A → α)
    (hinjective : Function.Injective spine)
    (hspine : ∀ i, multiplicity (spine i) = 4)
    (hoff : ∀ p, p ∉ Set.range spine → multiplicity p ≤ 2) :
    valueCount multiplicity 4 = A := by
  classical
  have hset : Finset.univ.filter (fun p => multiplicity p = 4) =
      Finset.univ.image spine := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hp
      have hrange : p ∈ Set.range spine := by
        by_contra hn
        have := hoff p hn
        omega
      obtain ⟨i, rfl⟩ := hrange
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact hspine i
  rw [valueCount, hset, Finset.card_image_of_injective _ hinjective]
  simp

/-- Count and refined square-sum bound for a finite injective order-four
chain whose complement has entries at most two. Empty chains are allowed. -/
theorem quartic_spine_count_and_squareSum_bound
    {A : ℕ} (multiplicity : α → ℕ) (spine : Fin A → α)
    (hinjective : Function.Injective spine)
    (hspine : ∀ i, multiplicity (spine i) = 4)
    (hoff : ∀ p, p ∉ Set.range spine → multiplicity p ≤ 2) :
    valueCount multiplicity 4 = A ∧ squareSum multiplicity ≤ 2 * sum multiplicity + 8 * A := by
  have hcount := valueCount_four_eq_of_spine multiplicity spine hinjective hspine hoff
  refine ⟨hcount, ?_⟩
  rw [← hcount]
  apply squareSum_le_two_sum_add_eight_valueCount
  intro p
  by_cases hp : p ∈ Set.range spine
  · obtain ⟨i, rfl⟩ := hp
    exact Or.inr (hspine i)
  · exact Or.inl (hoff p hp)

end OnLeConjecture.Numerical.MultiplicityCounts
