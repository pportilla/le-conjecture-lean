/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationORectangle

/-!
# The square derivative commutes with the reverse row matching

The correspondence exchanges the adjacent rows in a rectangle whose two endpoints
have the same matching status. It preserves the region and hence every square weight.
Rectangles from a matching source to a nonsource do not occur.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (a q : Fin n)

/-- Applying the adjacent-row relabeling twice returns the state. -/
theorem rowMatchingRelabel_twice (x : GridState (n + 1)) :
    (x.relabelRows (Equiv.swap q.castSucc q.succ)).relabelRows
      (Equiv.swap q.castSucc q.succ) = x := by
  ext c
  simp only [GridState.relabelRows_apply, Equiv.swap_apply_self]

variable (S : Type*) [CommSemiring S]

open Classical in
/-- Reverse the adjacent-row matching with coefficient one, and kill its source states. -/
noncomputable def rowReverseMatching : Module.End S (GridState (n + 1) →₀ S) :=
  Finsupp.linearCombination S fun x =>
    if RowMatchingSource a q x then 0 else
      single (x.relabelRows (Equiv.swap q.castSucc q.succ)) 1

open Classical in
theorem rowReverseMatching_single (x : GridState (n + 1)) (v : S) :
    rowReverseMatching a q S (single x v) =
      if RowMatchingSource a q x then 0 else
        single (x.relabelRows (Equiv.swap q.castSucc q.succ)) v := by
  simp only [rowReverseMatching, Finsupp.linearCombination_single]
  split_ifs
  · exact smul_zero _
  · rw [Finsupp.smul_single, smul_eq_mul, mul_one]

open Classical in
/-- The reverse matching reads the coefficient of the row-swapped state at each source. -/
theorem rowReverseMatching_apply (c : GridState (n + 1) →₀ S) (y : GridState (n + 1)) :
    rowReverseMatching a q S c y = if RowMatchingSource a q y then
      c (y.relabelRows (Equiv.swap q.castSucc q.succ)) else 0 := by
  rw [finiteEnd_apply_apply]
  have hsum : (∑ x : GridState (n + 1), c x * rowReverseMatching a q S (single x 1) y) =
      c (y.relabelRows (Equiv.swap q.castSucc q.succ)) *
        rowReverseMatching a q S
          (single (y.relabelRows (Equiv.swap q.castSucc q.succ)) 1) y := by
    apply Finset.sum_eq_single
    · intro x _ hxy
      rw [rowReverseMatching_single]
      split_ifs
      · rw [Finsupp.zero_apply, mul_zero]
      · have hne : y ≠ x.relabelRows (Equiv.swap q.castSucc q.succ) := by
          intro h
          apply hxy
          rw [h, rowMatchingRelabel_twice]
        rw [Finsupp.single_eq_of_ne hne, mul_zero]
    · exact fun h => (h (Finset.mem_univ _)).elim
  rw [hsum, rowReverseMatching_single, rowMatchingRelabel_twice]
  simp only [rowMatchingSource_relabel_swap]
  by_cases hy : RowMatchingSource a q y <;> simp [hy]

/-- A square derivative on one basis state is its polynomial coefficient matrix entry. -/
theorem squareDerivative_single_apply {S : Type*} [CommSemiring S]
    (w : Fin (n + 1) × Fin (n + 1) → S) (x y : GridState (n + 1)) :
    squareDerivative w a.castSucc q.castSucc (single x 1) y =
      (squareWeightedCoefficient (deformAtSquare w a.castSucc q.castSucc) x y).coeff 1 := by
  rw [squareDerivative, polynomialCoefficientOperator_apply_apply,
    Finsupp.sum_single_index]
  · exact one_mul _
  · exact zero_mul _

/-- The square derivative commutes with the concrete reverse row matching. -/
theorem rowReverseMatching_squareDerivative_commute
    (w : Fin (n + 1) × Fin (n + 1) → S) :
    rowReverseMatching a q S ∘ₗ squareDerivative w a.castSucc q.castSucc =
      squareDerivative w a.castSucc q.castSucc ∘ₗ rowReverseMatching a q S := by
  classical
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  ext y
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, rowReverseMatching_apply,
    rowReverseMatching_single]
  by_cases hx : RowMatchingSource a q x
  · rw [if_pos hx, map_zero, Finsupp.zero_apply]
    by_cases hy : RowMatchingSource a q y
    · rw [if_pos hy, squareDerivative_single_apply]
      apply squareDerivative_coefficient_eq_zero_of_source a q w _ _ hx
      intro h
      exact (rowMatchingSource_relabel_swap a q y).mp h hy
    · exact if_neg hy
  · rw [if_neg hx, squareDerivative_single_apply]
    by_cases hy : RowMatchingSource a q y
    · rw [if_pos hy, squareDerivative_single_apply]
      have hys : ¬RowMatchingSource a q (y.relabelRows (Equiv.swap q.castSucc q.succ)) := by
        intro h
        exact (rowMatchingSource_relabel_swap a q y).mp h hy
      have h := squareDerivative_coefficient_rowSwap a q w x
        (y.relabelRows (Equiv.swap q.castSucc q.succ)) (iff_of_false hx hys)
      simpa only [rowMatchingRelabel_twice] using h.symm
    · rw [if_neg hy]
      symm
      rw [squareDerivative_single_apply]
      exact squareDerivative_coefficient_eq_zero_of_source a q w _ _
        ((rowMatchingSource_relabel_swap a q x).mpr hx) hy

end OnLeConjecture.KnotFloer.GridFull
