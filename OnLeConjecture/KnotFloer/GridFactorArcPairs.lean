/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFactorCorner

/-!
# The corner grading as a sum over pairs of horizontal arcs

Let `G` be a grid diagram of size `n ≥ 1`. The row `α` carries a horizontal arc from the column
`p_α = O⁻¹ α` of its `O`-marking to the column `q_α = X⁻¹ α` of its `X`-marking. For two rows put

`Ψ(α, β) = 2 [q_α ≤ p_β] - [p_α < p_β] - [q_α < q_β]`.

The doubled Alexander grading of the corner state `x₀ = cornerShift G.O` is a sum over pairs of
rows:

`2 A(x₀) + (n - 1) = ∑_{α < β} Ψ(α, β)`.

This follows from the column form of the Alexander grading
(`GridDiagram.alexanderTwoℤ_eq_sum_southwestCount`) after each southwest count is written as a
count of pairs of rows (`sum_southwestCount_eq_sum_rows`). The point of `x₀` in column `c` lies in
the row whose `O`-marking is in column `c - 1`, so its column is `finRotate n (O⁻¹ β)`, and
`[u < finRotate n v] = [u ≤ v] [v ≠ n - 1]`.

## Main results

* `sum_southwestCount_eq_sum_rows`: a sum of southwest counts as a count of pairs of rows.
* `alexanderTwoℤ_cornerShift_add_eq_sum_arcPairWeight`: the arc pair formula.

All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ}

/-- The weight `Ψ(α, β)` of an ordered pair of rows. -/
def arcPairWeight (G : GridDiagram n) (α β : Fin n) : ℤ :=
  2 * (if G.X.toPerm.symm α ≤ G.O.toPerm.symm β then 1 else 0) -
    (if G.O.toPerm.symm α < G.O.toPerm.symm β then 1 else 0) -
      (if G.X.toPerm.symm α < G.X.toPerm.symm β then 1 else 0)

/-- A sum of southwest counts of `m` at the points of `y` counts the pairs of rows `α < β` such
that the point of `m` in row `α` lies strictly left of the point of `y` in row `β`. -/
theorem sum_southwestCount_eq_sum_rows (m y : GridState n) :
    ∑ c : Fin n, (m.southwestCount c (y c) : ℤ) =
      ∑ α : Fin n, ∑ β : Fin n,
        if m.toPerm.symm α < y.toPerm.symm β ∧ α < β then 1 else 0 := by
  simp only [southwestCount_eq_sum]
  rw [Finset.sum_comm]
  refine Fintype.sum_equiv m.toPerm _ _ fun d => ?_
  refine Fintype.sum_equiv y.toPerm _ _ fun c => ?_
  simp only [Equiv.symm_apply_apply]

theorem cornerShift_symm_apply (O : GridState n) (β : Fin n) :
    (cornerShift O).toPerm.symm β = finRotate n (O.toPerm.symm β) := by
  rw [Equiv.symm_apply_eq]
  change β = cornerShift O (finRotate n (O.toPerm.symm β))
  rw [cornerShift_finRotate]
  exact (Equiv.apply_symm_apply _ _).symm

/-- Comparison with a cyclic successor. -/
theorem lt_finRotate_iff {k : ℕ} (u v : Fin (k + 1)) :
    u < finRotate (k + 1) v ↔ u ≤ v ∧ v ≠ Fin.last k := by
  rcases eq_or_ne v (Fin.last k) with rfl | hv
  · rw [finRotate_last]
    simp only [ne_eq, not_true_eq_false, and_false, iff_false, not_lt]
    exact Fin.zero_le u
  · have h := coe_finRotate_of_ne_last hv
    simp only [Fin.lt_def, Fin.le_def, h, ne_eq, hv, not_false_eq_true, and_true]
    omega

/-- **The arc pair formula.** For a grid of size at least one,
`2 A(x₀) + (n - 1) = ∑_{α < β} Ψ(α, β)`. -/
theorem alexanderTwoℤ_cornerShift_add_eq_sum_arcPairWeight (G : GridDiagram n) (hn : 1 ≤ n) :
    G.alexanderTwoℤ (cornerShift G.O) + ((n : ℤ) - 1) =
      ∑ α : Fin n, ∑ β : Fin n, if α < β then arcPairWeight G α β else 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [GridDiagram.alexanderTwoℤ_eq_sum_southwestCount, Finset.sum_sub_distrib,
    sum_southwestCount_eq_sum_rows, sum_southwestCount_eq_sum_rows,
    sum_southwestCount_eq_sum_rows, sum_southwestCount_eq_sum_rows]
  simp only [cornerShift_symm_apply]
  have key : ∀ α β : Fin (k + 1), (if α < β then arcPairWeight G α β else 0) =
      2 * ((if G.X.toPerm.symm α < finRotate (k + 1) (G.O.toPerm.symm β) ∧ α < β then 1 else 0) -
        (if G.O.toPerm.symm α < finRotate (k + 1) (G.O.toPerm.symm β) ∧ α < β then 1 else 0)) +
      (if G.O.toPerm.symm α < G.O.toPerm.symm β ∧ α < β then 1 else 0) -
      (if G.X.toPerm.symm α < G.X.toPerm.symm β ∧ α < β then 1 else 0) := by
    intro α β
    by_cases hαβ : α < β
    · have hne : G.O.toPerm.symm α ≠ G.O.toPerm.symm β := fun h =>
        (ne_of_lt hαβ) (G.O.toPerm.symm.injective h)
      simp only [hαβ, and_true, if_true, arcPairWeight, lt_finRotate_iff]
      have hne' : (G.O.toPerm.symm α).val ≠ (G.O.toPerm.symm β).val := fun h =>
        hne (Fin.ext h)
      have hl := (G.O.toPerm.symm β).isLt
      simp only [Fin.lt_def, Fin.le_def, ne_eq, Fin.ext_iff, Fin.val_last]
      split_ifs <;> omega
    · simp [hαβ]
  rw [Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => key α β]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  push_cast
  ring

end OnLeConjecture.KnotFloer.GridFull
