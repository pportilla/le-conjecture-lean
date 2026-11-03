/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamDomainProjectionBoundary
import Mathlib.Tactic

/-!
# The point-count grading of a retained state with identity marks

For the identity permutation of marks, the point-count grading `gridMarkMaslov 1` of a retained
state `seamState x z` differs from `gridMarkMaslov 1 x + gridMarkMaslov 1 z` by a quantity
depending only on `n` and `m` (`gridMarkMaslov_one_seamState_sub`).

The proof splits each of the three state-dependent pair counts into the blocks of the first `n`
seam columns and the last `m + 1` seam columns. With `t = x n`, the retained state has the point
`(n + e, t)` for the unique `e` with `z e = 0`, and the point `(n + e, n + z e)` otherwise:
* the count of strictly increasing pairs of points gains `n m`;
* the count of pairs `(c₁, c₂)` with `c₁ ≤ c₂` and `s c₁ ≤ c₂` gains `n m - 1`;
* the count of pairs with `c₁ < c₂` and `c₁ < s c₂` gains `n m`.

The written proof uses the marks `O₂(j) = j + 1` on the second factor. The identity marks used
here also satisfy the marking count identity of the written proof, see
`GridConnectedSumSeamDomainProjection`.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti
open scoped BigOperators

/-! ### The three pair counts -/

/-- The number of strictly increasing pairs of points of a state. -/
def stateCountLt {K : ℕ} (u : GridState K) : ℤ :=
  ∑ a, ∑ b, if a < b ∧ u a < u b then (1 : ℤ) else 0

/-- The number of pairs of a point `(a, u a)` and an identity mark `(b + 1/2, b + 1/2)` that
increase in both coordinates. -/
def stateCountLeMark {K : ℕ} (u : GridState K) : ℤ :=
  ∑ a, ∑ b, if a ≤ b ∧ u a ≤ b then (1 : ℤ) else 0

/-- The number of pairs of an identity mark `(a + 1/2, a + 1/2)` and a point `(b, u b)` that
increase in both coordinates. -/
def stateCountMarkLt {K : ℕ} (u : GridState K) : ℤ :=
  ∑ a, ∑ b, if a < b ∧ a < u b then (1 : ℤ) else 0

/-- The point-count grading with identity marks in terms of the three pair counts. -/
theorem gridMarkMaslov_one_eq {K : ℕ} (u : GridState K) :
    gridMarkMaslov 1 u = stateCountLt u - stateCountLeMark u - stateCountMarkLt u +
      ∑ a : Fin K, ∑ b : Fin K, if a < b ∧ a < b then (1 : ℤ) else 0 := by
  simp only [gridMarkMaslov, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, Fintype.sum_prod_type]
  simp only [Equiv.Perm.one_apply, stateCountLt, stateCountLeMark, stateCountMarkLt]
  rfl

/-! ### Splitting sums over the seam columns -/

variable {n m : ℕ}

/-- A sum over the seam columns splits into the first `n` columns and the last `m + 1`. -/
theorem sum_seam_columns (f : Fin (n + m + 1) → ℤ) :
    ∑ c, f c =
      ∑ i : Fin n, f (seamLeft n m i.castSucc) + ∑ e : Fin (m + 1), f (seamRight n m e) := by
  rw [← (seamRightIndexEquiv n m).sum_comp, Fintype.sum_sum_type]
  simp only [seamRightIndexEquiv_inl, seamRightIndexEquiv_inr]

/-- A sum of a function of `z e` with one value at `0` and another value elsewhere. -/
theorem sum_ite_eq_zero (z : GridState (m + 1)) (a b : ℤ) :
    ∑ e, (if z e = 0 then a else b) = a + m * b := by
  have h := Equiv.sum_comp z.toPerm (fun j => if j = 0 then a else b)
  rw [h, Fin.sum_univ_succ]
  simp [Fin.succ_ne_zero]

/-- The value of a retained state in a second-block column. -/
theorem seamState_right_val (x : GridState (n + 1)) (z : GridState (m + 1)) (e : Fin (m + 1)) :
    (seamState x z (seamRight n m e)).val =
      if z e = 0 then (x (Fin.last n)).val else n + (z e).val := by
  rw [seamState_right]
  split_ifs <;> simp

theorem seamState_left_val (x : GridState (n + 1)) (z : GridState (m + 1)) (i : Fin n) :
    (seamState x z (seamLeft n m i.castSucc)).val = (x i.castSucc).val := by
  rw [seamState_left_castSucc, seamLeft_val]

/-! ### Strictly increasing pairs of points -/

theorem stateCountLt_seamState (x : GridState (n + 1)) (z : GridState (m + 1)) :
    stateCountLt (seamState x z) = stateCountLt x + stateCountLt z + n * m := by
  have hx := (x (Fin.last n)).isLt
  have hLL : ∀ i₁ i₂ : Fin n,
      (if seamLeft n m i₁.castSucc < seamLeft n m i₂.castSucc ∧
          seamState x z (seamLeft n m i₁.castSucc) < seamState x z (seamLeft n m i₂.castSucc)
        then (1 : ℤ) else 0) =
      if i₁.castSucc < i₂.castSucc ∧ x i₁.castSucc < x i₂.castSucc then 1 else 0 := by
    intro i₁ i₂
    simp only [Fin.lt_def, seamState_left_val, seamLeft_val, Fin.val_castSucc]
  have hLR : ∀ (i₁ : Fin n) (e₂ : Fin (m + 1)),
      (if seamLeft n m i₁.castSucc < seamRight n m e₂ ∧
          seamState x z (seamLeft n m i₁.castSucc) < seamState x z (seamRight n m e₂)
        then (1 : ℤ) else 0) =
      if z e₂ = 0 then (if x i₁.castSucc < x (Fin.last n) then 1 else 0) else 1 := by
    intro i₁ e₂
    have h1 := (x i₁.castSucc).isLt
    simp only [Fin.lt_def, seamState_left_val, seamState_right_val, seamLeft_val, seamRight_val,
      Fin.val_castSucc]
    by_cases hz : z e₂ = 0
    · simp only [hz, if_true]
      split_ifs <;> omega
    · have hz' : (z e₂).val ≠ 0 := fun h => hz (Fin.ext h)
      simp only [hz, if_false]
      split_ifs <;> omega
  have hRL : ∀ (e₁ : Fin (m + 1)) (i₂ : Fin n),
      (if seamRight n m e₁ < seamLeft n m i₂.castSucc ∧
          seamState x z (seamRight n m e₁) < seamState x z (seamLeft n m i₂.castSucc)
        then (1 : ℤ) else 0) = 0 := by
    intro e₁ i₂
    rw [if_neg]
    simp only [Fin.lt_def, seamLeft_val, seamRight_val, Fin.val_castSucc]
    omega
  have hRR : ∀ e₁ e₂ : Fin (m + 1),
      (if seamRight n m e₁ < seamRight n m e₂ ∧
          seamState x z (seamRight n m e₁) < seamState x z (seamRight n m e₂)
        then (1 : ℤ) else 0) =
      if e₁ < e₂ ∧ z e₁ < z e₂ then 1 else 0 := by
    intro e₁ e₂
    have hinj : z e₁ = z e₂ → e₁ = e₂ := fun h => z.toPerm.injective h
    simp only [Fin.lt_def, seamState_right_val, seamRight_val]
    by_cases h1 : z e₁ = 0 <;> by_cases h2 : z e₂ = 0
    · have := hinj (h1.trans h2.symm)
      subst this
      simp
    · have h2' : (z e₂).val ≠ 0 := fun h => h2 (Fin.ext h)
      simp only [h1, h2, if_true, if_false, Fin.val_zero]
      split_ifs <;> omega
    · simp only [h1, h2, if_true, if_false, Fin.val_zero]
      split_ifs <;> omega
    · simp only [h1, h2, if_false]
      split_ifs <;> omega
  have hlast : ∀ b : Fin (n + 1),
      (if Fin.last n < b ∧ x (Fin.last n) < x b then (1 : ℤ) else 0) = 0 := by
    intro b
    rw [if_neg]
    rintro ⟨h, -⟩
    exact absurd h (not_lt.mpr (Fin.le_last b))
  have hcl : ∀ i₁ : Fin n,
      (if i₁.castSucc < Fin.last n ∧ x i₁.castSucc < x (Fin.last n) then (1 : ℤ) else 0) =
        if x i₁.castSucc < x (Fin.last n) then 1 else 0 := by
    intro i₁
    simp only [Fin.castSucc_lt_last, true_and]
  unfold stateCountLt
  rw [sum_seam_columns]
  simp only [sum_seam_columns (n := n) (m := m), hLL, hLR, hRL, hRR, sum_ite_eq_zero,
    Finset.sum_const_zero, zero_add, Fin.sum_univ_castSucc (n := n), hlast, hcl, add_zero,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  ring

/-! ### Pairs of a point and a later identity mark -/

theorem stateCountLeMark_seamState (x : GridState (n + 1)) (z : GridState (m + 1)) :
    stateCountLeMark (seamState x z) = stateCountLeMark x + stateCountLeMark z + n * m - 1 := by
  have hx := (x (Fin.last n)).isLt
  have hLL : ∀ i₁ i₂ : Fin n,
      (if seamLeft n m i₁.castSucc ≤ seamLeft n m i₂.castSucc ∧
          seamState x z (seamLeft n m i₁.castSucc) ≤ seamLeft n m i₂.castSucc
        then (1 : ℤ) else 0) =
      if i₁.castSucc ≤ i₂.castSucc ∧ x i₁.castSucc ≤ i₂.castSucc then 1 else 0 := by
    intro i₁ i₂
    simp only [Fin.le_def, seamState_left_val, seamLeft_val, Fin.val_castSucc]
  have hLR : ∀ (i₁ : Fin n) (e₂ : Fin (m + 1)),
      (if seamLeft n m i₁.castSucc ≤ seamRight n m e₂ ∧
          seamState x z (seamLeft n m i₁.castSucc) ≤ seamRight n m e₂
        then (1 : ℤ) else 0) = 1 := by
    intro i₁ e₂
    have h1 := (x i₁.castSucc).isLt
    rw [if_pos]
    simp only [Fin.le_def, seamState_left_val, seamLeft_val, seamRight_val, Fin.val_castSucc]
    omega
  have hRL : ∀ (e₁ : Fin (m + 1)) (i₂ : Fin n),
      (if seamRight n m e₁ ≤ seamLeft n m i₂.castSucc ∧
          seamState x z (seamRight n m e₁) ≤ seamLeft n m i₂.castSucc
        then (1 : ℤ) else 0) = 0 := by
    intro e₁ i₂
    rw [if_neg]
    simp only [Fin.le_def, seamLeft_val, seamRight_val, Fin.val_castSucc]
    omega
  have hRR : ∀ e₁ e₂ : Fin (m + 1),
      (if seamRight n m e₁ ≤ seamRight n m e₂ ∧
          seamState x z (seamRight n m e₁) ≤ seamRight n m e₂
        then (1 : ℤ) else 0) =
      if e₁ ≤ e₂ ∧ z e₁ ≤ e₂ then 1 else 0 := by
    intro e₁ e₂
    simp only [Fin.le_def, seamState_right_val, seamRight_val]
    by_cases h1 : z e₁ = 0
    · simp only [h1, if_true, Fin.val_zero]
      split_ifs <;> omega
    · simp only [h1, if_false]
      split_ifs <;> omega
  have hlast : ∀ b : Fin n,
      (if Fin.last n ≤ b.castSucc ∧ x (Fin.last n) ≤ b.castSucc then (1 : ℤ) else 0) = 0 := by
    intro b
    rw [if_neg]
    rintro ⟨h, -⟩
    exact absurd h (not_le.mpr (Fin.castSucc_lt_last b))
  have hcl : ∀ i₁ : Fin n,
      (if i₁.castSucc ≤ Fin.last n ∧ x i₁.castSucc ≤ Fin.last n then (1 : ℤ) else 0) = 1 := by
    intro i₁
    rw [if_pos ⟨Fin.le_last _, Fin.le_last _⟩]
  have hll : (if Fin.last n ≤ Fin.last n ∧ x (Fin.last n) ≤ Fin.last n then (1 : ℤ) else 0) = 1 :=
    if_pos ⟨le_refl _, Fin.le_last _⟩
  unfold stateCountLeMark
  rw [sum_seam_columns]
  simp only [sum_seam_columns (n := n) (m := m), hLL, hLR, hRL, hRR,
    Finset.sum_const_zero, zero_add, Fin.sum_univ_castSucc (n := n), hlast, hcl, hll,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  push_cast
  ring

/-! ### Pairs of an identity mark and a later point -/

theorem stateCountMarkLt_seamState (x : GridState (n + 1)) (z : GridState (m + 1)) :
    stateCountMarkLt (seamState x z) = stateCountMarkLt x + stateCountMarkLt z + n * m := by
  have hx := (x (Fin.last n)).isLt
  have hLL : ∀ i₁ i₂ : Fin n,
      (if seamLeft n m i₁.castSucc < seamLeft n m i₂.castSucc ∧
          seamLeft n m i₁.castSucc < seamState x z (seamLeft n m i₂.castSucc)
        then (1 : ℤ) else 0) =
      if i₁.castSucc < i₂.castSucc ∧ i₁.castSucc < x i₂.castSucc then 1 else 0 := by
    intro i₁ i₂
    simp only [Fin.lt_def, seamState_left_val, seamLeft_val, Fin.val_castSucc]
  have hLR : ∀ (i₁ : Fin n) (e₂ : Fin (m + 1)),
      (if seamLeft n m i₁.castSucc < seamRight n m e₂ ∧
          seamLeft n m i₁.castSucc < seamState x z (seamRight n m e₂)
        then (1 : ℤ) else 0) =
      if z e₂ = 0 then (if i₁.castSucc < x (Fin.last n) then 1 else 0) else 1 := by
    intro i₁ e₂
    have h1 := i₁.isLt
    simp only [Fin.lt_def, seamState_right_val, seamLeft_val, seamRight_val, Fin.val_castSucc]
    by_cases hz : z e₂ = 0
    · simp only [hz, if_true]
      split_ifs <;> omega
    · have hz' : (z e₂).val ≠ 0 := fun h => hz (Fin.ext h)
      simp only [hz, if_false]
      split_ifs <;> omega
  have hRL : ∀ (e₁ : Fin (m + 1)) (i₂ : Fin n),
      (if seamRight n m e₁ < seamLeft n m i₂.castSucc ∧
          seamRight n m e₁ < seamState x z (seamLeft n m i₂.castSucc)
        then (1 : ℤ) else 0) = 0 := by
    intro e₁ i₂
    rw [if_neg]
    simp only [Fin.lt_def, seamLeft_val, seamRight_val, Fin.val_castSucc]
    omega
  have hRR : ∀ e₁ e₂ : Fin (m + 1),
      (if seamRight n m e₁ < seamRight n m e₂ ∧
          seamRight n m e₁ < seamState x z (seamRight n m e₂)
        then (1 : ℤ) else 0) =
      if e₁ < e₂ ∧ e₁ < z e₂ then 1 else 0 := by
    intro e₁ e₂
    simp only [Fin.lt_def, seamState_right_val, seamRight_val]
    by_cases h2 : z e₂ = 0
    · simp only [h2, if_true, Fin.val_zero]
      split_ifs <;> omega
    · simp only [h2, if_false]
      split_ifs <;> omega
  have hlast : ∀ b : Fin (n + 1),
      (if Fin.last n < b ∧ Fin.last n < x b then (1 : ℤ) else 0) = 0 := by
    intro b
    rw [if_neg]
    rintro ⟨h, -⟩
    exact absurd h (not_lt.mpr (Fin.le_last b))
  have hcl : ∀ i₁ : Fin n,
      (if i₁.castSucc < Fin.last n ∧ i₁.castSucc < x (Fin.last n) then (1 : ℤ) else 0) =
        if i₁.castSucc < x (Fin.last n) then 1 else 0 := by
    intro i₁
    simp only [Fin.castSucc_lt_last, true_and]
  unfold stateCountMarkLt
  rw [sum_seam_columns]
  simp only [sum_seam_columns (n := n) (m := m), hLL, hLR, hRL, hRR, sum_ite_eq_zero,
    Finset.sum_const_zero, zero_add, Fin.sum_univ_castSucc (n := n), hlast, hcl, add_zero,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  ring

/-! ### The grading of a retained state -/

/-- With identity marks, the point-count grading of a retained state is the sum of the gradings
of its two factor states up to a quantity depending only on `n` and `m`. -/
theorem gridMarkMaslov_one_seamState_sub (x y : GridState (n + 1)) (z w : GridState (m + 1)) :
    gridMarkMaslov 1 (seamState x z) - gridMarkMaslov 1 (seamState y w) =
      (gridMarkMaslov 1 x - gridMarkMaslov 1 y) + (gridMarkMaslov 1 z - gridMarkMaslov 1 w) := by
  rw [gridMarkMaslov_one_eq (seamState x z), gridMarkMaslov_one_eq (seamState y w),
    gridMarkMaslov_one_eq x, gridMarkMaslov_one_eq y, gridMarkMaslov_one_eq z,
    gridMarkMaslov_one_eq w, stateCountLt_seamState, stateCountLt_seamState,
    stateCountLeMark_seamState, stateCountLeMark_seamState, stateCountMarkLt_seamState,
    stateCountMarkLt_seamState]
  ring

end OnLeConjecture.KnotFloer.GridFull
