/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSignedDomain
import Mathlib.Tactic

/-!
# Boundaries of the factor projections of a seam domain

Let `N = n + m + 1`, and let `D` be a domain on the seam grid from `seamState x z` to
`seamState y w`. The first projection `seamFirstProjection D` is a domain from `x` to `y`
(`seamFirstProjection_isFrom`), and the second projection `seamSecondProjection D` is a domain
from `z` to `w` (`seamSecondProjection_isFrom`).

At a vertex `(i, j)` whose two adjacent cell columns and two adjacent cell rows are adjacent on
the seam grid, the mixed difference of a projection is a mixed difference of `D`. The remaining
vertices lie on one factor row or one factor column. On them the mixed difference is determined
by the vanishing of the sum of the mixed differences along that row or column
(`GridDomain.boundary_eq_of_forall_ne_fst` and `GridDomain.boundary_eq_of_forall_ne_snd`).

For `c < n` and `n < r`, both retained endpoint states have no point at `(c, r)`. This gives the
northeast formula `D(c, n + j) = D(c, n) + D(N - 1, n + j) - D(N - 1, n)`
(`seamDomain_northeast`), which is the written Lemma J07:lem:j07-northeast-domain.
For the signed domain of a correction path, both projections are nonnegative.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
open scoped BigOperators

/-! ### Sums of mixed differences and of state indicators -/

namespace GridDomain

variable {K : ℕ} [NeZero K]

/-- The mixed differences of a domain along a row sum to zero. -/
theorem sum_boundary_fst (D : GridDomain K) (r : Fin K) : ∑ c, D.boundary c r = 0 := by
  have h := sum_comp_sub_one (fun c => D c r - D c (r - 1))
  have e : ∀ c, D.boundary c r = (D c r - D c (r - 1)) - (D (c - 1) r - D (c - 1) (r - 1)) := by
    intro c
    simp only [boundary]
    ring
  simp only [e]
  rw [Finset.sum_sub_distrib, h, sub_self]

/-- The mixed differences of a domain along a column sum to zero. -/
theorem sum_boundary_snd (D : GridDomain K) (c : Fin K) : ∑ r, D.boundary c r = 0 := by
  have h := sum_comp_sub_one (fun r => D c r - D (c - 1) r)
  have e : ∀ r, D.boundary c r = (D c r - D (c - 1) r) - (D c (r - 1) - D (c - 1) (r - 1)) := by
    intro r
    simp only [boundary]
    ring
  simp only [e]
  rw [Finset.sum_sub_distrib, h, sub_self]

omit [NeZero K] in
/-- A grid state has exactly one point in each row. -/
theorem sum_gridStateIndicator_fst (u : GridState K) (r : Fin K) :
    ∑ c, gridStateIndicator u c r = 1 := by
  have h := Equiv.sum_comp u.toPerm (fun r' => if r' = r then (1 : ℤ) else 0)
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  exact h

omit [NeZero K] in
/-- A grid state has exactly one point in each column. -/
theorem sum_gridStateIndicator_snd (u : GridState K) (c : Fin K) :
    ∑ r, gridStateIndicator u c r = 1 := by
  simp [gridStateIndicator]

/-- If the mixed difference of a domain agrees with `[u] - [v]` away from one column, then it
agrees on that column. -/
theorem boundary_eq_of_forall_ne_fst {E : GridDomain K} {u v : GridState K} (i₀ : Fin K)
    (h : ∀ i, i ≠ i₀ → ∀ j,
      E.boundary i j = gridStateIndicator u i j - gridStateIndicator v i j)
    (j : Fin K) :
    E.boundary i₀ j = gridStateIndicator u i₀ j - gridStateIndicator v i₀ j := by
  have h1 := sum_boundary_fst E j
  have h2 := sum_gridStateIndicator_fst u j
  have h3 := sum_gridStateIndicator_fst v j
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)] at h1 h2 h3
  have h4 : ∑ i ∈ Finset.univ.erase i₀, E.boundary i j =
      ∑ i ∈ Finset.univ.erase i₀, (gridStateIndicator u i j - gridStateIndicator v i j) :=
    Finset.sum_congr rfl fun i hi => h i (Finset.ne_of_mem_erase hi) j
  rw [Finset.sum_sub_distrib] at h4
  linarith

/-- If the mixed difference of a domain agrees with `[u] - [v]` away from one row, then it
agrees on that row. -/
theorem boundary_eq_of_forall_ne_snd {E : GridDomain K} {u v : GridState K} (j₀ : Fin K)
    (i : Fin K) (h : ∀ j, j ≠ j₀ →
      E.boundary i j = gridStateIndicator u i j - gridStateIndicator v i j) :
    E.boundary i j₀ = gridStateIndicator u i j₀ - gridStateIndicator v i j₀ := by
  have h1 := sum_boundary_snd E i
  have h2 := sum_gridStateIndicator_snd u i
  have h3 := sum_gridStateIndicator_snd v i
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)] at h1 h2 h3
  have h4 : ∑ j ∈ Finset.univ.erase j₀, E.boundary i j =
      ∑ j ∈ Finset.univ.erase j₀, (gridStateIndicator u i j - gridStateIndicator v i j) :=
    Finset.sum_congr rfl fun j hj => h j (Finset.ne_of_mem_erase hj)
  rw [Finset.sum_sub_distrib] at h4
  linarith

end GridDomain

variable {n m : ℕ}

/-! ### Seam coordinates -/

theorem seamFirstColumn_val (i : Fin (n + 1)) :
    (seamFirstColumn (m := m) i).val = if i.val < n then i.val else n + m := by
  unfold seamFirstColumn
  split_ifs <;> simp

/-- The first projection column of a factor column `i < n` is the seam column `i`. -/
theorem seamFirstColumn_castSucc (i : Fin n) :
    seamFirstColumn (m := m) i.castSucc = seamLeft n m i.castSucc := by
  apply Fin.ext
  rw [seamFirstColumn_val, if_pos (by simp)]
  simp

/-- The first projection column of the last factor column is the last seam column. -/
theorem seamFirstColumn_last : seamFirstColumn (m := m) (Fin.last n) = Fin.last (n + m) := by
  apply Fin.ext
  rw [seamFirstColumn_val, if_neg (by simp)]
  simp

theorem seamFirstColumn_sub_one (i : Fin (n + 1)) (hi : i.val < n) :
    seamFirstColumn (m := m) (i - 1) = seamFirstColumn i - 1 := by
  apply Fin.ext
  rw [seamFirstColumn_val, val_sub_one_cyclic (seamFirstColumn (m := m) i), seamFirstColumn_val,
    val_sub_one_cyclic i]
  split_ifs <;> omega

theorem seamLeft_sub_one (j : Fin (n + 1)) (hj : j ≠ 0) :
    seamLeft n m (j - 1) = seamLeft n m j - 1 := by
  have hj' : j.val ≠ 0 := fun h => hj (Fin.ext h)
  apply Fin.ext
  rw [seamLeft_val, val_sub_one_cyclic, val_sub_one_cyclic, seamLeft_val, if_neg hj', if_neg hj']

theorem seamRight_sub_one (j : Fin (m + 1)) (hj : j ≠ 0) :
    seamRight n m (j - 1) = seamRight n m j - 1 := by
  have hj' : j.val ≠ 0 := fun h => hj (Fin.ext h)
  apply Fin.ext
  rw [seamRight_val, val_sub_one_cyclic, val_sub_one_cyclic, seamRight_val, if_neg hj',
    if_neg (by omega)]
  omega

/-- The value of a retained state in a second-block column. -/
theorem seamState_right (x : GridState (n + 1)) (z : GridState (m + 1)) (e : Fin (m + 1)) :
    seamState x z (seamRight n m e) =
      if z e = 0 then seamLeft n m (x (Fin.last n)) else seamRight n m (z e) := by
  split_ifs with h
  · exact seamState_right_of_zero x z e h
  · exact seamState_right_of_ne_zero x z e h

/-- Every retained point in a column `c < n` has row at most `n`. -/
theorem seamState_val_le_of_lt (x : GridState (n + 1)) (z : GridState (m + 1))
    (c : Fin (n + m + 1)) (hc : c.val < n) : (seamState x z c).val ≤ n := by
  have he : c = seamLeft n m (Fin.castSucc ⟨c.val, hc⟩) := Fin.ext rfl
  rw [he, seamState_left_castSucc, seamLeft_val]
  exact Nat.lt_succ_iff.mp (x _).isLt

/-- The indicator of a retained state at a first-projection vertex in a column `i < n`. -/
theorem gridStateIndicator_seamState_first (x : GridState (n + 1)) (z : GridState (m + 1))
    (i : Fin (n + 1)) (hi : i.val < n) (j : Fin (n + 1)) :
    gridStateIndicator (seamState x z) (seamFirstColumn (m := m) i) (seamLeft n m j) =
      gridStateIndicator x i j := by
  have he : i = Fin.castSucc ⟨i.val, hi⟩ := Fin.ext rfl
  rw [he, seamFirstColumn_castSucc]
  simp only [gridStateIndicator, seamState_left_castSucc,
    (seamLeft_injective (n := n) (m := m)).eq_iff]

/-- The indicator of a retained state at a second-projection vertex in a row `j ≠ 0`. -/
theorem gridStateIndicator_seamState_second (x : GridState (n + 1)) (z : GridState (m + 1))
    (i j : Fin (m + 1)) (hj : j ≠ 0) :
    gridStateIndicator (seamState x z) (seamRight n m i) (seamRight n m j) =
      gridStateIndicator z i j := by
  simp only [gridStateIndicator, seamState_right]
  by_cases hz : z i = 0
  · rw [if_pos hz, if_neg, if_neg]
    · rw [hz]
      exact Ne.symm hj
    · intro h
      have h1 := congrArg Fin.val h
      have h2 := (x (Fin.last n)).isLt
      have h3 : j.val ≠ 0 := fun h' => hj (Fin.ext h')
      simp only [seamLeft_val, seamRight_val] at h1
      omega
  · rw [if_neg hz]
    simp only [(seamRight_injective (n := n) (m := m)).eq_iff]

/-! ### The two projections are domains -/

theorem seamFirstProjection_boundary_of_ne (D : GridDomain (n + m + 1)) (i j : Fin (n + 1))
    (hi : i.val < n) (hj : j ≠ 0) :
    (seamFirstProjection (m := m) D).boundary i j =
      D.boundary (seamFirstColumn (m := m) i) (seamLeft n m j) := by
  simp only [GridDomain.boundary, seamFirstProjection, seamFirstColumn_sub_one i hi,
    seamLeft_sub_one j hj]

theorem seamSecondProjection_boundary_of_ne (D : GridDomain (n + m + 1)) (i j : Fin (m + 1))
    (hi : i ≠ 0) (hj : j ≠ 0) :
    (seamSecondProjection (n := n) D).boundary i j =
      D.boundary (seamRight n m i) (seamRight n m j) := by
  simp only [GridDomain.boundary, seamSecondProjection, seamRight_sub_one i hi,
    seamRight_sub_one j hj]

/-- The first projection of a domain between retained states is a domain between the first
factor states. -/
theorem seamFirstProjection_isFrom {D : GridDomain (n + m + 1)} {x y : GridState (n + 1)}
    {z w : GridState (m + 1)} (hD : D.IsFrom (seamState x z) (seamState y w)) :
    (seamFirstProjection (m := m) D).IsFrom x y := by
  have h1 : ∀ i : Fin (n + 1), i.val < n → ∀ j : Fin (n + 1), j ≠ 0 →
      (seamFirstProjection (m := m) D).boundary i j =
        gridStateIndicator x i j - gridStateIndicator y i j := by
    intro i hi j hj
    rw [seamFirstProjection_boundary_of_ne D i j hi hj, hD,
      gridStateIndicator_seamState_first x z i hi j, gridStateIndicator_seamState_first y w i hi j]
  have h2 : ∀ i : Fin (n + 1), i.val < n → ∀ j : Fin (n + 1),
      (seamFirstProjection (m := m) D).boundary i j =
        gridStateIndicator x i j - gridStateIndicator y i j := by
    intro i hi j
    by_cases hj : j = 0
    · subst hj
      exact GridDomain.boundary_eq_of_forall_ne_snd 0 i (fun j hj => h1 i hi j hj)
    · exact h1 i hi j hj
  intro i j
  by_cases hi : i.val < n
  · exact h2 i hi j
  · have he : i = Fin.last n := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
    subst he
    refine GridDomain.boundary_eq_of_forall_ne_fst (Fin.last n) (fun i hi j => h2 i ?_ j) j
    have h' : i.val ≠ n := fun h => hi (Fin.ext (by simpa using h))
    have := i.isLt
    omega

/-- The second projection of a domain between retained states is a domain between the second
factor states. -/
theorem seamSecondProjection_isFrom {D : GridDomain (n + m + 1)} {x y : GridState (n + 1)}
    {z w : GridState (m + 1)} (hD : D.IsFrom (seamState x z) (seamState y w)) :
    (seamSecondProjection (n := n) D).IsFrom z w := by
  have h1 : ∀ i : Fin (m + 1), i ≠ 0 → ∀ j : Fin (m + 1), j ≠ 0 →
      (seamSecondProjection (n := n) D).boundary i j =
        gridStateIndicator z i j - gridStateIndicator w i j := by
    intro i hi j hj
    rw [seamSecondProjection_boundary_of_ne D i j hi hj, hD,
      gridStateIndicator_seamState_second x z i j hj,
      gridStateIndicator_seamState_second y w i j hj]
  have h2 : ∀ i : Fin (m + 1), i ≠ 0 → ∀ j : Fin (m + 1),
      (seamSecondProjection (n := n) D).boundary i j =
        gridStateIndicator z i j - gridStateIndicator w i j := by
    intro i hi j
    by_cases hj : j = 0
    · subst hj
      exact GridDomain.boundary_eq_of_forall_ne_snd 0 i (fun j hj => h1 i hi j hj)
    · exact h1 i hi j hj
  intro i j
  by_cases hi : i = 0
  · subst hi
    exact GridDomain.boundary_eq_of_forall_ne_fst 0 (fun i hi j => h2 i hi j) j
  · exact h2 i hi j

/-! ### The northeast region -/

/-- In a column `c < n`, the vertical differences of a domain between retained states agree
with those of the last column at every row `r > n`. -/
theorem seamDomain_vertical_eq {D : GridDomain (n + m + 1)} {x y : GridState (n + 1)}
    {z w : GridState (m + 1)} (hD : D.IsFrom (seamState x z) (seamState y w))
    (r : Fin (n + m + 1)) (hr : n < r.val) :
    ∀ c : Fin (n + m + 1), c.val < n →
      D c r - D c (r - 1) = D (Fin.last (n + m)) r - D (Fin.last (n + m)) (r - 1) := by
  have hb : ∀ c : Fin (n + m + 1), c.val < n →
      D c r - D c (r - 1) = D (c - 1) r - D (c - 1) (r - 1) := by
    intro c hc
    have h := hD c r
    have hx := seamState_val_le_of_lt x z c hc
    have hy := seamState_val_le_of_lt y w c hc
    have e1 : gridStateIndicator (seamState x z) c r = 0 := by
      rw [gridStateIndicator, if_neg]
      intro he
      rw [he] at hx
      omega
    have e2 : gridStateIndicator (seamState y w) c r = 0 := by
      rw [gridStateIndicator, if_neg]
      intro he
      rw [he] at hy
      omega
    rw [e1, e2, GridDomain.boundary] at h
    linarith
  have key : ∀ t : ℕ, ∀ c : Fin (n + m + 1), c.val = t → t < n →
      D c r - D c (r - 1) = D (Fin.last (n + m)) r - D (Fin.last (n + m)) (r - 1) := by
    intro t
    induction t with
    | zero =>
      intro c hc ht
      rw [hb c (by omega)]
      have he : c - 1 = Fin.last (n + m) := by
        apply Fin.ext
        rw [val_sub_one_cyclic, if_pos hc]
        simp
      rw [he]
    | succ t ih =>
      intro c hc ht
      rw [hb c (by omega)]
      apply ih (c - 1) _ (by omega)
      rw [val_sub_one_cyclic, if_neg (by omega)]
      omega
  exact fun c hc => key c.val c rfl hc

/-- The northeast formula for a domain between retained states:
`D(c, n + j) = D(c, n) + D(N - 1, n + j) - D(N - 1, n)` for every column `c < n`. -/
theorem seamDomain_northeast {D : GridDomain (n + m + 1)} {x y : GridState (n + 1)}
    {z w : GridState (m + 1)} (hD : D.IsFrom (seamState x z) (seamState y w))
    (c : Fin (n + m + 1)) (hc : c.val < n) (j : Fin (m + 1)) :
    D c (seamRight n m j) = D c (seamLeft n m (Fin.last n)) +
      D (Fin.last (n + m)) (seamRight n m j) -
        D (Fin.last (n + m)) (seamLeft n m (Fin.last n)) := by
  have key : ∀ t : ℕ, ∀ ht : t < m + 1,
      D c (seamRight n m ⟨t, ht⟩) = D c (seamLeft n m (Fin.last n)) +
        D (Fin.last (n + m)) (seamRight n m ⟨t, ht⟩) -
          D (Fin.last (n + m)) (seamLeft n m (Fin.last n)) := by
    intro t
    induction t with
    | zero =>
      intro ht
      have he : seamRight n m ⟨0, ht⟩ = seamLeft n m (Fin.last n) := Fin.ext (by simp)
      rw [he]
      ring
    | succ t ih =>
      intro ht
      have hv := seamDomain_vertical_eq hD (seamRight n m ⟨t + 1, ht⟩)
        (by simp only [seamRight_val]; omega) c hc
      have he : seamRight n m ⟨t + 1, ht⟩ - 1 = seamRight n m ⟨t, by omega⟩ := by
        apply Fin.ext
        rw [val_sub_one_cyclic, if_neg (by simp only [seamRight_val]; omega)]
        simp only [seamRight_val]
        omega
      rw [he] at hv
      have := ih (by omega)
      linarith
  exact key j.val j.isLt

/-! ### The signed domain of a correction path -/

variable {k : ℕ}

/-- The first projection of the signed domain of a correction path is nonnegative. -/
theorem SeamCorrectionPath.firstProjection_nonneg {p q : SeamRetainedIndex n m}
    (π : SeamCorrectionPath k p q) (i j : Fin (n + 1)) :
    0 ≤ seamFirstProjection (m := m) π.signedDomain i j := by
  apply π.signedDomain_nonneg_of
  rw [seamFirstColumn_val]
  split_ifs with h
  · exact Or.inl h
  · exact Or.inr (Or.inl rfl)

/-- The second projection of the signed domain of a correction path is nonnegative. -/
theorem SeamCorrectionPath.secondProjection_nonneg {p q : SeamRetainedIndex n m}
    (π : SeamCorrectionPath k p q) (i j : Fin (m + 1)) :
    0 ≤ seamSecondProjection (n := n) π.signedDomain i j := by
  apply π.signedDomain_nonneg_of_high
  simp

/-- The northeast formula for the signed domain, in terms of its two projections and the
shared cell: `D(c, n + j) = D₁(c, n) + D₂(m, j) - d` for every column `c < n`. -/
theorem SeamCorrectionPath.signedDomain_northeast {x y : GridState (n + 1)}
    {z w : GridState (m + 1)} (π : SeamCorrectionPath k (x, z) (y, w)) (c : Fin (n + m + 1))
    (hc : c.val < n) (j : Fin (m + 1)) :
    π.signedDomain c (seamRight n m j) =
      seamFirstProjection (m := m) π.signedDomain (Fin.castSucc ⟨c.val, hc⟩) (Fin.last n) +
        seamSecondProjection (n := n) π.signedDomain (Fin.last m) j -
          seamSharedCell π.signedDomain := by
  have hc' : seamFirstColumn (m := m) (Fin.castSucc (⟨c.val, hc⟩ : Fin n)) = c := by
    rw [seamFirstColumn_castSucc]
    rfl
  have hl : seamRight n m (Fin.last m) = Fin.last (n + m) := Fin.ext (by simp)
  simp only [seamFirstProjection, seamSecondProjection, seamSharedCell, hc', hl]
  exact seamDomain_northeast π.signedDomain_isFrom c hc j

end OnLeConjecture.KnotFloer.GridFull
