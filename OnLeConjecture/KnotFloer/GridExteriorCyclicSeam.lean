/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorSimpleFactor

/-!
# The cyclic block grid and the cyclic exposure of a seam factor

This file formalizes the cyclic block formula and the cyclic exposure of a factor, in the setting
of Sections 10 and 11 of the written proof of Statement E (statement_E_complete_proof.tex). The
source is the subsection "Strict associativity and a cyclic block formula" of Section 10, and
Section 11 applies the same cyclic exposure. The file builds on `GridExteriorSeamCoordinates` and
`GridExteriorSimpleFactor`.

Let `T` be a triply prepared grid of size `d + 1` (`TriplyPrepared`). Across the toroidal boundary
it carries the markings `X(d, d)`, `O(d, 0)` and `X(0, 0)`. If the `O` marking of column `0` does
not lie in row `d`, then the fourth corner `(0, d)` is empty, and `cornerDestabilization` removes
column `d` and row `0`. The result is a grid of size `d` whose `X` marking of column `0` lies in
row `d - 1`. Conversely `T` is the `X` stabilization of this grid with the new column `d`, the new
row `0` and the split column `0` (`cornerDestabilization_stabilizeX`). The column condition of this
stabilization holds in the first form, because `finRotate` sends the last column to `0`, and the
row condition holds in the second form.

For a triply prepared family `D_1, …, D_r` with `r ≥ 2`, the cyclic block grid `cyclicBlockGrid` is
the corner destabilization of the seam chain. It satisfies the cyclic block formula of the written
proof (`gridRowVal_cyclicBlockGrid`). Its cyclic shift by the first block is the cyclic block grid
of the rotated family `D_2, …, D_r, D_1` (`cyclicShift_cyclicBlockGrid`). The proof reduces this
statement to two factors by the strict associativity of the seam, and then compares coordinates
(`cyclicShift_seamCyclicGrid`).

## Main results

* `connectedSumSeamGrid_movesTo_swap`: the seam of two triply prepared grids `A` and `B` is related
  by grid moves to the seam of `B` with `A`.
* `seamChainGrid_movesTo_rotate` and `seamChainGrid_movesTo_rotate_pow`: the seam chain of a triply
  prepared family of at least two grids is related by grid moves to the seam chain of the family
  rotated by one factor, and by any number of factors.
* `iteratedSeamGrid_movesTo_rotate_pow`: the same statement for `iteratedSeamGrid`.
* `exists_seamChainGrid_rotate_canonical_map` and `exists_iteratedSeamGrid_rotate_canonical_map`:
  chain maps between the native `ZMod 2` complexes with filtration shifts `(0, 0)` that send the
  normalized class to the normalized class.

Grids of different sizes are compared as elements of `Σ k, GridDiagram k`, and grid moves relate
grids of possibly different sizes.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

/-! ### Preliminaries on sizes, sigma equalities and cyclic shifts -/

/-- A grid diagram of size `k + 1` has `1 ≤ k`, since no grid diagram of size one exists. -/
theorem one_le_of_gridDiagram {k : ℕ} (G : GridDiagram (k + 1)) : 1 ≤ k := by
  rcases k with _ | k
  · exact absurd (Fin.ext (by have := (G.O 0).isLt; have := (G.X 0).isLt; omega)) (G.disjoint 0)
  · omega

/-- A grid diagram of size `k + 1` has `0 < k`. -/
theorem pos_of_gridDiagram {k : ℕ} (G : GridDiagram (k + 1)) : 0 < k :=
  one_le_of_gridDiagram G

/-- Grid diagrams that are equal as elements of `Σ k, GridDiagram k` are related by grid moves. -/
theorem movesTo_of_sigma_eq {n m : ℕ} {G : GridDiagram n} {G' : GridDiagram m}
    (h : (⟨n, G⟩ : Σ k, GridDiagram k) = ⟨m, G'⟩) : G.MovesTo G' := by
  obtain ⟨rfl, hG⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl := eq_of_heq hG
  exact GridDiagram.MovesTo.refl G

/-- The value of `(finRotate n ^ m) v` for `v < n` and `m ≤ n`: the number `v + m`, reduced by `n`
when it is at least `n`. -/
def natRot (n m v : ℕ) : ℕ := if v + m < n then v + m else v + m - n

/-- For `k ≤ n`, the power `finRotate n ^ k` adds `k` modulo `n`, in the form `natRot n k`. -/
theorem val_finRotate_pow {n : ℕ} (k : ℕ) (hk : k ≤ n) (c : Fin n) :
    ((finRotate n ^ k) c).val = natRot n k c.val := by
  rcases n with _ | N
  · exact c.elim0
  induction k with
  | zero =>
    have := c.isLt
    simp only [pow_zero, Equiv.Perm.one_apply, natRot, Nat.add_zero]
    split_ifs
    omega
  | succ k ih =>
    have ih' := ih (by omega)
    rw [pow_succ', Equiv.Perm.mul_apply, coe_finRotate]
    unfold natRot at ih' ⊢
    by_cases hl : (finRotate (N + 1) ^ k) c = Fin.last N
    · rw [if_pos hl]
      have h := congrArg Fin.val hl
      rw [ih', Fin.val_last] at h
      have := c.isLt
      split_ifs at h ⊢ <;> omega
    · rw [if_neg hl, ih']
      have h : ((finRotate (N + 1) ^ k) c).val ≠ N := fun h => hl (Fin.ext h)
      rw [ih'] at h
      have := c.isLt
      split_ifs at h ⊢ <;> omega

/-- A power of the cyclic column permutation gives a grid-move relation. -/
theorem cyclicColumns_pow_movesTo {n : ℕ} (G : GridDiagram n) (k : ℕ) :
    G.MovesTo (G.relabelColumns ((finRotate n) ^ k)) := by
  induction k with
  | zero =>
    rw [pow_zero]
    change G.MovesTo (G.relabelColumns (Equiv.refl _))
    rw [GridDiagram.relabelColumns_refl]
  | succ k ih =>
    have hs := GridDiagram.cyclicColumns_movesTo (G.relabelColumns ((finRotate n) ^ k))
    rw [GridDiagram.relabelColumns_relabelColumns] at hs
    have hp : ((finRotate n) ^ k).trans (finRotate n) = (finRotate n) ^ (k + 1) := by
      ext c
      simp only [Equiv.trans_apply, pow_succ', Equiv.Perm.mul_apply]
    rw [hp] at hs
    exact ih.trans hs

/-- The cyclic shift of a grid diagram of size `n` by `k ≤ n`. The new column `c` carries the
markings of the old column `c + k`, and every row index is decreased by `k`, both modulo `n`. -/
def cyclicShift (n k : ℕ) (G : GridDiagram n) : GridDiagram n :=
  (G.relabelColumns (finRotate n ^ k).symm).relabelRows (finRotate n ^ (n - k))

/-- A cyclic shift is a composite of cyclic column and row permutations, hence a sequence of grid
moves. -/
theorem cyclicShift_movesTo {n : ℕ} (k : ℕ) (G : GridDiagram n) :
    G.MovesTo (cyclicShift n k G) := by
  have h1 := cyclicColumns_pow_movesTo (G.relabelColumns (finRotate n ^ k).symm) k
  rw [GridDiagram.relabelColumns_relabelColumns, Equiv.symm_trans_self,
    GridDiagram.relabelColumns_refl] at h1
  exact h1.symm.trans (cyclicRows_pow_movesTo _ _)

/-- Natural-number coordinates of the `O` state of a cyclic shift. -/
theorem gridRowVal_cyclicShift_O {n k : ℕ} (hk : k ≤ n) (G : GridDiagram n) {c : ℕ} (hc : c < n) :
    gridRowVal (cyclicShift n k G).O c = natRot n (n - k) (gridRowVal G.O (natRot n k c)) := by
  have hr : natRot n k c < n := by unfold natRot; split_ifs <;> omega
  rw [gridRowVal_mk _ _ hc, gridRowVal_mk _ _ hr]
  simp only [cyclicShift, GridDiagram.relabelRows_O_apply, GridDiagram.relabelColumns_O_apply,
    Equiv.symm_symm]
  rw [val_finRotate_pow _ (by omega)]
  congr 3
  exact Fin.ext (val_finRotate_pow _ hk _)

/-- Natural-number coordinates of the `X` state of a cyclic shift. -/
theorem gridRowVal_cyclicShift_X {n k : ℕ} (hk : k ≤ n) (G : GridDiagram n) {c : ℕ} (hc : c < n) :
    gridRowVal (cyclicShift n k G).X c = natRot n (n - k) (gridRowVal G.X (natRot n k c)) := by
  have hr : natRot n k c < n := by unfold natRot; split_ifs <;> omega
  rw [gridRowVal_mk _ _ hc, gridRowVal_mk _ _ hr]
  simp only [cyclicShift, GridDiagram.relabelRows_X_apply, GridDiagram.relabelColumns_X_apply,
    Equiv.symm_symm]
  rw [val_finRotate_pow _ (by omega)]
  congr 3
  exact Fin.ext (val_finRotate_pow _ hk _)

/-! ### The corner destabilization of a triply prepared grid -/

section CornerDestabilization

variable {d : ℕ} (T : GridDiagram (d + 1))

/-- If the `X` marking of column `0` lies in row `0`, then after exchanging the first and the last
column the `X` marking of the last column lies in row `0`. -/
theorem swapColumns_last_zero_apply_last (hX0 : T.X 0 = 0) :
    (T.X.swapColumns (Fin.last d) 0) (Fin.last d) = 0 := by
  rw [GridState.swapColumns_apply, Equiv.swap_apply_left, hX0]

/-- The `O` state of the corner destabilization: the `O` state of `T` with the point of the last
column, which lies in row `0`, removed. -/
def cornerDestabilizationO (hO : T.O (Fin.last d) = 0) : GridState d :=
  (GridState.exists_insertPoint_eq hO).choose

/-- Inserting the point `(d, 0)` into `cornerDestabilizationO T hO` recovers the `O` state of
`T`. -/
theorem cornerDestabilizationO_insertPoint (hO : T.O (Fin.last d) = 0) :
    (cornerDestabilizationO T hO).insertPoint (Fin.last d) 0 = T.O :=
  (GridState.exists_insertPoint_eq hO).choose_spec

/-- The `X` state of the corner destabilization: the `X` state of `T` with its first and last
columns exchanged and the resulting point `(d, 0)` removed. -/
def cornerDestabilizationX (hX0 : T.X 0 = 0) : GridState d :=
  (GridState.exists_insertPoint_eq (swapColumns_last_zero_apply_last T hX0)).choose

/-- Inserting the point `(d, 0)` into `cornerDestabilizationX T hX0` recovers the `X` state of `T`
with its first and last columns exchanged. -/
theorem cornerDestabilizationX_insertPoint (hX0 : T.X 0 = 0) :
    (cornerDestabilizationX T hX0).insertPoint (Fin.last d) 0 =
      T.X.swapColumns (Fin.last d) 0 :=
  (GridState.exists_insertPoint_eq (swapColumns_last_zero_apply_last T hX0)).choose_spec

/-- **The corner destabilization.** Let `T` be a triply prepared grid of size `d + 1`. Its markings
across the toroidal boundary are `X(d, d)`, `O(d, 0)` and `X(0, 0)`. If the `O` marking of column
`0` does not lie in row `d`, then the fourth corner `(0, d)` is empty, and the `X` destabilization
of this block deletes column `d` and row `0` and replaces the two `X` markings by one `X` marking
in column `0` and row `d - 1`. -/
def cornerDestabilization (ht : TriplyPrepared T) (hc : T.O 0 ≠ Fin.last d) : GridDiagram d where
  O := cornerDestabilizationO T ht.2.1
  X := cornerDestabilizationX T ht.1
  disjoint c h := by
    have hO := congrArg (fun x : GridState (d + 1) => x ((Fin.last d).succAbove c))
      (cornerDestabilizationO_insertPoint T ht.2.1)
    have hX := congrArg (fun x : GridState (d + 1) => x ((Fin.last d).succAbove c))
      (cornerDestabilizationX_insertPoint T ht.1)
    simp only [GridState.insertPoint_apply_succAbove] at hO hX
    rw [h, hX, GridState.swapColumns_apply, Fin.succAbove_last] at hO
    by_cases hc0 : c.castSucc = 0
    · rw [hc0, Equiv.swap_apply_right, ht.2.2] at hO
      exact hc (hc0 ▸ hO.symm)
    · rw [Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_ne_last c) hc0] at hO
      exact T.disjoint _ hO.symm

variable (ht : TriplyPrepared T) (hc : T.O 0 ≠ Fin.last d)

/-- The `O` state of the corner destabilization. -/
theorem cornerDestabilization_O :
    (cornerDestabilization T ht hc).O = cornerDestabilizationO T ht.2.1 := rfl

/-- The `X` state of the corner destabilization. -/
theorem cornerDestabilization_X :
    (cornerDestabilization T ht hc).X = cornerDestabilizationX T ht.1 := rfl

/-- Below the last column, the `O` rows of the corner destabilization are those of `T` minus one. -/
theorem gridRowVal_cornerDestabilization_O {k : ℕ} (hk : k < d) :
    gridRowVal (cornerDestabilization T ht hc).O k + 1 = gridRowVal T.O k := by
  conv_rhs => rw [← cornerDestabilizationO_insertPoint T ht.2.1]
  rw [gridRowVal_insertPoint, cornerDestabilization_O]
  simp [natSuccAbove, natPredAbove, hk, hk.ne, show k < d + 1 by omega]

/-- Below the last column, the `X` rows of the corner destabilization are those of `T` with its
first and last columns exchanged, minus one. -/
theorem gridRowVal_cornerDestabilization_X_swap {k : ℕ} (hk : k < d) :
    gridRowVal (cornerDestabilization T ht hc).X k + 1 =
      gridRowVal (T.X.swapColumns (Fin.last d) 0) k := by
  rw [← cornerDestabilizationX_insertPoint T ht.1, gridRowVal_insertPoint, cornerDestabilization_X]
  simp [natSuccAbove, natPredAbove, hk, hk.ne, show k < d + 1 by omega]

/-- The `X` marking of column `0` of the corner destabilization lies in row `d - 1`. -/
theorem gridRowVal_cornerDestabilization_X_zero :
    gridRowVal (cornerDestabilization T ht hc).X 0 + 1 = d := by
  have hd := one_le_of_gridDiagram T
  rw [gridRowVal_cornerDestabilization_X_swap T ht hc (by omega), gridRowVal_mk _ _ (by omega)]
  rw [GridState.swapColumns_apply, show (⟨0, by omega⟩ : Fin (d + 1)) = 0 from rfl,
    Equiv.swap_apply_right, ht.2.2, Fin.val_last]

/-- In the columns `0 < k < d`, the `X` rows of the corner destabilization are those of `T` minus
one. -/
theorem gridRowVal_cornerDestabilization_X {k : ℕ} (hk0 : 0 < k) (hk : k < d) :
    gridRowVal (cornerDestabilization T ht hc).X k + 1 = gridRowVal T.X k := by
  rw [gridRowVal_cornerDestabilization_X_swap T ht hc hk, gridRowVal_mk _ _ (by omega),
    gridRowVal_mk _ _ (by omega), GridState.swapColumns_apply,
    Equiv.swap_apply_of_ne_of_ne]
  · exact fun h => by simp [Fin.ext_iff] at h; omega
  · exact fun h => by simp [Fin.ext_iff] at h; omega

/-- The triply prepared grid `T` is the `X` stabilization of its corner destabilization that splits
the `X` marking of column `0`, with the new column `d` and the new row `0`. -/
theorem cornerDestabilization_stabilizeX :
    (cornerDestabilization T ht hc).stabilizeX (Fin.last d) 0 ⟨0, pos_of_gridDiagram T⟩ = T := by
  have hd := pos_of_gridDiagram T
  ext1
  · rw [GridDiagram.stabilizeX_O, cornerDestabilization_O, cornerDestabilizationO_insertPoint]
  · apply gridState_ext_gridRowVal
    intro k hk
    have h0 := gridRowVal_cornerDestabilization_X_zero T ht hc
    have hT0 : gridRowVal T.X 0 = 0 := by
      have h := gridRowVal_val T.X 0
      rw [Fin.val_zero] at h
      rw [h, ht.1, Fin.val_zero]
    have hTd := gridRowVal_last_of_X_last ht.2.2
    rw [GridDiagram.stabilizeX_X, gridRowVal_splitPoint, cornerDestabilization_X]
    rcases (show k = d ∨ k = 0 ∨ (0 < k ∧ k < d) by omega) with rfl | rfl | ⟨hk0, hkd⟩
    · simp only [Fin.val_last, if_true, Fin.val_zero, natSuccAbove]
      rw [← cornerDestabilization_X T ht hc]
      simp only [Nat.not_lt_zero, if_false]
      omega
    · simp only [Fin.val_last, Fin.val_zero, natSuccAbove, hd, if_true, hT0]
      simp [hd.ne]
    · have h1 := gridRowVal_cornerDestabilization_X T ht hc hk0 hkd
      rw [cornerDestabilization_X] at h1
      simp only [Fin.val_last, Fin.val_zero, natSuccAbove, natPredAbove, hkd, hkd.ne, if_true,
        if_false, Nat.not_lt_zero, hk0.ne', hk, hd]
      omega

/-- The triply prepared grid `T` is an elementary `X` stabilization of its corner destabilization.
The column condition holds in the first form and the row condition in the second form. -/
theorem isXStabilization_cornerDestabilization :
    GridDiagram.IsXStabilization (cornerDestabilization T ht hc) T := by
  have hd := pos_of_gridDiagram T
  have h := GridDiagram.isXStabilization_stabilizeX (cornerDestabilization T ht hc) (Fin.last d) 0
    ⟨0, hd⟩ (Or.inl ?_) (Or.inr ?_)
  · rwa [cornerDestabilization_stabilizeX] at h
  · rw [finRotate_last]
    exact Fin.ext (by rw [val_succAbove_eq_natSuccAbove]; simp [natSuccAbove, hd])
  · have h0 := gridRowVal_cornerDestabilization_X_zero T ht hc
    rw [gridRowVal_mk _ _ hd] at h0
    have h1 : (0 : Fin (d + 1)).succAbove ((cornerDestabilization T ht hc).X ⟨0, hd⟩) =
        Fin.last d := Fin.ext (by
      rw [val_succAbove_eq_natSuccAbove, Fin.val_last, Fin.val_zero]
      simp only [natSuccAbove, Nat.not_lt_zero, if_false]
      omega)
    rw [h1, finRotate_last]

/-- A triply prepared grid whose `O` marking of column `0` does not lie in the last row is related
by grid moves to its corner destabilization. -/
theorem movesTo_cornerDestabilization : T.MovesTo (cornerDestabilization T ht hc) :=
  (GridDiagram.IsStabilization.movesTo ((GridDiagram.isStabilization_iff _ _).mpr
    (Or.inr (isXStabilization_cornerDestabilization T ht hc)))).symm

end CornerDestabilization

/-! ### The cyclic block grid of two factors -/

section BinaryRotation

variable {a b : ℕ} {A : GridDiagram (a + 1)} {B : GridDiagram (b + 1)}

/-- In the seam of two triply prepared grids, the `O` marking of column `0` lies in the first row
block, hence not in the last row. -/
theorem connectedSumSeamGrid_O_zero_ne_last (hA : TriplyPrepared A) (hB : TriplyPrepared B) :
    (connectedSumSeamGrid A B hA.2.2 hB.1).O 0 ≠ Fin.last (a + b) := by
  have ha := pos_of_gridDiagram A
  have hb := pos_of_gridDiagram B
  intro h
  have h1 := gridRowVal_val (connectedSumSeamGrid A B hA.2.2 hB.1).O 0
  rw [h, Fin.val_zero, Fin.val_last, connectedSumSeamGrid_O_eq, gridRowVal_seamState,
    if_pos ha] at h1
  have := gridRowVal_lt A.O 0
  omega

/-- The cyclic block grid `C(A, B)` of two triply prepared grids: the corner destabilization of
their seam. It has size `a + b`. -/
def seamCyclicGrid (hA : TriplyPrepared A) (hB : TriplyPrepared B) : GridDiagram (a + b) :=
  cornerDestabilization (connectedSumSeamGrid A B hA.2.2 hB.1)
    (triplyPrepared_connectedSumSeamGrid hA hB) (connectedSumSeamGrid_O_zero_ne_last hA hB)

variable (hA : TriplyPrepared A) (hB : TriplyPrepared B)

/-- The `O` rows of `C(A, B)` in the first block: `O_C(j) = O_A(j) - 1` for `j < a`. -/
theorem gridRowVal_seamCyclicGrid_O_left {j : ℕ} (hj : j < a) :
    gridRowVal (seamCyclicGrid hA hB).O j + 1 = gridRowVal A.O j := by
  have hb := pos_of_gridDiagram B
  rw [seamCyclicGrid, gridRowVal_cornerDestabilization_O _ _ _ (by omega),
    connectedSumSeamGrid_O_eq, gridRowVal_seamState, if_pos hj]

/-- The `O` rows of `C(A, B)` in the second block: `O_C(a + j) = a + O_B(j) - 1` for `j < b`. -/
theorem gridRowVal_seamCyclicGrid_O_right {j : ℕ} (hj : j < b) :
    gridRowVal (seamCyclicGrid hA hB).O (a + j) + 1 = a + gridRowVal B.O j := by
  rw [seamCyclicGrid, gridRowVal_cornerDestabilization_O _ _ _ (by omega),
    connectedSumSeamGrid_O_eq, gridRowVal_seamState, if_neg (by omega), if_pos (by omega),
    Nat.add_sub_cancel_left, if_neg (gridRowVal_ne_zero_of_O_last hB.2.1 hj)]

/-- The `X` marking of column `0` of `C(A, B)` lies in row `a + b - 1`. -/
theorem gridRowVal_seamCyclicGrid_X_zero :
    gridRowVal (seamCyclicGrid hA hB).X 0 + 1 = a + b :=
  gridRowVal_cornerDestabilization_X_zero _ _ _

/-- The `X` rows of `C(A, B)` in the first block: `X_C(j) = X_A(j) - 1` for `0 < j < a`. -/
theorem gridRowVal_seamCyclicGrid_X_left {j : ℕ} (hj0 : 0 < j) (hj : j < a) :
    gridRowVal (seamCyclicGrid hA hB).X j + 1 = gridRowVal A.X j := by
  have hb := pos_of_gridDiagram B
  rw [seamCyclicGrid, gridRowVal_cornerDestabilization_X _ _ _ hj0 (by omega),
    connectedSumSeamGrid_X_eq, gridRowVal_seamState, if_pos hj]

/-- The `X` rows of `C(A, B)` in the second block: `X_C(a + j) = a + X_B(j) - 1` for `j < b`. -/
theorem gridRowVal_seamCyclicGrid_X_right {j : ℕ} (hj : j < b) :
    gridRowVal (seamCyclicGrid hA hB).X (a + j) + 1 = a + gridRowVal B.X j := by
  have ha := pos_of_gridDiagram A
  have hAa := gridRowVal_last_of_X_last hA.2.2
  rw [seamCyclicGrid, gridRowVal_cornerDestabilization_X _ _ _ (by omega) (by omega),
    connectedSumSeamGrid_X_eq, gridRowVal_seamState, if_neg (by omega), if_pos (by omega),
    Nat.add_sub_cancel_left]
  split_ifs with h
  · omega
  · rfl

/-- **Cyclic symmetry of the binary cyclic block grid.** The cyclic shift of `C(A, B)` by `a` is
`C(B, A)`, after the identification of the sizes `b + a = a + b`. -/
theorem cyclicShift_seamCyclicGrid :
    cyclicShift (a + b) a (seamCyclicGrid hA hB) =
      gridCast (Nat.add_comm b a) (seamCyclicGrid hB hA) := by
  have ha := pos_of_gridDiagram A
  have hb := pos_of_gridDiagram B
  have hA0 : gridRowVal A.X 0 = 0 := by
    have h := gridRowVal_val A.X 0
    rw [Fin.val_zero] at h
    rw [h, hA.1, Fin.val_zero]
  have hB0 : gridRowVal B.X 0 = 0 := by
    have h := gridRowVal_val B.X 0
    rw [Fin.val_zero] at h
    rw [h, hB.1, Fin.val_zero]
  ext1 <;> apply gridState_ext_gridRowVal <;> intro k hk
  · rw [gridRowVal_gridCast_O, gridRowVal_cyclicShift_O (Nat.le_add_right a b) _ hk,
      Nat.add_sub_cancel_left]
    rcases (show k < b ∨ ∃ j, j < a ∧ k = b + j from
      if h : k < b then Or.inl h else Or.inr ⟨k - b, by omega, by omega⟩)
      with hkb | ⟨j, hj, rfl⟩
    · rw [show natRot (a + b) a k = a + k by unfold natRot; split_ifs <;> omega]
      have h1 := gridRowVal_seamCyclicGrid_O_right hA hB hkb
      have h2 := gridRowVal_seamCyclicGrid_O_left hB hA hkb
      have h3 := gridRowVal_lt B.O k
      unfold natRot
      split_ifs <;> omega
    · rw [show natRot (a + b) a (b + j) = j by unfold natRot; split_ifs <;> omega]
      have h1 := gridRowVal_seamCyclicGrid_O_left hA hB hj
      have h2 := gridRowVal_seamCyclicGrid_O_right hB hA hj
      have h3 := gridRowVal_lt A.O j
      have h4 := gridRowVal_ne_zero_of_O_last hA.2.1 hj
      unfold natRot
      split_ifs <;> omega
  · rw [gridRowVal_gridCast_X, gridRowVal_cyclicShift_X (Nat.le_add_right a b) _ hk,
      Nat.add_sub_cancel_left]
    rcases (show k < b ∨ ∃ j, j < a ∧ k = b + j from
      if h : k < b then Or.inl h else Or.inr ⟨k - b, by omega, by omega⟩)
      with hkb | ⟨j, hj, rfl⟩
    · rw [show natRot (a + b) a k = a + k by unfold natRot; split_ifs <;> omega]
      have h1 := gridRowVal_seamCyclicGrid_X_right hA hB hkb
      have h3 := gridRowVal_lt B.X k
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · have h2 := gridRowVal_seamCyclicGrid_X_zero hB hA
        unfold natRot
        split_ifs <;> omega
      · have h2 := gridRowVal_seamCyclicGrid_X_left hB hA hk0 hkb
        unfold natRot
        split_ifs <;> omega
    · rw [show natRot (a + b) a (b + j) = j by unfold natRot; split_ifs <;> omega]
      have h2 := gridRowVal_seamCyclicGrid_X_right hB hA hj
      have h3 := gridRowVal_lt A.X j
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · have h1 := gridRowVal_seamCyclicGrid_X_zero hA hB
        unfold natRot
        split_ifs <;> omega
      · have h1 := gridRowVal_seamCyclicGrid_X_left hA hB hj0 hj
        unfold natRot
        split_ifs <;> omega

/-- **Exchange of two triply prepared seam factors.** The seam of `A` with `B` is related by grid
moves to the seam of `B` with `A`. -/
theorem connectedSumSeamGrid_movesTo_swap :
    (connectedSumSeamGrid A B hA.2.2 hB.1).MovesTo (connectedSumSeamGrid B A hB.2.2 hA.1) := by
  have h := cyclicShift_movesTo a (seamCyclicGrid hA hB)
  rw [cyclicShift_seamCyclicGrid] at h
  exact (movesTo_cornerDestabilization _ _ _).trans (h.trans
    ((movesTo_gridCast _ _).symm.trans (movesTo_cornerDestabilization _ _ _).symm))

end BinaryRotation

/-! ### Cyclic exposure of a factor in a seam chain -/

section ChainRotation

/-- Seam chains of two families that agree factorwise as elements of `Σ k, GridDiagram k` agree as
elements of `Σ k, GridDiagram k`. -/
theorem seamChainGrid_sigma_congr {M : ℕ} {p p' : Fin (M + 1) → ℕ}
    {E : ∀ j, GridDiagram (p j + 1)} {E' : ∀ j, GridDiagram (p' j + 1)}
    (hE : ∀ j : Fin M, (E j.succ).X 0 = 0) (hE' : ∀ j : Fin M, (E' j.succ).X 0 = 0)
    (h : ∀ j, (⟨p j + 1, E j⟩ : Σ k, GridDiagram k) = ⟨p' j + 1, E' j⟩) :
    (⟨_, seamChainGrid M E hE⟩ : Σ k, GridDiagram k) = ⟨_, seamChainGrid M E' hE'⟩ := by
  have hp : p = p' := funext fun j => by
    have := congrArg Sigma.fst (h j)
    simp only at this
    omega
  subst hp
  have hEE : E = E' := funext fun j => eq_of_heq (Sigma.mk.inj_iff.mp (h j)).2
  subst hEE
  rfl

/-- Binary seams of factors that agree as elements of `Σ k, GridDiagram k` agree as elements of
`Σ k, GridDiagram k`. -/
theorem connectedSumSeamGrid_sigma_congr {n n' m m' : ℕ} {G : GridDiagram (n + 1)}
    {G' : GridDiagram (n' + 1)} {H : GridDiagram (m + 1)} {H' : GridDiagram (m' + 1)}
    (hG : G.X (Fin.last n) = Fin.last n) (hG' : G'.X (Fin.last n') = Fin.last n')
    (hH : H.X 0 = 0) (hH' : H'.X 0 = 0)
    (h1 : (⟨n + 1, G⟩ : Σ k, GridDiagram k) = ⟨n' + 1, G'⟩)
    (h2 : (⟨m + 1, H⟩ : Σ k, GridDiagram k) = ⟨m' + 1, H'⟩) :
    (⟨_, connectedSumSeamGrid G H hG hH⟩ : Σ k, GridDiagram k) =
      ⟨_, connectedSumSeamGrid G' H' hG' hH'⟩ := by
  obtain ⟨hn, hGG⟩ := Sigma.mk.inj_iff.mp h1
  obtain rfl : n = n' := by omega
  obtain rfl := eq_of_heq hGG
  obtain ⟨hm, hHH⟩ := Sigma.mk.inj_iff.mp h2
  obtain rfl : m = m' := by omega
  obtain rfl := eq_of_heq hHH
  rfl

/-- Strict associativity of the seam, as an equality in `Σ k, GridDiagram k`. -/
theorem connectedSumSeamGrid_assoc_sigma {a b c : ℕ} (A : GridDiagram (a + 1))
    (B : GridDiagram (b + 1)) (C : GridDiagram (c + 1)) (hA : A.X (Fin.last a) = Fin.last a)
    (hB0 : B.X 0 = 0) (hB : B.X (Fin.last b) = Fin.last b) (hC : C.X 0 = 0)
    (hAB : (connectedSumSeamGrid A B hA hB0).X (Fin.last (a + b)) = Fin.last (a + b))
    (hBC : (connectedSumSeamGrid B C hB hC).X 0 = 0) :
    (⟨_, connectedSumSeamGrid (connectedSumSeamGrid A B hA hB0) C hAB hC⟩ :
        Σ k, GridDiagram k) =
      ⟨_, connectedSumSeamGrid A (connectedSumSeamGrid B C hB hC) hA hBC⟩ := by
  rw [connectedSumSeamGrid_assoc A B C hA hB0 hB hC]
  exact gridCast_sigma _ _

/-- The `X` marking of column `0` of the seam chain of a triply prepared family lies in row `0`. -/
theorem seamChainGrid_X_zero : (M : ℕ) → {p : Fin (M + 1) → ℕ} →
    (E : ∀ j, GridDiagram (p j + 1)) → (hE : ∀ j : Fin M, (E j.succ).X 0 = 0) →
    (∀ j, TriplyPrepared (E j)) → (seamChainGrid M E hE).X 0 = 0 :=
  fun M _ E hE ht => (seamChainGrid_triplyPrepared M E hE ht).1

/-- The seam chain of a triply prepared family of `M + 2` grids is the binary seam of the first
factor with the seam chain of the remaining factors, as elements of `Σ k, GridDiagram k`. -/
theorem seamChainGrid_sigma_eq_right : (M : ℕ) → {p : Fin (M + 1 + 1) → ℕ} →
    (E : ∀ j, GridDiagram (p j + 1)) → (hE : ∀ j : Fin (M + 1), (E j.succ).X 0 = 0) →
    (ht : ∀ j, TriplyPrepared (E j)) →
    (⟨_, seamChainGrid (M + 1) E hE⟩ : Σ k, GridDiagram k) =
      ⟨_, connectedSumSeamGrid (E 0) (seamChainGrid M (fun j => E j.succ) (fun j => hE j.succ))
        (ht 0).2.2 (seamChainGrid_X_zero M _ _ fun j => ht j.succ)⟩
  | 0, p, E, hE, ht => by
    rw [seamChainGrid_succ_of_X_last 0 E hE fun j => (ht j).2.2]
    rfl
  | M + 1, p, E, hE, ht => by
    rw [seamChainGrid_succ_of_X_last (M + 1) E hE fun j => (ht j).2.2]
    have ih := seamChainGrid_sigma_eq_right M (fun j => E j.castSucc) (fun j => hE j.castSucc)
      (fun j => ht j.castSucc)
    have hS := seamChainGrid_triplyPrepared M (fun j => E j.succ.castSucc)
      (fun j => hE j.succ.castSucc) (fun j => ht j.succ.castSucc)
    refine (connectedSumSeamGrid_sigma_congr _ ?_ _ (hE (Fin.last (M + 1))) ih rfl).trans ?_
    · exact connectedSumSeamGrid_X_last _ _ _ _ hS.2.2
    refine (connectedSumSeamGrid_assoc_sigma _ _ _ _ _ hS.2.2 _ _
      (connectedSumSeamGrid_X_zero _ _ _ _ hS.1)).trans ?_
    refine connectedSumSeamGrid_sigma_congr _ _ _ _ rfl ?_
    rw [seamChainGrid_succ_of_X_last M (fun j => E j.succ) (fun j => hE j.succ)
      fun j => (ht j.succ).2.2]
    rfl

/-- The cyclic translation sends `j.castSucc` to `j.succ`. -/
theorem finRotate_castSucc_eq_succ {N : ℕ} (j : Fin N) : finRotate (N + 1) j.castSucc = j.succ :=
  Fin.ext (by rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last j)]; simp)

/-- Equal indices give equal factors in `Σ k, GridDiagram k`. -/
theorem sigma_eq_of_index_eq {N : ℕ} {p : Fin N → ℕ} (E : ∀ j, GridDiagram (p j + 1))
    {i i' : Fin N} (h : i = i') :
    (⟨p i + 1, E i⟩ : Σ k, GridDiagram k) = ⟨p i' + 1, E i'⟩ := by
  subst h
  rfl

/-- The binary seam of the seam chain of the factors `1, …, M + 1` with the factor `0` is the seam
chain of the family rotated by one factor, as elements of `Σ k, GridDiagram k`. -/
theorem seamChainGrid_finRotate_sigma_eq (M : ℕ) {p : Fin (M + 1 + 1) → ℕ}
    (E : ∀ j, GridDiagram (p j + 1)) (hE : ∀ j : Fin (M + 1), (E j.succ).X 0 = 0)
    (ht : ∀ j, TriplyPrepared (E j)) :
    (⟨_, connectedSumSeamGrid (seamChainGrid M (fun j => E j.succ) (fun j => hE j.succ)) (E 0)
        (seamChainGrid_X_last M _ _ fun j => (ht j.succ).2.2) (ht 0).1⟩ :
        Σ k, GridDiagram k) =
      ⟨_, seamChainGrid (M + 1) (fun j => E (finRotate (M + 1 + 1) j)) (fun _ => (ht _).1)⟩ := by
  rw [seamChainGrid_succ_of_X_last M _ _ fun _ => (ht _).2.2]
  refine connectedSumSeamGrid_sigma_congr _ _ _ _ ?_ ?_
  · exact seamChainGrid_sigma_congr _ _ fun j =>
      sigma_eq_of_index_eq E (finRotate_castSucc_eq_succ j).symm
  · exact sigma_eq_of_index_eq E finRotate_last.symm

/-- **Cyclic exposure by one factor.** The seam chain of a triply prepared family `E` of `M + 2`
grids is related by grid moves to the seam chain of the rotated family `j ↦ E (j + 1)`. -/
theorem seamChainGrid_movesTo_rotate (M : ℕ) {p : Fin (M + 1 + 1) → ℕ}
    (E : ∀ j, GridDiagram (p j + 1)) (hE : ∀ j : Fin (M + 1), (E j.succ).X 0 = 0)
    (ht : ∀ j, TriplyPrepared (E j)) :
    (seamChainGrid (M + 1) E hE).MovesTo
      (seamChainGrid (M + 1) (fun j => E (finRotate (M + 1 + 1) j)) (fun _ => (ht _).1)) := by
  have hS := seamChainGrid_triplyPrepared M (fun j => E j.succ) (fun j => hE j.succ)
    (fun j => ht j.succ)
  exact (movesTo_of_sigma_eq (seamChainGrid_sigma_eq_right M E hE ht)).trans
    ((connectedSumSeamGrid_movesTo_swap (ht 0) hS).trans
      (movesTo_of_sigma_eq (seamChainGrid_finRotate_sigma_eq M E hE ht)))

/-- **Cyclic exposure.** The seam chain of a triply prepared family `E` of `M + 2` grids is related
by grid moves to the seam chain of the family rotated by any number `k` of factors. -/
theorem seamChainGrid_movesTo_rotate_pow (M : ℕ) {p : Fin (M + 1 + 1) → ℕ}
    (E : ∀ j, GridDiagram (p j + 1)) (hE : ∀ j : Fin (M + 1), (E j.succ).X 0 = 0)
    (ht : ∀ j, TriplyPrepared (E j)) (k : ℕ) :
    (seamChainGrid (M + 1) E hE).MovesTo
      (seamChainGrid (M + 1) (fun j => E ((finRotate (M + 1 + 1) ^ k) j))
        (fun _ => (ht _).1)) := by
  induction k with
  | zero =>
    exact movesTo_of_sigma_eq (seamChainGrid_sigma_congr _ _ fun j =>
      sigma_eq_of_index_eq E (by rw [pow_zero, Equiv.Perm.one_apply]))
  | succ k ih =>
    refine ih.trans ((seamChainGrid_movesTo_rotate M (fun j => E ((finRotate (M + 1 + 1) ^ k) j))
      _ fun _ => ht _).trans (movesTo_of_sigma_eq (seamChainGrid_sigma_congr _ _ fun j =>
        sigma_eq_of_index_eq E ?_)))
    rw [pow_succ, Equiv.Perm.mul_apply]

end ChainRotation

/-! ### The cyclic block grid of a seam chain -/

section CyclicBlockGrid

/-- The block of the factor `0` starts at column `0`. -/
theorem seamChainOffset_zero {M : ℕ} (p : Fin (M + 1) → ℕ) : seamChainOffset p 0 = 0 := by
  simp [seamChainOffset]

variable (M : ℕ) {p : Fin (M + 1 + 1) → ℕ} (E : ∀ j, GridDiagram (p j + 1))
  (hE : ∀ j : Fin (M + 1), (E j.succ).X 0 = 0) (ht : ∀ j, TriplyPrepared (E j))

include ht in
/-- In the seam chain of a triply prepared family of at least two grids, the `O` marking of column
`0` lies in the first row block, hence not in the last row. -/
theorem seamChainGrid_O_zero_ne_last :
    (seamChainGrid (M + 1) E hE).O 0 ≠ Fin.last (seamChainSize (M + 1) p) := by
  intro h
  have h1 := (seamChainGrid_gridRowVal (M + 1) E hE ht 0 0 (pos_of_gridDiagram (E 0))).1
  rw [seamChainOffset_zero, Nat.zero_add, Nat.zero_add] at h1
  have h2 := gridRowVal_val (seamChainGrid (M + 1) E hE).O 0
  rw [h, Fin.val_zero, Fin.val_last, h1] at h2
  have h3 := gridRowVal_lt (E 0).O 0
  have h4 := seamChainOffset_add_le M (fun i => p i.castSucc) 0
  simp only [seamChainOffset_zero, Fin.castSucc_zero, Nat.zero_add] at h4
  have h5 := pos_of_gridDiagram (E (Fin.last (M + 1)))
  have h6 : seamChainSize (M + 1) p =
    seamChainSize M (fun i => p i.castSucc) + p (Fin.last (M + 1)) := rfl
  omega

/-- **The cyclic block grid** `C(D_1, …, D_r)` of a triply prepared family of `r = M + 2` grids: the
corner destabilization of their seam chain. Its size is `d = seamChainSize (M + 1) p`. -/
def cyclicBlockGrid : GridDiagram (seamChainSize (M + 1) p) :=
  cornerDestabilization (seamChainGrid (M + 1) E hE) (seamChainGrid_triplyPrepared (M + 1) E hE ht)
    (seamChainGrid_O_zero_ne_last M E hE ht)

/-- The seam chain is the `X` stabilization of the cyclic block grid that splits the `X` marking of
column `0`, with the new column `d` and the new row `0`. -/
theorem cyclicBlockGrid_stabilizeX :
    (cyclicBlockGrid M E hE ht).stabilizeX (Fin.last _) 0
        ⟨0, pos_of_gridDiagram (seamChainGrid (M + 1) E hE)⟩ = seamChainGrid (M + 1) E hE :=
  cornerDestabilization_stabilizeX _ _ _

/-- The seam chain is an elementary `X` stabilization of the cyclic block grid. -/
theorem isXStabilization_cyclicBlockGrid :
    GridDiagram.IsXStabilization (cyclicBlockGrid M E hE ht) (seamChainGrid (M + 1) E hE) :=
  isXStabilization_cornerDestabilization _ _ _

/-- The seam chain is related by grid moves to the cyclic block grid. -/
theorem seamChainGrid_movesTo_cyclicBlockGrid :
    (seamChainGrid (M + 1) E hE).MovesTo (cyclicBlockGrid M E hE ht) :=
  movesTo_cornerDestabilization _ _ _

/-- The `X` marking of column `0` of the cyclic block grid lies in row `d - 1`. -/
theorem gridRowVal_cyclicBlockGrid_X_zero :
    gridRowVal (cyclicBlockGrid M E hE ht).X 0 + 1 = seamChainSize (M + 1) p :=
  gridRowVal_cornerDestabilization_X_zero _ _ _

/-- **The cyclic block formula.** For every factor `l`, with offset `c_l = seamChainOffset p l`, and
every `j < p l`, the cyclic block grid satisfies `O_C(c_l + j) = c_l + O_{D_l}(j) - 1`, and
`X_C(c_l + j) = c_l + X_{D_l}(j) - 1` when `c_l + j > 0`. Since `X_{D_l}(0) = 0`, the second
formula gives `X_C(c_l) = c_l - 1` for `l > 0`, and `gridRowVal_cyclicBlockGrid_X_zero` gives
`X_C(0) = d - 1`. -/
theorem gridRowVal_cyclicBlockGrid (l : Fin (M + 1 + 1)) {j : ℕ} (hj : j < p l) :
    gridRowVal (cyclicBlockGrid M E hE ht).O (seamChainOffset p l + j) + 1 =
        seamChainOffset p l + gridRowVal (E l).O j ∧
      (0 < seamChainOffset p l + j →
        gridRowVal (cyclicBlockGrid M E hE ht).X (seamChainOffset p l + j) + 1 =
          seamChainOffset p l + gridRowVal (E l).X j) := by
  have hle := seamChainOffset_add_le (M + 1) p l
  have hT := seamChainGrid_gridRowVal (M + 1) E hE ht l j hj
  refine ⟨?_, fun h0 => ?_⟩
  · rw [cyclicBlockGrid, gridRowVal_cornerDestabilization_O _ _ _ (by omega), hT.1]
  · rw [cyclicBlockGrid, gridRowVal_cornerDestabilization_X _ _ _ h0 (by omega), hT.2]

/-- Corner destabilizations of grids that agree as elements of `Σ k, GridDiagram k` agree as
elements of `Σ k, GridDiagram k`. -/
theorem cornerDestabilization_sigma_congr {d d' : ℕ} {T : GridDiagram (d + 1)}
    {T' : GridDiagram (d' + 1)} (ht : TriplyPrepared T) (hc : T.O 0 ≠ Fin.last d)
    (ht' : TriplyPrepared T') (hc' : T'.O 0 ≠ Fin.last d')
    (h : (⟨d + 1, T⟩ : Σ k, GridDiagram k) = ⟨d' + 1, T'⟩) :
    (⟨d, cornerDestabilization T ht hc⟩ : Σ k, GridDiagram k) =
      ⟨d', cornerDestabilization T' ht' hc'⟩ := by
  obtain ⟨hd, hTT⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl : d = d' := by omega
  obtain rfl := eq_of_heq hTT
  rfl

/-- Cyclic shifts of grids that agree as elements of `Σ k, GridDiagram k` agree as elements of
`Σ k, GridDiagram k`. -/
theorem cyclicShift_sigma_congr {n n' : ℕ} (k : ℕ) {G : GridDiagram n} {G' : GridDiagram n'}
    (h : (⟨n, G⟩ : Σ k, GridDiagram k) = ⟨n', G'⟩) :
    (⟨n, cyclicShift n k G⟩ : Σ k, GridDiagram k) = ⟨n', cyclicShift n' k G'⟩ := by
  obtain ⟨rfl, hG⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl := eq_of_heq hG
  rfl

/-- An equality in `Σ k, GridDiagram k` is an equality after the size transport `gridCast`. -/
theorem eq_gridCast_of_sigma_eq {n n' : ℕ} {G : GridDiagram n} {G' : GridDiagram n'}
    (h : n' = n) (hs : (⟨n, G⟩ : Σ k, GridDiagram k) = ⟨n', G'⟩) : G = gridCast h G' := by
  subst h
  exact eq_of_heq (Sigma.mk.inj_iff.mp hs).2

/-- Reindexing a family by a permutation does not change the size of its seam chain. -/
theorem seamChainSize_comp_perm (M : ℕ) (p : Fin (M + 1) → ℕ) (σ : Equiv.Perm (Fin (M + 1))) :
    seamChainSize M (fun j => p (σ j)) = seamChainSize M p := by
  rw [seamChainSize_eq_sum, seamChainSize_eq_sum]
  exact Equiv.sum_comp σ p

/-- **Cyclic symmetry of the cyclic block grid.** The cyclic shift of `C(D_1, …, D_r)` by the size
parameter `p 0` of the first factor is `C(D_2, …, D_r, D_1)`, after the identification of the
sizes. -/
theorem cyclicShift_cyclicBlockGrid :
    cyclicShift (seamChainSize (M + 1) p) (p 0) (cyclicBlockGrid M E hE ht) =
      gridCast (seamChainSize_comp_perm (M + 1) p (finRotate (M + 1 + 1)))
        (cyclicBlockGrid M (fun j => E (finRotate (M + 1 + 1) j)) (fun _ => (ht _).1)
          (fun _ => ht _)) := by
  apply eq_gridCast_of_sigma_eq
  have hS := seamChainGrid_triplyPrepared M (fun j => E j.succ) (fun j => hE j.succ)
    (fun j => ht j.succ)
  have s1 : (⟨_, cyclicBlockGrid M E hE ht⟩ : Σ k, GridDiagram k) =
      ⟨_, seamCyclicGrid (ht 0) hS⟩ :=
    cornerDestabilization_sigma_congr _ _ _ _ (seamChainGrid_sigma_eq_right M E hE ht)
  have s2 := cyclicShift_sigma_congr (p 0) s1
  rw [cyclicShift_seamCyclicGrid] at s2
  have s4 : (⟨_, seamCyclicGrid hS (ht 0)⟩ : Σ k, GridDiagram k) =
      ⟨_, cyclicBlockGrid M (fun j => E (finRotate (M + 1 + 1) j)) (fun _ => (ht _).1)
          (fun _ => ht _)⟩ :=
    cornerDestabilization_sigma_congr _ _ _ _ (seamChainGrid_finRotate_sigma_eq M E hE ht)
  exact s2.trans ((gridCast_sigma _ _).trans s4)

end CyclicBlockGrid

/-! ### Iterated seams and native maps -/

section NativeMaps

/-- The seam chain of a family of grid diagrams has size at least two. -/
theorem two_le_seamChainSize_of_grids (M : ℕ) {p : Fin (M + 1) → ℕ}
    (E : ∀ j, GridDiagram (p j + 1)) : 2 ≤ seamChainSize M p + 1 :=
  two_le_seamChainSize M fun j => one_le_of_gridDiagram (E j)

/-- **Native map of the cyclic exposure.** For a triply prepared family `E` of `M + 2` grids and
every `k`, some chain map from the native `ZMod 2` complex of the seam chain of `E` to that of the
family rotated by `k` factors has filtration shifts `(0, 0)` and sends the normalized class to the
normalized class. -/
theorem exists_seamChainGrid_rotate_canonical_map (M : ℕ) {p : Fin (M + 1 + 1) → ℕ}
    (E : ∀ j, GridDiagram (p j + 1)) (hE : ∀ j : Fin (M + 1), (E j.succ).X 0 = 0)
    (ht : ∀ j, TriplyPrepared (E j)) (k : ℕ) :
    ∃ φ : laurentMaslovComplex (seamChainGrid (M + 1) E hE) (ZMod 2) ⟶
        laurentMaslovComplex (seamChainGrid (M + 1) (fun j => E ((finRotate (M + 1 + 1) ^ k) j))
          (fun _ => (ht _).1)) (ZMod 2),
      (laurentMaslovBifiltration (seamChainGrid (M + 1) E hE) (ZMod 2)).Shifts
          (laurentMaslovBifiltration (seamChainGrid (M + 1)
            (fun j => E ((finRotate (M + 1 + 1) ^ k) j)) (fun _ => (ht _).1)) (ZMod 2)) φ 0 0 ∧
        homologyMap φ 0 (gridCanonicalClass (seamChainGrid (M + 1) E hE)
            (two_le_seamChainSize_of_grids (M + 1) E)) =
          gridCanonicalClass (seamChainGrid (M + 1) (fun j => E ((finRotate (M + 1 + 1) ^ k) j))
              (fun _ => (ht _).1))
            (two_le_seamChainSize_of_grids (M + 1)
              fun j => E ((finRotate (M + 1 + 1) ^ k) j)) := by
  obtain ⟨_, φ, hφ, hc⟩ := exists_movesTo_canonical_map_of_two_le _ _
    (two_le_seamChainSize_of_grids (M + 1) E) (seamChainGrid_movesTo_rotate_pow M E hE ht k)
  exact ⟨φ, hφ, hc⟩

/-- Under the size transport `gridCast`, the condition that the last `X` marking lies in the last
row is the corresponding condition on the original grid. -/
theorem gridCast_X_last_iff {n m : ℕ} (h : n = m + 1) (G : GridDiagram n) :
    (gridCast h G).X (Fin.last m) = Fin.last m ↔ G.X ⟨m, by omega⟩ = ⟨m, by omega⟩ := by
  subst h
  rfl

/-- A prepared family whose successor-size factors are all triply prepared stays prepared after any
reindexing by a permutation. -/
theorem SeamPrepared.comp_perm {N : ℕ} {sizes : Fin N → ℕ} {D : ∀ j, GridDiagram (sizes j)}
    (hprep : SeamPrepared D) (ht : ∀ j, TriplyPrepared (preparedCast D hprep j))
    (σ : Equiv.Perm (Fin N)) : SeamPrepared (fun j => D (σ j)) where
  pos j := hprep.pos (σ j)
  first h0 := (gridCast_X_last_iff _ _).mp (ht (σ ⟨0, h0⟩)).2.2
  rest j _ := ⟨(gridCast_X_zero_iff _ _).mp (ht (σ j)).1,
    (gridCast_O_last_iff _ _).mp (ht (σ j)).2.1⟩

/-- **Cyclic exposure for iterated seams.** If every factor of a prepared family of `M + 2` grids is
triply prepared, then its iterated seam grid is related by grid moves to the iterated seam grid of
the family rotated by any number `k` of factors. -/
theorem iteratedSeamGrid_movesTo_rotate_pow {M : ℕ} {sizes : Fin (M + 1 + 1) → ℕ}
    (D : ∀ j, GridDiagram (sizes j)) (hprep : SeamPrepared D)
    (ht : ∀ j, TriplyPrepared (preparedCast D hprep j)) (k : ℕ) :
    (iteratedSeamGrid D hprep).MovesTo
      (iteratedSeamGrid (fun j => D ((finRotate (M + 1 + 1) ^ k) j))
        (hprep.comp_perm ht (finRotate (M + 1 + 1) ^ k))) :=
  (movesTo_gridCast _ _).symm.trans
    ((seamChainGrid_movesTo_rotate_pow M (preparedCast D hprep) (preparedCast_X D hprep) ht
      k).trans (movesTo_gridCast _ _))

/-- Every factor of a prepared family has size at least two. -/
theorem SeamPrepared.two_le_sizes {N : ℕ} {sizes : Fin N → ℕ}
    {D : ∀ j, GridDiagram (sizes j)} (hprep : SeamPrepared D) (j : Fin N) : 2 ≤ sizes j := by
  have h1 := one_le_of_gridDiagram (preparedCast D hprep j)
  have h2 := hprep.pos j
  omega

/-- **Native map of the cyclic exposure for iterated seams.** For a prepared family of `M + 2`
triply prepared grids and every `k`, some chain map from the native `ZMod 2` complex of its
iterated seam grid to that of the family rotated by `k` factors has filtration shifts `(0, 0)` and
sends the normalized class to the normalized class. -/
theorem exists_iteratedSeamGrid_rotate_canonical_map {M : ℕ} {sizes : Fin (M + 1 + 1) → ℕ}
    (D : ∀ j, GridDiagram (sizes j)) (hprep : SeamPrepared D)
    (ht : ∀ j, TriplyPrepared (preparedCast D hprep j)) (k : ℕ) :
    ∃ φ : laurentMaslovComplex (iteratedSeamGrid D hprep) (ZMod 2) ⟶
        laurentMaslovComplex (iteratedSeamGrid (fun j => D ((finRotate (M + 1 + 1) ^ k) j))
          (hprep.comp_perm ht (finRotate (M + 1 + 1) ^ k))) (ZMod 2),
      (laurentMaslovBifiltration (iteratedSeamGrid D hprep) (ZMod 2)).Shifts
          (laurentMaslovBifiltration (iteratedSeamGrid (fun j => D ((finRotate (M + 1 + 1) ^ k) j))
            (hprep.comp_perm ht (finRotate (M + 1 + 1) ^ k))) (ZMod 2)) φ 0 0 ∧
        homologyMap φ 0 (gridCanonicalClass (iteratedSeamGrid D hprep)
            (two_le_iteratedSeamSize (Nat.succ_pos _) (hprep.two_le_sizes))) =
          gridCanonicalClass (iteratedSeamGrid (fun j => D ((finRotate (M + 1 + 1) ^ k) j))
              (hprep.comp_perm ht (finRotate (M + 1 + 1) ^ k)))
            (two_le_iteratedSeamSize (Nat.succ_pos _)
              ((hprep.comp_perm ht _).two_le_sizes)) := by
  obtain ⟨_, φ, hφ, hc⟩ := exists_movesTo_canonical_map_of_two_le _ _
    (two_le_iteratedSeamSize (Nat.succ_pos _) (hprep.two_le_sizes))
    (iteratedSeamGrid_movesTo_rotate_pow D hprep ht k)
  exact ⟨φ, hφ, hc⟩

end NativeMaps

end OnLeConjecture.KnotFloer.GridFull
