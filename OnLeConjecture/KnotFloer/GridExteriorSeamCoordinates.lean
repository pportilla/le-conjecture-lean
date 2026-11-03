/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumIterated

/-!
# Exact seam coordinates of triply prepared factors

This file formalizes the exact seam coordinates used in Sections 10 and 11 of the written proof
of Statement E (statement_E_complete_proof.tex). A grid diagram `D` of size `e + 1` is
*triply prepared* (`TriplyPrepared`) if `X_D(0) = 0`, `O_D(e) = 0` and `X_D(e) = e`.

To compare grids of different sizes, a grid state `x` of size `N` is read as the function
`gridRowVal x : ℕ → ℕ` that sends a column `k < N` to the row of `x` in column `k` and sends
every `k ≥ N` to zero. Two grid states of the same size are equal exactly when these functions
agree below the size (`gridState_ext_gridRowVal`). In these coordinates the binary seam
`connectedSumSeamGrid` is given by the formula of the written proof (`gridRowVal_seamState`).

## Main results

* `seamLeftGrid_eq_self`: if the `X` marking of the last column lies in the last row, then the
  row rotation `seamLeftGrid` of the iterated seam is the identity.
* `connectedSumSeamGrid_X_apply_right`, `connectedSumSeamGrid_O_apply_right`,
  `connectedSumSeamGrid_O_last`, `connectedSumSeamGrid_X_last`: explicit marking values of a
  binary seam, and `triplyPrepared_connectedSumSeamGrid`: the seam of two triply prepared grids
  is triply prepared.
* `connectedSumSeamGrid_assoc`: strict associativity of the seam, after the transport
  `gridCast` along the identity of sizes. Only the `X` conditions that define both sides are
  assumed.
* `seamChainGrid_succ_of_X_last` and `seamChainGrid_triplyPrepared`: the seam chain of a
  family whose factors have their last `X` marking in the last row uses no row rotation, and the
  seam chain of a triply prepared family is triply prepared.
* `seamChainGrid_gridRowVal`: the block formula `Y_T(c_l + j) = c_l + Y_{D_l}(j)` for
  `0 ≤ j < e_l`, where `c_l = seamChainOffset p l` is the sum of the earlier `e_i`.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

/-! ### Triply prepared grids and the trivial row rotation -/

/-- A grid diagram `D` of size `e + 1` is triply prepared if its `X` marking in column `0` lies in
row `0`, its `O` marking in the last column lies in row `0`, and its `X` marking in the last
column lies in the last row. -/
def TriplyPrepared {e : ℕ} (D : GridDiagram (e + 1)) : Prop :=
  D.X 0 = 0 ∧ D.O (Fin.last e) = 0 ∧ D.X (Fin.last e) = Fin.last e

/-- A power of the cyclic translation `finRotate (n + 1)` that fixes one point is the identity. -/
theorem finRotate_pow_eq_one_of_apply_eq {n : ℕ} (k : ℕ) (x : Fin (n + 1))
    (h : ((finRotate (n + 1)) ^ k) x = x) : (finRotate (n + 1)) ^ k = 1 := by
  rcases n with _ | n
  · ext y
    have := ((finRotate (0 + 1) ^ k) y).isLt
    simp only [Equiv.Perm.one_apply]
    omega
  · exact Equiv.Perm.IsCycle.pow_eq_one_iff isCycle_finRotate |>.mpr ⟨x, by simp, h⟩

/-- If the `X` marking of the last column of `G` lies in the last row, then the row rotation
`seamLeftGrid G` is `G` itself. -/
theorem seamLeftGrid_eq_self {n : ℕ} (G : GridDiagram (n + 1))
    (h : G.X (Fin.last n) = Fin.last n) : seamLeftGrid G = G := by
  have hk := seamLeftGrid_X G
  simp only [seamLeftGrid, GridDiagram.relabelRows_X_apply, h] at hk
  have h1 := finRotate_pow_eq_one_of_apply_eq _ _ hk
  ext c <;> simp [seamLeftGrid, h1]

/-! ### Natural-number coordinates of grid states -/

/-- The row of the grid state `x` in the column with index `k`, as a natural number. It is
zero when `k` is not smaller than the size `N`. -/
def gridRowVal {N : ℕ} (x : GridState N) (k : ℕ) : ℕ :=
  if h : k < N then (x ⟨k, h⟩).val else 0

/-- At the index of a column, `gridRowVal` is the row of that column. -/
theorem gridRowVal_val {N : ℕ} (x : GridState N) (c : Fin N) :
    gridRowVal x c.val = (x c).val := by
  simp [gridRowVal, c.isLt]

/-- Below the size, `gridRowVal` is the row of the corresponding column. -/
theorem gridRowVal_mk {N : ℕ} (x : GridState N) (k : ℕ) (hk : k < N) :
    gridRowVal x k = (x ⟨k, hk⟩).val := by
  simp [gridRowVal, hk]

/-- Every value of `gridRowVal` for a grid state of size `N + 1` is at most `N`. -/
theorem gridRowVal_lt {N : ℕ} (x : GridState (N + 1)) (k : ℕ) : gridRowVal x k < N + 1 := by
  unfold gridRowVal
  split_ifs
  · exact Fin.isLt _
  · omega

/-- Two grid states of size `N` are equal if their values of `gridRowVal` agree below `N`. -/
theorem gridState_ext_gridRowVal {N : ℕ} {x y : GridState N}
    (h : ∀ k < N, gridRowVal x k = gridRowVal y k) : x = y := by
  ext c
  rw [← gridRowVal_val, ← gridRowVal_val]
  exact h c.val c.isLt

/-- The size transport `gridCast` does not change the `O` coordinates. -/
theorem gridRowVal_gridCast_O {N N' : ℕ} (h : N = N') (G : GridDiagram N) (k : ℕ) :
    gridRowVal (gridCast h G).O k = gridRowVal G.O k := by
  subst h
  rfl

/-- The size transport `gridCast` does not change the `X` coordinates. -/
theorem gridRowVal_gridCast_X {N N' : ℕ} (h : N = N') (G : GridDiagram N) (k : ℕ) :
    gridRowVal (gridCast h G).X k = gridRowVal G.X k := by
  subst h
  rfl

/-! ### The binary seam -/

/-- The binary seam formula in natural-number coordinates. Below `n` the seam state agrees
with the first state. At a column `n + d` of the second block it is `n` plus the row of the
second state in column `d` when that row is nonzero, and the row of the first state in its last
column otherwise. -/
theorem gridRowVal_seamState {n m : ℕ} (x : GridState (n + 1)) (y : GridState (m + 1))
    (k : ℕ) :
    gridRowVal (seamState x y) k =
      if k < n then gridRowVal x k else if k < n + m + 1 then
        (if gridRowVal y (k - n) = 0 then gridRowVal x n else n + gridRowVal y (k - n))
      else 0 := by
  by_cases hk : k < n
  · rw [if_pos hk, gridRowVal_mk _ _ (by omega), gridRowVal_mk _ _ (by omega)]
    have h := seamState_left_castSucc x y ⟨k, hk⟩
    rw [show seamLeft n m (Fin.castSucc ⟨k, hk⟩) = ⟨k, by omega⟩ from rfl] at h
    rw [h]
    rfl
  · rw [if_neg hk]
    by_cases hk' : k < n + m + 1
    · rw [if_pos hk', gridRowVal_mk _ _ hk', gridRowVal_mk y _ (by omega : k - n < m + 1),
        gridRowVal_mk x n (by omega)]
      have hc : (⟨k, hk'⟩ : Fin (n + m + 1)) = seamRight n m ⟨k - n, by omega⟩ := by
        ext
        simp only [seamRight_val]
        omega
      rw [hc]
      by_cases hy : y ⟨k - n, by omega⟩ = 0
      · rw [seamState_right_of_zero _ _ _ hy, hy]
        simp only [Fin.val_zero, if_true]
        rfl
      · have hy' : (y ⟨k - n, by omega⟩).val ≠ 0 := fun h => hy (Fin.ext h)
        rw [seamState_right_of_ne_zero _ _ _ hy, if_neg hy']
        rfl
    · rw [if_neg hk']
      simp [gridRowVal, hk']

/-- The seam of three grid states is strictly associative in natural-number coordinates. -/
theorem gridRowVal_seamState_assoc {a b c : ℕ} (x : GridState (a + 1))
    (y : GridState (b + 1)) (z : GridState (c + 1)) (k : ℕ) :
    gridRowVal (seamState (seamState x y) z) k =
      gridRowVal (seamState x (seamState y z)) k := by
  simp only [gridRowVal_seamState, Nat.sub_sub, Nat.add_sub_cancel_left]
  split_ifs <;> omega

section BinarySeam

variable {n m : ℕ} (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
  (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)

/-- The `O` state of the binary seam is the seam of the two `O` states. -/
theorem connectedSumSeamGrid_O_eq :
    (connectedSumSeamGrid G H hG hH).O = seamState G.O H.O := rfl

/-- The `X` state of the binary seam is the seam of the two `X` states. -/
theorem connectedSumSeamGrid_X_eq :
    (connectedSumSeamGrid G H hG hH).X = seamState G.X H.X := rfl

/-- In a column `c < n` of the first block the seam has the `O` marking of the first factor. -/
theorem connectedSumSeamGrid_O_apply_left (c : Fin n) :
    (connectedSumSeamGrid G H hG hH).O (seamLeft n m c.castSucc) =
      seamLeft n m (G.O c.castSucc) :=
  seamState_left_castSucc _ _ c

/-- In every column of the first block the seam has the `X` marking of the first factor. -/
theorem connectedSumSeamGrid_X_apply_left (c : Fin (n + 1)) :
    (connectedSumSeamGrid G H hG hH).X (seamLeft n m c) = seamLeft n m (G.X c) :=
  seamState_left _ _ hH c

/-- In every column of the second block the seam has the `X` marking of the second factor. -/
theorem connectedSumSeamGrid_X_apply_right (d : Fin (m + 1)) :
    (connectedSumSeamGrid G H hG hH).X (seamRight n m d) = seamRight n m (H.X d) := by
  by_cases hd : H.X d = 0
  · change seamState G.X H.X _ = _
    rw [seamState_right_of_zero _ _ _ hd, hG, hd, seamLeft_last]
  · exact seamState_right_of_ne_zero _ _ _ hd

/-- If the `O` marking of the last column of the second factor lies in row `0`, then in a column
`n + d` with `d < m` the seam has the `O` marking of the second factor. -/
theorem connectedSumSeamGrid_O_apply_right (hO : H.O (Fin.last m) = 0) (d : Fin m) :
    (connectedSumSeamGrid G H hG hH).O (seamRight n m d.castSucc) =
      seamRight n m (H.O d.castSucc) := by
  have hd : H.O d.castSucc ≠ 0 := fun h =>
    Fin.castSucc_ne_last d (H.O.toPerm.injective (h.trans hO.symm))
  exact seamState_right_of_ne_zero _ _ _ hd

/-- The last column of the seam is the last column of the second block. -/
theorem last_eq_seamRight_last : Fin.last (n + m) = seamRight n m (Fin.last m) :=
  Fin.ext (by simp)

/-- The first column of the seam is the first column of the first block. -/
theorem seamLeft_zero : seamLeft n m 0 = 0 :=
  Fin.ext (by simp)

/-- If the `O` marking of the last column of the second factor lies in row `0`, then the `O`
marking of the last column of the seam lies in the row of the `O` marking of the last column
of the first factor. -/
theorem connectedSumSeamGrid_O_last (hO : H.O (Fin.last m) = 0) :
    (connectedSumSeamGrid G H hG hH).O (Fin.last (n + m)) =
      seamLeft n m (G.O (Fin.last n)) := by
  rw [last_eq_seamRight_last]
  exact seamState_right_of_zero _ _ _ hO

/-- If the `X` marking of the last column of the second factor lies in its last row, then the
`X` marking of the last column of the seam lies in the last row. -/
theorem connectedSumSeamGrid_X_last (hX : H.X (Fin.last m) = Fin.last m) :
    (connectedSumSeamGrid G H hG hH).X (Fin.last (n + m)) = Fin.last (n + m) := by
  rw [last_eq_seamRight_last, connectedSumSeamGrid_X_apply_right, hX]

/-- If the `X` marking of column `0` of the first factor lies in row `0`, then the same holds
for the seam. -/
theorem connectedSumSeamGrid_X_zero (hG0 : G.X 0 = 0) :
    (connectedSumSeamGrid G H hG hH).X 0 = 0 := by
  have h := connectedSumSeamGrid_X_apply_left G H hG hH 0
  rwa [hG0, seamLeft_zero] at h

end BinarySeam

/-- The seam of two triply prepared grids is triply prepared. -/
theorem triplyPrepared_connectedSumSeamGrid {n m : ℕ} {G : GridDiagram (n + 1)}
    {H : GridDiagram (m + 1)} (hGt : TriplyPrepared G) (hHt : TriplyPrepared H) :
    TriplyPrepared (connectedSumSeamGrid G H hGt.2.2 hHt.1) := by
  refine ⟨connectedSumSeamGrid_X_zero G H _ _ hGt.1, ?_,
    connectedSumSeamGrid_X_last G H _ _ hHt.2.2⟩
  rw [connectedSumSeamGrid_O_last G H _ _ hHt.2.1, hGt.2.1, seamLeft_zero]

/-- **Strict associativity of the seam.** For grids `A`, `B`, `C` of sizes `a + 1`, `b + 1` and
`c + 1` such that both iterated seams are defined, the two parenthesizations have the same
markings after the identification of the sizes `a + (b + c) + 1 = a + b + c + 1`. -/
theorem connectedSumSeamGrid_assoc {a b c : ℕ} (A : GridDiagram (a + 1))
    (B : GridDiagram (b + 1)) (C : GridDiagram (c + 1)) (hA : A.X (Fin.last a) = Fin.last a)
    (hB0 : B.X 0 = 0) (hB : B.X (Fin.last b) = Fin.last b) (hC : C.X 0 = 0) :
    connectedSumSeamGrid (connectedSumSeamGrid A B hA hB0) C
        (connectedSumSeamGrid_X_last A B hA hB0 hB) hC =
      gridCast (by omega) (connectedSumSeamGrid A (connectedSumSeamGrid B C hB hC) hA
        (connectedSumSeamGrid_X_zero B C hB hC hB0)) := by
  ext1 <;> apply gridState_ext_gridRowVal <;> intro k _
  · rw [gridRowVal_gridCast_O]
    exact gridRowVal_seamState_assoc A.O B.O C.O k
  · rw [gridRowVal_gridCast_X]
    exact gridRowVal_seamState_assoc A.X B.X C.X k

/-! ### Seam chains of triply prepared factors -/

/-- If every factor of a seam chain has its last `X` marking in its last row, then so does the
seam chain. -/
theorem seamChainGrid_X_last : (M : ℕ) → {p : Fin (M + 1) → ℕ} →
    (E : ∀ j, GridDiagram (p j + 1)) → (hE : ∀ j : Fin M, (E j.succ).X 0 = 0) →
    (∀ j, (E j).X (Fin.last (p j)) = Fin.last (p j)) →
      (seamChainGrid M E hE).X (Fin.last (seamChainSize M p)) = Fin.last (seamChainSize M p)
  | 0, _, _, _, hX => hX 0
  | M + 1, _, E, _, hX => connectedSumSeamGrid_X_last _ (E (Fin.last (M + 1))) _ _ (hX _)

/-- If every factor of a seam chain has its last `X` marking in its last row, then the seam chain
of `M + 2` factors is the binary seam of the seam chain of the first `M + 1` factors with the
last factor, without row rotation. -/
theorem seamChainGrid_succ_of_X_last (M : ℕ) {p : Fin (M + 1 + 1) → ℕ}
    (E : ∀ j, GridDiagram (p j + 1)) (hE : ∀ j : Fin (M + 1), (E j.succ).X 0 = 0)
    (hX : ∀ j, (E j).X (Fin.last (p j)) = Fin.last (p j)) :
    seamChainGrid (M + 1) E hE =
      connectedSumSeamGrid (seamChainGrid M (fun j => E j.castSucc) (fun j => hE j.castSucc))
        (E (Fin.last (M + 1)))
        (seamChainGrid_X_last M (fun j => E j.castSucc) (fun j => hE j.castSucc)
          (fun j => hX j.castSucc))
        (hE (Fin.last M)) := by
  rw [seamChainGrid_succ]
  congr 1
  exact seamLeftGrid_eq_self _ (seamChainGrid_X_last M _ _ fun j => hX j.castSucc)

/-- The seam chain of a triply prepared family of `M + 2` grids is the binary seam of the seam
chain of the first `M + 1` factors with the last factor, without row rotation. -/
theorem seamChainGrid_succ_of_triplyPrepared (M : ℕ) {p : Fin (M + 1 + 1) → ℕ}
    (E : ∀ j, GridDiagram (p j + 1)) (hE : ∀ j : Fin (M + 1), (E j.succ).X 0 = 0)
    (ht : ∀ j, TriplyPrepared (E j)) :
    seamChainGrid (M + 1) E hE =
      connectedSumSeamGrid (seamChainGrid M (fun j => E j.castSucc) (fun j => hE j.castSucc))
        (E (Fin.last (M + 1)))
        (seamChainGrid_X_last M (fun j => E j.castSucc) (fun j => hE j.castSucc)
          (fun j => (ht j.castSucc).2.2))
        (hE (Fin.last M)) :=
  seamChainGrid_succ_of_X_last M E hE fun j => (ht j).2.2

/-- The seam chain of a triply prepared family is triply prepared. -/
theorem seamChainGrid_triplyPrepared : (M : ℕ) → {p : Fin (M + 1) → ℕ} →
    (E : ∀ j, GridDiagram (p j + 1)) → (hE : ∀ j : Fin M, (E j.succ).X 0 = 0) →
    (∀ j, TriplyPrepared (E j)) → TriplyPrepared (seamChainGrid M E hE)
  | 0, _, _, _, ht => ht 0
  | M + 1, _, E, hE, ht => by
    rw [seamChainGrid_succ_of_X_last M E hE fun j => (ht j).2.2]
    exact triplyPrepared_connectedSumSeamGrid
      (seamChainGrid_triplyPrepared M _ _ fun j => ht j.castSucc) (ht (Fin.last (M + 1)))

/-- The column offset `c_l` of the block of the factor `l` in a seam chain: the sum of the
numbers `p i` over the factors `i` before `l`. -/
def seamChainOffset {M : ℕ} (p : Fin (M + 1) → ℕ) (l : Fin (M + 1)) : ℕ :=
  ∑ i : Fin l, p (Fin.castLE l.isLt.le i)

/-- The offset of an earlier factor does not depend on the last factor. -/
theorem seamChainOffset_castSucc {M : ℕ} (p : Fin (M + 1 + 1) → ℕ) (l : Fin (M + 1)) :
    seamChainOffset p l.castSucc = seamChainOffset (fun i => p i.castSucc) l :=
  rfl

/-- The offset of the last factor is the size parameter of the seam chain of the earlier
factors. -/
theorem seamChainOffset_last {M : ℕ} (p : Fin (M + 1 + 1) → ℕ) :
    seamChainOffset p (Fin.last (M + 1)) = seamChainSize M (fun i => p i.castSucc) := by
  rw [seamChainSize_eq_sum]
  rfl

/-- The block of every factor lies inside the seam chain. -/
theorem seamChainOffset_add_le : (M : ℕ) → (p : Fin (M + 1) → ℕ) → (l : Fin (M + 1)) →
    seamChainOffset p l + p l ≤ seamChainSize M p
  | 0, p, l => by
    obtain rfl : l = 0 := Fin.ext (Nat.lt_one_iff.mp l.isLt)
    simp [seamChainOffset, seamChainSize]
  | M + 1, p, l => by
    induction l using Fin.lastCases with
    | last =>
      rw [seamChainOffset_last]
      rfl
    | cast l =>
      rw [seamChainOffset_castSucc]
      have := seamChainOffset_add_le M (fun i => p i.castSucc) l
      change _ ≤ seamChainSize M (fun i => p i.castSucc) + p (Fin.last (M + 1))
      omega

/-- If the `O` marking of the last column of `D` lies in row `0`, then no other column of `D`
has its `O` marking in row `0`. -/
theorem gridRowVal_ne_zero_of_O_last {e : ℕ} {D : GridDiagram (e + 1)}
    (hD : D.O (Fin.last e) = 0) {j : ℕ} (hj : j < e) : gridRowVal D.O j ≠ 0 := by
  rw [gridRowVal_mk _ _ (by omega)]
  intro h
  have h' : D.O ⟨j, by omega⟩ = D.O (Fin.last e) := by
    rw [hD]
    exact Fin.ext h
  have := congrArg Fin.val (D.O.toPerm.injective h')
  simp only [Fin.val_last] at this
  omega

/-- If the `X` marking of the last column of `D` lies in the last row, then `gridRowVal` of the
`X` state at the last column is the last row. -/
theorem gridRowVal_last_of_X_last {e : ℕ} {D : GridDiagram (e + 1)}
    (hD : D.X (Fin.last e) = Fin.last e) : gridRowVal D.X e = e := by
  have h := gridRowVal_val D.X (Fin.last e)
  simp only [Fin.val_last] at h
  rw [h, hD, Fin.val_last]

/-- **Block formula of a seam chain.** Let `T` be the seam chain of a triply prepared family `E`
with sizes `p l + 1`, and let `c_l = seamChainOffset p l`. For every factor `l` and every
`j < p l`, the `O` and `X` markings of `T` in column `c_l + j` lie in the rows `c_l + O_{E l}(j)`
and `c_l + X_{E l}(j)`. -/
theorem seamChainGrid_gridRowVal : (M : ℕ) → {p : Fin (M + 1) → ℕ} →
    (E : ∀ j, GridDiagram (p j + 1)) → (hE : ∀ j : Fin M, (E j.succ).X 0 = 0) →
    (ht : ∀ j, TriplyPrepared (E j)) → (l : Fin (M + 1)) → (j : ℕ) → j < p l →
      gridRowVal (seamChainGrid M E hE).O (seamChainOffset p l + j) =
          seamChainOffset p l + gridRowVal (E l).O j ∧
        gridRowVal (seamChainGrid M E hE).X (seamChainOffset p l + j) =
          seamChainOffset p l + gridRowVal (E l).X j
  | 0, p, E, hE, ht, l, j, hj => by
    obtain rfl : l = 0 := Fin.ext (Nat.lt_one_iff.mp l.isLt)
    simp only [seamChainOffset, Fin.val_zero, Finset.univ_eq_empty, Finset.sum_empty,
      Nat.zero_add]
    exact ⟨rfl, rfl⟩
  | M + 1, p, E, hE, ht, l, j, hj => by
    have hT := seamChainGrid_succ_of_X_last M E hE fun j => (ht j).2.2
    have hO : ∀ k, gridRowVal (seamChainGrid (M + 1) E hE).O k =
        gridRowVal (seamState (seamChainGrid M (fun j => E j.castSucc)
          (fun j => hE j.castSucc)).O (E (Fin.last (M + 1))).O) k := by
      intro k
      rw [hT]
      rfl
    have hX : ∀ k, gridRowVal (seamChainGrid (M + 1) E hE).X k =
        gridRowVal (seamState (seamChainGrid M (fun j => E j.castSucc)
          (fun j => hE j.castSucc)).X (E (Fin.last (M + 1))).X) k := by
      intro k
      rw [hT]
      rfl
    rw [hO, hX, gridRowVal_seamState, gridRowVal_seamState]
    induction l using Fin.lastCases with
    | last =>
      rw [seamChainOffset_last]
      have hO := gridRowVal_ne_zero_of_O_last (ht (Fin.last (M + 1))).2.1 hj
      have hX := gridRowVal_last_of_X_last (seamChainGrid_X_last M (fun j => E j.castSucc)
        (fun j => hE j.castSucc) fun j => (ht j.castSucc).2.2)
      constructor
      · rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left, if_neg hO]
      · rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
        split_ifs with h
        · rw [hX, h]
          rfl
        · rfl
    | cast l =>
      rw [seamChainOffset_castSucc]
      have hle := seamChainOffset_add_le M (fun i => p i.castSucc) l
      have ih := seamChainGrid_gridRowVal M (fun j => E j.castSucc) (fun j => hE j.castSucc)
        (fun j => ht j.castSucc) l j hj
      have hlt : seamChainOffset (fun i => p i.castSucc) l + j <
          seamChainSize M (fun i => p i.castSucc) := by
        change j < p l.castSucc at hj
        omega
      rw [if_pos hlt, if_pos hlt]
      exact ih

end OnLeConjecture.KnotFloer.GridFull
