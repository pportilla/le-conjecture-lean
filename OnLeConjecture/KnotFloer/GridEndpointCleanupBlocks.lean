/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorSimpleFactor

/-!
# Four-mark blocks at arbitrary positions and the binary seam

This file treats the auxiliary `2 × 2` blocks of the cleanup of the scissor endpoint in the
written proof of Statement E (`statement_E_complete_proof.tex`, Section 10, last paragraphs of
"The invariant under marked inverse-pair cancellation").

For a grid diagram `G` of size `n` and positions `c, q ≤ n`, `blockInsert G c q` is the grid of
size `n + 2` obtained by inserting two columns before column `c` and two rows before row `q`,
with `O` markings at `(c, q)` and `(c + 1, q + 1)` and `X` markings at `(c, q + 1)` and
`(c + 1, q)`. A four-mark insertion (`IsFourMarkInsertion`) at the column `c` is the block
insertion at the position `(c, X_G(c))` (`isFourMarkInsertion_iff_blockInsert`).

In the natural-number coordinates `gridRowVal` a block insertion shifts the rows from `q` on by
two and the columns from `c` on by two (`gridRowVal_blockInsert_O`, `gridRowVal_blockInsert_X`).
A block inserted in the first factor of a binary seam, at a position not after its last column
and not above its last row, is a block of the seam at the same position
(`connectedSumSeamGrid_blockInsert_left`). A block inserted in the second factor, at a position
after its first column and above its first row and not after its last column, is a block of the
seam at the shifted position (`connectedSumSeamGrid_blockInsert_right`).

A *frame tower* (`FrameTower`) is a sequence of block insertions at positions that keep the first
column, the first row, the last column and the last row of the grid. Frame towers preserve triple
preparation (`FrameTower.triplyPrepared`), compose (`FrameTower.trans`), and pass through both
sides of a binary seam (`FrameTower.seam_left`, `FrameTower.seam_right`) and through seam chains
(`FrameTower.seamChain`). The *canonical stack* (`CanonStack`) inserts the blocks diagonally at the
origin; it passes through the left side of seams and seam chains (`CanonStack.seam_left`,
`CanonStack.seamChain`) and is a four-mark tower at the column `0` when `X_G(0) = 0`
(`CanonStack.fourMarkTower`). All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

/-! ### Natural-number coordinates -/

/-- The new row of an old row `v` after two rows are inserted at position `q`. -/
def blockShift (q v : ℕ) : ℕ := if v < q then v else v + 2

/-- The old column of a new column `k` after two columns are inserted at position `c`. -/
def blockBack (c k : ℕ) : ℕ := if k < c then k else k - 2

/-- Natural-number coordinates of a grid state with two rows exchanged. -/
theorem gridRowVal_swapRows_endpoint {N : ℕ} (x : GridState N) (a b : Fin N) (k : ℕ) :
    gridRowVal (x.swapRows a b) k =
      if k < N then
        (if gridRowVal x k = a.val then b.val
        else if gridRowVal x k = b.val then a.val else gridRowVal x k)
      else 0 := by
  by_cases hk : k < N
  · rw [if_pos hk, gridRowVal_mk _ _ hk, gridRowVal_mk _ _ hk, GridState.swapRows_apply,
      Equiv.swap_apply_def]
    by_cases h1 : x ⟨k, hk⟩ = a
    · rw [if_pos h1, if_pos (congrArg Fin.val h1)]
    · rw [if_neg h1, if_neg (fun h => h1 (Fin.ext h))]
      by_cases h2 : x ⟨k, hk⟩ = b
      · rw [if_pos h2, if_pos (congrArg Fin.val h2)]
      · rw [if_neg h2, if_neg (fun h => h2 (Fin.ext h))]
  · rw [if_neg hk]
    simp [gridRowVal, hk]

/-! ### Block insertion and the seam formula on natural numbers -/

/-- The seam formula `gridRowVal_seamState` for functions on natural numbers. -/
def seamFun (f g : ℕ → ℕ) (n m k : ℕ) : ℕ :=
  if k < n then f k else if k < n + m + 1 then (if g (k - n) = 0 then f n else n + g (k - n))
  else 0

/-- The block insertion formula for functions on natural numbers, with the values `u` and `v` in
the two new columns. -/
def blockFun (f : ℕ → ℕ) (N c q u v k : ℕ) : ℕ :=
  if k = c then u else if k = c + 1 then v
  else if k < N + 2 then blockShift q (f (blockBack c k)) else 0

/-- A block in the first factor of a seam, on natural numbers. -/
theorem seamFun_blockFun_left (f g : ℕ → ℕ) {a b c q u v k : ℕ} (hc : c ≤ a) (hq : q ≤ a) :
    seamFun (blockFun f (a + 1) c q u v) g (a + 2) b k =
      blockFun (seamFun f g a b) (a + b + 1) c q u v k := by
  unfold seamFun blockFun
  by_cases h1 : k < a + 2
  · simp only [if_pos h1]
    by_cases hk0 : k = c
    · simp only [if_pos hk0]
    · simp only [if_neg hk0]
      by_cases hk1 : k = c + 1
      · simp only [if_pos hk1]
      · have hbb : blockBack c k < a := by unfold blockBack; split_ifs <;> omega
        simp only [if_neg hk1, if_pos (show k < a + 1 + 2 by omega),
          if_pos (show k < a + b + 1 + 2 by omega), if_pos hbb]
  · have hbb : blockBack c k = k - 2 := by unfold blockBack; split_ifs <;> omega
    have hbb2 : blockBack c (a + 2) = a := by unfold blockBack; split_ifs <;> omega
    simp only [if_neg h1, if_neg (show k ≠ c by omega), if_neg (show k ≠ c + 1 by omega), hbb,
      if_neg (show a + 2 ≠ c by omega), if_neg (show a + 2 ≠ c + 1 by omega),
      if_pos (show a + 2 < a + 1 + 2 by omega), hbb2, if_neg (show ¬ k - 2 < a by omega)]
    by_cases h2 : k < a + 2 + b + 1
    · simp only [if_pos h2, if_pos (show k < a + b + 1 + 2 by omega),
        if_pos (show k - 2 < a + b + 1 by omega), show k - 2 - a = k - (a + 2) by omega]
      split_ifs with h3
      · rfl
      · unfold blockShift
        rw [if_neg (by omega)]
        omega
    · simp only [if_neg h2, if_neg (show ¬ k < a + b + 1 + 2 by omega)]

/-- A block in the second factor of a seam, on natural numbers. -/
theorem seamFun_blockFun_right (f g : ℕ → ℕ) {a b c q u v k : ℕ} (hc : 1 ≤ c) (hcb : c ≤ b)
    (hq : 1 ≤ q) (hu : 1 ≤ u) (hv : 1 ≤ v) (hf : ∀ j, f j ≤ a) :
    seamFun f (blockFun g (b + 1) c q u v) a (b + 2) k =
      blockFun (seamFun f g a b) (a + b + 1) (a + c) (a + q) (a + u) (a + v) k := by
  unfold seamFun blockFun
  by_cases h0 : k < a
  · have hbb : blockBack (a + c) k = k := by unfold blockBack; split_ifs <;> omega
    have := hf k
    simp only [if_pos h0, if_neg (show k ≠ a + c by omega),
      if_neg (show k ≠ a + c + 1 by omega), if_pos (show k < a + b + 1 + 2 by omega), hbb]
    unfold blockShift
    rw [if_pos (by omega)]
  · simp only [if_neg h0]
    by_cases hk0 : k = a + c
    · simp only [if_pos hk0, show k - a = c by omega, if_pos (show k < a + (b + 2) + 1 by omega),
        ↓reduceIte, if_neg (show u ≠ 0 by omega)]
    · by_cases hk1 : k = a + c + 1
      · simp only [if_neg hk0, if_pos hk1, show k - a = c + 1 by omega,
          if_neg (show c + 1 ≠ c by omega), if_pos (show k < a + (b + 2) + 1 by omega),
          ↓reduceIte, if_neg (show v ≠ 0 by omega)]
      · simp only [if_neg hk0, if_neg hk1, if_neg (show k - a ≠ c by omega),
          if_neg (show k - a ≠ c + 1 by omega)]
        by_cases h2 : k < a + (b + 2) + 1
        · have hbb : blockBack (a + c) k = a + blockBack c (k - a) := by
            unfold blockBack; split_ifs <;> omega
          have hbl : blockBack c (k - a) ≤ b := by unfold blockBack; split_ifs <;> omega
          have hfa := hf a
          generalize blockBack c (k - a) = w at hbb hbl
          simp only [if_pos h2, if_pos (show k - a < b + 1 + 2 by omega),
            if_pos (show k < a + b + 1 + 2 by omega), hbb, if_neg (show ¬ a + w < a by omega),
            if_pos (show a + w < a + b + 1 by omega), Nat.add_sub_cancel_left]
          by_cases hg : g w = 0
          · have e1 : blockShift q (g w) = 0 := by
              unfold blockShift; rw [if_pos (by omega)]; exact hg
            have e2 : blockShift (a + q) (f a) = f a := by unfold blockShift; rw [if_pos (by omega)]
            rw [if_pos e1, if_pos hg, e2]
          · have e1 : blockShift q (g w) ≠ 0 := by unfold blockShift; split_ifs <;> omega
            rw [if_neg e1, if_neg hg]
            unfold blockShift
            split_ifs <;> omega
        · simp only [if_neg h2, if_neg (show ¬ k < a + b + 1 + 2 by omega)]

/-! ### Block insertion -/

section BlockInsert

variable {n : ℕ}

/-- The `O` state after a block insertion at the position `(c, q)`. -/
def blockInsertO (x : GridState n) (c q : Fin (n + 1)) : GridState (n + 2) :=
  (x.insertPoint c q).insertPoint c.succ q.succ

/-- The `X` state after a block insertion at the position `(c, q)`. -/
def blockInsertX (x : GridState n) (c q : Fin (n + 1)) : GridState (n + 2) :=
  ((x.insertPoint c q).insertPoint c.succ q.succ).swapRows q.castSucc q.succ

/-- Natural-number coordinates of the double point insertion. -/
theorem gridRowVal_blockInsertO (x : GridState n) (c q : Fin (n + 1)) (k : ℕ) :
    gridRowVal (blockInsertO x c q) k =
      if k = c.val then q.val else if k = c.val + 1 then q.val + 1
      else if k < n + 2 then blockShift q.val (gridRowVal x (blockBack c.val k)) else 0 := by
  have hc := c.isLt
  unfold blockInsertO
  rw [gridRowVal_insertPoint]
  simp only [Fin.val_succ]
  by_cases h0 : k = c.val
  · subst h0
    rw [if_neg (by omega), if_pos (by omega), gridRowVal_insertPoint, if_pos rfl]
    · simp [natPredAbove, natSuccAbove]
  · by_cases h1 : k = c.val + 1
    · rw [if_pos h1, if_neg h0, if_pos h1]
    · rw [if_neg h1, if_neg h0, if_neg h1]
      by_cases hk : k < n + 1 + 1
      · rw [if_pos hk, if_pos (by omega), gridRowVal_insertPoint]
        have e : natPredAbove (c.val + 1) k ≠ c.val := by
          unfold natPredAbove; split_ifs <;> omega
        rw [if_neg e, if_pos (by unfold natPredAbove; split_ifs <;> omega)]
        have e2 : natPredAbove c.val (natPredAbove (c.val + 1) k) = blockBack c.val k := by
          unfold natPredAbove blockBack; split_ifs <;> omega
        rw [e2]
        unfold natSuccAbove blockShift
        split_ifs <;> omega
      · rw [if_neg hk, if_neg (by omega)]

/-- Natural-number coordinates of the `X` state after a block insertion. -/
theorem gridRowVal_blockInsertX (x : GridState n) (c q : Fin (n + 1)) (k : ℕ) :
    gridRowVal (blockInsertX x c q) k =
      if k = c.val then q.val + 1 else if k = c.val + 1 then q.val
      else if k < n + 2 then blockShift q.val (gridRowVal x (blockBack c.val k)) else 0 := by
  have hc := c.isLt
  unfold blockInsertX
  rw [gridRowVal_swapRows_endpoint]
  change (if k < n + 2 then
    (if gridRowVal (blockInsertO x c q) k = q.val then q.val + 1
    else if gridRowVal (blockInsertO x c q) k = q.val + 1 then q.val
    else gridRowVal (blockInsertO x c q) k) else 0) = _
  rw [gridRowVal_blockInsertO]
  unfold blockShift
  split_ifs <;> omega

/-- **Block insertion.** Two columns are inserted before column `c` and two rows before row `q`;
the block carries `O` markings at `(c, q)` and `(c + 1, q + 1)` and `X` markings at `(c, q + 1)`
and `(c + 1, q)`. -/
def blockInsert (G : GridDiagram n) (c q : Fin (n + 1)) : GridDiagram (n + 2) where
  O := blockInsertO G.O c q
  X := blockInsertX G.X c q
  disjoint k h := by
    have h' := congrArg Fin.val h
    have hO := gridRowVal_blockInsertO G.O c q k.val
    have hX := gridRowVal_blockInsertX G.X c q k.val
    rw [gridRowVal_val] at hO hX
    rw [hO, hX] at h'
    have hk := k.isLt
    by_cases h0 : k.val = c.val
    · simp [h0] at h'
    · by_cases h1 : k.val = c.val + 1
      · simp [h1] at h'
      · rw [if_neg h0, if_neg h1, if_pos hk, if_neg h0, if_neg h1, if_pos hk] at h'
        have hb : blockBack c.val k.val < n := by
          have := c.isLt; unfold blockBack; split_ifs <;> omega
        have hd := G.disjoint ⟨_, hb⟩
        rw [gridRowVal_mk _ _ hb, gridRowVal_mk _ _ hb] at h'
        apply hd
        apply Fin.ext
        unfold blockShift at h'
        split_ifs at h' <;> omega

theorem gridRowVal_blockInsert_O (G : GridDiagram n) (c q : Fin (n + 1)) (k : ℕ) :
    gridRowVal (blockInsert G c q).O k =
      if k = c.val then q.val else if k = c.val + 1 then q.val + 1
      else if k < n + 2 then blockShift q.val (gridRowVal G.O (blockBack c.val k)) else 0 :=
  gridRowVal_blockInsertO G.O c q k

theorem gridRowVal_blockInsert_X (G : GridDiagram n) (c q : Fin (n + 1)) (k : ℕ) :
    gridRowVal (blockInsert G c q).X k =
      if k = c.val then q.val + 1 else if k = c.val + 1 then q.val
      else if k < n + 2 then blockShift q.val (gridRowVal G.X (blockBack c.val k)) else 0 :=
  gridRowVal_blockInsertX G.X c q k

theorem gridRowVal_blockInsert_O_eq (G : GridDiagram n) (c q : Fin (n + 1)) :
    gridRowVal (blockInsert G c q).O =
      blockFun (gridRowVal G.O) n c.val q.val q.val (q.val + 1) :=
  funext (gridRowVal_blockInsert_O G c q)

theorem gridRowVal_blockInsert_X_eq (G : GridDiagram n) (c q : Fin (n + 1)) :
    gridRowVal (blockInsert G c q).X =
      blockFun (gridRowVal G.X) n c.val q.val (q.val + 1) q.val :=
  funext (gridRowVal_blockInsert_X G c q)

end BlockInsert

/-! ### Grid diagrams that agree as elements of `Σ k, GridDiagram k` -/

/-- Grids with equal coordinates are equal. -/
theorem gridDiagram_ext_gridRowVal {N : ℕ} {G G' : GridDiagram N}
    (hO : ∀ k < N, gridRowVal G.O k = gridRowVal G'.O k)
    (hX : ∀ k < N, gridRowVal G.X k = gridRowVal G'.X k) : G = G' := by
  ext1
  · exact gridState_ext_gridRowVal hO
  · exact gridState_ext_gridRowVal hX

/-! ### Block insertions and the binary seam -/

section Seam

variable {a b : ℕ} (A : GridDiagram (a + 1)) (B : GridDiagram (b + 1))

/-- A block inserted at a position not after the last column and not above the last row keeps
the `X` marking of the last column in the last row. -/
theorem blockInsert_X_last (hA : A.X (Fin.last a) = Fin.last a) {c q : ℕ} (hc : c ≤ a)
    (hq : q ≤ a) :
    (blockInsert A ⟨c, by omega⟩ ⟨q, by omega⟩).X (Fin.last (a + 2)) = Fin.last (a + 2) := by
  have h := gridRowVal_last_of_X_last hA
  have hbb : blockBack c (a + 2) = a := by unfold blockBack; split_ifs <;> omega
  have h1 : gridRowVal (blockInsert A ⟨c, by omega⟩ ⟨q, by omega⟩).X (a + 2) = a + 2 := by
    rw [gridRowVal_blockInsert_X]
    simp only [hbb, h]
    unfold blockShift
    split_ifs <;> omega
  apply Fin.ext
  have h2 := gridRowVal_val (blockInsert A ⟨c, by omega⟩ ⟨q, by omega⟩).X (Fin.last (a + 2))
  simp only [Fin.val_last] at h2 ⊢
  rw [← h2, h1]

/-- A block inserted after the first column and above the first row keeps the `X` marking of the
first column in the first row. -/
theorem blockInsert_X_zero (hB : B.X 0 = 0) {c q : ℕ} (hc : 1 ≤ c) (hcb : c ≤ b + 1)
    (hq : 1 ≤ q) (hqb : q ≤ b + 1) :
    (blockInsert B ⟨c, by omega⟩ ⟨q, by omega⟩).X 0 = 0 := by
  have h : gridRowVal B.X 0 = 0 := by
    have := gridRowVal_val B.X 0
    rw [hB] at this
    simpa using this
  have hbb : blockBack c 0 = 0 := by unfold blockBack; split_ifs <;> omega
  have h1 : gridRowVal (blockInsert B ⟨c, by omega⟩ ⟨q, by omega⟩).X 0 = 0 := by
    rw [gridRowVal_blockInsert_X]
    change (if (0 : ℕ) = c then q + 1 else if (0 : ℕ) = c + 1 then q
      else if (0 : ℕ) < b + 1 + 2 then blockShift q (gridRowVal B.X (blockBack c 0)) else 0) = 0
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), hbb, h]
    unfold blockShift
    rw [if_pos (by omega)]
  apply Fin.ext
  have h2 := gridRowVal_val (blockInsert B ⟨c, by omega⟩ ⟨q, by omega⟩).X 0
  simp only [Fin.val_zero] at h2 ⊢
  rw [← h2, h1]

/-- A block inserted not after the last column and above the first row keeps the `O` marking of
the last column in the first row. -/
theorem blockInsert_O_last (hB : B.O (Fin.last b) = 0) {c q : ℕ} (hcb : c ≤ b) (hq : 1 ≤ q)
    (hqb : q ≤ b + 1) :
    (blockInsert B ⟨c, by omega⟩ ⟨q, by omega⟩).O (Fin.last (b + 2)) = 0 := by
  have h : gridRowVal B.O b = 0 := by
    have := gridRowVal_val B.O (Fin.last b)
    rw [hB] at this
    simpa using this
  have hbb : blockBack c (b + 2) = b := by unfold blockBack; split_ifs <;> omega
  have h1 : gridRowVal (blockInsert B ⟨c, by omega⟩ ⟨q, by omega⟩).O (b + 2) = 0 := by
    rw [gridRowVal_blockInsert_O]
    simp only [hbb, h]
    unfold blockShift
    split_ifs <;> omega
  apply Fin.ext
  have h2 := gridRowVal_val (blockInsert B ⟨c, by omega⟩ ⟨q, by omega⟩).O (Fin.last (b + 2))
  simp only [Fin.val_last, Fin.val_zero] at h2 ⊢
  rw [← h2, h1]

theorem gridRowVal_seam_O (hA : A.X (Fin.last a) = Fin.last a) (hB : B.X 0 = 0) :
    gridRowVal (connectedSumSeamGrid A B hA hB).O =
      seamFun (gridRowVal A.O) (gridRowVal B.O) a b :=
  funext (gridRowVal_seamState A.O B.O)

theorem gridRowVal_seam_X (hA : A.X (Fin.last a) = Fin.last a) (hB : B.X 0 = 0) :
    gridRowVal (connectedSumSeamGrid A B hA hB).X =
      seamFun (gridRowVal A.X) (gridRowVal B.X) a b :=
  funext (gridRowVal_seamState A.X B.X)

/-- **A block in the first factor of a seam.** -/
theorem connectedSumSeamGrid_blockInsert_left (hA : A.X (Fin.last a) = Fin.last a)
    (hB : B.X 0 = 0) {c q : ℕ} (hc : c ≤ a) (hq : q ≤ a) :
    connectedSumSeamGrid (blockInsert A ⟨c, by omega⟩ ⟨q, by omega⟩) B
        (blockInsert_X_last A hA hc hq) hB =
      gridCast (by omega)
        (blockInsert (connectedSumSeamGrid A B hA hB) ⟨c, by omega⟩ ⟨q, by omega⟩) := by
  apply gridDiagram_ext_gridRowVal
  · intro k _
    rw [gridRowVal_gridCast_O, gridRowVal_seam_O, gridRowVal_blockInsert_O_eq,
      gridRowVal_blockInsert_O_eq, gridRowVal_seam_O]
    exact seamFun_blockFun_left _ _ hc hq
  · intro k _
    rw [gridRowVal_gridCast_X, gridRowVal_seam_X, gridRowVal_blockInsert_X_eq,
      gridRowVal_blockInsert_X_eq, gridRowVal_seam_X]
    exact seamFun_blockFun_left _ _ hc hq

/-- **A block in the second factor of a seam.** -/
theorem connectedSumSeamGrid_blockInsert_right (hA : A.X (Fin.last a) = Fin.last a)
    (hB : B.X 0 = 0) {c q : ℕ} (hc : 1 ≤ c) (hcb : c ≤ b) (hq : 1 ≤ q) (hqb : q ≤ b) :
    connectedSumSeamGrid A (blockInsert B ⟨c, by omega⟩ ⟨q, by omega⟩) hA
        (blockInsert_X_zero B hB hc (by omega) hq (by omega)) =
      gridCast (by omega)
        (blockInsert (connectedSumSeamGrid A B hA hB) ⟨a + c, by omega⟩
          ⟨a + q, by omega⟩) := by
  have hAX := gridRowVal_last_of_X_last hA
  apply gridDiagram_ext_gridRowVal
  · intro k _
    rw [gridRowVal_gridCast_O, gridRowVal_seam_O, gridRowVal_blockInsert_O_eq,
      gridRowVal_blockInsert_O_eq, gridRowVal_seam_O]
    exact seamFun_blockFun_right _ _ hc hcb hq (by omega) (by omega)
      (fun j => by have := gridRowVal_lt A.O j; omega)
  · intro k _
    rw [gridRowVal_gridCast_X, gridRowVal_seam_X, gridRowVal_blockInsert_X_eq,
      gridRowVal_blockInsert_X_eq, gridRowVal_seam_X]
    exact seamFun_blockFun_right _ _ hc hcb hq (by omega) (by omega)
      (fun j => by have := gridRowVal_lt A.X j; omega)

end Seam


/-! ### Frame towers -/

/-- **Frame towers.** A sequence of `k` block insertions into `T`, each at a position after the
first column and the first row and not after the last column and the last row. -/
inductive FrameTower {a : ℕ} (T : GridDiagram (a + 1)) : ℕ → {b : ℕ} → GridDiagram (b + 1) → Prop
  | base : FrameTower T 0 T
  | insert {k b : ℕ} {G : GridDiagram (b + 1)} (h : FrameTower T k G) (c q : ℕ) (hc : 1 ≤ c)
      (hcb : c ≤ b) (hq : 1 ≤ q) (hqb : q ≤ b) :
      FrameTower T (k + 1) (b := b + 2) (blockInsert G ⟨c, by omega⟩ ⟨q, by omega⟩)

/-- Block insertions at frame positions preserve triple preparation. -/
theorem triplyPrepared_blockInsert {b : ℕ} {G : GridDiagram (b + 1)} (hG : TriplyPrepared G)
    {c q : ℕ} (hc : 1 ≤ c) (hcb : c ≤ b) (hq : 1 ≤ q) (hqb : q ≤ b) :
    TriplyPrepared (blockInsert G ⟨c, by omega⟩ ⟨q, by omega⟩) :=
  ⟨blockInsert_X_zero G hG.1 hc (by omega) hq (by omega), blockInsert_O_last G hG.2.1 hcb hq
    (by omega), blockInsert_X_last G hG.2.2 hcb hqb⟩

namespace FrameTower

variable {a : ℕ} {T : GridDiagram (a + 1)}

/-- A frame tower over a triply prepared grid is triply prepared. -/
theorem triplyPrepared (hT : TriplyPrepared T) {k b : ℕ} {G : GridDiagram (b + 1)}
    (h : FrameTower T k G) : TriplyPrepared G := by
  induction h with
  | base => exact hT
  | insert _ c q hc hcb hq hqb ih => exact triplyPrepared_blockInsert ih hc hcb hq hqb

/-- Frame towers compose. -/
theorem trans {k b : ℕ} {G : GridDiagram (b + 1)} (h : FrameTower T k G) {k' b' : ℕ}
    {G' : GridDiagram (b' + 1)} (h' : FrameTower G k' G') : FrameTower T (k + k') G' := by
  induction h' with
  | base => exact h
  | insert _ c q hc hcb hq hqb ih => exact ih.insert c q hc hcb hq hqb

/-- Frame towers are invariant under the transport `gridCast`. -/
theorem gridCast {k b b' : ℕ} {G : GridDiagram (b + 1)} (h : FrameTower T k G)
    (e : b + 1 = b' + 1) : FrameTower T k (GridFull.gridCast e G) := by
  obtain rfl : b = b' := by omega
  exact h

/-- **Frame towers in the first factor of a seam.** -/
theorem seam_left (hT : TriplyPrepared T) {k b : ℕ} {G : GridDiagram (b + 1)}
    (h : FrameTower T k G) {m : ℕ} (B : GridDiagram (m + 1)) (hB : B.X 0 = 0) :
    FrameTower (connectedSumSeamGrid T B hT.2.2 hB) k
      (connectedSumSeamGrid G B (h.triplyPrepared hT).2.2 hB) := by
  induction h with
  | base => exact base
  | insert h' c q hc hcb hq hqb ih =>
    have hG := (h'.triplyPrepared hT).2.2
    rw [connectedSumSeamGrid_blockInsert_left _ B hG hB hcb hqb]
    exact (ih.insert c q hc (by omega) hq (by omega)).gridCast _

/-- **Frame towers in the second factor of a seam.** -/
theorem seam_right (hT : TriplyPrepared T) {k b : ℕ} {G : GridDiagram (b + 1)}
    (h : FrameTower T k G) {m : ℕ} (A : GridDiagram (m + 1))
    (hA : A.X (Fin.last m) = Fin.last m) :
    FrameTower (connectedSumSeamGrid A T hA hT.1) k
      (connectedSumSeamGrid A G hA (h.triplyPrepared hT).1) := by
  induction h with
  | base => exact base
  | insert h' c q hc hcb hq hqb ih =>
    have hG := (h'.triplyPrepared hT).1
    rw [connectedSumSeamGrid_blockInsert_right A _ hA hG hc hcb hq hqb]
    exact (ih.insert (m + c) (m + q) (by omega) (by omega) (by omega) (by omega)).gridCast _

end FrameTower

/-- **Frame towers in seam chains.** If every factor of a triply prepared family `E` is a frame
tower over the corresponding factor of a triply prepared family `P`, then the seam chain of `E`
is a frame tower over the seam chain of `P`, with the total number of blocks. -/
theorem FrameTower.seamChain : (M : ℕ) → {p p' : Fin (M + 1) → ℕ} →
    (P : ∀ j, GridDiagram (p j + 1)) → (E : ∀ j, GridDiagram (p' j + 1)) →
    (hP : ∀ j, TriplyPrepared (P j)) → (hE : ∀ j, TriplyPrepared (E j)) →
    (k : Fin (M + 1) → ℕ) → (∀ j, FrameTower (P j) (k j) (E j)) →
    FrameTower (seamChainGrid M P fun j => (hP j.succ).1) (∑ j, k j)
      (seamChainGrid M E fun j => (hE j.succ).1)
  | 0, _, _, P, E, hP, hE, k, h => by
    rw [Fin.sum_univ_one]
    exact h 0
  | M + 1, _, _, P, E, hP, hE, k, h => by
    rw [seamChainGrid_succ_of_triplyPrepared M P _ hP,
      seamChainGrid_succ_of_triplyPrepared M E _ hE, Fin.sum_univ_castSucc]
    have ih := FrameTower.seamChain M (fun j => P j.castSucc) (fun j => E j.castSucc)
      (fun j => hP j.castSucc) (fun j => hE j.castSucc) (fun j => k j.castSucc)
      (fun j => h j.castSucc)
    have hPt := seamChainGrid_triplyPrepared M (fun j => P j.castSucc)
      (fun j => (hP j.castSucc.succ).1) fun j => hP j.castSucc
    have h1 := ih.seam_left hPt (P (Fin.last (M + 1))) (hP _).1
    have h2 := (h (Fin.last (M + 1))).seam_right (hP _)
      (seamChainGrid M (fun j => E j.castSucc) fun j => (hE j.castSucc.succ).1)
      (ih.triplyPrepared hPt).2.2
    exact FrameTower.trans h1 h2

/-! ### The canonical stack -/

/-- **The canonical stack.** The blocks are inserted at the origin, one after the other, so that
the `t`-th block occupies the columns and rows `2 t` and `2 t + 1`. -/
inductive CanonStack {a : ℕ} (T : GridDiagram (a + 1)) : ℕ → {b : ℕ} → GridDiagram (b + 1) → Prop
  | base : CanonStack T 0 T
  | insert {k b : ℕ} {G : GridDiagram (b + 1)} (h : CanonStack T k G) (hk : 2 * k ≤ b) :
      CanonStack T (k + 1) (b := b + 2) (blockInsert G ⟨2 * k, by omega⟩ ⟨2 * k, by omega⟩)

namespace CanonStack

variable {a : ℕ} {T : GridDiagram (a + 1)}

theorem size {k b : ℕ} {G : GridDiagram (b + 1)} (h : CanonStack T k G) : b = a + 2 * k := by
  induction h with
  | base => rfl
  | insert _ _ ih => omega

/-- Every number of blocks has a canonical stack. -/
theorem exists_canonStack (T : GridDiagram (a + 1)) (k : ℕ) :
    ∃ (b : ℕ) (G : GridDiagram (b + 1)), CanonStack T k G := by
  induction k with
  | zero => exact ⟨a, T, base⟩
  | succ k ih =>
    obtain ⟨b, G, h⟩ := ih
    exact ⟨b + 2, _, h.insert (by have := h.size; omega)⟩

/-- The canonical stack is unique. -/
theorem unique {k b b' : ℕ} {G : GridDiagram (b + 1)} {G' : GridDiagram (b' + 1)}
    (h : CanonStack T k G) (h' : CanonStack T k G') :
    (⟨b + 1, G⟩ : Σ n, GridDiagram n) = ⟨b' + 1, G'⟩ := by
  induction h generalizing b' with
  | base =>
    cases h'
    rfl
  | insert h₁ hk ih =>
    cases h' with
    | insert h₂ hk' =>
      have e := ih h₂
      obtain ⟨hb, hG⟩ := Sigma.mk.inj_iff.mp e
      have hb' : _ = _ := Nat.succ.inj hb
      subst hb'
      obtain rfl := eq_of_heq hG
      rfl

/-- A canonical stack over a grid with its last `X` marking in the last row has the same
property. -/
theorem X_last (hT : T.X (Fin.last a) = Fin.last a) {k b : ℕ} {G : GridDiagram (b + 1)}
    (h : CanonStack T k G) : G.X (Fin.last b) = Fin.last b := by
  induction h with
  | base => exact hT
  | insert h' hk ih =>
    have := h'.size
    exact blockInsert_X_last _ ih (by omega) (by omega)

/-- Canonical stacks are invariant under the transport `gridCast`. -/
theorem gridCast {k b b' : ℕ} {G : GridDiagram (b + 1)} (h : CanonStack T k G)
    (e : b + 1 = b' + 1) : CanonStack T k (GridFull.gridCast e G) := by
  obtain rfl : b = b' := by omega
  exact h

/-- **Canonical stacks in the first factor of a seam.** -/
theorem seam_left (hT : T.X (Fin.last a) = Fin.last a) {k b : ℕ} {G : GridDiagram (b + 1)}
    (h : CanonStack T k G) {m : ℕ} (B : GridDiagram (m + 1)) (hB : B.X 0 = 0) :
    CanonStack (connectedSumSeamGrid T B hT hB) k (connectedSumSeamGrid G B (h.X_last hT) hB) := by
  induction h with
  | base => exact base
  | insert h' hk ih =>
    have hG := h'.X_last hT
    have := h'.size
    rw [connectedSumSeamGrid_blockInsert_left _ B hG hB (by omega) (by omega)]
    exact (ih.insert (by omega)).gridCast _

end CanonStack

end OnLeConjecture.KnotFloer.GridFull
