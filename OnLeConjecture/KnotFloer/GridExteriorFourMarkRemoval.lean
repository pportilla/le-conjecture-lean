/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorScissorSteps
public import OnLeConjecture.KnotFloer.GridExteriorAuxiliaryPair
public import OnLeConjecture.KnotFloer.GridExteriorSimpleFactor

/-!
# Removal of a four-mark block: the marking identities

Let `G` be a grid diagram of size `n`, let `c` be a column and put `q = X_G(c)`. A four-mark
insertion `K` of `G` at `c` (`IsFourMarkInsertion`, `GridExteriorScissorSteps`) carries an unknot
block in the columns `c, c + 1` and the rows `q, q + 1`, with `O` markings on the diagonal
`(c, q), (c + 1, q + 1)` and `X` markings on the antidiagonal.

Exchanging the `O` markings of the columns `c` and `c + 1` of `K` produces the `O` markings of the
double stabilization `A₂ = A₁.stabilizeX c c₁ c`, where `A₁ = G.stabilizeX c q c` and
`c₁ = X_{A₁}(c) = q + 1` (`fourMarkStabTwo_O_eq_swapColumns`). Both stabilizations are of the
south-west corner type of `GridStabilizationCornerMaps`. Consequently the block can be removed by
the `O` switch map of `K` at the column `c`, the derivatives of `A₂` at the two block columns and
the canonical destabilization maps of `A₂` and `A₁` (`GridExteriorFourMarkMap`). The colour
naturality of the destabilization maps is proved in `GridStabilizationColourNatural`.

After the switch, the two `O` markings of the block coincide with its two `X` markings. The
auxiliary pair `fourMarkSwitchPair` with the `O` markings of `A₂` and the `X` markings of `K`
records this intermediate stage of the written proof of Statement E
(`statement_E_complete_proof.tex`, Proposition `fourMarkBlockCollapse`).
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ} (G : GridDiagram n) (c : Fin n)

/-- The first south-west stabilization `A₁ = G.stabilizeX c q c`, with `q = X_G(c)`. -/
def fourMarkStabOne : GridDiagram (n + 1) :=
  G.stabilizeX c.castSucc (G.X c).castSucc c

theorem fourMarkStabOne_X_castSucc : (fourMarkStabOne G c).X c.castSucc = (G.X c).succ := by
  rw [fourMarkStabOne, GridDiagram.stabilizeX_X, GridState.splitPoint_apply_newColumn]
  ext
  simp [Fin.succAbove]

/-- The second south-west stabilization `A₂`, at the new column `c` of `A₁`. -/
def fourMarkStabTwo : GridDiagram (n + 2) :=
  (fourMarkStabOne G c).stabilizeX c.castSucc.castSucc
    ((fourMarkStabOne G c).X c.castSucc).castSucc c.castSucc

theorem fourMarkStabTwo_O :
    (fourMarkStabTwo G c).O =
      (G.O.insertPoint c.castSucc (G.X c).castSucc).insertPoint c.castSucc.castSucc
        (G.X c).succ.castSucc := by
  rw [fourMarkStabTwo, GridDiagram.stabilizeX_O, fourMarkStabOne_X_castSucc, fourMarkStabOne,
    GridDiagram.stabilizeX_O]

/-- The column `c + 1` of the enlarged grid is the cyclic successor of the column `c`. -/
theorem finRotate_castSucc_castSucc :
    finRotate (n + 2) c.castSucc.castSucc = c.castSucc.succ :=
  finRotate_castSucc_eq_succ c.castSucc

theorem gridRowVal_insertPoint_self {N : ℕ} (x : GridState N) (a b : Fin (N + 1)) :
    gridRowVal (x.insertPoint a b) a.val = b.val := by
  rw [gridRowVal_insertPoint, if_pos rfl]

theorem gridRowVal_insertPoint_of_lt {N : ℕ} (x : GridState N) (a b : Fin (N + 1)) {k : ℕ}
    (hk : k < a.val) :
    gridRowVal (x.insertPoint a b) k = natSuccAbove b.val (gridRowVal x k) := by
  have ha := a.isLt
  rw [gridRowVal_insertPoint, if_neg (by omega), if_pos (by omega), natPredAbove, if_pos hk]

theorem gridRowVal_insertPoint_of_gt {N : ℕ} (x : GridState N) (a b : Fin (N + 1)) {k : ℕ}
    (hk : a.val < k) (hkN : k < N + 1) :
    gridRowVal (x.insertPoint a b) k = natSuccAbove b.val (gridRowVal x (k - 1)) := by
  rw [gridRowVal_insertPoint, if_neg (by omega), if_pos hkN, natPredAbove, if_neg (by omega)]

/-- Natural-number coordinates of a column swap. -/
theorem gridRowVal_swapColumns {N : ℕ} (x : GridState N) (a b : Fin N) (k : ℕ) (hk : k < N) :
    gridRowVal (x.swapColumns a b) k =
      gridRowVal x (if k = a.val then b.val else if k = b.val then a.val else k) := by
  rw [gridRowVal_mk _ _ hk, GridState.swapColumns_apply, ← gridRowVal_val]
  congr 1
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2 h3 h4 h5 h6 <;> simp_all [Fin.ext_iff]

/-- Switching the two `O` markings of an inserted four-mark block gives the `O` markings of the
double south-west stabilization. -/
theorem fourMarkStabTwo_O_eq_swapColumns {K : GridDiagram (n + 2)}
    (hK : IsFourMarkInsertion G c K) :
    (fourMarkStabTwo G c).O =
      K.O.swapColumns c.castSucc.castSucc (finRotate (n + 2) c.castSucc.castSucc) := by
  rw [fourMarkStabTwo_O, hK.1, finRotate_castSucc_castSucc]
  apply gridState_ext_gridRowVal
  intro k hk
  rw [gridRowVal_swapColumns _ _ _ k hk]
  have hc := c.isLt
  simp only [Fin.val_castSucc, Fin.val_succ]
  rcases lt_trichotomy k c.val with hkc | rfl | hkc
  · rw [if_neg (by omega), if_neg (by omega),
      gridRowVal_insertPoint_of_lt _ _ _ (by simpa using hkc),
      gridRowVal_insertPoint_of_lt _ _ _ (by simpa using hkc),
      gridRowVal_insertPoint_of_lt _ _ _ (by simp; omega),
      gridRowVal_insertPoint_of_lt _ _ _ (by simpa using hkc)]
    simp
  · rw [if_pos rfl]
    have h1 := gridRowVal_insertPoint_self (G.O.insertPoint c.castSucc (G.X c).castSucc)
      c.castSucc.castSucc (G.X c).succ.castSucc
    have h2 := gridRowVal_insertPoint_self (G.O.insertPoint c.castSucc (G.X c).castSucc)
      c.castSucc.succ (G.X c).castSucc.succ
    simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
    rw [h1, h2]
  · set q := G.X c
    have hq := q.isLt
    have hin1 (j : ℕ) (hj : c.val < j) (hjn : j < n + 1) :
        gridRowVal (G.O.insertPoint c.castSucc q.castSucc) j =
          natSuccAbove q.val (gridRowVal G.O (j - 1)) := by
      have h := gridRowVal_insertPoint_of_gt G.O c.castSucc q.castSucc
        (show c.castSucc.val < j by simp only [Fin.val_castSucc]; omega) hjn
      simpa only [Fin.val_castSucc] using h
    have hin0 : gridRowVal (G.O.insertPoint c.castSucc q.castSucc) c.val = q.val := by
      have h := gridRowVal_insertPoint_self G.O c.castSucc q.castSucc
      simpa only [Fin.val_castSucc] using h
    rcases Nat.lt_or_ge (c.val + 1) k with hk1 | hk1
    · rw [if_neg (by omega), if_neg (by omega)]
      have hL := gridRowVal_insertPoint_of_gt (G.O.insertPoint c.castSucc q.castSucc)
        c.castSucc.castSucc q.succ.castSucc
        (show c.castSucc.castSucc.val < k by simp only [Fin.val_castSucc]; omega) hk
      have hR := gridRowVal_insertPoint_of_gt (G.O.insertPoint c.castSucc q.castSucc)
        c.castSucc.succ q.castSucc.succ
        (show c.castSucc.succ.val < k by simp only [Fin.val_castSucc, Fin.val_succ]; omega) hk
      rw [hL, hR, hin1 (k - 1) (by omega) (by omega)]
      simp only [Fin.val_castSucc, Fin.val_succ]
    · obtain rfl : k = c.val + 1 := by omega
      rw [if_neg (by omega), if_pos rfl]
      have hL := gridRowVal_insertPoint_of_gt (G.O.insertPoint c.castSucc q.castSucc)
        c.castSucc.castSucc q.succ.castSucc
        (show c.castSucc.castSucc.val < c.val + 1 by simp only [Fin.val_castSucc]; omega) hk
      have hR := gridRowVal_insertPoint_of_lt (G.O.insertPoint c.castSucc q.castSucc)
        c.castSucc.succ q.castSucc.succ
        (show c.val < c.castSucc.succ.val by simp only [Fin.val_castSucc, Fin.val_succ]; omega)
      rw [hL, hR, Nat.add_sub_cancel, hin0]
      simp only [Fin.val_castSucc, Fin.val_succ]

/-! ### The X markings -/

/-- Natural-number coordinates of a row swap. -/
theorem gridRowVal_swapRows {N : ℕ} (x : GridState N) (a b : Fin N) (k : ℕ) (hk : k < N) :
    gridRowVal (x.swapRows a b) k =
      if gridRowVal x k = a.val then b.val
      else if gridRowVal x k = b.val then a.val else gridRowVal x k := by
  rw [gridRowVal_mk _ _ hk, GridState.swapRows_apply, gridRowVal_mk _ _ hk, Equiv.swap_apply_def]
  split_ifs with h1 h2 h3 h4 h5 h6 <;> simp_all [Fin.ext_iff]

theorem fourMarkStabOne_X :
    (fourMarkStabOne G c).X = G.X.splitPoint c.castSucc (G.X c).castSucc c := by
  rw [fourMarkStabOne, GridDiagram.stabilizeX_X]

theorem fourMarkStabTwo_X :
    (fourMarkStabTwo G c).X =
      (G.X.splitPoint c.castSucc (G.X c).castSucc c).splitPoint c.castSucc.castSucc
        (G.X c).succ.castSucc c.castSucc := by
  rw [fourMarkStabTwo, GridDiagram.stabilizeX_X, fourMarkStabOne_X_castSucc, fourMarkStabOne_X]

/-- The column `c + 2` of the enlarged grid is the cyclic successor of the column `c + 1`. -/
theorem finRotate_castSucc_succ :
    finRotate (n + 2) c.castSucc.succ = c.succ.succ := by
  ext
  rw [finRotate_of_lt (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)]
  simp

theorem gridRowVal_splitPoint_self {N : ℕ} (x : GridState N) (a b : Fin (N + 1)) (s : Fin N) :
    gridRowVal (x.splitPoint a b s) a.val = natSuccAbove b.val (gridRowVal x s.val) := by
  rw [gridRowVal_splitPoint, if_pos rfl]

theorem gridRowVal_splitPoint_split {N : ℕ} (x : GridState N) (a b : Fin (N + 1)) (s : Fin N)
    {k : ℕ} (hk : k = natSuccAbove a.val s.val) (hka : k ≠ a.val) :
    gridRowVal (x.splitPoint a b s) k = b.val := by
  rw [gridRowVal_splitPoint, if_neg hka, if_pos hk]

theorem gridRowVal_splitPoint_of_ne {N : ℕ} (x : GridState N) (a b : Fin (N + 1)) (s : Fin N)
    {k : ℕ} (hka : k ≠ a.val) (hks : k ≠ natSuccAbove a.val s.val) (hk : k < N + 1) :
    gridRowVal (x.splitPoint a b s) k =
      natSuccAbove b.val (gridRowVal x (natPredAbove a.val k)) := by
  rw [gridRowVal_splitPoint, if_neg hka, if_neg hks, if_pos hk]

/-- The X markings of the double stabilization arise from those of the four-mark insertion by
two adjacent column exchanges. -/
theorem fourMarkStabTwo_X_eq_swapColumns {K : GridDiagram (n + 2)}
    (hK : IsFourMarkInsertion G c K) :
    (fourMarkStabTwo G c).X =
      (K.X.swapColumns c.castSucc.succ (finRotate (n + 2) c.castSucc.succ)).swapColumns
        c.castSucc.castSucc (finRotate (n + 2) c.castSucc.castSucc) := by
  rw [fourMarkStabTwo_X, hK.2, finRotate_castSucc_succ, finRotate_castSucc_castSucc]
  apply gridState_ext_gridRowVal
  intro k hk
  have hc := c.isLt
  set q := G.X c with hqdef
  have hq := q.isLt
  have hX0 : gridRowVal G.X c.val = q.val := by rw [gridRowVal_val]
  -- names for the four states
  set S1 := G.X.splitPoint c.castSucc q.castSucc c with hS1
  set S2 := S1.splitPoint c.castSucc.castSucc q.succ.castSucc c.castSucc with hS2
  set I1 := G.X.insertPoint c.castSucc q.castSucc with hI1
  set I2 := I1.insertPoint c.castSucc.succ q.castSucc.succ with hI2
  set W := I2.swapRows q.castSucc.castSucc q.castSucc.succ with hW
  -- coordinates of the right-hand side
  have hWval (j : ℕ) (hj : j < n + 2) : gridRowVal W j =
      if gridRowVal I2 j = q.val then q.val + 1
      else if gridRowVal I2 j = q.val + 1 then q.val else gridRowVal I2 j := by
    rw [hW, gridRowVal_swapRows _ _ _ j hj]
    simp only [Fin.val_castSucc, Fin.val_succ]
  -- generic old-column values never meet the two new rows
  have hold (v : ℕ) : natSuccAbove (q.val + 1) (natSuccAbove q.val v) ≠ q.val ∧
      natSuccAbove (q.val + 1) (natSuccAbove q.val v) ≠ q.val + 1 := by
    unfold natSuccAbove
    constructor <;> split_ifs <;> omega
  -- values of the left-hand side
  have hI1v (j : ℕ) (hj : j < n + 1) (hjc : j ≠ c.val) :
      gridRowVal I1 j = natSuccAbove q.val (gridRowVal G.X (natPredAbove c.val j)) := by
    rw [hI1, gridRowVal_insertPoint, if_neg (by simpa using hjc), if_pos hj]
    simp only [Fin.val_castSucc]
  have hI1c : gridRowVal I1 c.val = q.val := by
    have h := gridRowVal_insertPoint_self G.X c.castSucc q.castSucc
    simpa only [Fin.val_castSucc, hI1] using h
  have hI2v (j : ℕ) (hj : j < n + 2) (hjc : j ≠ c.val + 1) :
      gridRowVal I2 j = natSuccAbove (q.val + 1) (gridRowVal I1 (natPredAbove (c.val + 1) j)) := by
    rw [hI2, gridRowVal_insertPoint, if_neg (by simpa using hjc), if_pos hj]
    simp only [Fin.val_castSucc, Fin.val_succ]
  have hI2c : gridRowVal I2 (c.val + 1) = q.val + 1 := by
    have h := gridRowVal_insertPoint_self I1 c.castSucc.succ q.castSucc.succ
    simpa only [Fin.val_castSucc, Fin.val_succ, hI2] using h
  have hS1v (j : ℕ) (hj : j < n + 1) (hjc : j ≠ c.val) (hjc1 : j ≠ c.val + 1) :
      gridRowVal S1 j = natSuccAbove q.val (gridRowVal G.X (natPredAbove c.val j)) := by
    rw [hS1, gridRowVal_splitPoint_of_ne _ _ _ _ (by simpa using hjc)
      (by simp only [Fin.val_castSucc, natSuccAbove]; split_ifs <;> omega) hj]
    simp only [Fin.val_castSucc]
  have hS1c : gridRowVal S1 c.val = natSuccAbove q.val q.val := by
    have h := gridRowVal_splitPoint_self G.X c.castSucc q.castSucc c
    simpa only [Fin.val_castSucc, hX0, hS1] using h
  have hS1c1 : gridRowVal S1 (c.val + 1) = q.val := by
    have h := gridRowVal_splitPoint_split G.X c.castSucc q.castSucc c (k := c.val + 1)
      (by simp only [Fin.val_castSucc, natSuccAbove]; split_ifs <;> omega) (by simp)
    simpa only [Fin.val_castSucc, hS1] using h
  have hS2v (j : ℕ) (hj : j < n + 2) (hjc : j ≠ c.val) (hjc1 : j ≠ c.val + 1) :
      gridRowVal S2 j = natSuccAbove (q.val + 1) (gridRowVal S1 (natPredAbove c.val j)) := by
    rw [hS2, gridRowVal_splitPoint_of_ne _ _ _ _ (by simpa using hjc)
      (by simp only [Fin.val_castSucc, natSuccAbove]; split_ifs <;> omega) hj]
    simp only [Fin.val_castSucc, Fin.val_succ]
  have hS2c : gridRowVal S2 c.val = natSuccAbove (q.val + 1) (natSuccAbove q.val q.val) := by
    have h := gridRowVal_splitPoint_self S1 c.castSucc.castSucc q.succ.castSucc c.castSucc
    simp only [Fin.val_castSucc, Fin.val_succ, hS1c] at h
    simpa only [hS2] using h
  have hS2c1 : gridRowVal S2 (c.val + 1) = q.val + 1 := by
    have h := gridRowVal_splitPoint_split S1 c.castSucc.castSucc q.succ.castSucc c.castSucc
      (k := c.val + 1) (by simp only [Fin.val_castSucc, natSuccAbove]; split_ifs <;> omega)
      (by simp)
    simpa only [Fin.val_castSucc, Fin.val_succ, hS2] using h
  -- the double column swap on the right-hand side
  rw [gridRowVal_swapColumns _ _ _ k hk]
  simp only [Fin.val_castSucc, Fin.val_succ]
  rcases lt_trichotomy k c.val with hkc | rfl | hkc
  · rw [if_neg (by omega), if_neg (by omega), gridRowVal_swapColumns _ _ _ k hk]
    simp only [Fin.val_castSucc, Fin.val_succ]
    rw [if_neg (by omega), if_neg (by omega), hWval k hk, hI2v k hk (by omega),
      hS2v k hk (by omega) (by omega)]
    simp only [natPredAbove, if_pos hkc, if_pos (show k < c.val + 1 by omega)]
    rw [hI1v k (by omega) (by omega), hS1v k (by omega) (by omega) (by omega)]
    simp only [natPredAbove, if_pos hkc]
    rw [if_neg (hold _).1, if_neg (hold _).2]
  · rw [if_pos rfl, gridRowVal_swapColumns _ _ _ (c.val + 1) (by omega)]
    simp only [Fin.val_castSucc, Fin.val_succ]
    rw [if_true, hWval (c.val + 1 + 1) (by omega),
      hI2v (c.val + 1 + 1) (by omega) (by omega)]
    simp only [natPredAbove, if_neg (show ¬ c.val + 1 + 1 < c.val + 1 by omega),
      Nat.add_sub_cancel]
    rw [hI1v (c.val + 1) (by omega) (by omega), hS2c]
    simp only [natPredAbove, if_neg (show ¬ c.val + 1 < c.val by omega), Nat.add_sub_cancel, hX0]
    unfold natSuccAbove
    split_ifs <;> omega
  · rcases lt_trichotomy k (c.val + 1) with hk1 | rfl | hk1
    · omega
    · rw [if_neg (by omega), if_pos rfl, gridRowVal_swapColumns _ _ _ c.val (by omega)]
      simp only [Fin.val_castSucc, Fin.val_succ]
      rw [if_neg (by omega), if_neg (by omega), hWval c.val (by omega),
        hI2v c.val (by omega) (by omega), hS2c1]
      simp only [natPredAbove, if_pos (show c.val < c.val + 1 by omega)]
      rw [hI1c]
      unfold natSuccAbove
      split_ifs <;> omega
    · rcases lt_trichotomy k (c.val + 2) with hk2 | rfl | hk2
      · omega
      · rw [if_neg (by omega), if_neg (by omega),
          gridRowVal_swapColumns _ _ _ (c.val + 2) hk]
        simp only [Fin.val_castSucc, Fin.val_succ]
        rw [if_neg (by omega), if_true, hWval (c.val + 1) (by omega), hI2c,
          hS2v (c.val + 2) hk (by omega) (by omega)]
        simp only [natPredAbove, if_neg (show ¬ c.val + 2 < c.val by omega),
          show c.val + 2 - 1 = c.val + 1 by omega]
        rw [hS1c1]
        unfold natSuccAbove
        split_ifs <;> omega
      · rw [if_neg (by omega), if_neg (by omega), gridRowVal_swapColumns _ _ _ k hk]
        simp only [Fin.val_castSucc, Fin.val_succ]
        rw [if_neg (by omega), if_neg (by omega), hWval k hk, hI2v k hk (by omega),
          hS2v k hk (by omega) (by omega)]
        simp only [natPredAbove, if_neg (show ¬ k < c.val + 1 by omega),
          if_neg (show ¬ k < c.val by omega)]
        rw [hI1v (k - 1) (by omega) (by omega), hS1v (k - 1) (by omega) (by omega) (by omega)]
        simp only [natPredAbove, if_neg (show ¬ k - 1 < c.val by omega)]
        rw [if_neg (hold _).1, if_neg (hold _).2]

end OnLeConjecture.KnotFloer.GridFull
