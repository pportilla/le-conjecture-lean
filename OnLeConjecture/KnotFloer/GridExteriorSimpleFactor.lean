/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorSeamCoordinates
public import OnLeConjecture.KnotFloer.GridMovesToCanonicalMap

/-!
# Removal of simple factors from an iterated seam

This file formalizes the removal of simple factors from an iterated seam, in the setting of
Sections 10 and 11 of the written proof of Statement E (statement_E_complete_proof.tex).

The simple factor `simpleFactorGrid` is the grid diagram of size four with
`O = (1, 3, 2, 0)` and `X = (0, 2, 1, 3)`, the values being listed by column. It is triply
prepared (`simpleFactorGrid_triplyPrepared`). It is related by one `X` destabilization and one
cyclic row permutation to the three-by-three grid `positiveGeneratorWordGrid` with
`O = (1, 0, 2)` and `X = (0, 2, 1)`, which Section 11 of the written proof uses as the word
grid of one positive generator on two strands (`simpleFactorGrid_movesTo_wordGrid`).

Let `G` be a grid diagram of size `n + 1` whose `X` marking of the last column lies in the last
row, and let `Σ` be the binary seam of `G` with `simpleFactorGrid`. The grid `Σ` has size
`n + 4`. It agrees with `G` in the columns `c < n`, and its last four columns carry
`O = (n + 1, n + 3, n + 2, O_G(n))` and `X = (n, n + 2, n + 1, n + 3)`. The file proves that `Σ`
is obtained from `G` by one `X` stabilization followed by two `O` stabilizations
(`connectedSumSeamGrid_simpleFactor_eq`). Consequently `Σ` is related to `G` by grid moves
(`connectedSumSeamGrid_simpleFactor_movesTo`).

The marking computations use the natural-number coordinates `gridRowVal` of
`GridExteriorSeamCoordinates`, together with explicit coordinate formulas for the inserted and
split points of a stabilization (`gridRowVal_insertPoint`, `gridRowVal_splitPoint`).

## Main results

* `connectedSumSeamGrid_simpleFactor_movesTo`: the seam of `G` with the simple factor is related
  to `G` by grid moves.
* `seamChainGrid_succ_movesTo_of_last_simpleFactor` and
  `iteratedSeamGrid_movesTo_of_last_simpleFactor`: if the last factor of a seam chain, or of a
  prepared family with at least one other factor, is the simple factor, then the iterated seam
  is related by grid moves to the iterated seam of the family without that factor.
* `iteratedSeamGrid_movesTo_of_trailing_simpleFactors`: the same statement for `B` trailing
  simple factors.
* `exists_iteratedSeam_trailing_simpleFactors_canonical_map`: a chain map between the native
  `ZMod 2` complexes of these two iterated seams, with filtration shifts `(0, 0)`, that sends the
  normalized class to the normalized class.

The proof of the last statement composes the maps along grid moves of
`GridMovesToCanonicalMap`. It does not use the functional on the three-by-three word grid that
the written proof uses for the same purpose.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

/-! ### Natural-number coordinates of stabilizations -/

/-- The value of `Fin.succAbove p` on natural numbers: `v` below `p`, and `v + 1` from `p` on. -/
def natSuccAbove (p v : ℕ) : ℕ := if v < p then v else v + 1

/-- The old column index of a column `k ≠ p` after a column `p` is inserted: `k` below `p`, and
`k - 1` above `p`. -/
def natPredAbove (p k : ℕ) : ℕ := if k < p then k else k - 1

/-- Away from the inserted column, `natSuccAbove` inverts `natPredAbove`. -/
theorem natSuccAbove_natPredAbove (a k : ℕ) (h : k ≠ a) :
    natSuccAbove a (natPredAbove a k) = k := by
  unfold natSuccAbove natPredAbove
  split_ifs <;> omega

/-- The value of `p.succAbove i` is `natSuccAbove p i`. -/
theorem val_succAbove_eq_natSuccAbove {N : ℕ} (p : Fin (N + 1)) (i : Fin N) :
    (p.succAbove i).val = natSuccAbove p.val i.val := by
  unfold Fin.succAbove natSuccAbove
  split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def]

/-- Away from the last index, the cyclic translation `finRotate (N + 1)` adds one. -/
theorem val_finRotate_of_lt {N : ℕ} (i : Fin (N + 1)) (h : i.val < N) :
    (finRotate (N + 1) i).val = i.val + 1 :=
  coe_finRotate_of_ne_last fun he => by simp [he] at h

/-- Natural-number coordinates of a grid state with an inserted point `(a, b)`. The inserted
column has row `b`, and every other column below the new size has the embedded row of the
corresponding old column. -/
theorem gridRowVal_insertPoint {N : ℕ} (x : GridState N) (a b : Fin (N + 1)) (k : ℕ) :
    gridRowVal (x.insertPoint a b) k =
      if k = a.val then b.val else if k < N + 1 then
        natSuccAbove b.val (gridRowVal x (natPredAbove a.val k)) else 0 := by
  by_cases hka : k = a.val
  · subst hka
    rw [if_pos rfl, gridRowVal_val, GridState.insertPoint_apply_newColumn]
  · rw [if_neg hka]
    by_cases hk : k < N + 1
    · have ha := a.isLt
      have hp : natPredAbove a.val k < N := by
        unfold natPredAbove
        split_ifs <;> omega
      have hc : (⟨k, hk⟩ : Fin (N + 1)) = a.succAbove ⟨natPredAbove a.val k, hp⟩ := by
        ext
        rw [val_succAbove_eq_natSuccAbove, natSuccAbove_natPredAbove _ _ hka]
      rw [if_pos hk, gridRowVal_mk _ _ hk, hc, GridState.insertPoint_apply_succAbove,
        val_succAbove_eq_natSuccAbove, gridRowVal_mk _ _ hp]
    · rw [if_neg hk]
      simp [gridRowVal, hk]

/-- Natural-number coordinates of a grid state whose point in column `s` is split across the
inserted row `b` and column `a`. The inserted column has the embedded old row of column `s`, the
embedded column `s` has row `b`, and every other column below the new size has the embedded row
of the corresponding old column. -/
theorem gridRowVal_splitPoint {N : ℕ} (x : GridState N) (a b : Fin (N + 1)) (s : Fin N)
    (k : ℕ) :
    gridRowVal (x.splitPoint a b s) k =
      if k = a.val then natSuccAbove b.val (gridRowVal x s.val)
      else if k = natSuccAbove a.val s.val then b.val
      else if k < N + 1 then natSuccAbove b.val (gridRowVal x (natPredAbove a.val k))
      else 0 := by
  by_cases hka : k = a.val
  · subst hka
    rw [if_pos rfl, gridRowVal_val, GridState.splitPoint_apply_newColumn,
      val_succAbove_eq_natSuccAbove, gridRowVal_val]
  · rw [if_neg hka]
    by_cases hks : k = natSuccAbove a.val s.val
    · subst hks
      rw [if_pos rfl, ← val_succAbove_eq_natSuccAbove, gridRowVal_val,
        GridState.splitPoint_apply_splitColumn]
    · rw [if_neg hks]
      by_cases hk : k < N + 1
      · have ha := a.isLt
        have hp : natPredAbove a.val k < N := by
          unfold natPredAbove
          split_ifs <;> omega
        have hc : (⟨k, hk⟩ : Fin (N + 1)) = a.succAbove ⟨natPredAbove a.val k, hp⟩ := by
          ext
          rw [val_succAbove_eq_natSuccAbove, natSuccAbove_natPredAbove _ _ hka]
        have hne : (⟨natPredAbove a.val k, hp⟩ : Fin N) ≠ s := by
          rintro rfl
          apply hks
          rw [← val_succAbove_eq_natSuccAbove, ← hc]
        rw [if_pos hk, gridRowVal_mk _ _ hk, hc, GridState.splitPoint_apply_succAbove,
          if_neg hne, val_succAbove_eq_natSuccAbove, gridRowVal_mk _ _ hp]
      · rw [if_neg hk]
        simp [gridRowVal, hk]

/-! ### The simple factor -/

/-- The permutation of `Fin 4` with values `(1, 3, 2, 0)`. -/
def simpleFactorO : Equiv.Perm (Fin 4) where
  toFun := ![1, 3, 2, 0]
  invFun := ![3, 0, 2, 1]
  left_inv := by decide
  right_inv := by decide

/-- The permutation of `Fin 4` with values `(0, 2, 1, 3)`. -/
def simpleFactorX : Equiv.Perm (Fin 4) where
  toFun := ![0, 2, 1, 3]
  invFun := ![0, 2, 1, 3]
  left_inv := by decide
  right_inv := by decide

/-- The simple factor: the grid diagram of size four with `O = (1, 3, 2, 0)` and
`X = (0, 2, 1, 3)`, the values being listed by column. -/
def simpleFactorGrid : GridDiagram 4 where
  O := ⟨simpleFactorO⟩
  X := ⟨simpleFactorX⟩
  disjoint := by decide

/-- The `X` marking of column `0` of the simple factor lies in row `0`. -/
theorem simpleFactorGrid_X_zero : simpleFactorGrid.X 0 = 0 := by decide

/-- The simple factor is triply prepared. -/
theorem simpleFactorGrid_triplyPrepared : TriplyPrepared simpleFactorGrid :=
  ⟨by decide, by decide, by decide⟩

/-- The `O` coordinates of the simple factor. -/
theorem gridRowVal_simpleFactorGrid_O (k : ℕ) :
    gridRowVal simpleFactorGrid.O k =
      if k = 0 then 1 else if k = 1 then 3 else if k = 2 then 2 else 0 := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k by omega) with rfl | rfl | rfl | rfl | hk
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [gridRowVal, show ¬k < 4 by omega, show k ≠ 0 by omega, show k ≠ 1 by omega,
      show k ≠ 2 by omega]

/-- The `X` coordinates of the simple factor. -/
theorem gridRowVal_simpleFactorGrid_X (k : ℕ) :
    gridRowVal simpleFactorGrid.X k =
      if k = 1 then 2 else if k = 2 then 1 else if k < 4 then k else 0 := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k by omega) with rfl | rfl | rfl | rfl | hk
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [gridRowVal, show ¬k < 4 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega]

/-! ### The seam with the simple factor as three stabilizations -/

section Stabilizations

variable {n : ℕ} (G : GridDiagram (n + 1))

/-- The first stabilization: split the `X` marking of the last column of `G`, with the new column
`n` and the new row `n + 1`. -/
def simpleStabOne : GridDiagram (n + 1 + 1) :=
  G.stabilizeX ⟨n, by omega⟩ ⟨n + 1, by omega⟩ (Fin.last n)

/-- The second stabilization: split the `O` marking of column `n` of `simpleStabOne G`, with the
new column `n + 1` and the new row `n + 1`. -/
def simpleStabTwo : GridDiagram (n + 1 + 1 + 1) :=
  (simpleStabOne G).stabilizeO ⟨n + 1, by omega⟩ ⟨n + 1, by omega⟩ ⟨n, by omega⟩

/-- The third stabilization: split the `O` marking of column `n + 1` of `simpleStabTwo G`, with
the new column `n + 1` and the new row `n + 2`. -/
def simpleStabThree : GridDiagram (n + 1 + 1 + 1 + 1) :=
  (simpleStabTwo G).stabilizeO ⟨n + 1, by omega⟩ ⟨n + 2, by omega⟩ ⟨n + 1, by omega⟩

/-- If the `X` marking of the last column of `G` lies in the last row, then `simpleStabOne G`
is an elementary `X` stabilization of `G`. -/
theorem isXStabilization_simpleStabOne (hG : G.X (Fin.last n) = Fin.last n) :
    GridDiagram.IsXStabilization G (simpleStabOne G) := by
  apply GridDiagram.isXStabilization_stabilizeX
  · left
    exact Fin.ext (by
      rw [val_finRotate_of_lt _ (by simp)]
      simp [val_succAbove_eq_natSuccAbove, natSuccAbove])
  · right
    rw [hG]
    exact Fin.ext (by
      rw [val_finRotate_of_lt _ (by simp [val_succAbove_eq_natSuccAbove, natSuccAbove])]
      simp [val_succAbove_eq_natSuccAbove, natSuccAbove])

/-- The grid `simpleStabTwo G` is an elementary `O` stabilization of `simpleStabOne G`. -/
theorem isOStabilization_simpleStabTwo :
    GridDiagram.IsOStabilization (simpleStabOne G) (simpleStabTwo G) := by
  apply GridDiagram.isOStabilization_stabilizeO
  · right
    exact Fin.ext (by
      rw [val_finRotate_of_lt _ (by simp [val_succAbove_eq_natSuccAbove, natSuccAbove])]
      simp [val_succAbove_eq_natSuccAbove, natSuccAbove])
  · left
    simp only [simpleStabOne, GridDiagram.stabilizeX_O, GridState.insertPoint_apply_newColumn]
    exact Fin.ext (by
      rw [val_finRotate_of_lt _ (by simp)]
      simp [val_succAbove_eq_natSuccAbove, natSuccAbove])

/-- The grid `simpleStabThree G` is an elementary `O` stabilization of `simpleStabTwo G`. -/
theorem isOStabilization_simpleStabThree :
    GridDiagram.IsOStabilization (simpleStabTwo G) (simpleStabThree G) := by
  apply GridDiagram.isOStabilization_stabilizeO
  · left
    exact Fin.ext (by
      rw [val_finRotate_of_lt _ (by simp)]
      simp [val_succAbove_eq_natSuccAbove, natSuccAbove])
  · left
    simp only [simpleStabTwo, simpleStabOne, GridDiagram.stabilizeO_O, GridDiagram.stabilizeX_O,
      GridState.splitPoint_apply_newColumn, GridState.insertPoint_apply_newColumn]
    exact Fin.ext (by
      rw [val_finRotate_of_lt _ (by simp)]
      simp [val_succAbove_eq_natSuccAbove, natSuccAbove])

/-- If the `X` marking of the last column of `G` lies in the last row, then `simpleStabThree G`
is related to `G` by grid moves. -/
theorem simpleStabThree_movesTo (hG : G.X (Fin.last n) = Fin.last n) :
    (simpleStabThree G).MovesTo G :=
  ((GridDiagram.IsStabilization.movesTo ((GridDiagram.isStabilization_iff _ _).mpr
      (Or.inr (isXStabilization_simpleStabOne G hG)))).trans
    ((GridDiagram.IsStabilization.movesTo ((GridDiagram.isStabilization_iff _ _).mpr
      (Or.inl (isOStabilization_simpleStabTwo G)))).trans
      (GridDiagram.IsStabilization.movesTo ((GridDiagram.isStabilization_iff _ _).mpr
        (Or.inl (isOStabilization_simpleStabThree G)))))).symm

/-- If the `X` marking of the last column of `G` lies in the last row, then the seam of `G` with
the simple factor is the triple stabilization `simpleStabThree G`. -/
theorem connectedSumSeamGrid_simpleFactor_eq (hG : G.X (Fin.last n) = Fin.last n) :
    connectedSumSeamGrid G simpleFactorGrid hG simpleFactorGrid_X_zero =
      simpleStabThree G := by
  have hO := gridRowVal_lt G.O
  have hX := gridRowVal_lt G.X
  have hGX : gridRowVal G.X n = n := gridRowVal_last_of_X_last hG
  ext1 <;> apply gridState_ext_gridRowVal <;> intro k hk
  · simp only [simpleStabThree, simpleStabTwo, simpleStabOne, GridDiagram.stabilizeO_O,
      GridDiagram.stabilizeX_O, connectedSumSeamGrid_O_eq]
    rcases (show k < n ∨ k = n ∨ k = n + 1 ∨ k = n + 2 ∨ k = n + 3 by omega)
      with hk' | hk' | hk' | hk' | hk'
    · have h1 : k ≠ n := by omega
      have h2 : k ≠ n + 1 := by omega
      have h3 : k ≠ n + 2 := by omega
      have h4 : k < n + 1 := by omega
      have h5 : k < n + 2 := by omega
      have h6 : k < n + 3 := by omega
      have g1 := hO k
      have g2 : gridRowVal G.O k < n + 2 := by omega
      simp [gridRowVal_seamState, gridRowVal_splitPoint, gridRowVal_insertPoint,
        natSuccAbove, natPredAbove, hk', h1, h2, h3, h4, h5, h6, g1, g2]
      omega
    all_goals subst k
    all_goals
      have g1 := hO n
      have g2 : gridRowVal G.O n < n + 2 := by omega
      simp [gridRowVal_seamState, gridRowVal_splitPoint, gridRowVal_insertPoint,
        gridRowVal_simpleFactorGrid_O, natSuccAbove, natPredAbove, g1, g2, Nat.add_assoc]
  · simp only [simpleStabThree, simpleStabTwo, simpleStabOne, GridDiagram.stabilizeO_X,
      GridDiagram.stabilizeX_X, connectedSumSeamGrid_X_eq]
    rcases (show k < n ∨ k = n ∨ k = n + 1 ∨ k = n + 2 ∨ k = n + 3 by omega)
      with hk' | hk' | hk' | hk' | hk'
    · have h1 : k ≠ n := by omega
      have h2 : k ≠ n + 1 := by omega
      have h4 : k < n + 1 := by omega
      have h5 : k < n + 2 := by omega
      have h6 : k < n + 3 := by omega
      have g1 := hX k
      have g2 : gridRowVal G.X k < n + 2 := by omega
      simp [gridRowVal_seamState, gridRowVal_splitPoint, gridRowVal_insertPoint,
        natSuccAbove, natPredAbove, hk', h1, h2, h4, h5, h6, g1, g2]
      omega
    all_goals subst k
    all_goals
      simp [gridRowVal_seamState, gridRowVal_splitPoint, gridRowVal_insertPoint,
        gridRowVal_simpleFactorGrid_X, natSuccAbove, natPredAbove, hGX, Nat.add_assoc]

/-- **Removal of one simple factor.** If the `X` marking of the last column of `G` lies in the
last row, then the seam of `G` with the simple factor is related to `G` by grid moves. -/
theorem connectedSumSeamGrid_simpleFactor_movesTo (hG : G.X (Fin.last n) = Fin.last n) :
    (connectedSumSeamGrid G simpleFactorGrid hG simpleFactorGrid_X_zero).MovesTo G := by
  rw [connectedSumSeamGrid_simpleFactor_eq G hG]
  exact simpleStabThree_movesTo G hG

end Stabilizations

/-- The removal of one simple factor, for a second factor `H` that is the simple factor up to
the identification of its size `m + 1` with `4`. -/
theorem connectedSumSeamGrid_movesTo_of_simpleFactor {n m : ℕ} (G : GridDiagram (n + 1))
    (H : GridDiagram (m + 1)) (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (hS : (⟨m + 1, H⟩ : Σ k, GridDiagram k) = ⟨4, simpleFactorGrid⟩) :
    (connectedSumSeamGrid G H hG hH).MovesTo G := by
  obtain ⟨hm, hH'⟩ := Sigma.mk.inj_iff.mp hS
  obtain rfl : m = 3 := by omega
  obtain rfl := eq_of_heq hH'
  exact connectedSumSeamGrid_simpleFactor_movesTo G hG

/-! ### Removal of trailing simple factors from iterated seams -/

/-- If the last factor of a seam chain of `M + 2` factors is the simple factor, then the seam
chain is related by grid moves to the seam chain of the first `M + 1` factors. -/
theorem seamChainGrid_succ_movesTo_of_last_simpleFactor (M : ℕ) {p : Fin (M + 1 + 1) → ℕ}
    (E : ∀ j, GridDiagram (p j + 1)) (hE : ∀ j : Fin (M + 1), (E j.succ).X 0 = 0)
    (hS : (⟨p (Fin.last (M + 1)) + 1, E (Fin.last (M + 1))⟩ : Σ k, GridDiagram k) =
      ⟨4, simpleFactorGrid⟩) :
    (seamChainGrid (M + 1) E hE).MovesTo
      (seamChainGrid M (fun j => E j.castSucc) (fun j => hE j.castSucc)) := by
  rw [seamChainGrid_succ]
  exact (connectedSumSeamGrid_movesTo_of_simpleFactor _ _ _ _ hS).trans
    (seamLeftGrid_movesTo _).symm

/-- The restriction of a prepared family to an initial segment is prepared. -/
theorem SeamPrepared.castLE {N N' : ℕ} (h : N ≤ N') {sizes : Fin N' → ℕ}
    {D : ∀ j, GridDiagram (sizes j)} (hp : SeamPrepared D) :
    SeamPrepared (fun j : Fin N => D (Fin.castLE h j)) where
  pos j := hp.pos _
  first h0 := hp.first (by omega)
  rest j hj := hp.rest (Fin.castLE h j) hj

/-- If the last factor of a prepared family of `N + 1` grids with `0 < N` is the simple factor,
then the iterated seam grid of the family is related by grid moves to the iterated seam grid of
the first `N` factors. -/
theorem iteratedSeamGrid_movesTo_of_last_simpleFactor {N : ℕ} (hN : 0 < N)
    {sizes : Fin (N + 1) → ℕ} (D : ∀ j, GridDiagram (sizes j)) (hprep : SeamPrepared D)
    (hS : (⟨sizes (Fin.last N), D (Fin.last N)⟩ : Σ k, GridDiagram k) =
      ⟨4, simpleFactorGrid⟩) :
    (iteratedSeamGrid D hprep).MovesTo
      (iteratedSeamGrid (fun j : Fin N => D j.castSucc) (hprep.castLE (Nat.le_succ N))) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hS' : (⟨sizes (Fin.last (M + 1)) - 1 + 1, preparedCast D hprep (Fin.last (M + 1))⟩ :
      Σ k, GridDiagram k) = ⟨4, simpleFactorGrid⟩ :=
    (gridCast_sigma _ _).trans hS
  exact (movesTo_gridCast _ _).symm.trans
    ((seamChainGrid_succ_movesTo_of_last_simpleFactor M _ _ hS').trans (movesTo_gridCast _ _))

/-- **Removal of trailing simple factors.** If the last `B` factors of a prepared family of
`M + 1 + B` grids are simple factors, then the iterated seam grid of the family is related by
grid moves to the iterated seam grid of the first `M + 1` factors. -/
theorem iteratedSeamGrid_movesTo_of_trailing_simpleFactors (M : ℕ) :
    (B : ℕ) → {sizes : Fin (M + 1 + B) → ℕ} → (D : ∀ j, GridDiagram (sizes j)) →
      (hprep : SeamPrepared D) →
      (∀ i : Fin B, (⟨sizes (Fin.natAdd (M + 1) i), D (Fin.natAdd (M + 1) i)⟩ :
        Σ k, GridDiagram k) = ⟨4, simpleFactorGrid⟩) →
      (iteratedSeamGrid D hprep).MovesTo
        (iteratedSeamGrid (fun j : Fin (M + 1) => D (Fin.castAdd B j))
          (hprep.castLE (Nat.le_add_right _ _)))
  | 0, _, _, _, _ => GridDiagram.MovesTo.refl _
  | B + 1, _, D, hprep, hS =>
    (iteratedSeamGrid_movesTo_of_last_simpleFactor (Nat.add_pos_left (Nat.succ_pos M) B) D hprep
        (hS (Fin.last B))).trans
      (iteratedSeamGrid_movesTo_of_trailing_simpleFactors M B (fun j => D j.castSucc)
        (hprep.castLE (Nat.le_succ _)) fun i => hS i.castSucc)

/-- **Native map removing trailing simple factors.** Let a prepared family of `M + 1 + B` grids
of sizes at least two end with `B` simple factors. Some chain map from the native `ZMod 2`
complex of its iterated seam grid to the native complex of the iterated seam grid of the first
`M + 1` factors has filtration shifts `(0, 0)` and sends the normalized class to the normalized
class. -/
theorem exists_iteratedSeam_trailing_simpleFactors_canonical_map (M B : ℕ)
    {sizes : Fin (M + 1 + B) → ℕ} (D : ∀ j, GridDiagram (sizes j)) (hD : ∀ j, 2 ≤ sizes j)
    (hprep : SeamPrepared D)
    (hS : ∀ i : Fin B, (⟨sizes (Fin.natAdd (M + 1) i), D (Fin.natAdd (M + 1) i)⟩ :
      Σ k, GridDiagram k) = ⟨4, simpleFactorGrid⟩) :
    ∃ φ : laurentMaslovComplex (iteratedSeamGrid D hprep) (ZMod 2) ⟶
        laurentMaslovComplex (iteratedSeamGrid (fun j : Fin (M + 1) => D (Fin.castAdd B j))
          (hprep.castLE (Nat.le_add_right _ _))) (ZMod 2),
      (laurentMaslovBifiltration (iteratedSeamGrid D hprep) (ZMod 2)).Shifts
          (laurentMaslovBifiltration (iteratedSeamGrid (fun j : Fin (M + 1) => D (Fin.castAdd B j))
            (hprep.castLE (Nat.le_add_right _ _))) (ZMod 2)) φ 0 0 ∧
        homologyMap φ 0
            (gridCanonicalClass (iteratedSeamGrid D hprep)
              (two_le_iteratedSeamSize (by omega) hD)) =
          gridCanonicalClass (iteratedSeamGrid (fun j : Fin (M + 1) => D (Fin.castAdd B j))
              (hprep.castLE (Nat.le_add_right _ _)))
            (two_le_iteratedSeamSize (Nat.succ_pos M) fun j => hD _) := by
  obtain ⟨_, φ, hφ, hc⟩ := exists_movesTo_canonical_map_of_two_le _ _
    (two_le_iteratedSeamSize (by omega) hD)
    (iteratedSeamGrid_movesTo_of_trailing_simpleFactors M B D hprep hS)
  exact ⟨φ, hφ, hc⟩

/-! ### The simple factor and the word grid of a positive generator -/

/-- The permutation of `Fin 3` with values `(1, 0, 2)`. -/
def positiveGeneratorWordO : Equiv.Perm (Fin 3) where
  toFun := ![1, 0, 2]
  invFun := ![1, 0, 2]
  left_inv := by decide
  right_inv := by decide

/-- The permutation of `Fin 3` with values `(0, 2, 1)`. -/
def positiveGeneratorWordX : Equiv.Perm (Fin 3) where
  toFun := ![0, 2, 1]
  invFun := ![0, 2, 1]
  left_inv := by decide
  right_inv := by decide

/-- The three-by-three grid diagram with `O = (1, 0, 2)` and `X = (0, 2, 1)`. Section 11 of the
written proof uses it as the word grid of one positive generator on two strands. -/
def positiveGeneratorWordGrid : GridDiagram 3 where
  O := ⟨positiveGeneratorWordO⟩
  X := ⟨positiveGeneratorWordX⟩
  disjoint := by decide

/-- The permutation of `Fin 3` with values `(0, 2, 1)`. -/
def simpleFactorCoreO : Equiv.Perm (Fin 3) where
  toFun := ![0, 2, 1]
  invFun := ![0, 2, 1]
  left_inv := by decide
  right_inv := by decide

/-- The permutation of `Fin 3` with values `(2, 1, 0)`. -/
def simpleFactorCoreX : Equiv.Perm (Fin 3) where
  toFun := ![2, 1, 0]
  invFun := ![2, 1, 0]
  left_inv := by decide
  right_inv := by decide

/-- The three-by-three grid diagram with `O = (0, 2, 1)` and `X = (2, 1, 0)`. Its cyclic row
permutation is `positiveGeneratorWordGrid`, and the simple factor is an `X` stabilization of
it. -/
def simpleFactorCoreGrid : GridDiagram 3 where
  O := ⟨simpleFactorCoreO⟩
  X := ⟨simpleFactorCoreX⟩
  disjoint := by decide

/-- The `O` coordinates of `simpleFactorCoreGrid`. -/
theorem gridRowVal_simpleFactorCoreGrid_O (k : ℕ) :
    gridRowVal simpleFactorCoreGrid.O k = if k = 1 then 2 else if k = 2 then 1 else 0 := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | rfl | hk
  · rfl
  · rfl
  · rfl
  · simp [gridRowVal, show ¬k < 3 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega]

/-- The `X` coordinates of `simpleFactorCoreGrid`. -/
theorem gridRowVal_simpleFactorCoreGrid_X (k : ℕ) :
    gridRowVal simpleFactorCoreGrid.X k = if k = 0 then 2 else if k = 1 then 1 else 0 := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | rfl | hk
  · rfl
  · rfl
  · rfl
  · simp [gridRowVal, show ¬k < 3 by omega, show k ≠ 0 by omega, show k ≠ 1 by omega]

/-- The simple factor is the `X` stabilization of `simpleFactorCoreGrid` that splits the `X`
marking of column `0`, with the new column `3` and the new row `0`. -/
theorem simpleFactorGrid_eq_stabilizeX :
    simpleFactorGrid = simpleFactorCoreGrid.stabilizeX 3 0 0 := by
  ext1 <;> apply gridState_ext_gridRowVal <;> intro k hk <;>
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp [gridRowVal_insertPoint, gridRowVal_splitPoint, gridRowVal_simpleFactorGrid_O,
      gridRowVal_simpleFactorGrid_X, gridRowVal_simpleFactorCoreGrid_O,
      gridRowVal_simpleFactorCoreGrid_X, natSuccAbove, natPredAbove]

/-- The simple factor is an elementary `X` stabilization of `simpleFactorCoreGrid`. -/
theorem isXStabilization_simpleFactorGrid :
    GridDiagram.IsXStabilization simpleFactorCoreGrid simpleFactorGrid := by
  rw [simpleFactorGrid_eq_stabilizeX]
  apply GridDiagram.isXStabilization_stabilizeX
  · left
    exact Fin.ext (by
      rw [show (3 : Fin (3 + 1)) = Fin.last 3 from rfl, finRotate_last]
      simp)
  · right
    have h : (0 : Fin (3 + 1)).succAbove (simpleFactorCoreGrid.X 0) = Fin.last 3 :=
      Fin.ext (by
        rw [val_succAbove_eq_natSuccAbove, ← gridRowVal_val, gridRowVal_simpleFactorCoreGrid_X]
        simp [natSuccAbove])
    rw [h, finRotate_last]

/-- The cyclic row permutation of `simpleFactorCoreGrid` is `positiveGeneratorWordGrid`. -/
theorem simpleFactorCoreGrid_relabelRows :
    simpleFactorCoreGrid.relabelRows (finRotate 3) = positiveGeneratorWordGrid := by
  ext c <;> fin_cases c <;> rfl

/-- The simple factor is related by grid moves to the word grid `positiveGeneratorWordGrid`,
by one `X` destabilization and one cyclic row permutation. -/
theorem simpleFactorGrid_movesTo_wordGrid :
    simpleFactorGrid.MovesTo positiveGeneratorWordGrid := by
  have h := GridDiagram.cyclicRows_movesTo simpleFactorCoreGrid
  rw [simpleFactorCoreGrid_relabelRows] at h
  exact (GridDiagram.IsStabilization.movesTo ((GridDiagram.isStabilization_iff _ _).mpr
    (Or.inr isXStabilization_simpleFactorGrid))).symm.trans h

end OnLeConjecture.KnotFloer.GridFull
