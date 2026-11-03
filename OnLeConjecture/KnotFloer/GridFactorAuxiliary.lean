/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.GridMoveRecognition
public import OnLeConjecture.KnotFloer.GridCanonicalMoves
public import OnLeConjecture.KnotFloer.GridFullTwoByTwoSpectral

/-!
# Auxiliary grids whose horizontal arcs advance one column

For a permutation `O` of the rows of an `n × n` grid with `n ≥ 2`, the auxiliary grid
`auxiliaryGrid O` has `O`-markings `O` and the `X`-marking of column `c` in the row `O (c - 1)`,
with column indices taken cyclically (Definition 2.1 of the factor lower bound proof). Its
`X`-marking state is `cornerShift O`, the state whose point in column `c` is the lower right
corner of the `O`-marked square of column `c - 1`.

Erasing the `O`-marking of column `0` together with its row is a sequence of grid moves
(`GridDiagram.movesTo_eraseOCorner`), and the erased diagram is again an auxiliary grid. By
induction every auxiliary grid is related by grid moves to the standard `2 × 2` grid
(Lemma 2.2). Native move invariance then shows that the canonical class of every auxiliary grid
has weighted spectral threshold zero at every parameter in `[0,2]` (Lemma 2.3).

## Main results

* `auxiliaryGrid_movesTo_twoByTwo`: every auxiliary grid is related to `GridDiagram.twoByTwo` by
  grid moves.
* `auxiliaryGrid_spectralThreshold`: the canonical class of an auxiliary grid has threshold zero
  on `[0,2]`.

All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ}

/-- The state whose point in column `c` lies in the row `O (c - 1)`, with the column index taken
cyclically. For the `O`-markings of a grid it occupies the lower right corners of the `O`-marked
squares. -/
def cornerShift (O : GridState n) : GridState n :=
  O.relabelColumns (finRotate n)

theorem cornerShift_apply (O : GridState n) (c : Fin n) :
    cornerShift O c = O ((finRotate n).symm c) :=
  rfl

theorem cornerShift_finRotate (O : GridState n) (c : Fin n) :
    cornerShift O (finRotate n c) = O c := by
  rw [cornerShift_apply, Equiv.symm_apply_apply]

/-- The auxiliary grid `Q(O)`: the `O`-markings are `O`, and the `X`-marking of column `c` lies
in the row of the `O`-marking of column `c - 1`. -/
def auxiliaryGrid (O : GridState n) (hn : 2 ≤ n) : GridDiagram n where
  O := O
  X := cornerShift O
  disjoint c h := by
    rw [cornerShift_apply] at h
    have hc : c = (finRotate n).symm c := O.toPerm.injective h
    have hc' : finRotate n c = c := by
      conv_lhs => rw [hc]
      exact Equiv.apply_symm_apply _ _
    exact Grid.finRotate_ne_self (by omega) c hc'

@[simp]
theorem auxiliaryGrid_O (O : GridState n) (hn : 2 ≤ n) : (auxiliaryGrid O hn).O = O :=
  rfl

@[simp]
theorem auxiliaryGrid_X (O : GridState n) (hn : 2 ≤ n) :
    (auxiliaryGrid O hn).X = cornerShift O :=
  rfl

/-- The cyclic successor of a cyclic successor, read in a grid of size at least three. -/
private theorem finRotate_finRotate_zero_ne (k : ℕ) (hk : 2 ≤ k) :
    finRotate (k + 1) (finRotate (k + 1) 0) ≠ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  intro h
  have h1 : (finRotate (m + 3) 0 : Fin (m + 3)) = 1 := by
    ext
    rw [coe_finRotate_of_ne_last (by simp [Fin.ext_iff])]
    rfl
  rw [h1] at h
  have h2 := congrArg Fin.val h
  rw [coe_finRotate_of_ne_last (by simp [Fin.ext_iff])] at h2
  simp at h2

/-- The index identity behind the erasure of column `0`: the cyclic predecessor of the
transposed successor of `j + 1` is the successor of the cyclic predecessor of `j`. -/
private theorem finRotate_symm_swap_succ (k : ℕ) (hk : 2 ≤ k) (j : Fin k) :
    (finRotate (k + 1)).symm (Equiv.swap 0 (finRotate (k + 1) 0) j.succ) =
      ((finRotate k).symm j).succ := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  obtain ⟨i, rfl⟩ := (finRotate (m + 2)).surjective j
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_eq]
  have h1 : (finRotate (m + 3) 0 : Fin (m + 3)) = 1 := by
    ext
    rw [coe_finRotate_of_ne_last (by simp [Fin.ext_iff])]
    rfl
  rw [h1]
  rcases eq_or_ne i (Fin.last (m + 1)) with rfl | hi
  · rw [finRotate_last]
    have h2 : (Fin.last (m + 1)).succ = Fin.last (m + 2) := Fin.succ_last (m + 1)
    rw [h2, finRotate_last]
    have h3 : (0 : Fin (m + 2)).succ = (1 : Fin (m + 3)) := rfl
    rw [h3, Equiv.swap_apply_right]
  · have hv : ((finRotate (m + 2)) i).val = i.val + 1 := by
      rw [coe_finRotate_of_ne_last hi]
    have hi' : i.succ ≠ Fin.last (m + 2) := by
      intro he
      apply hi
      exact Fin.succ_injective _ (he.trans (Fin.succ_last (m + 1)).symm)
    have hv' : ((finRotate (m + 3)) i.succ).val = i.val + 2 := by
      rw [coe_finRotate_of_ne_last hi', Fin.val_succ]
    rw [Equiv.swap_apply_of_ne_of_ne]
    · ext
      rw [Fin.val_succ, hv, hv']
    · intro he
      have := congrArg Fin.val he
      rw [Fin.val_succ, hv] at this
      simp at this
    · intro he
      have := congrArg Fin.val he
      rw [Fin.val_succ, hv] at this
      simp at this

/-- Erasing the `O`-marking of column `0` of an auxiliary grid of size at least three, together
with its row, is a sequence of grid moves, and it produces the auxiliary grid of the erased
marking state. -/
theorem auxiliaryGrid_movesTo_erasePoint (k : ℕ) (hk : 2 ≤ k) (O : GridState (k + 1)) :
    (auxiliaryGrid O (by omega)).MovesTo (auxiliaryGrid (O.erasePoint 0 (O 0) rfl) hk) := by
  set G := auxiliaryGrid O (by omega) with hGdef
  have hd : G.X (finRotate (k + 1) 0) = G.O 0 := by
    change cornerShift O (finRotate (k + 1) 0) = O 0
    exact cornerShift_finRotate O 0
  have h4 : G.O (finRotate (k + 1) 0) ≠ G.X 0 := by
    change O (finRotate (k + 1) 0) ≠ cornerShift O 0
    rw [cornerShift_apply]
    intro h
    have h' : finRotate (k + 1) 0 = (finRotate (k + 1)).symm 0 := O.toPerm.injective h
    apply finRotate_finRotate_zero_ne k hk
    conv_lhs => rw [h']
    exact Equiv.apply_symm_apply _ _
  have hmove := G.movesTo_eraseOCorner 0 (finRotate (k + 1) 0) hd h4
    (by
      intro j hj
      rw [Grid.cIoo_finRotate_eq_empty] at hj
      simp at hj)
    (by
      intro j j' _ hjj'
      have hj' : (finRotate (k + 1)).symm j' = j := by
        change cornerShift O j' = O j at hjj'
        rw [cornerShift_apply] at hjj'
        exact O.toPerm.injective hjj'
      have hj'' : j' = finRotate (k + 1) j := by
        rw [← hj', Equiv.apply_symm_apply]
      subst hj''
      rw [Grid.noninterleaving_iff, Grid.cIoo_finRotate_eq_empty, Grid.cIoo_finRotate_eq_empty]
      simp)
  have heq : G.eraseOCorner 0 (finRotate (k + 1) 0) hd h4 =
      auxiliaryGrid (O.erasePoint 0 (O 0) rfl) hk := by
    ext1
    · rfl
    · refine GridState.ext fun j => ?_
      apply Fin.succAbove_right_injective (p := O 0)
      change (G.O 0).succAbove ((G.eraseOCorner 0 (finRotate (k + 1) 0) hd h4).X j) =
        (O 0).succAbove (O.erasePoint 0 (O 0) rfl ((finRotate k).symm j))
      rw [GridDiagram.succAbove_eraseOCorner_X, GridState.succAbove_erasePoint]
      change cornerShift O _ = _
      rw [cornerShift_apply]
      simp only [Fin.succAbove_zero]
      rw [finRotate_symm_swap_succ k hk j]
  rw [← heq]
  exact hmove

/-- The two auxiliary grids of size two are the standard `2 × 2` grid and its cyclic row
translate. -/
private theorem auxiliaryGrid_two_movesTo_twoByTwo (O : GridState 2) :
    (auxiliaryGrid O le_rfl).MovesTo GridDiagram.twoByTwo := by
  have hO : O.toPerm = 1 ∨ O.toPerm = Equiv.swap 0 1 := by
    generalize O.toPerm = σ
    revert σ
    decide
  rcases hO with h | h
  · have heq : auxiliaryGrid O le_rfl = GridDiagram.twoByTwo := by
      ext1
      · exact GridState.ext fun c => by
          change O.toPerm c = _
          rw [h]
          fin_cases c <;> rfl
      · exact GridState.ext fun c => by
          change O.toPerm _ = _
          rw [h]
          fin_cases c <;> rfl
    rw [heq]
  · have heq : auxiliaryGrid O le_rfl = GridDiagram.twoByTwo.relabelRows (finRotate 2) := by
      ext1
      · exact GridState.ext fun c => by
          change O.toPerm c = _
          rw [h]
          fin_cases c <;> rfl
      · exact GridState.ext fun c => by
          change O.toPerm _ = _
          rw [h]
          fin_cases c <;> rfl
    rw [heq]
    exact (GridDiagram.cyclicRows_movesTo _).symm

/-- **Lemma 2.2.** Every auxiliary grid is related by grid moves to the standard `2 × 2` grid. -/
theorem auxiliaryGrid_movesTo_twoByTwo (O : GridState n) (hn : 2 ≤ n) :
    (auxiliaryGrid O hn).MovesTo GridDiagram.twoByTwo := by
  induction n, hn using Nat.le_induction with
  | base => exact auxiliaryGrid_two_movesTo_twoByTwo O
  | succ k hk ih =>
    exact (auxiliaryGrid_movesTo_erasePoint k hk O).trans (ih _)

/-- **Lemma 2.3.** The canonical class of every auxiliary grid has weighted spectral threshold
zero at every parameter in `[0,2]`. -/
theorem auxiliaryGrid_spectralThreshold (O : GridState n) (hn : 2 ≤ n) (u : ℝ) (hu0 : 0 ≤ u)
    (hu2 : u ≤ 2) :
    ((laurentMaslovBifiltration (auxiliaryGrid O hn) (ZMod 2)).weighted u).spectralThreshold 0
      (gridCanonicalClass (auxiliaryGrid O hn) hn) = 0 := by
  rw [gridCanonicalClass_spectralThreshold_movesTo _ GridDiagram.twoByTwo hn le_rfl
    (auxiliaryGrid_movesTo_twoByTwo O hn) u]
  exact spectralThreshold_twoByTwo_degree_zero (ZMod 2) _
    (gridCanonicalClass_ne_zero _ le_rfl) u hu0 hu2

end OnLeConjecture.KnotFloer.GridFull
