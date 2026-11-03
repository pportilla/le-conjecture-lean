/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.TorusWordGridHybrid
public import OnLeConjecture.KnotTheory.PositiveWordGridMovesTransport
public import OnLeConjecture.KnotFloer.GridReflectedTorusBasic

/-! # Hybrid grids without blocks are reflected torus grids

When no block of `β` remains, the hybrid grid `H_{A+1,k}(∅)` is the torus grid `R_{A+1,k}` of
`docs/route-n/J11-torus-word-grid.tex`, Definition *R*, and `R_{A+1,k}` is obtained from the
reflected standard torus grid `reflectedDiagram (torusLink A (k - 1))` by one cyclic permutation
of the rows (Lemma *R-reflect*). The main result is `IsHybrid.movesTo_reflectedTorusLink`. All
results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory

open TauCeti OnLeConjecture.KnotFloer.GridFull

theorem finRotate_pow_val {N : ℕ} (p : ℕ) (hp : p ≤ N) (x : Fin N) :
    ((finRotate N ^ p) x).val = if x.val + p < N then x.val + p else x.val + p - N := by
  induction p generalizing x with
  | zero => have := x.isLt; simp
  | succ p ih =>
    have hx := x.isLt
    rw [pow_succ, Equiv.Perm.mul_apply, ih (by omega), finRotate_val_eq]
    split_ifs <;> omega

theorem range'_split (s n m : ℕ) :
    List.range' s (n + 1 + m) = List.range' s n ++ (s + n) :: List.range' (s + n + 1) m := by
  rw [show n + 1 + m = n + (1 + m) by omega, ← List.range'_append_1, add_comm 1 m,
    List.range'_succ]

/-- The rows of the hybrid grid without blocks, from bottom to top. -/
def torusRows (A k' : ℕ) : List TorusRow :=
  rRow 0 :: ((List.range (A + 1)).map iRow ++ (List.range' (A + 2) k').map rRow)

theorem mem_torusRows {A k' : ℕ} {x : TorusRow} :
    x ∈ torusRows A k' ↔ HybRow A (k' + 1) 0 x := by
  simp only [torusRows, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
    List.mem_range', HybRow]
  constructor
  · rintro (h | ⟨r, hr, rfl⟩ | ⟨_, ⟨i, hi, rfl⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl ⟨r, by omega, rfl⟩))
    · exact Or.inr (Or.inl ⟨A + 2 + 1 * i, by omega, by omega, rfl⟩)
  · rintro (h | ⟨t, h1, h2, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨b, hb, -⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨t, ⟨t - (A + 2), by omega, by omega⟩, rfl⟩)
    · exact Or.inr (Or.inl ⟨r, by omega, rfl⟩)
    · omega

theorem torusRows_nodup (A k' : ℕ) : (torusRows A k').Nodup := by
  unfold torusRows
  refine List.nodup_cons.mpr ⟨?_, List.nodup_append.mpr ⟨?_, ?_, ?_⟩⟩
  · simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_range', not_or,
      not_exists, not_and]
    refine ⟨fun r _ h => iRow_ne_rRow r 0 h, fun t _ h => ?_⟩
    simp only [rRow_inj_iff] at h; omega
  · exact List.nodup_range.map fun a b h => by simpa using h
  · exact List.Nodup.map (fun a b h => by simpa using h) List.nodup_range'
  · simp only [List.mem_map, List.mem_range, List.mem_range']
    rintro _ ⟨r, -, rfl⟩ _ ⟨t, -, rfl⟩ h
    exact iRow_ne_rRow _ _ h

theorem torusRows_pairwise (A k' : ℕ) : (torusRows A k').Pairwise (hybLtS A 0 0) := by
  unfold torusRows
  refine List.pairwise_cons.mpr ⟨?_, List.pairwise_append.mpr ⟨?_, ?_, ?_⟩⟩
  · simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_range']
    rintro _ (⟨r, -, rfl⟩ | ⟨_, ⟨i, -, rfl⟩, rfl⟩) <;> left <;> simp
  · refine List.pairwise_map.mpr ((List.pairwise_lt_range (n := A + 1)).imp fun h => ?_)
    left; simp; omega
  · refine List.pairwise_map.mpr ((List.pairwise_lt_range' (s := A + 2) (n := k') (step := 1)
      (by omega)).imp fun h => ?_)
    left; simp; split_ifs <;> omega
  · simp only [List.mem_map, List.mem_range, List.mem_range'_1]
    rintro _ ⟨r, hr, rfl⟩ _ ⟨i, hi, rfl⟩
    left; simp; split_ifs <;> omega

theorem IsHybrid.rows_eq {n A k' : ℕ} {G : LabeledGrid n TorusCol TorusRow}
    (hG : IsHybrid A (k' + 1) 0 G) : G.rows = torusRows A k' := by
  apply List.Perm.eq_of_pairwise _ hG.sorted (torusRows_pairwise A k')
  · exact (List.perm_ext_iff_of_nodup G.rows_nodup (torusRows_nodup A k')).mpr fun x => by
      rw [hG.rows_iff, mem_torusRows]
  · intro a b _ _ h h'
    exact absurd h' (hybLtS_asymm h)

theorem IsHybrid.rpos_winO {n A k' t : ℕ} {G : LabeledGrid n TorusCol TorusRow}
    (hG : IsHybrid A (k' + 1) 0 G) (ht : t < A + 1 + (k' + 1)) : G.rpos (winO A t) = t := by
  have hr := hG.rows_eq
  unfold winO
  split_ifs with h
  · have e : List.range (A + 1) = List.range (t - 1) ++ (t - 1) :: List.range' t (A + 1 - t) := by
      have := range'_split 0 (t - 1) (A + 1 - t)
      rw [show t - 1 + 1 + (A + 1 - t) = A + 1 by omega, show 0 + (t - 1) = t - 1 by omega,
        show t - 1 + 1 = t by omega] at this
      rw [List.range_eq_range', this, List.range_eq_range']
    rw [G.rpos_of_rows_eq (m₁ := rRow 0 :: (List.range (t - 1)).map iRow)
      (m₂ := (List.range' t (A + 1 - t)).map iRow ++ (List.range' (A + 2) k').map rRow)]
    · simp; omega
    · rw [hr, torusRows, e]; simp
  · by_cases h0 : t = 0
    · subst h0
      exact G.rpos_of_rows_eq (m₁ := []) (by rw [hr]; rfl)
    · have e : List.range' (A + 2) k' = List.range' (A + 2) (t - (A + 2)) ++
          t :: List.range' (t + 1) (A + 1 + (k' + 1) - (t + 1)) := by
        have := range'_split (A + 2) (t - (A + 2)) (A + 1 + (k' + 1) - (t + 1))
        rw [show t - (A + 2) + 1 + (A + 1 + (k' + 1) - (t + 1)) = k' by omega,
          show A + 2 + (t - (A + 2)) = t by omega] at this
        exact this
      rw [G.rpos_of_rows_eq (m₁ := rRow 0 :: ((List.range (A + 1)).map iRow ++
        (List.range' (A + 2) (t - (A + 2))).map rRow))
        (m₂ := (List.range' (t + 1) (A + 1 + (k' + 1) - (t + 1))).map rRow)]
      · simp; omega
      · rw [hr, torusRows, e]; simp

theorem winX_zero (A t : ℕ) : winX A 0 t = winO A t := by
  simp [winX, winO, inRow]

/-- **Lemma R-reflect.** A hybrid grid without blocks is obtained from the reflected standard
torus grid by one cyclic permutation of the rows. -/
theorem IsHybrid.toGrid_eq {A k' : ℕ} {G : LabeledGrid (A + 1 + (k' + 1)) TorusCol TorusRow}
    (hG : IsHybrid A (k' + 1) 0 G) :
    G.toGrid = (reflectedDiagram (GridDiagram.torusLink A k')).relabelRows
      (finRotate (A + 1 + (k' + 1))) := by
  have hcols : G.cols = rCols (A + 1 + (k' + 1)) := by
    rw [hG.cols, hybCols]; simp [wordCols]
  have hcol : ∀ i : Fin (A + 1 + (k' + 1)), G.colAt i = rCol i.val := fun i => by
    rw [G.colAt_eq_of_cols hcols]
    simp [rCols, rColsR]
  have hmem : ∀ i : Fin (A + 1 + (k' + 1)), rCol i.val ∈ G.cols := fun i => by
    rw [hcols, mem_rCols]; exact ⟨i.val, i.isLt, rfl⟩
  ext i
  · have hi := i.isLt
    rw [LabeledGrid.toGrid_O_val, hcol, hG.O_eq _ (hmem i), hybO_rCol,
      hG.rpos_winO (by unfold oRes; split_ifs <;> omega)]
    simp only [GridDiagram.relabelRows_O_apply, reflectedDiagram_O,
      GridDiagram.torusLink_O_apply]
    rw [finRotate_val_eq, Fin.val_rev, oRes]
    split_ifs <;> omega
  · have hi := i.isLt
    rw [LabeledGrid.toGrid_X_val, hcol, hG.X_eq _ (hmem i), hybX_rCol, winX_zero,
      hG.rpos_winO (by unfold xRes; split_ifs <;> omega)]
    simp only [GridDiagram.relabelRows_X_apply, reflectedDiagram_X,
      GridDiagram.torusLink_X_apply]
    rw [finRotate_val_eq, Fin.val_rev, finRotate_pow_val _ (by omega), xRes]
    split_ifs <;> omega

/-- A hybrid grid without blocks is related to the reflected standard torus grid. -/
theorem IsHybrid.movesTo_reflectedTorusLink {A k' : ℕ}
    {G : LabeledGrid (A + 1 + (k' + 1)) TorusCol TorusRow} (hG : IsHybrid A (k' + 1) 0 G) :
    (reflectedDiagram (GridDiagram.torusLink A k')).MovesTo G.toGrid := by
  rw [hG.toGrid_eq]
  exact Relation.EqvGen.rel _ _ (GridDiagram.IsMove.cyclicRows (Or.inl rfl))

end OnLeConjecture.KnotTheory
