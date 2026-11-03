/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridMarkedCancelEntry
public import OnLeConjecture.KnotFloer.GridEndpointCleanupRelocate
public import OnLeConjecture.KnotTheory.ExteriorHurwitzWords

/-!
# Comparison facts for the marked factor cleanup

* A grid diagram whose closing arc lies in the bottom row is related by grid moves to its frame
  preparation (`movesTo_framePrep`): a cyclic permutation of the rows followed by an `X`
  stabilization.
* Two frame towers with the same number of blocks, one over the protected grid and one over the
  second factor, give seams related by grid moves (`seam_tower_movesTo`): both are frame towers
  over the same seam, and frame towers relocate to the canonical stack.
* The strand `0` enters the core of a conjugate factor in which it is moved
  (`follow_lt_of_perm_ne`).
* A signed word whose first letter is `σ_0` and whose last letter is `σ_0⁻¹` has a signed word
  grid with its closing arc in the bottom row (`exists_closingRowBottom`).
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.MarkedCancel

open TauCeti OnLeConjecture.KnotTheory SignedGrid BraidWindow LabeledGrid
  OnLeConjecture.KnotFloer.GridFull SignedAdjacentWord

/-! ### The frame preparation -/

/-- **A grid is related to its frame preparation.** -/
theorem movesTo_framePrep {n : ℕ} (G : GridDiagram n) (hG : ClosingRowBottom G) :
    G.MovesTo (framePrep G hG) := by
  obtain ⟨hn, hO, hX⟩ := hG
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  set G' := G.relabelRows (finRotate (d + 1)).symm with hG'
  have h1 : G.MovesTo G' := by
    have e : G = G'.relabelRows (finRotate (d + 1)) := by
      rw [hG', GridDiagram.relabelRows_relabelRows, Equiv.symm_trans_self,
        GridDiagram.relabelRows_refl]
    exact (GridDiagram.IsMove.cyclicRows (Or.inr e)).movesTo
  have hrot : G'.X ⟨0, hn⟩ = Fin.last d := by
    have hX' : G.X ⟨0, hn⟩ = 0 := hX
    simp only [hG', GridDiagram.relabelRows_X, GridState.relabelRows_apply]
    rw [hX', Equiv.symm_apply_eq, finRotate_last]
  have hs := GridDiagram.isXStabilization_stabilizeX G' (Fin.last (d + 1)) 0 ⟨0, hn⟩
    (Or.inl (by rw [finRotate_last]; rfl)) (Or.inr (by
      rw [hrot, Fin.succAbove_zero, Fin.succ_last, finRotate_last]))
  exact h1.trans ((GridDiagram.isStabilization_iff G' _).mpr (Or.inr hs)).movesTo

/-! ### Frame towers on both sides of a seam -/

/-- **Comparison of frame towers in a seam.** -/
theorem seam_tower_movesTo {k a j k' b : ℕ} {H : GridDiagram (k + 1)} (hH : TriplyPrepared H)
    {H' : GridDiagram (k' + 1)} (hHH : FrameTower H j H') {P : GridDiagram (a + 1)}
    (hP : TriplyPrepared P) {E : GridDiagram (b + 1)} (hPE : FrameTower P j E) :
    (connectedSumSeamGrid H' P (hHH.triplyPrepared hH).2.2 hP.1).MovesTo
      (connectedSumSeamGrid H E hH.2.2 (hPE.triplyPrepared hP).1) := by
  have h1 := hHH.seam_left hH P hP.1
  have h2 := hPE.seam_right hP H hH.2.2
  obtain ⟨b₁, Y₁, hY₁, m₁⟩ := h1.exists_canonStack
  obtain ⟨b₂, Y₂, hY₂, m₂⟩ := h2.exists_canonStack
  exact m₁.trans ((movesTo_of_sigma_eq (hY₁.unique hY₂)).trans m₂.symm)

/-! ### Strands and permutations -/

theorem adjacentSwap_val {m : ℕ} (a : Fin (m - 1) × ℤˣ) (x : Fin m) :
    (adjacentSwap a.1 x).val = swapAt a x.val := by
  rw [adjacentSwap_apply_val]
  rfl

theorem follow_eq_perm_inv {m : ℕ} : ∀ (u : SignedAdjacentWord m) (x : Fin m),
    follow x.val u = ((permutation u)⁻¹ x).val
  | [], x => by simp [follow_nil]
  | a :: u, x => by
    have ih := follow_eq_perm_inv u (adjacentSwap a.1 x)
    rw [adjacentSwap_val] at ih
    change follow (swapAt a x.val) u = _
    rw [ih, permutation_cons, mul_inv_rev, Equiv.Perm.mul_apply, adjacentSwap_inv]

theorem perm_fix_of_not_touch {m : ℕ} : ∀ (η : SignedAdjacentWord m) (x : Fin m),
    (∀ b ∈ η, b.1.val ≠ x.val ∧ b.1.val + 1 ≠ x.val) → permutation η x = x
  | [], _, _ => by simp
  | b :: η, x, h => by
    rw [permutation_cons, Equiv.Perm.mul_apply,
      perm_fix_of_not_touch η x (fun c hc => h c (List.mem_cons_of_mem _ hc))]
    apply Fin.ext
    rw [adjacentSwap_val]
    obtain ⟨h1, h2⟩ := h b (List.mem_cons_self ..)
    exact swapAt_of_not_occ h1 h2

/-- **The strand `0` enters the core.** If the conjugate `A η A⁻¹` moves the strand `0` and every
letter of `η` lies below `a`, then the strand `0` reaches a strand below `a` through `A`. -/
theorem follow_lt_of_perm_ne {m : ℕ} (A η : SignedAdjacentWord m) {a : ℕ}
    (hη : ∀ b ∈ η, b.1.val + 2 ≤ a) (h0 : 0 < m)
    (hz : (conjugateWord A η).permutation ⟨0, h0⟩ ≠ ⟨0, h0⟩) : follow 0 A < a := by
  by_contra hlt
  apply hz
  rw [permutation_conjugateWord, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  have hf := follow_eq_perm_inv A ⟨0, h0⟩
  simp only at hf
  rw [perm_fix_of_not_touch η _ (fun b hb => by have := hη b hb; constructor <;> omega)]
  rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]

/-! ### A signed word grid with the closing arc in the bottom row -/

section Closing

/-- A row with a strictly smallest key in a sorted list of rows is the bottom row. -/
theorem rpos_eq_zero_of_min {n : ℕ} {C R : Type*} [DecidableEq R] (G : LabeledGrid n C R)
    {f : R → ℕ} (hs : G.rows.Pairwise (fun a b => f a ≤ f b)) {x : R} (hx : x ∈ G.rows)
    (hmin : ∀ y ∈ G.rows, y ≠ x → f x < f y) : G.rpos x = 0 := by
  unfold LabeledGrid.rpos
  have hlen : 0 < G.rows.length := List.length_pos_of_mem hx
  by_contra hne
  have hb0 : G.rows.idxOf (G.rows[0]'hlen) = 0 := G.rows_nodup.idxOf_getElem 0 hlen
  have hbx : G.rows[0]'hlen ≠ x := fun e => hne (by rw [← e, hb0])
  have := idxOf_lt_of_level hs hx (List.getElem_mem hlen) (hmin _ (List.getElem_mem hlen) hbx)
  omega

variable {m : ℕ}

/-- The closing arc of a word that starts with `σ_0` and ends with `σ_0⁻¹` arrives at the middle
corner of the first letter. -/
theorem sM_last_eq (v : SignedAdjacentWord m) (hv0 : 0 < v.length) (a₀ : Fin (m - 1))
    (ha₀ : a₀.val = 0) (hfst : v[0]'hv0 = (a₀, 1)) (hlst : v[v.length - 1]'(by omega) = (a₀, -1)) :
    sM v (⟨v.length - 1, by omega⟩, 2) = (⟨0, hv0⟩, 0) := by
  apply sM_eq_of_spec _ _ _ (show (2 : Fin 3) ≠ 0 by decide)
  · simp only [SignedAdjacentWord.xHeight2, SignedAdjacentWord.oHeight2]
    rw [hfst, hlst]
    simp [signedXHeight2, signedOHeight2, ha₀]
  · right
    refine ⟨Nat.zero_le _, fun k _ => ⟨Nat.zero_le _, ?_⟩⟩
    change k.val ≤ _ - 1
    have := k.isLt; omega

/-- The key of the closing-arc grid: the closing arc first, then the admissible key. -/
def closeKey (v : SignedAdjacentWord m) (hv0 : 0 < v.length) (p : Fin v.length × Fin 3) : ℕ :=
  if p = (⟨v.length - 1, by omega⟩, 2) then 0 else admKey v p + 1

theorem closeKey_last (v : SignedAdjacentWord m) (hv0 : 0 < v.length) :
    closeKey v hv0 (⟨v.length - 1, by omega⟩, 2) = 0 := if_pos rfl

theorem closeKey_other (v : SignedAdjacentWord m) (hv0 : 0 < v.length)
    {p : Fin v.length × Fin 3} (hp : p ≠ (⟨v.length - 1, by omega⟩, 2)) :
    closeKey v hv0 p = admKey v p + 1 := if_neg hp

theorem closeKey_mono (v : SignedAdjacentWord m) (hv0 : 0 < v.length) (a₀ : Fin (m - 1))
    (ha₀ : a₀.val = 0) (hlst : v[v.length - 1]'(by omega) = (a₀, -1)) :
    ∀ a b, v.oHeight2 a < v.oHeight2 b → closeKey v hv0 a < closeKey v hv0 b := by
  intro a b h
  have hlo : v.oHeight2 (⟨v.length - 1, by omega⟩, 2) = 0 := by
    simp only [SignedAdjacentWord.oHeight2]; rw [hlst]; simp [signedOHeight2, ha₀]
  unfold closeKey
  split_ifs with h1 h2 h2
  · subst h1; subst h2; exact absurd h (lt_irrefl _)
  · omega
  · subst h2; rw [hlo] at h; omega
  · have := admKey_mono v a b h; omega

/-- **A signed word grid with the closing arc in the bottom row.** -/
theorem exists_closingRowBottom (v : SignedAdjacentWord m) (hv0 : 0 < v.length)
    (a₀ : Fin (m - 1)) (ha₀ : a₀.val = 0) (hfst : v[0]'hv0 = (a₀, 1))
    (hlst : v[v.length - 1]'(by omega) = (a₀, -1)) :
    ∃ G : GridDiagram (v.length * 3), IsSignedWordGrid v G ∧ ClosingRowBottom G := by
  have hmono := closeKey_mono v hv0 a₀ ha₀ hlst
  have hmin : (sCornerGrid v (closeKey v hv0)).rpos (⟨v.length - 1, by omega⟩, 2) = 0 := by
    refine rpos_eq_zero_of_min (sCornerGrid v (closeKey v hv0)) (sRows_sorted v _)
      (mem_sRows v _ _) (fun y _ hy => ?_)
    rw [closeKey_last, closeKey_other v hv0 hy]; omega
  have hcol_last : finProdFinEquiv.symm (⟨v.length * 3 - 1, by omega⟩ : Fin (v.length * 3)) =
      (⟨v.length - 1, by omega⟩, 2) := by
    rw [Equiv.symm_apply_eq]; apply Fin.ext; exact (fpe_lastCorner v hv0).symm
  have hcol_zero : finProdFinEquiv.symm (⟨0, by omega⟩ : Fin (v.length * 3)) =
      ((⟨0, hv0⟩, 0) : Fin v.length × Fin 3) := by
    rw [Equiv.symm_apply_eq]; apply Fin.ext; exact (fpe_zero_corner v hv0).symm
  have hsM := sM_last_eq v hv0 a₀ ha₀ hfst hlst
  refine ⟨(sCornerGrid v (closeKey v hv0)).toGrid, sCornerGrid_signed v _ hmono, by omega, ?_, ?_⟩
  · apply Fin.ext
    rw [LabeledGrid.toGrid_O_val, sCornerGrid_colAt, hcol_last]
    exact hmin
  · apply Fin.ext
    rw [LabeledGrid.toGrid_X_val, sCornerGrid_colAt, hcol_zero]
    change (sCornerGrid v (closeKey v hv0)).rpos ((sM v).symm (⟨0, hv0⟩, 0)) = 0
    rw [← hsM, Equiv.symm_apply_apply]
    exact hmin

end Closing

end OnLeConjecture.KnotTheory.MarkedCancel
